import StrataGenerators.HasTypeAGen.Core
import StrataGenerators.HasTypeAGen.TestSupport
import StrataGenerators.RetryGen
import Basalt.PlausibleGen
open Lambda RandomChoice Plausible

/-! Measurement for #64: is a *polymorphic* factory application reachable
    under an `ite` arm / `abs` body / `quant` body? -/

def polyNames : List String := corePolyOps.map Prod.fst
def monoNames : List String := corePartialOps.map Prod.fst

/-- Head of an application spine plus the number of arguments applied. -/
partial def spineHead : LExpr' → Option (LExpr' × Nat)
  | .app () fn _ => match spineHead fn with
                    | some (h, k) => some (h, k + 1)
                    | none => some (fn, 1)
  | _ => none

def isPolyApplied (e : LExpr') : Bool :=
  match spineHead e with
  | some (.op () o _, k) => k > 0 && polyNames.contains o.name
  | _ => false

def isAnyApplied (e : LExpr') : Bool :=
  match spineHead e with
  | some (.op () o _, k) => k > 0 && (polyNames.contains o.name || monoNames.contains o.name)
  | _ => false

partial def existsSub (pred : LExpr' → Bool) : LExpr' → Bool
  | e@(.app () fn arg) => pred e || existsSub pred fn || existsSub pred arg
  | e@(.abs () _ _ b) => pred e || existsSub pred b
  | e@(.ite () c t f) => pred e || existsSub pred c || existsSub pred t || existsSub pred f
  | e@(.eq () a b) => pred e || existsSub pred a || existsSub pred b
  | e@(.quant () _ _ _ tr b) => pred e || existsSub pred tr || existsSub pred b
  | e => pred e

/-- Does `pred` hold strictly underneath an `ite` arm, `abs` body, or `quant`
    body — exactly the position class #64 targets? -/
partial def underBinderOrIte (pred : LExpr' → Bool) : LExpr' → Bool
  | .ite () c t f =>
      existsSub pred t || existsSub pred f
      || underBinderOrIte pred c || underBinderOrIte pred t || underBinderOrIte pred f
  | .abs () _ _ b => existsSub pred b || underBinderOrIte pred b
  | .quant () _ _ _ tr b =>
      existsSub pred tr || existsSub pred b
      || underBinderOrIte pred tr || underBinderOrIte pred b
  | .app () fn arg => underBinderOrIte pred fn || underBinderOrIte pred arg
  | .eq () a b => underBinderOrIte pred a || underBinderOrIte pred b
  | _ => false

def trial (n : Nat) (depth : Nat) (τ : LMonoTy) : IO (Nat × Nat × Nat) := do
  let mut ok := 0
  let mut poly := 0
  let mut anyApp := 0
  for _ in [0:n] do
    let g : Plausible.Gen LExpr' :=
      genLExpr (G := Plausible.Gen) [] corePartialOps corePolyOps [] [] depth τ 3
        (retryGenArg 20)
    let r ← (do let e ← Gen.run (retryGen 500 g) 10; pure (some e))
              |>.toBaseIO
    match r with
    | .ok (some e) =>
      ok := ok + 1
      if underBinderOrIte isPolyApplied e then poly := poly + 1
      if underBinderOrIte isAnyApplied e then anyApp := anyApp + 1
    | _ => pure ()
  return (ok, poly, anyApp)

def main : IO Unit := do
  for (nm, τ) in [("int", LMonoTy.int), ("bool", LMonoTy.bool),
                  ("Sequence int", LMonoTy.seq LMonoTy.int)] do
    for depth in [2, 3] do
      let (ok, poly, anyApp) ← trial 400 depth τ
      IO.println s!"target={nm} depth={depth}: ok={ok}/400  polyApp-under-binder/ite={poly}  anyApp-under-binder/ite={anyApp}"
