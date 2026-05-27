import Strata.DL.Lambda.Denote.LExprAnnotated

open Lambda

/-- Given a polymorphic type scheme `∀α₁...αₙ. body` and a monomorphic target
type, compute the substitution `[α₁ := σ₁, ..., αₙ := σₙ]` such that
`body[αᵢ := σᵢ] = target`, or return `none` if no such substitution exists.

This is used in a generator targeting the `HasType` relation (Hindley-Milner without
let-polymorphism). In that system, operators and variables enter the
derivation with polymorphic schemes via `tvar`/`top`, and are immediately
instantiated to a monomorphic type via `tinst`. A generator fuses these two
steps into a single "GenVarInst"/"GenOpInst" rule: given a generation target
`τ`, scan the context for a variable or operator whose type (a type scheme) can be matched
against `τ`. This function performs that match — it is essentially first-order
pattern matching (not full unification, since `target` is always ground). -/
def matchScheme (typeScheme : LTy) (target : LMonoTy) : Option (List LMonoTy) :=
    match typeScheme with
    | .forAll tyVars body => do
      let assignment ← go tyVars body target {}
      tyVars.mapM assignment.find?
  where
    /-- Traverse `body` and `target` in parallel, building up a
    substitution map from the names of quantified type variables to monomorphic types.
    (The `subst` argument is the substitution that has been accumulated so far.)

    - If `body` is a quantified variable (`ftvar` in `tyVars`),
      and it is not in `subst`, extend `subst` with a new binding.
      Otherwise, just return `subst` as is.
    - If `body` is a free type variable (i.e. `body ∉ tyVars`),
      check that `body` and `target` are syntactically the same
      type identifier.
    - If `body` is a type constructor, check that the
      names of the type constructor matches and recurse
      through argument lists via `goArgs`. -/
    go (tyVars : List TyIdentifier) (body : LMonoTy) (target : LMonoTy)
       (subst : Map TyIdentifier LMonoTy)
        : Option (Map TyIdentifier LMonoTy) :=
      match body, target with
      | .ftvar name, t =>
        if name ∈ tyVars then
          match subst.find? name with
          | none          => some (subst.insert name t)
          | some existing => if existing == t then some subst else none
        else
          if t == .ftvar name then some subst else none

      | .tcons name1 args1, .tcons name2 args2 =>
        if name1 == name2 && args1.length == args2.length then
          goArgs tyVars args1 args2 subst
        else none

      | .bitvec n1, .bitvec n2 =>
        if n1 == n2 then some subst else none

      | _, _ => none

    /-- Fold over two lists `args1`, `args2`, threading the subst through
    each pair. Fails if the lists have different lengths or any pair fails
    to match. Note: this function is defined via mutual recursion with `go` in order
    to satisfy Lean's termination checker. -/
    goArgs (tyVars : List TyIdentifier) (args1 : List LMonoTy) (args2 : List LMonoTy)
      (subst : Map TyIdentifier LMonoTy) : Option (Map TyIdentifier LMonoTy) :=
      match args1, args2 with
      | [], [] => some subst
      | a :: as, b :: bs => do
          let subst' ← go tyVars a b subst
          goArgs tyVars as bs subst'
      | _, _ => none
