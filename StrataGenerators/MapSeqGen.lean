import StrataGenerators.HasTypeAGen.Defs

open Lambda RandomChoice

/-!
# Bespoke `Sequence` and `Map` literal generators (issue #5)

Strata Core has no sequence/map literal syntax: the only way to build a
non-empty `Sequence a` or `Map k v` is a chain of factory calls. The baseline
`genLExprBase` arms for `.seq`/`.map` (`HasTypeAGen/Core.lean`) only ever pick a
bound variable, a free variable, an operator, or an `ite`, so a generated value
of either type is in practice an *opaque variable*. Every interesting property
about these datatypes is then vacuous — much like the 599/600 vacuous
`ANFEncoder` samples noted in issue #36.

This module closes that gap the way issue #5 proposes: draw a plain Lean list
(or list of key/value pairs), then desugar it into the chain of factory calls
that denotes it.

## The two chain shapes

Both are pinned to what `Strata/Languages/Core/Factory.lean` actually declares,
which is *not* what issue #5 assumed:

- **Sequences are built by snoc onto empty.** There is no `Sequence.insert`;
  `SeqOpKind` is `Length | Empty | Append | Select | Build | Update | Contains |
  Take | Drop`. The builder is `Sequence.build : ∀a. (Sequence a, a) → Sequence a`,
  which appends *one* element to the end (`SeqModel.lean` models it as
  `s ++ [v]`). So `[10, 20]` becomes

  ```
  Sequence.build(Sequence.build(Sequence.empty<int>(), 10), 20)
  ```

  Note the element order: `foldl` over the list, so the head of the list ends up
  at index `0`, matching `SeqModel`'s `List` mapping.

- **Maps are built by update onto a constant map.** There is no empty map — the
  base case is `mapConst : ∀k v. v → Map k v`, which maps *every* key to a
  default. So `[(1, 10), (2, 20)]` with default `d` becomes

  ```
  update(update(mapConst<int>(d), 1, 10), 2, 20)
  ```

  Because later updates win, duplicate keys in the drawn list are resolved
  last-write-wins; `mapLiteralEntries` reflects that so the oracle agrees.

## Why the annotations are explicit

Every `.op` node is stamped with its *instantiated* monomorphic type, built with
`LMonoTy.mkArrow'` — the same builder `factoryOps`/`factoryPolyOps` use, and the
form `OpsConsistent`/`OpsConsistentR` canonicalize operators to. This keeps
literals op-consistent by construction, so they need no reconciliation to be
accepted by the annotation-driven typing relation, and it is what lets the
printer recover the type arguments for `Sequence.empty<A>` / `mapConst<K>`
(`FormatCore.lean` reads them back off the op's annotation; an unannotated op
prints as the `$__unknown_type` placeholder instead).
-/

namespace StrataGenerators.MapSeqGen

-- ── Sequence literals ────────────────────────────────────────────────

/-- The `Sequence.empty` op node at element type `τ`, annotated `Sequence τ`.

    `Sequence.empty` is nullary, so the annotation is the bare result type
    rather than an arrow. The printer needs exactly this annotation to emit the
    explicit type argument in `Sequence.empty<τ>()`. -/
def seqEmptyOp (τ : LMonoTy) : LExpr' :=
  .op () ⟨"Sequence.empty", ()⟩ (some (.seq τ))

/-- The `Sequence.build` op node at element type `τ`, annotated
    `(Sequence τ, τ) → Sequence τ`. -/
def seqBuildOp (τ : LMonoTy) : LExpr' :=
  .op () ⟨"Sequence.build", ()⟩
    (some (LMonoTy.mkArrow' (.seq τ) [.seq τ, τ]))

/-- Desugar `elems` into a snoc-chain of `Sequence.build` calls over
    `Sequence.empty`. The head of `elems` lands at index `0`.

    `[]` yields bare `Sequence.empty<τ>()`, which is a legitimate (if
    uninteresting) sequence literal; callers wanting non-empty sequences should
    draw a non-empty list — see `genSeqLiteral`. -/
def seqLiteralOfList (τ : LMonoTy) (elems : List LExpr') : LExpr' :=
  elems.foldl
    (fun acc v => .app () (.app () (seqBuildOp τ) acc) v)
    (seqEmptyOp τ)

/-- Generate a `Sequence τ` literal of length `n` whose elements come from
    `genElem`. Used with `n ≥ 1` this is the generator issue #5 asks for: it
    makes properties over *non-empty* sequences reachable with high probability
    instead of essentially never. -/
def genSeqLiteralOfLength [Gen G] (τ : LMonoTy) (genElem : G LExpr')
    (n : Nat) : G LExpr' := do
  let elems ← (List.range n).mapM (fun _ => genElem)
  pure (seqLiteralOfList τ elems)

/-- Generate a `Sequence τ` literal of length `1 … maxLen` (clamped to at least
    1, so the result is always non-empty). -/
def genSeqLiteral [Gen G] (τ : LMonoTy) (genElem : G LExpr')
    (maxLen : Nat := 3) : G LExpr' := do
  let n ← chooseNat 1 (max 1 maxLen) (Nat.le_max_left 1 maxLen)
  genSeqLiteralOfLength τ genElem n

-- ── Map literals ─────────────────────────────────────────────────────

/-- The `mapConst` op node at key type `κ` and value type `ν`, annotated
    `ν → Map κ ν`.

    The key type is *not* inferable from the single value argument, which is why
    the surface syntax is `mapConst<K>(v)` and why the printer recovers `K` from
    this annotation (`FormatCore.lean`'s `lappToExpr`). An unannotated
    `mapConst` prints its key type as `$__unknown_type`. -/
def mapConstOp (κ ν : LMonoTy) : LExpr' :=
  .op () ⟨"mapConst", ()⟩ (some (LMonoTy.mkArrow' (.map κ ν) [ν]))

/-- The Map `update` op node at key type `κ` and value type `ν`, annotated
    `(Map κ ν, κ, ν) → Map κ ν`. -/
def mapUpdateOp (κ ν : LMonoTy) : LExpr' :=
  .op () ⟨"update", ()⟩
    (some (LMonoTy.mkArrow' (.map κ ν) [.map κ ν, κ, ν]))

/-- Desugar `entries` into a chain of Map `update` calls over `mapConst<κ>(dflt)`.

    Updates are applied left to right, so on duplicate keys the *last* entry
    wins. `mapLiteralEntries` computes the same resolution, so an oracle can
    predict what the literal denotes without re-deriving it. -/
def mapLiteralOfList (κ ν : LMonoTy) (dflt : LExpr')
    (entries : List (LExpr' × LExpr')) : LExpr' :=
  entries.foldl
    (fun acc (k, v) =>
      .app () (.app () (.app () (mapUpdateOp κ ν) acc) k) v)
    (.app () (mapConstOp κ ν) dflt)

/-- The effective key→value bindings of `mapLiteralOfList … entries`, i.e.
    `entries` with earlier duplicates of a key dropped (last write wins).

    Kept next to the builder so the two cannot drift: any oracle predicting
    `select(literal, k)` should consult this rather than `entries` directly. -/
def mapLiteralEntries (entries : List (LExpr' × LExpr')) :
    List (LExpr' × LExpr') :=
  -- Fold from the right, keeping the first occurrence seen (which is the
  -- *last* in left-to-right order) for each key.
  (entries.reverse.foldl
    (fun acc (k, v) => if acc.any (fun (k', _) => k' == k) then acc else (k, v) :: acc)
    []).reverse

/-- Generate a `Map κ ν` literal with `n` updates over a constant map, drawing
    keys from `genKey` and values (and the constant-map default) from
    `genVal`. -/
def genMapLiteralOfSize [Gen G] (κ ν : LMonoTy)
    (genKey genVal : G LExpr') (n : Nat) : G LExpr' := do
  let dflt ← genVal
  let entries ← (List.range n).mapM (fun _ => do
    let k ← genKey
    let v ← genVal
    pure (k, v))
  pure (mapLiteralOfList κ ν dflt entries)

/-- Generate a `Map κ ν` literal with `1 … maxSize` updates (clamped to at least
    1, so the result is never a bare constant map). -/
def genMapLiteral [Gen G] (κ ν : LMonoTy)
    (genKey genVal : G LExpr') (maxSize : Nat := 3) : G LExpr' := do
  let n ← chooseNat 1 (max 1 maxSize) (Nat.le_max_left 1 maxSize)
  genMapLiteralOfSize κ ν genKey genVal n

end StrataGenerators.MapSeqGen
