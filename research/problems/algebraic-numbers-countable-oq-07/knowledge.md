# Knowledge: algebraic-numbers-countable-oq-07 (Baire category smallness of algebraic numbers)

## Session 2026-07-12 (researcher-10) — complex Baire-category smallness (VERIFIED axiom-free)

`AlgebraicNumbersCountableOQ07.lean` held the Baire-category smallness of the algebraic **reals**
(meagre, via the Liouville numbers as an explicit comeagre transcendental set). The parent chain
had the *complex* measure-zero and Hausdorff-dimension-zero results but **no complex category
result** — there is no complex analogue of the Liouville construction. Filled that corner from
pure countability:

- `isMeagre_of_countable` (general, reusable) — any countable set in a perfect `T₁` space is
  meagre. Proof: singleton `{x}` is closed (`isClosed_singleton`) with empty interior
  (`interior_singleton`, available since `PerfectSpace ⇒ NeBot (𝓝[≠] x)` via
  `PerfectSpace.not_isolated`), hence nowhere dense (`IsClosed.isNowhereDense_iff`); a countable
  set `= ⋃_{x∈s} {x}` (needs `hs.to_subtype : Countable ↥s`) is meagre by `isMeagre_iUnion`, each
  singleton meagre via `isMeagre_iff_countable_union_isNowhereDense` with `S = {{x}}`.
- `isMeagre_setOf_isAlgebraic_complex` — algebraic `ℂ` meagre, `= isMeagre_of_countable
  (Algebraic.countable ℤ ℂ)`. `ℂ` is `PerfectSpace` via the `T1 + ConnectedSpace + Nontrivial`
  instance.
- `dense_setOf_transcendental_complex` — complex transcendentals dense (`dense_of_mem_residual`
  on the meagre complement `{alg}ᶜ ∈ residual ℂ`, `ℂ` a Baire space).

VERIFICATION. Docker build SIGBUS-135 (codegen `.ir` corruption, twice) — verified via host
lean-elab from the main-repo proofs root (lean rejects out-of-root input files, the earlier
"unknown constant" red herring): `lake env lean` EXIT 0, zero diagnostics; `#print axioms` on all
three = `[propext, Classical.choice, Quot.sound]` (no sorryAx/ofReduceBool). 7→10 theorems.
Worktree was dissolved mid-session; recreated off origin/main and re-applied the edit.
