# wilsons-theorem-oq-02-ext-oq-01

**Open question (from parent `wilsons-theorem-oq-02-ext`):**
Can the two-involution trick be formalized as a general theorem about finite
abelian groups — that ∏ G = 1 whenever |{x ∈ G : x² = 1}| ≥ 3 — using abstract
group theory?

**Answer: YES.** Formalized as `prod_eq_one_of_card_sq_eq_one_ge_three`.

## Summary

The parent file `WilsonsTheoremOQ02Ext.lean` already contained every piece of
the two-involution machinery in fully generic `CommGroup G` form:

- `prod_eq_prod_sq_eq_one` : ∏ G = ∏ {x | x²=1} (pair each non-involution with
  its distinct inverse via `Finset.prod_involution`).
- `prod_involution_const`  : FPF involution with constant pair product `c` on `S`
  gives ∏ S = c^(|S|/2).
- `mul_involution_on_sq_eq_one` : `x ↦ cx` is such an involution on `{x|x²=1}`.

The proof `prod_units_one_of_not_cyclic_ext` used these on `(ZMod n)ˣ`, but its
actual argument (steps 3–9) only consumed the hypothesis `3 ≤ |S|`. So the OQ is
answered by *lifting that hypothesis into the statement* and dropping the
`(ZMod n)ˣ`-specific derivation of `|S| ≥ 3`.

## What was done (Session 1, 2026-06-15, FRESH → ACT)

- Added `prod_eq_one_of_card_sq_eq_one_ge_three`
  (`proofs/Proofs/WilsonsTheoremOQ02Ext.lean:376`):
  for any `[CommGroup G] [Fintype G] [DecidableEq G]`, `3 ≤ |{x | x²=1}|` ⟹
  `∏ x : G, x = 1`. Proof mirrors the original steps 3–9 verbatim with `G`
  generic; `|S|≥3` is now a hypothesis instead of being derived.
- Refactored `prod_units_one_of_not_cyclic_ext` into a one-line corollary that
  feeds `card_sq_eq_one_ge_three_of_not_cyclic_zmod` to the abstract theorem.
  Net: removed ~55 lines of duplicated argument.
- Verifier `research/scripts/verify_two_involution_abstract.py`: exact-integer
  sweep over 25 finite abelian groups (cyclic + ranks 2–4). All pass the full
  trichotomy:
    - |S| ≥ 3 ⟹ ∏ = e   (11 groups, e.g. Z₂×Z₂, Z₂³, Z₂×Z₂×Z₄)
    - |S| = 2 ⟹ ∏ = the unique involution
    - |S| = 1 ⟹ ∏ = e
  and |S| is always a power of two.

## Key facts

- The hypothesis `|S| ≥ 3` is **essential** and cannot be replaced by
  "non-cyclic": Z₃×Z₃ is non-cyclic but has |S| = 1 (odd order ⇒ only the
  identity squares to 1). The parent file's NOTE at the specialized lemma is
  correct; the verifier reproduces this (`G=Z[3,3] |S|=1`).
- Because S is elementary abelian 2-torsion, |S| is a power of 2, so `|S| ≥ 3`
  is the same as `|S| ≥ 4`. The proof does not need this — it works directly
  from `|S| ≥ 3` and `|S|/2` via `prod_involution_const`.

## Status

- 0 sorries, 0 axioms (file unchanged in those counts).
- Build-pending: Docker build wrapper unavailable this session (host blackout);
  Aristotle not needed (no sorries). The new proof is a near-mechanical
  abstraction of an already-compiling block, so compile risk is low.

## Next steps (follow-ups, not required)

- OQ-02 of the parent (Gauss–Wilson for rings of integers 𝒪_K) is a separate,
  much harder problem — still open in the pool as a distinct slug.
- Possible micro-follow-up: package the full trichotomy
  (∏ G = e if |S|≠2, else the unique involution) as a single characterization
  theorem; would subsume both the cyclic (∏=−1) and non-cyclic (∏=1) ZMod cases
  uniformly. Low novelty; only worth it if it simplifies downstream use.
