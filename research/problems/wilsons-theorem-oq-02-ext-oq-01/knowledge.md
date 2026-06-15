# wilsons-theorem-oq-02-ext-oq-01 — Two-Involution Trick for General Finite Abelian Groups

## Problem

OQ-01 of `wilsons-theorem-oq-02-ext`:

> Can the two-involution trick be formalized as a **general theorem about finite
> abelian groups**, rather than only the unit group `(ZMod n)ˣ`?

**Answer: yes**, and the general statement is strictly more elementary than the
already-proven `(ZMod n)ˣ` specialization.

## The general Gauss-Wilson theorem

Let `G` be a finite abelian group and `S = {x ∈ G : x² = 1}`. Then:

1. **Pairing.** `∏_{x∈G} x = ∏_{x∈S} x`. (Pair each `x ∉ S` with `x⁻¹ ≠ x`;
   already proven generally as `WilsonsTheoremOQ02Ext.prod_eq_prod_sq_eq_one`.)
2. **Structure.** `S = ker(x ↦ x²)` is an elementary abelian 2-group, so
   `|S| = 2^r` for `r =` the 2-rank. In particular `|S| ∈ {1,2,4,8,…}`,
   never `3`.
3. **Trichotomy.**
   - `|S| = 1` (`r = 0`): `∏ G = 1`.
   - `|S| = 2` (`r = 1`): `S = {1, t}`, `∏ G = t` (the unique involution).
   - `|S| ≥ 4` (`r ≥ 2`): `∏ G = 1`, by the **two-involution trick**.

Equivalently: **the product of all elements of a finite abelian group is the
unique element of order two if one exists, and `1` otherwise.**

## Key ORIENT insight (why this is the right generalization)

The companion file proves the `(ZMod n)ˣ` case in
`prod_units_one_of_not_cyclic_ext` (`WilsonsTheoremOQ02Ext.lean:362-436`).
Reading that proof line-by-line:

- Line **373** is the *only* `(ZMod n)`-specific step: it derives
  `3 ≤ |S|` from `¬ IsCyclic (ZMod n)ˣ` via `GaussWilsonNonCyclic`
  (CRT splitting + the `n = 2^k` explicit `2^{k-1}+1` construction).
- **Every line from `prod_eq_prod_sq_eq_one` (line 370) onward** is already
  written for an arbitrary `[CommGroup G] [Fintype G] [DecidableEq G]`:
  picking `c, d ∈ S \ {1}` distinct, building the FPF involutions
  `x ↦ cx`, `x ↦ cdx`, applying `prod_involution_const`, and concluding
  `c^{|S|/2} = (cd)^{|S|/2} ⟹ d^{|S|/2} = 1 ⟹ ∏S = c^{|S|/2} = 1`.

So the general theorem is obtained by **taking `3 ≤ |S|` as a hypothesis** and
copying the proven proof body. It *sheds* all of `GaussWilsonNonCyclic`
(the CRT and `2^k` case analysis) — the hardest part of the original — because
that machinery only existed to translate `¬IsCyclic` into the cardinality bound.

## Mathlib gap (honesty check)

Mathlib v4.26.0 has only the **field-units** case:
`FiniteField.prod_univ_units_id_eq_neg_one` (the engine behind
`ZMod.wilsons_lemma`). There is **no** general finite-abelian-group
"product = unique involution, else 1" theorem. The OQ is genuine.
(Classical reference: P. L. Clark, *Wilson's Theorem: An Algebraic Approach*.)

## Deliverables this session (ACT, build-pending)

New file `proofs/Proofs/WilsonsTheoremOQ02ExtOQ01.lean` (0 sorries, 0 axioms):

| theorem | statement |
|---|---|
| `prod_eq_one_of_three_le_card_sqrt_one` | `3 ≤ \|{x:x²=1}\|` ⇒ `∏ G = 1` (heart) |
| `prod_eq_one_of_no_involution` | no element of order 2 ⇒ `∏ G = 1` |
| `prod_eq_unique_involution` | unique `t` of order 2 ⇒ `∏ G = t` |
| `prod_eq_one_or_unique_involution` | full characterization |

The heart theorem reuses the public `WilsonsTheoremOQ02Ext` lemmas
(`prod_eq_prod_sq_eq_one`, `prod_involution_const`, `mul_sq_eq_one`) and a local
copy of the (private) `mul_involution_on_sq_eq_one` helper. Its proof body is a
near-verbatim transcription of the proven `(ZMod n)ˣ` proof with `(ZMod n)ˣ → G`
and the cardinality bound as a hypothesis.

## Exact verification

`research/verification/wilsons_oq02_ext_oq01_abelian.py` checks the full
trichotomy, the pairing lemma, and `|S|` being a power of two, exactly (integer
group arithmetic, no floats) over **1311 finite abelian groups**:
cyclic `ℤ/n` (`n ≤ 200`), products `ℤ/a × ℤ/b` (`a,b ≤ 30`), selected
higher-rank products (incl. 2-rank 2 and 3), and the unit groups `(ℤ/n)ˣ`
(`n ≤ 200`). **0 mismatches.**

## Blackout note

Docker build and Aristotle were both unavailable this session (Docker
hangs; Aristotle returns 404). The Lean file is therefore **build-pending** and
**not yet registered** in `proofs/Proofs.lean` — registering an unverified file
into the import-based aggregator risks breaking the auto-merged `main` build.

## Next steps

1. On a Docker-up session: build `Proofs.WilsonsTheoremOQ02ExtOQ01`, then add
   `import Proofs.WilsonsTheoremOQ02ExtOQ01` to `proofs/Proofs.lean`.
2. Optionally upstream the general two-involution theorem to Mathlib
   (self-contained, fills a clear gap).
3. Optionally re-derive `gaussWilson_abstract_ext` for `(ZMod n)ˣ` as a
   corollary of the new general theorem.

## Session log

### 2026-06-15 (Session 1, FRESH) — ACT, build-pending
- **Mode**: FRESH. **Outcome**: progress (general theorems written, math verified, build deferred).
- Found Mathlib lacks the general theorem; confirmed the proven `(ZMod n)ˣ` proof is general except for one cardinality-bound step.
- Wrote 4 general `CommGroup` theorems + 1 combined characterization.
- Verified the trichotomy exactly on 1311 groups.
- Did not register in the aggregator (dual-backend blackout).
