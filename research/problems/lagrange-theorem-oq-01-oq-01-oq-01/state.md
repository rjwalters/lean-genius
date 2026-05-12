# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-10): Survey three approaches to constructing an explicit
non-cyclic group of order `pq` whenever `p | (q-1)`. Settled on
**Approach A** (specialize to `p = 2`, use Mathlib's `DihedralGroup q`)
as the S2 attack target — single PR, ~50 lines Lean, requires only the
stable `DihedralGroup.card` + `DihedralGroup.not_isCyclic` API.

The parent `Proofs/LagrangeTheoremOQ01OQ01.lean` (169 lines, 13 theorems,
0 sorries, 0 axioms) classifies pq-groups via Sylow theory and proves the
universal cyclic statement `pq_unique_when_coprime` when `p ∤ (q-1)`, plus
the conditional non-abelian fact `lagrange_pq_nonabelian_n_p_eq_q` when
`p | (q-1)` (but only assuming `¬ IsCyclic G`). What is *missing* is an
existence witness for the non-cyclic case: an explicit group `G` with
`|G| = p*q` and `¬ IsCyclic G`. This OQ supplies that.

## Active Approach

**Approach A: Specialize to `p = 2`, use `DihedralGroup q`**

For `q` an odd prime, `DihedralGroup q` has cardinality `2*q = p*q` and
is non-cyclic (`q ≠ 1`). Mathlib provides both facts at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```lean
theorem DihedralGroup.card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n
theorem DihedralGroup.not_isCyclic (h1 : n ≠ 1) : ¬ IsCyclic (DihedralGroup n)
```

The `NeZero q` instance follows from `q` prime (positive); `q ≠ 1` from
`Nat.Prime.one_lt`. The condition `2 | (q - 1)` follows from `q` being
odd (which holds for any prime `q ≠ 2`).

## Blockers

None mathematical.

**Practical**: the `proofs/.lake` symlink in researcher worktrees points
to itself (see `feedback_researcher_lake_symlink_broken.md`), forcing any
Docker build to fresh-clone Mathlib (~25 min). S1 is doc-only, so unaffected.
S2 will need a build verification but can be deferred to a follow-up
`*-prep` PR per the precedent in
`bezout-identity-oq-01-oq-01-oq-01-oq-01` (PR #17990) and
`cube-root-3-irrational-oq-04` (PR #17718).

## Next Action

**S2 (any researcher)**: Implement Approach A in a new file
`proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01.lean`. Three deliverables:

1. **Main existence theorem** (~15 lines):
   ```lean
   import Mathlib
   import Proofs.LagrangeTheoremOQ01OQ01

   namespace LagrangeOQ01OQ01OQ01

   /-- When `q` is an odd prime, `DihedralGroup q` is a non-cyclic group
       of order `2q`. This exhibits a non-cyclic witness in the case
       `p = 2`, `q` odd prime (where `p | q - 1` holds because `q - 1` is
       even). -/
   theorem exists_noncyclic_of_order_two_mul_odd_prime
       {q : ℕ} (hq : Nat.Prime q) (hq_ne_two : q ≠ 2) :
       ∃ (G : Type) (_ : Group G) (_ : Fintype G),
         Fintype.card G = 2 * q ∧ ¬ IsCyclic G := by
     haveI : NeZero q := ⟨hq.ne_zero⟩
     refine ⟨DihedralGroup q, inferInstance, inferInstance,
             DihedralGroup.card, ?_⟩
     exact DihedralGroup.not_isCyclic (fun h => hq.one_lt.ne' h.symm)
   ```

2. **Concrete corollaries** matching parent's `order_*_non_unique` lemmas
   (~30 lines, one per case):
   ```lean
   /-- Order 6 = 2 × 3: a non-cyclic group exists (S₃ ≅ DihedralGroup 3). -/
   theorem exists_noncyclic_of_order_6 :
       ∃ (G : Type) (_ : Group G) (_ : Fintype G),
         Fintype.card G = 6 ∧ ¬ IsCyclic G :=
     exists_noncyclic_of_order_two_mul_odd_prime
       (by norm_num : Nat.Prime 3) (by norm_num)

   /-- Order 10 = 2 × 5: a non-cyclic group exists (DihedralGroup 5). -/
   theorem exists_noncyclic_of_order_10 : ... := ...

   /-- Order 14 = 2 × 7: a non-cyclic group exists (DihedralGroup 7). -/
   theorem exists_noncyclic_of_order_14 : ... := ...

   /-- Order 22 = 2 × 11: a non-cyclic group exists (DihedralGroup 11). -/
   theorem exists_noncyclic_of_order_22 : ... := ...
   ```

3. **Gallery entry** at `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/`
   (meta.json + annotations.json + index.ts; ~80 lines). After S2 lands,
   update `lagrange-theorem-oq-01-oq-01` parent meta.json's
   `relatedProofs` / `openQuestions` to mark this OQ as resolved (at least
   for the `p = 2` specialization).

**Estimated effort for S2**: 1 session, single PR, ~50 lines of new Lean
(1 main theorem + 4 corollaries + namespace boilerplate; no helper
lemmas needed because `DihedralGroup.card` and `DihedralGroup.not_isCyclic`
are both direct).

## Future Iterations (Deferred)

**S3+ (Approach B): general `p, q` with `p | (q-1)`**. Construct
`ZMod q ⋊[φ] ZMod p` where `φ : ZMod p →* MulAut (ZMod q)` is non-trivial.
Required pieces:

- (S3a) Show `(ZMod q)ˣ` is cyclic of order `q-1` for `q` prime
  (Mathlib has `ZMod.unitsCyclic` or derive via `IsCyclic_isMaximalOrder`).
- (S3b) Extract an element of order `p` from `(ZMod q)ˣ` using
  `p | q - 1 = Nat.card (ZMod q)ˣ` + cyclic-group divisor existence
  (`IsCyclic.exists_orderOf_eq` or similar).
- (S3c) Lift to a non-trivial hom `φ : ZMod p →* MulAut (ZMod q)`.
- (S3d) Assemble `ZMod q ⋊[φ] ZMod p`, verify `Nat.card = p * q`,
  prove `¬ IsCyclic`.

~200 lines total, 3-4 sessions, multi-PR.

**S4+ (Optional gallery enhancement)**: Add explicit multiplication-table
examples for order-21 and order-55 non-abelian groups as supplementary
content. ~50 lines per case.

## Attempt Counts

- Total attempts: 1 (S1 survey)
- Current approach attempts: 0 (no Lean changes yet)
- Approaches tried: 0 (3 surveyed: A=DihedralGroup q for p=2,
  B=ZMod q ⋊ ZMod p in general, C=direct small-case construction)

## Open files

- `problem.md` — Full problem statement, three approaches, sub-lemma list,
  Mathlib API map.
- `knowledge.md` — S1 session note: parent context, API verification at
  pinned rev, edge-case analysis.

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/problem.md` (~280 lines)
- `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md` (this file)
- `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/knowledge.md` (S1 session note)
- `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-01.json` (research index entry)
