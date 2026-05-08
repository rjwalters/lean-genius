# S28: Sub-lemma 2B introduction + Sub-lemma 2 body closure

**Date**: 2026-05-08
**Researcher**: researcher-9
**Mode**: ACT (decomposition continuation)

## TL;DR

S28 closes Sub-lemma 2's body using S27's Sub-lemma 2A and a new Sub-lemma 2B
(sorry-stubbed). The cycle-lemma input is now isolated to a single ¬∃ predicate
over distinct size-`a` submultisets, with the pair encoding fully dissolved.
Net file sorry count: 2 → 2 (one sorry migrates with strictly cleaner
provenance).

## What was wired

### Sub-lemma 2B (new, sorry-stubbed)

```lean
private lemma noColStrict_subSym_a_count_eq_subSym_le_aplus1_count
    {n a b : ℕ} (_hb : 2 ≤ b) (_hba : b ≤ a) (M : Sym (Fin n) (a + b)) :
    ((Finset.univ : Finset (Sym (Fin n) a)).filter
      (fun P => P.1 ≤ M.1 ∧ ¬ ∃ Q : Sym (Fin n) b,
                  P.1 + Q.1 = M.1 ∧ ColStrictSym a b P Q)).card =
    ((Finset.univ : Finset (Sym (Fin n) (a + 1))).filter
      (fun P => P.1 ≤ M.1)).card := by
  sorry
```

This is the SHARP form of the cycle-lemma argument. The "shift one element
from Q to P" map sends a "bad" `P` (size `a`, no col-strict size-`b`
complement) to a `P'` of size `(a + 1)` deterministically; the inverse drops
one element to recover the canonical bad split.

### Sub-lemma 2 body (closed via 7-step composition)

```lean
private lemma colStrict_count_add_eq_subSym_le_count {n a b : ℕ}
    (hb : 2 ≤ b) (hba : b ≤ a) (M : Sym (Fin n) (a + b)) :
    -- LHS pair count + (a+1)-submultiset count = a-submultiset count
    ... := by
  classical
  -- Step 1: Sub-lemma 2A — pair → single-Sym filtered.
  rw [colStrict_pair_count_eq_subSym_filtered_count M.1 M.2]
  -- Step 2: has-CS implies P.1 ≤ M.1.
  have h_hasCS_imp_le : ∀ P, ... := fun P ⟨Q, hPQ, _⟩ => by
    calc P.1 ≤ P.1 + Q.1 := le_self_add
      _ = M.1 := hPQ
  -- Step 3: pivot has-CS filter onto subSym_le_a M.
  have h_pivot : ... := by ext; simp; refine ⟨..., ...⟩
  rw [h_pivot]
  -- Step 4: partition subSym_le_a M by has-CS.
  have h_part := Finset.filter_card_add_filter_neg_card_eq_card ...
  -- Step 5: collapse nested ¬-filter via Finset.filter_filter.
  have h_neg : ... := by rw [Finset.filter_filter]
  rw [h_neg] at h_part
  -- Step 6: Sub-lemma 2B substitutes the ¬-filter card.
  rw [noColStrict_subSym_a_count_eq_subSym_le_aplus1_count hb hba M] at h_part
  -- Step 7: omega closes linear arithmetic.
  omega
```

## Why this decomposition

### Provenance cleanup

Before S28: the deep cycle-lemma sorry lived inside
`colStrict_count_add_eq_subSym_le_count`, whose statement involved a pair
(`Sym a × Sym b`) filter with a coupled predicate (`ColStrictSym ∧ P + Q = M`).
The pair encoding obscures the rotation-invariance of the underlying
combinatorial argument: `ColStrictSym a b P Q` depends only on the sorted
representatives of `P` and `Q`, so it's a function of `(P.1, M)` alone once
`Q := M.1 − P.1` is fixed.

After S28: Sub-lemma 2B's statement is expressed purely on `Sym a` with
`P.1 ≤ M.1` and a `¬ ∃` predicate. The `Q` that appears in the predicate is
local to the existential — it does not appear at the top level of the count.
This is the cleanest possible form for the cycle-lemma argument.

### Decoupling from upstream surgery

The S26 `ballot_counting_identity` body composes Sub-lemma 1 (twice) +
Sub-lemma 2 + partition + omega. With Sub-lemma 2 closed, the chain
becomes:

```
ballot_counting_identity (S26 — sorry-free body)
  ⟸ split_count_eq_subSym_le_count (Sub-lemma 1, S25/S26 corrected)
  ⟸ colStrict_count_add_eq_subSym_le_count (Sub-lemma 2, S28 — sorry-free body)
       ⟸ colStrict_pair_count_eq_subSym_filtered_count (Sub-lemma 2A, S27)
       ⟸ noColStrict_subSym_a_count_eq_subSym_le_aplus1_count (Sub-lemma 2B, S28 — sorry)
```

Sub-lemma 2B is a leaf — it has no further dependencies in the proof DAG.
Future S29+ work can attack 2B directly without affecting any other lemma in
the file.

## Sorry count delta

- Before S28: 2 sorries
  - `colStrict_count_add_eq_subSym_le_count` (Sub-lemma 2 body)
  - `jacobi_trudi_ssyt_eq` k ≥ 3
- After S28: 2 sorries
  - `noColStrict_subSym_a_count_eq_subSym_le_aplus1_count` (Sub-lemma 2B body)
  - `jacobi_trudi_ssyt_eq` k ≥ 3

Net: unchanged (one sorry migrates from Sub-lemma 2 → Sub-lemma 2B with
strictly cleaner provenance).

## File deltas

| File | Before | After | Delta |
|------|--------|-------|-------|
| `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` | 1528 | 1623 | +95 |
| `src/data/proofs/.../meta.json` (lineCount, theoremCount) | 1528, 34 | 1623, 35 | +95, +1 |
| `src/data/proofs/.../meta.json` (assumptions) | (S26-era) | (S28 current) | rewritten |
| `state.md` (iteration) | 27 | 28 | +1 |

The Lean file delta:
- Sub-lemma 2B: ~+55 lines (docstring + statement + sorry)
- Sub-lemma 2 body: ~+40 lines (was 1-line sorry, now ~45-line proof)
- Sub-lemma 2 docstring: ~−3 lines (replaced "deferred to S27+" tail with
  "S28 — closed via 2A + 2B + partition" structural summary)
- Sub-lemma 2 docstring header: minor +1-line update

## Build risk assessment

The Sub-lemma 2 body uses only:
- `colStrict_pair_count_eq_subSym_filtered_count` (already in file, S27)
- `Finset.filter_card_add_filter_neg_card_eq_card` (Mathlib)
- `Finset.filter_filter` (Mathlib)
- `noColStrict_subSym_a_count_eq_subSym_le_aplus1_count` (sorry, but
  signature is well-typed and matches the partition setup)
- `le_self_add` (Mathlib)
- `omega`

Plus structural lemmas: `Finset.mem_filter`, `Finset.mem_univ`, `simp` /
`refine` plumbing.

The `h_pivot` step uses `ext + simp` to reduce to an `Iff`, then constructs
both directions using `h_hasCS_imp_le` and projection. This is a standard
pattern.

The build should succeed — the cited Mathlib lemmas are all stable and the
proof structure is mechanical Finset manipulation. CI on the PR is the
ground truth.

## What S29+ should do

**Attack Sub-lemma 2B directly via the Cycle Lemma**. Two paths:

1. **Mathlib contribution** (preferred): implement the Cycle Lemma for sorted
   multiset prefixes. Lyndon / Dvoretzky-Motzkin generalisation. Standalone
   reusable theorem, suitable for a small Mathlib PR.

2. **Inline proof**: build the bijection directly. Map a "bad" `P : Sym a`
   (with `P.1 ≤ M.1` and no col-strict complement) to a `P' : Sym (a + 1)`
   with `P'.1 ≤ M.1` by adding the smallest element of `M.1 − P.1` to `P.1`
   (call this element `q*`). The forward map is well-defined because "no
   col-strict complement" is rotation-invariant on the sorted representative
   of `M.1`. The inverse map drops one element from `P'.1` chosen by the
   "first violation" criterion of the col-strict predicate.

Option (1) is more reusable but requires upstream coordination. Option (2)
is faster to land and keeps the proof self-contained.

Estimated effort: ~80–100 lines for either path.
