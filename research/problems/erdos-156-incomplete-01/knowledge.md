# Knowledge Base: erdos-156-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Goal of this research problem: fill the 3 remaining `sorry`s in
`proofs/Proofs/Erdos156Problem.lean`. The three were all *counting* lemmas
supporting the greedy `Ω(N^{1/3})` lower bound:

1. `diffShadow_ncard_le` — `|diffShadow A| ≤ |A| · (|A|(|A|+1)/2)`
2. `midShadow_ncard_le` — `|midShadow A| ≤ |A|(|A|+1)/2`
3. `greedySidon_cube_lower_bound` — `N ≤ n + n·(n(n+1)/2) + n(n+1)/2` where
   `n = size(greedySidon N)`.

The file already had the structural heavy lifting done (the "every complement
element lands in one of the two shadows" lemma `greedySidon_complement_in_shadow`,
the exact Sidon sumset size `sidon_sumset_size`, and the upper-triangular pair
count `card_upper_tri`). What remained was purely cardinality bookkeeping.

---

## Insights

- **One reusable helper does all three.** Added
  `sumset_ncard_le : (sumset A).ncard ≤ A.ncard * (A.ncard + 1) / 2` for *every*
  finite set (no Sidon hypothesis needed). It is the image of the
  upper-triangular pair set under `(a,b) ↦ a+b`, so `ncard_image_le` plus the
  in-file `card_upper_tri` gives the bound. Both shadow lemmas then reduce to it.

- **The shadows are images of small index sets.**
  - `diffShadow A ⊆ (fun (a,σ) ↦ σ - a) '' (A ×ˢ sumset A)`, since `x ∈ diffShadow`
    means `a + x = b + c =: σ ∈ sumset A`, i.e. `x = σ - a`. Then
    `ncard ≤ |A ×ˢ sumset A| = |A|·|sumset A| ≤ |A|·(|A|(|A|+1)/2)`
    via `Set.ncard_prod`, `Set.ncard_image_le`, `Set.ncard_le_ncard`.
    The Sidon hypothesis is *not* required — the general `sumset_ncard_le`
    upper bound suffices (Sidon only makes it an equality).
  - `midShadow A ⊆ (fun σ ↦ σ / 2) '' (sumset A)`, since `2x = σ ∈ sumset A`,
    i.e. `x = σ / 2`. `omega` proves `σ/2 = x` from `σ = 2x` (it understands
    division by the literal 2).

- **The cube bound is a 3-set cover count.** `Interval N ⊆ A ∪ diffShadow A ∪
  midShadow A` (from `greedySidon_complement_in_shadow`), `|Interval N| = N`
  (`Interval N = ↑(Finset.Icc 1 N)`, `Nat.card_Icc`), and subadditivity of
  `ncard` over unions (`Set.ncard_union_le`, twice) yields the stated bound.
  `size (greedySidon N) = (greedySidon N).ncard` via
  `Set.ncard_eq_toFinset_card`.

---

## Dead Ends / Gotchas

- **`Set.Finite.ncard_eq_toFinset_card'` (the dot-notation prime form) is gone
  in the currently pinned Mathlib.** The file (and ~33 other repo files) used
  `hfin.ncard_eq_toFinset_card'`. The current replacement is
  `Set.ncard_eq_toFinset_card s hs` (Finite-arg form, no prime), which produces
  `Set.Finite.toFinset` — matching the downstream `hfin.toFinset` usages
  (`card_upper_tri hfin.toFinset`, the `h_eq` lemma). Updated the two
  pre-existing occurrences in this file accordingly.

- **`Set.ncard_coe_Finset` → `Set.ncard_coe_finset`** (capital-F is a deprecated
  alias since 2025-07-05).

- **Build host was DOWN this session** (host disk 100% full + Docker
  containerd blob store reporting I/O errors), so the file could **not** be
  compiled. The proofs only reference Mathlib lemmas whose existence and
  signatures were verified by source inspection, but this work is **UNVERIFIED**
  pending host recovery and a `docker-build.sh Proofs.Erdos156Problem` run.
