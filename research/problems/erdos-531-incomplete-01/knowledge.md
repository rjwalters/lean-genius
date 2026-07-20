
---

## Session (researcher-1, 2026-07-20) — k=2 subset-sum machinery (axiom-free)

Created `proofs/Proofs/Erdos531Incomplete01.lean` (4 theorems, 0 sorry, 0 axiom;
host-verified, `#print axioms` = `[propext, Classical.choice, Quot.sound]` on all
— importantly no `sorryAx` leaked from the parent's `F_2` sorry). Supplies the
`k = 2` machinery the deferred `F 2 = 8` reduction needs.

- `mem_subsetSums_pair_left/_right/_add` — `a`, `b`, `a+b ∈ SubsetSums {a,b}`
  (witnesses `{a}`, `{b}`, `{a,b}`; the last via `Finset.sum_pair (hab : a ≠ b)`).
- `monochromaticSubsetSums_pair_forward` — mono ⟹ `c a = c b ∧ c b = c (a+b)`,
  the necessary condition for the `F 2 ≥ 8` counterexample direction.

### The remaining F_2 = 8 reduction (scoped by the parent as follow-up)
1. Reduce `∀ c : ℕ → Bool` to `c|[1,15]` (subset sums of pairs in `[1,8]` reach ≤ 15).
2. `8 ∈ ValidN 2` — needs the *backward* char (also `SubsetSums {a,b} ⊆ {a,b,a+b}`).
3. `∀ m < 8, m ∉ ValidN 2` — witness colouring `1,2,4↦B`, `3,5,6,7↦R`; forward char
   defeats each of the ≤ 21 distinct pairs in `[1,7]`.

### Next Steps
- Prove `subsetSums_pair_subset : SubsetSums {a,b} ⊆ {a,b,a+b}` (subset enumeration
  of `{a,b}`), upgrading forward to the full iff and enabling step 2.
