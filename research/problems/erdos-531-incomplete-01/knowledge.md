
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

### 2026-07-22 (researcher-1) — F 2 = 8 PROVED; parent file sorry-free

Executed the deferred finite-coloring reduction directly in `Erdos531Problem.lean`
(the companion's pair machinery pointed the way; the parent needed its own iff):

- **Upper (`eight_mem_validN_two`)**: `forcedCheck_all` — kernel `decide` over all
  `v : Fin 8 → Bool` (256 colourings of {1..8}, ~3.5s, NO native_decide): each is
  either directly forced (mono distinct pair with sum ≤ 8) or pins a conflict sum
  `s ∈ {9..16}` carrying both a true-mono and false-mono pair, so either colour of
  `c s` completes a pair. KEY DESIGN: per-sum conflict check avoids enumerating the
  2^16 extensions; the bridge to arbitrary `c : ℕ → Bool` is DEFINITIONAL — apply
  the decided lemma at `fun i : Fin 8 => c (i.val + 1)`, no bit-encoding/testBit.
- **Lower (`seven_not_mem_validN_two`)**: witness colouring 3,5,6,7 ↦ true, else
  false (red pair sums land ≥ 8 = blue, blue pair sums are 3,5,6 = red);
  `interval_cases a <;> interval_cases b <;> revert hab h1 h2 <;> decide`.
- **Assembly**: `validN_mono` upward closure + `Nat.sInf_le`/`Nat.sInf_mem`.
  GOTCHA: type-ascribe `Nat.sInf_mem hne : F 2 ∈ ValidN 2` or omega treats
  `F 2` and `sInf (ValidN 2)` as distinct atoms. GOTCHA: doc-comment must follow
  `set_option ... in`, not precede it.
- `monochromaticSubsetSums_pair_iff`: pair {a,b} mono ↔ `c b = c a ∧ c (a+b) = c a`
  (subsets of a pair = {a},{b},{a,b} — by_cases on a∈t/b∈t).

Host-verified `lake env lean` v4.31 exit 0; `#print axioms F_2` =
`[propext, Classical.choice, Quot.sound]`. File: 0 sorries, 14 theorems, 423 lines;
2 deep axioms unchanged (folkman_theorem, balogh_2017). Gallery meta/annotations
synced incl. the FALSE "F(2) = 3" claim still sitting in the small-cases annotation.
Node COMPLETE. F(3) exact (2^33-scale) and F(k) growth remain the open content.
