# Knowledge Base: abel-ruffini-galois-extensions-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

Instantiate Mathlib's `JordanHolderLattice` typeclass for `Subgroup G`, filling a marked TODO
in `Mathlib.Order.JordanHolder`. The three required axioms are:
1. `sup_eq_of_isMaximal` — x, y both maximal normal in z (x ≠ y) → x ⊔ y = z
2. `isMaximal_inf_left_of_isMaximal_sup` — x, y both maximal normal in x⊔y → x⊓y maximal normal in x
3. `second_iso` — (x⊔y)/x ≃* y/(x⊓y)

---

## Session 2026-04-24 (Session 1) — JordanHolderLattice Instance: 5/6 Proved

**Mode**: FRESH
**Outcome**: progress — 5 of 6 instance fields proved; 1 sorry remaining in maximality step

### What Was Done
- Defined `IsMaxNorm H K`: H < K, (H.subgroupOf K).Normal, maximality condition
- Defined `GroupQuotIso`: quotient iso predicate with explicit Normal witnesses
- Proved `le_normalizer_of_normal_in_sup`: K ≤ H.normalizer when (H.subgroupOf (H⊔K)).Normal
- Proved `sup_eq_of_isMaximal`:
  - `subgroupOf_sup` shows x⊔y relatively normal in z
  - Apply x's maximality: x⊔y = x or x⊔y = z
  - If x⊔y = x → y ≤ x → apply y's maximality to get contradiction with x ≠ y
- Proved `second_iso` via first isomorphism theorem:
  - φ = mk' ∘ inclusion le_sup_right : y →* (x⊔y)/x
  - ker φ = (x⊓y).subgroupOf y (by inf_subgroupOf_right)
  - surjective: g = a*b (a ∈ x, b ∈ y); φ(b) = [a*b] via hn_sup.conj_mem
  - `quotientKerEquivOfSurjective` closes the goal
- Proved `iso_symm` and `iso_trans`
- `isMaximal_inf_left_of_isMaximal_sup`: parts 1 (x⊓y < x) and 2 (Normal) proved; part 3 (maximality) sorry

### Key Findings
- `rw [sup_comm y x]` at `(y ⊔ x) ⧸ y.subgroupOf (y ⊔ x)` fails: "motive not type correct"
  because Normal typeclass instance depends on the rewritten term
- Fix: construct φ directly targeting `(x ⊔ y) ⧸ x.subgroupOf (x ⊔ y)` without any sup_comm rewrite
- `subgroupOf_sup {A B C} (hA : A ≤ C) (hB : B ≤ C) : (A ⊔ B).subgroupOf C = A.subgroupOf C ⊔ B.subgroupOf C`
- `inf_subgroupOf_right (H K) : (H ⊓ K).subgroupOf K = H.subgroupOf K`
- `normal_subgroupOf_iff_le_normalizer (hle : H ≤ K) : (H.subgroupOf K).Normal ↔ K ≤ H.normalizer`
- `normal_subgroupOf_of_le_normalizer : H ≤ N.normalizer → (N.subgroupOf H).Normal`
- `hn_sup.conj_mem` gives `b⁻¹ * a * b ∈ x` (Normal action), enabling surjectivity of φ

### Files Modified
- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ04.lean` (241 lines, 1 sorry)
- `src/data/proofs/abel-ruffini-galois-extensions-oq-04/` (gallery entry created)
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-04.json` (created)

### Next Steps
- Close maximality sorry in `isMaximal_inf_left_of_isMaximal_sup`:
  - Use `second_iso`-derived isomorphism `x/(x⊓y) ≃* (x⊔y)/y`
  - `IsMaxNorm y (x⊔y)` → `(x⊔y)/y` is simple (no normal subgroups between y and x⊔y)
  - Transfer simplicity to `x/(x⊓y)` via `IsSimpleGroup.of_mulEquiv`
  - Apply simplicity: N/(x⊓y) normal in x/(x⊓y) → N = x⊓y or N = x
- Submit maximality sorry to Aristotle (HARD classification)

---

## Insights

- `rw [sup_comm]` fails at quotient types with Normal typeclass — use direct construction instead
- `subgroupOf_sup` is the key for showing products of relative-normal subgroups are normal
- `GroupQuotIso` must carry explicit hn1/hn2 so `haveI` can instantiate before MulEquiv
- `quotientKerEquivOfSurjective` (first iso) is more tractable than `quotientInfEquivProdNormalizerQuotient` (second iso) for this particular goal
- `hn.conj_mem` for Normal subgroup H gives: `g ∈ H → ∀ k, k⁻¹ * g * k ∈ H`

---

## Dead Ends

- `rw [sup_comm y x]` at quotient types: "motive not type correct" — Normal instance depends on rewritten term; cannot use sup_comm to commute quotient indices
- `quotientInfEquivProdNormalizerQuotient` directly: would require `rw [sup_comm]` or `quotientMulEquivOfEq` to align types; both fail for the same reason
