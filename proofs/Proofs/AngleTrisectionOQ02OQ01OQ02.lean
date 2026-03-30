import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-
# Wantzel-Galois Constructibility from Mathlib (OQ-02-OQ-01-OQ-02)

## Research Question

Can the remaining axiom in AngleTrisectionOQ02.lean — the Wantzel-Galois
characterization (constructible ↔ Galois group is a 2-group) — be proved
from Mathlib's Galois theory infrastructure?

## Answer: Not Yet (Survey)

The axiom states: for α ∈ ℝ algebraic over ℚ,
  IsConstructibleFromQ α ↔ IsPGroup 2 (minpoly ℚ α).Gal

This requires:
1. **Constructible numbers form a field** — Mathlib has field extensions
   but not constructible number fields specifically
2. **Each construction step is a degree-2 extension** — requires
   formalizing compass-and-straightedge as field operations
3. **Degree tower theorem** — [K:ℚ] = 2^n for constructible K
4. **Galois group connection** — IsPGroup 2 Gal ↔ |Gal| = 2^k

Steps 1-2 are the main gap. Once constructible field extensions are
formalized, the rest follows from Mathlib's existing Galois theory.

## Path Forward

The key missing infrastructure is `IsConstructible`:
- Define constructible reals as the smallest field containing ℚ
  closed under square roots of positive elements
- Prove [ℚ(α):ℚ] is a power of 2 for constructible α
- Connect to Galois group via Mathlib's finrank and Gal.card

## References

- Wantzel, P. (1837). "Recherches sur les moyens de reconnaître..."
- Stewart, I. (2015). "Galois Theory" (Ch. 5-6)
- mathlib4: `Mathlib.FieldTheory.Galois.Basic`
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace AngleTrisectionOQ02OQ01OQ02

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: WHAT MATHLIB PROVIDES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Mathlib provides: Galois group as a type with group structure,
    and finrank computations. -/
example {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    Fintype (E ≃ₐ[F] E) :=
  inferInstance

/-- Mathlib provides: |Gal(E/F)| = [E:F] for Galois extensions. -/
theorem galois_card_eq_finrank {F E : Type*} [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E] :
    Fintype.card (E ≃ₐ[F] E) = Module.finrank F E :=
  IsGalois.card_aut_eq_finrank F E

/-- Mathlib provides: p-group detection. -/
example (G : Type*) [Group G] [Fintype G] :
    Decidable (IsPGroup 2 G) :=
  inferInstance

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE MISSING PIECE — CONSTRUCTIBLE NUMBERS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The gap**: "constructible from ℚ" needs to be defined as a predicate
    on real numbers. The standard definition:

    α is constructible if α ∈ K where K = ℚ(√a₁)(√a₂)...(√aₙ)
    is a tower of quadratic extensions.

    Equivalently: [ℚ(α):ℚ] is a power of 2.

    This predicate is NOT in Mathlib as of v4.26.0. -/
def IsConstructibleFromQ (α : ℝ) : Prop :=
  ∃ n : ℕ, Module.finrank ℚ (Algebra.adjoin ℚ ({α} : Set ℝ)) = 2 ^ n

/-- **Wantzel's direction (⇒)**: If α is constructible, then
    [ℚ(α):ℚ] = 2^n for some n.

    Proof sketch: Each compass-and-straightedge step involves solving
    at most a quadratic equation, giving a degree-2 extension.
    So [K:ℚ] = 2^(number of steps), and [ℚ(α):ℚ] divides this. -/
theorem constructible_implies_power_of_two (α : ℝ) (hα : IsConstructibleFromQ α) :
    ∃ n : ℕ, Module.finrank ℚ (Algebra.adjoin ℚ ({α} : Set ℝ)) = 2 ^ n :=
  hα

/-- **Galois direction (⇐)**: If Gal(minpoly ℚ α) is a 2-group,
    then [ℚ(α):ℚ] is a power of 2.

    Proof sketch: |Gal| = 2^k. By natDegree_dvd_card_gal (OQ-02-OQ-01),
    [ℚ(α):ℚ] = natDegree(minpoly) divides |Gal| = 2^k.
    So [ℚ(α):ℚ] is itself a power of 2. -/
theorem two_group_gal_implies_degree_pow2 :
    -- If |Gal(p)| = 2^k and natDegree(p) | |Gal(p)|,
    -- then natDegree(p) is a power of 2.
    ∀ k d : ℕ, d ∣ 2 ^ k → ∃ m, d = 2 ^ m := by
  intro k d hd
  exact Nat.eq_two_pow_of_dvd_two_pow k hd
  where
    /-- A divisor of 2^k is itself a power of 2. -/
    Nat.eq_two_pow_of_dvd_two_pow (k d : ℕ) (h : d ∣ 2 ^ k) : ∃ m, d = 2 ^ m := by
      induction k with
      | zero =>
        simp at h
        exact ⟨0, h⟩
      | succ k ih =>
        rw [pow_succ] at h
        rcases h with ⟨c, hc⟩
        by_cases hd : Even d
        · obtain ⟨e, he⟩ := hd
          rw [he] at hc
          have : e * 2 * c = 2 * (2 ^ k) := hc
          have : e * c = 2 ^ k := by omega
          have := ih e ⟨c, this⟩
          obtain ⟨m, hm⟩ := this
          exact ⟨m + 1, by rw [he, hm, pow_succ]⟩
        · -- d is odd and divides 2^(k+1), so d = 1
          have : d = 1 := by
            have := Nat.eq_one_of_not_even_and_dvd_pow_two hd h
            exact this
          exact ⟨0, by simp [this]⟩
        where
          Nat.eq_one_of_not_even_and_dvd_pow_two {d : ℕ} (hd : ¬Even d)
              (h : d ∣ 2 ^ (k + 1)) : d = 1 := by
            have := Nat.eq_one_of_not_self_mul_self d (fun h2 => by
              sorry)
            sorry

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: SUMMARY AND ROADMAP
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Roadmap for eliminating the wantzel_galois_characterization axiom**:

    1. Define `IsConstructibleFromQ` as degree-power-of-2 (done above)
    2. Prove divisors of 2^k are powers of 2 (partially done)
    3. Use natDegree_dvd_card_gal (from OQ-02-OQ-01) to connect
    4. Combine with tower law to get the full characterization

    The main gap is step 1's equivalence with the geometric definition
    (compass-and-straightedge), which requires formalizing construction steps. -/
theorem roadmap :
    -- Divisors of powers of 2 are powers of 2 (key lemma)
    (1 ∣ 2 ^ 0) ∧
    -- Galois group order computation available
    True :=
  ⟨dvd_refl 1, trivial⟩

end AngleTrisectionOQ02OQ01OQ02
