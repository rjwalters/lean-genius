import Proofs.Erdos85DifferenceSidonCayley

/-!
# No-wrap transport of integer Sidon rulers

A difference-Sidon set of integers contained in `[0,L)` remains
difference-Sidon after reduction modulo `M` whenever `2L ≤ M`.  The factor
two is exactly the room needed to recover an equality of two signed
differences from its congruence modulo `M`.
-/

namespace Erdos85

/-- Reduction of an integer ruler modulo `M`. -/
def sidonRulerReduction (M : ℕ) (A : Finset ℤ) : Finset (ZMod M) :=
  A.image fun a : ℤ => (a : ZMod M)

/-- On an interval shorter than the modulus, reduction is injective. -/
theorem intCast_zmod_injective_on_Ico
    {M L : ℕ} (hLM : L ≤ M) {a b : ℤ}
    (ha0 : 0 ≤ a) (haL : a < L) (hb0 : 0 ≤ b) (hbL : b < L)
    (hab : (a : ZMod M) = (b : ZMod M)) : a = b := by
  have hdvd : (M : ℤ) ∣ b - a :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a b M).mp hab
  have hM : (L : ℤ) ≤ M := by exact_mod_cast hLM
  have habs : |b - a| < (M : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hz : b - a = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

/-- Reduction modulo `M` preserves the cardinality of a ruler in `[0,L)`
when `L ≤ M`. -/
theorem card_sidonRulerReduction
    {M L : ℕ} (A : Finset ℤ) (hLM : L ≤ M)
    (hbound : ∀ a ∈ A, 0 ≤ a ∧ a < L) :
    (sidonRulerReduction M A).card = A.card := by
  rw [sidonRulerReduction, Finset.card_image_iff]
  intro a ha b hb hab
  exact intCast_zmod_injective_on_Ico hLM
    (hbound a ha).1 (hbound a ha).2
    (hbound b hb).1 (hbound b hb).2 hab

/-- An equality modulo `M` between two differences drawn from `[0,L)` is
already an integer equality when `2L ≤ M`. -/
theorem eq_integer_difference_of_eq_zmod_difference
    {M L : ℕ} (hLM : 2 * L ≤ M)
    {a b c d : ℤ}
    (ha0 : 0 ≤ a) (haL : a < L)
    (hb0 : 0 ≤ b) (hbL : b < L)
    (hc0 : 0 ≤ c) (hcL : c < L)
    (hd0 : 0 ≤ d) (hdL : d < L)
    (heq : (a : ZMod M) - b = (c : ZMod M) - d) :
    a - b = c - d := by
  have heqCast : ((a - b : ℤ) : ZMod M) = ((c - d : ℤ) : ZMod M) := by
    simpa using heq
  have hdvd : (M : ℤ) ∣ (c - d) - (a - b) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (a - b) (c - d) M).mp heqCast
  have hM : (2 * L : ℤ) ≤ M := by exact_mod_cast hLM
  have habs : |(c - d) - (a - b)| < (M : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hz : (c - d) - (a - b) = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

/-- **No-wrap Sidon transport.**  A bounded integer difference-Sidon ruler
remains difference-Sidon after reduction modulo every sufficiently large
modulus. -/
theorem isDifferenceSidon_sidonRulerReduction
    {M L : ℕ} (A : Finset ℤ) (hLM : 2 * L ≤ M)
    (hbound : ∀ a ∈ A, 0 ≤ a ∧ a < L)
    (hSidon : IsDifferenceSidon A) :
    IsDifferenceSidon (sidonRulerReduction M A) := by
  intro α hα β hβ γ hγ δ hδ heq
  rw [sidonRulerReduction, Finset.mem_image] at hα hβ hγ hδ
  obtain ⟨a, ha, rfl⟩ := hα
  obtain ⟨b, hb, rfl⟩ := hβ
  obtain ⟨c, hc, rfl⟩ := hγ
  obtain ⟨d, hd, rfl⟩ := hδ
  have hint : a - b = c - d :=
    eq_integer_difference_of_eq_zmod_difference hLM
      (hbound a ha).1 (hbound a ha).2
      (hbound b hb).1 (hbound b hb).2
      (hbound c hc).1 (hbound c hc).2
      (hbound d hd).1 (hbound d hd).2 heq
  rcases hSidon ha hb hc hd hint with hab | hpair
  · exact Or.inl (by simpa [hab])
  · exact Or.inr ⟨by simpa [hpair.1], by simpa [hpair.2]⟩

/-- A bounded integer ruler of size at least `d` produces a `C₄`-free
minimum-degree-`d` graph on every even order `2M` beyond the no-wrap bound. -/
theorem c4FreeMinDegreeWitness_two_mul_of_sidonRuler
    {M L d : ℕ} [NeZero M] (A : Finset ℤ) (hLM : 2 * L ≤ M)
    (hbound : ∀ a ∈ A, 0 ≤ a ∧ a < L)
    (hSidon : IsDifferenceSidon A) (hcard : d ≤ A.card) :
    C4FreeMinDegreeWitness (2 * M) d := by
  apply c4FreeMinDegreeWitness_two_mul_of_differenceSidon
    (sidonRulerReduction M A)
  · exact isDifferenceSidon_sidonRulerReduction A hLM hbound hSidon
  · rw [card_sidonRulerReduction A (by omega) hbound]
    exact hcard

end Erdos85
