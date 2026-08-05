import Proofs.Erdos85DifferenceArrayArithmetic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Prime-order Fourier uniformity

At a primitive character of prime order, vanishing of an integral Fourier
coefficient forces the coefficient function to be constant.  This is the
cyclotomic bridge used by the equal-cycle terminal argument.
-/

namespace Erdos85

open scoped BigOperators

/-- Prime-order Fourier vanishing makes every projected multiplicity equal. -/
theorem all_eq_of_prime_fourier_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (a : Fin p → ℤ)
    (hzero : ∑ i, (a i : K) * ζ ^ i.val = 0) :
    ∀ i j, a i = a j := by
  exact (hζ.sum_eq_zero_iff_forall_eq_int hp a).mp (by simpa using hzero)

/-- In particular, the prime divides the total multiplicity. -/
theorem prime_dvd_sum_of_fourier_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (a : Fin p → ℤ)
    (hzero : ∑ i, (a i : K) * ζ ^ i.val = 0) :
    (p : ℤ) ∣ ∑ i, a i := by
  have hall := all_eq_of_prime_fourier_eq_zero hp hζ a hzero
  let i0 : Fin p := ⟨0, hp.pos⟩
  refine ⟨a i0, ?_⟩
  calc
    ∑ i, a i = ∑ _i : Fin p, a i0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hall i i0
    _ = (p : ℤ) * a i0 := by simp

/-- Fibre-count form: if the Fourier sum of a finite multiset of labels
vanishes at a primitive prime-order character, then the prime divides the
size of the multiset. -/
theorem prime_dvd_card_of_label_fourier_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {A : Type*} [Fintype A] [DecidableEq A]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (label : A → Fin p)
    (hzero : ∑ i : Fin p,
      (((Finset.univ.filter fun a : A ↦ label a = i).card : ℤ) : K) *
        ζ ^ i.val = 0) :
    p ∣ Fintype.card A := by
  let count : Fin p → ℤ := fun i ↦
    ((Finset.univ.filter fun a : A ↦ label a = i).card : ℤ)
  have hdiv : (p : ℤ) ∣ ∑ i, count i :=
    prime_dvd_sum_of_fourier_eq_zero hp hζ count (by simpa only [count] using hzero)
  have hcardNat : Fintype.card A = ∑ i : Fin p,
      (Finset.univ.filter fun a : A ↦ label a = i).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
  have hsum : ∑ i, count i = (Fintype.card A : ℤ) := by
    rw [hcardNat, Nat.cast_sum]
  rw [hsum, Int.natCast_dvd_natCast] at hdiv
  exact hdiv

/-- The frequency-pair trace counts each diagonal anchor twice.  For an odd
prime, divisibility of that doubled mass still gives divisibility of the
degree itself. -/
theorem prime_dvd_of_dvd_two_mul
    {p d : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (h : p ∣ 2 * d) : p ∣ d := by
  rcases hp.dvd_mul.mp h with hpTwo | hpD
  · have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpTwo
    omega
  · exact hpD

/-- Once prime-order trace vanishing gives `p ∣ d`, the boundary order
forces that prime to be three. -/
theorem prime_eq_three_of_dvd_degree_and_boundary
    {p d : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hpd : p ∣ d) (hpBoundary : p ∣ d * (d - 1) + 3) : p = 3 := by
  have hprod : p ∣ d * (d - 1) := dvd_mul_of_dvd_left hpd _
  have hsum : p ∣ 3 + d * (d - 1) := by
    simpa [Nat.add_comm] using hpBoundary
  have hpDvdThree : p ∣ 3 := (Nat.dvd_add_iff_left hprod).mpr hsum
  have hple : p ≤ 3 := Nat.le_of_dvd (by norm_num) hpDvdThree
  omega

/-- Thus no prime at least five can simultaneously divide the degree and
the boundary order. -/
theorem not_prime_dvd_degree_and_boundary
    {p d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpd : p ∣ d) (hpBoundary : p ∣ d * (d - 1) + 3) : False := by
  have := prime_eq_three_of_dvd_degree_and_boundary hp (by omega) hpd hpBoundary
  omega

/-- Abstract terminal prime-frequency contradiction.  The graph-facing
Fourier calculation only has to provide the finite anchor type, its exact
cardinality `d`, and the displayed vanishing sum. -/
theorem false_of_prime_anchor_fourier_zero
    {K : Type*} [Field K] [CharZero K]
    {A : Type*} [Fintype A] [DecidableEq A]
    {p d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (label : A → Fin p) (hcard : Fintype.card A = d)
    (hpBoundary : p ∣ d * (d - 1) + 3)
    (hzero : ∑ i : Fin p,
      (((Finset.univ.filter fun a : A ↦ label a = i).card : ℤ) : K) *
        ζ ^ i.val = 0) : False := by
  have hpd : p ∣ d := by
    rw [← hcard]
    exact prime_dvd_card_of_label_fourier_eq_zero hp hζ label hzero
  exact not_prime_dvd_degree_and_boundary hp hp5 hpd hpBoundary

end Erdos85
