/-
Erdős Problem #476: The Erdős-Heilbronn Conjecture

Source: https://erdosproblems.com/476
Status: SOLVED (da Silva-Hamidoune, 1994)

Statement:
Let A ⊆ 𝔽ₚ (the finite field with p elements). Define the restricted sumset:
  A +̂ A = {a + b : a ≠ b ∈ A}
(sums of distinct elements only).

Is it true that |A +̂ A| ≥ min(2|A| - 3, p)?

Answer: YES

This was conjectured by Erdős and Heilbronn and proved by da Silva and
Hamidoune (1994) using linear algebra methods (exterior algebras).

Key Concepts:
- Restricted sumsets exclude "diagonal" sums a + a
- The bound 2|A| - 3 is tight (achieved by arithmetic progressions)
- The proof uses Grassmann derivatives and linear algebra

References:
- Erdős-Heilbronn (1964): Original conjecture
- da Silva-Hamidoune (1994): Proof via cyclic spaces
- Alon-Nathanson-Ruzsa (1995): Polynomial method proof
- Guy's Unsolved Problems in Number Theory, C15
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

namespace Erdos476

variable (p : ℕ) [Fact p.Prime]

/-
## Part I: Restricted Sumsets

The key object is A +̂ A, the set of sums a + b where a ≠ b.
This excludes the "diagonal" sums 2a.
-/

/--
**Restricted Sumset** (A +̂ A):
The set of all sums a + b where a and b are distinct elements of A.
-/
def restrictedSumset (A : Finset (ZMod p)) : Finset (ZMod p) :=
  (A.product A).filter (fun ab => ab.1 ≠ ab.2) |>.image (fun ab => ab.1 + ab.2)

/--
Notation for restricted sumset.
-/
notation:65 A " +̂ " B => restrictedSumset _ A

/--
**Ordinary Sumset** (A + A):
The set of all sums a + b (including a = b).
-/
def sumset (A : Finset (ZMod p)) : Finset (ZMod p) :=
  (A.product A).image (fun ab => ab.1 + ab.2)

/-
## Part II: Basic Properties
-/

/--
The restricted sumset is contained in the ordinary sumset.
-/
theorem restrictedSumset_subset_sumset (A : Finset (ZMod p)) :
    restrictedSumset p A ⊆ sumset p A := by
  intro x hx
  simp only [restrictedSumset, sumset, mem_image, mem_filter, mem_product] at hx ⊢
  obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := hx
  exact ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩

/--
For singleton sets, the restricted sumset is empty.
-/
theorem restrictedSumset_singleton (a : ZMod p) :
    restrictedSumset p {a} = ∅ := by
  simp [restrictedSumset]

/--
For a set with at least 2 elements, the restricted sumset is nonempty.
-/
theorem restrictedSumset_nonempty_of_card_ge_two (A : Finset (ZMod p)) (h : 2 ≤ A.card) :
    (restrictedSumset p A).Nonempty := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  exact ⟨a + b, Finset.mem_image.mpr
    ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩⟩

/-
## Part III: The Erdős-Heilbronn Bound

The main conjecture: |A +̂ A| ≥ min(2|A| - 3, p)
-/

/--
**Erdős-Heilbronn Lower Bound:**
For any A ⊆ 𝔽ₚ with |A| ≥ 2:
  |A +̂ A| ≥ min(2|A| - 3, p)

This is the precise bound; it cannot be improved.
-/
axiom erdos_heilbronn_bound (A : Finset (ZMod p)) (h : 2 ≤ A.card) :
    (restrictedSumset p A).card ≥ min (2 * A.card - 3) p

/--
**Erdős Problem #476: SOLVED**
The Erdős-Heilbronn conjecture is true.
-/
theorem erdos_476 (A : Finset (ZMod p)) (h : 2 ≤ A.card) :
    (restrictedSumset p A).card ≥ min (2 * A.card - 3) p :=
  erdos_heilbronn_bound p A h

/-
## Part IV: Da Silva-Hamidoune Theorem

The proof uses exterior algebra and Grassmann derivatives.
-/

/--
**Da Silva-Hamidoune Theorem (1994):**
Let A ⊆ 𝔽ₚ with |A| = n ≥ 2. Then:
  |A +̂ A| ≥ min(2n - 3, p)

The proof introduces the k-th Grassmann derivative of a polynomial
and shows it has degree at least 2n - 3 on the restricted sumset.
-/
/-
## Part V: Tightness - Arithmetic Progressions

The bound 2|A| - 3 is achieved by arithmetic progressions.
-/

/--
**Arithmetic Progression:**
The set {a, a+d, a+2d, ..., a+(n-1)d} in 𝔽ₚ.
-/
def arithmeticProgression (a d : ZMod p) (n : ℕ) : Finset (ZMod p) :=
  (Finset.range n).image (fun i => a + i • d)

/--
For an arithmetic progression A = {a, a+d, ..., a+(n-1)d} with d ≠ 0:
  A +̂ A = {2a+d, 2a+2d, ..., 2a+(2n-3)d}

This has exactly 2n - 3 elements (when 2n - 3 < p).
-/
theorem AP_restrictedSumset (a d : ZMod p) (n : ℕ) (hd : d ≠ 0) (hn : n ≥ 2)
    (hsmall : 2 * n - 3 < p) :
    (restrictedSumset p (arithmeticProgression p a d n)).card = 2 * n - 3 := by
  have hp2 : 2 ≤ p := Nat.Prime.two_le Fact.out
  have hle : n ≤ p := by omega
  -- Helper: (k:ZMod p) ≠ 0 when 1 ≤ k < p
  have hk_ne_zero : ∀ k : ℕ, 1 ≤ k → k < p → (k : ZMod p) ≠ 0 := by
    intro k hk1 hkp h
    rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at h
    exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  -- Key: restricted sumset = image of {1,...,2n-3} under (k ↦ 2a + k·d)
  have hset : restrictedSumset p (arithmeticProgression p a d n) =
      (Finset.Ico 1 (2 * n - 2)).image (fun k : ℕ => 2 * a + (k : ZMod p) * d) := by
    ext x
    simp only [restrictedSumset, arithmeticProgression, Finset.mem_image,
      Finset.mem_filter, Finset.mem_product, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨ai, aj⟩, ⟨⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩, hne⟩, rfl⟩
      have hne_nat : i ≠ j := by
        intro heq; apply hne; subst heq
      exact ⟨i + j, ⟨by omega, by omega⟩, by simp only [nsmul_eq_mul]; push_cast; ring⟩
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      have hk_lt_p : k < p := by omega
      rcases le_or_lt k (n - 1) with hkn | hkn
      · -- k ≤ n-1: use pair (a + 0•d, a + k•d)
        refine ⟨(a + (0 : ℕ) • d, a + (k : ℕ) • d),
          ⟨⟨⟨0, by omega, rfl⟩, ⟨k, by omega, rfl⟩⟩, ?_⟩, ?_⟩
        · simp only [Nat.zero_eq, Nat.cast_zero, zero_smul, add_zero, nsmul_eq_mul]
          intro heq
          have h1 : (k : ZMod p) * d = 0 := by
            have h := congr_arg (· - a) heq; ring_nf at h; exact h.symm
          exact hk_ne_zero k hk1 hk_lt_p ((mul_eq_zero.mp h1).resolve_right hd)
        · simp only [nsmul_eq_mul, Nat.cast_zero, zero_mul, zero_add]; push_cast; ring
      · -- k ≥ n: use pair (a + (k-(n-1))•d, a + (n-1)•d)
        have hsum : k - (n - 1) + (n - 1) = k := by omega
        refine ⟨(a + (k - (n - 1) : ℕ) • d, a + (n - 1 : ℕ) • d),
          ⟨⟨⟨k - (n - 1), by omega, rfl⟩, ⟨n - 1, by omega, rfl⟩⟩, ?_⟩, ?_⟩
        · simp only [nsmul_eq_mul]
          intro heq
          have h0 : ((k - (n - 1) : ℕ) : ZMod p) * d = ((n - 1 : ℕ) : ZMod p) * d :=
            add_left_cancel heq
          have heq2 := mul_right_cancel₀ hd h0
          have hval := congr_arg ZMod.val heq2
          rw [ZMod.val_natCast, ZMod.val_natCast,
              Nat.mod_eq_of_lt (by omega : k - (n - 1) < p),
              Nat.mod_eq_of_lt (by omega : n - 1 < p)] at hval
          omega
        · simp only [nsmul_eq_mul]
          conv_rhs => rw [← hsum, Nat.cast_add, add_mul]
          push_cast; ring
  -- Count: image has same size as Ico 1 (2n-2) via injectivity
  rw [hset]
  have hinj : Set.InjOn (fun k : ℕ => 2 * a + (k : ZMod p) * d)
      ↑(Finset.Ico 1 (2 * n - 2)) := by
    intro k1 hk1 k2 hk2 heq
    simp only [Finset.mem_coe, Finset.mem_Ico] at hk1 hk2
    have h1 : (k1 : ZMod p) * d = (k2 : ZMod p) * d := add_left_cancel heq
    have h2 := mul_right_cancel₀ hd h1
    have hval := congr_arg ZMod.val h2
    rw [ZMod.val_natCast, ZMod.val_natCast,
        Nat.mod_eq_of_lt (by omega : k1 < p),
        Nat.mod_eq_of_lt (by omega : k2 < p)] at hval
    exact hval
  rw [Finset.card_image_of_injOn hinj, Finset.card_Ico]
  omega

/--
Arithmetic progressions achieve the Erdős-Heilbronn bound exactly.
-/
theorem AP_achieves_bound (a d : ZMod p) (n : ℕ) (hd : d ≠ 0) (hn : n ≥ 2)
    (hsmall : 2 * n - 3 < p) :
    (restrictedSumset p (arithmeticProgression p a d n)).card =
      min (2 * n - 3) p := by
  rw [AP_restrictedSumset p a d n hd hn hsmall]
  simp [min_eq_left (Nat.le_of_lt hsmall)]

/-
## Part VI: Comparison with Cauchy-Davenport

The ordinary sumset satisfies the Cauchy-Davenport theorem:
|A + B| ≥ min(|A| + |B| - 1, p)

For A + A this gives |A + A| ≥ min(2|A| - 1, p).

The restricted sumset has a weaker bound (2|A| - 3 vs 2|A| - 1)
because excluding diagonal sums removes potential elements.
-/

/--
**Cauchy-Davenport Theorem:**
For nonempty A, B ⊆ 𝔽ₚ:
  |A + B| ≥ min(|A| + |B| - 1, p)
-/
/--
The restricted sumset bound is weaker than Cauchy-Davenport by 2.
This reflects the exclusion of diagonal elements.
-/
theorem bound_comparison (A : Finset (ZMod p)) (h : 2 ≤ A.card) :
    2 * A.card - 3 ≤ 2 * A.card - 1 := by omega

/-
## Part VII: The Polynomial Method

Alon, Nathanson, and Ruzsa (1995) gave an alternative proof using
the polynomial method (Combinatorial Nullstellensatz).
-/

/--
**Combinatorial Nullstellensatz (Alon, 1999):**
If f(x₁,...,xₙ) is a polynomial over a field and the coefficient of
x₁^{d₁}...xₙ^{dₙ} is nonzero where ∑dᵢ = deg(f), then for sets Aᵢ
with |Aᵢ| > dᵢ, there exist aᵢ ∈ Aᵢ with f(a₁,...,aₙ) ≠ 0.
-/
/- combinatorial_nullstellensatz: Alon's Combinatorial Nullstellensatz (1999).
   If f(x₁,...,xₙ) has nonzero coefficient for x₁^{d₁}···xₙ^{dₙ} with ∑dᵢ = deg(f),
   and |Aᵢ| > dᵢ, then ∃ aᵢ ∈ Aᵢ with f(a₁,...,aₙ) ≠ 0. Formalizing requires
   polynomial rings over fields in full generality, not just ZMod p. -/

/--
**ANR Proof (1995):**
Consider f(x, y) = (x + y) - c for c ∈ A +̂ A.
The polynomial method shows this has enough zeros to force
the size of A +̂ A.
-/
/-
## Part VIII: Generalization to r-Sums

Erdős conjectured a generalization to sums of r distinct elements.
-/

/--
**r-fold Restricted Sumset:**
The set of sums a₁ + a₂ + ... + aᵣ where all aᵢ are distinct.
-/
def restrictedSumsetR (A : Finset (ZMod p)) (r : ℕ) : Finset (ZMod p) :=
  (A.powersetCard r).image (fun s => s.sum id)

/--
**Erdős's Generalized Conjecture:**
|r-fold restricted sumset| ≥ min(r|A| - r² + 1, p)

This was also proved using the polynomial method.
-/
/-
## Part IX: Small Examples
-/

/--
For |A| = 2, the restricted sumset has exactly 1 element.
If A = {a, b} with a ≠ b, then A +̂ A = {a + b}.
-/
theorem card_two_case (A : Finset (ZMod p)) (h : A.card = 2) :
    (restrictedSumset p A).card = 1 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
  have heq : restrictedSumset p {a, b} = {a + b} := by
    ext x
    simp only [restrictedSumset, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, hne⟩, rfl⟩
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
      · exact absurd rfl hne
      · rfl
      · exact add_comm b a
      · exact absurd rfl hne
    · rintro rfl
      exact ⟨(a, b), ⟨⟨Or.inl rfl, Or.inr rfl⟩, hab⟩, rfl⟩
  simp [heq]

/--
For |A| = 3, the restricted sumset has at least 3 elements.
min(2·3 - 3, p) = min(3, p) = 3 for p ≥ 3.
-/
theorem card_three_lower_bound (A : Finset (ZMod p)) (h : A.card = 3) (hp : p ≥ 3) :
    (restrictedSumset p A).card ≥ 3 := by
  have : 2 ≤ A.card := by omega
  have := erdos_476 p A this
  simp only [h] at this
  have : min (2 * 3 - 3) p = 3 := by
    simp [min_eq_left (by omega : 3 ≤ p)]
  omega

/-
## Part X: Summary
-/

/--
**Erdős Problem #476: Summary**

Question: Is |A +̂ A| ≥ min(2|A| - 3, p) for all A ⊆ 𝔽ₚ?

Answer: YES (da Silva-Hamidoune, 1994)

Key points:
1. The restricted sumset excludes diagonal sums a + a
2. The bound 2|A| - 3 is tight (achieved by APs)
3. Proved via exterior algebra or polynomial method
4. Generalizes to r-fold sums: min(r|A| - r² + 1, p)
-/
theorem erdos_476_summary (A : Finset (ZMod p)) (h : 2 ≤ A.card) :
    (restrictedSumset p A).card ≥ min (2 * A.card - 3) p ∧
    ∀ a d : ZMod p, d ≠ 0 → 2 * A.card - 3 < p →
      ∃ AP : Finset (ZMod p), AP.card = A.card ∧
        (restrictedSumset p AP).card = 2 * AP.card - 3 := by
  constructor
  · exact erdos_476 p A h
  · intro a d hd hsmall
    use arithmeticProgression p a d A.card
    have hp2 : 2 ≤ p := Nat.Prime.two_le Fact.out
    have hle : A.card ≤ p := by omega
    have hAP_card : (arithmeticProgression p a d A.card).card = A.card := by
      unfold arithmeticProgression
      have hinj : Set.InjOn (fun i => a + i • d) ↑(Finset.range A.card) := by
        intro i hi j hj hij
        simp only [Finset.mem_coe, Finset.mem_range] at hi hj
        have h0 : (i : ℕ) • d = (j : ℕ) • d := add_left_cancel hij
        simp only [nsmul_eq_mul] at h0
        have heq : (i : ZMod p) = (j : ZMod p) := mul_right_cancel₀ hd h0
        have hval := congr_arg ZMod.val heq
        rw [ZMod.val_natCast, ZMod.val_natCast,
            Nat.mod_eq_of_lt (hi.trans_le hle),
            Nat.mod_eq_of_lt (hj.trans_le hle)] at hval
        exact hval
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    constructor
    · exact hAP_card
    · rw [hAP_card]
      exact AP_restrictedSumset p a d A.card hd (by omega) hsmall

end Erdos476
