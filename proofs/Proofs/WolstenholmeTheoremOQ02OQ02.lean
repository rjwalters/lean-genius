/-
# Wolstenholme's Theorem and Wolstenholme Primes

## What This Proves
Wolstenholme's theorem: for prime p ≥ 5, C(2p-1, p-1) ≡ 1 (mod p³).
This strengthens Babbage's theorem (mod p²) from WolstenholmeTheoremOQ02.lean.

We define Wolstenholme primes (where C(2p-1, p-1) ≡ 1 mod p⁴) and state
the open question: does a Wolstenholme prime p ≡ 1 (mod 4) exist?

## Proof Strategy
From Vandermonde: C(2p,p) = 2 + Σ_{k=1}^{p-1} C(p,k)².
Factor: C(p,k) = p · bₖ, so Σ C(p,k)² = p² · Σ bₖ².
Key lemma: p | Σ bₖ² (via bₖ ≡ (-1)^{k-1}/k mod p and power sum vanishing).
Combine: p³ | (C(2p,p) - 2), giving C(2p-1,p-1) ≡ 1 (mod p³).

## Historical Context
Joseph Wolstenholme proved this in 1862. Only two Wolstenholme primes
are known: 16843 and 2124679, both ≡ 3 (mod 4).
-/
import Mathlib

set_option linter.unusedSectionVars false

open Nat Finset BigOperators

namespace Wolstenholme

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-
## Section 1: Power Sum Lemma

For prime p and m with (p-1) ∤ m, Σ_{x ∈ (ZMod p)ˣ} x^m = 0.
Proof: pick generator g of cyclic group (ZMod p)ˣ.
g^m · S = S by reindexing via x ↦ g·x. Since g^m ≠ 1, S = 0.
-/

lemma sum_units_pow_eq_zero (m : ℕ) (hm : ¬((p - 1) ∣ m)) (hp2 : 2 ≤ p) :
    ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ m = 0 := by
  -- Get a generator g of the cyclic group (ZMod p)ˣ
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (ZMod p)ˣ)
  -- g^m ≠ 1 since orderOf g = |group| = p-1 and (p-1) ∤ m
  have hgm : g ^ m ≠ 1 := by
    intro heq
    apply hm
    rw [← ZMod.card_units_eq_totient p, ← Nat.totient_prime hp.out,
        ← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact orderOf_dvd_of_pow_eq_one heq
  -- Key: (↑g)^m * S = S by reindexing x ↦ g*x
  set S := ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ m with hS_def
  have key : (↑g : ZMod p) ^ m * S = S := by
    simp only [hS_def, Finset.mul_sum]
    conv_rhs => rw [show (Finset.univ : Finset (ZMod p)ˣ) =
      Finset.univ.map (Equiv.mulLeft g).toEmbedding from
      (Finset.map_univ_equiv _).symm]
    simp only [Finset.sum_map, Equiv.toEmbedding_apply, Equiv.mulLeft_apply,
               Units.val_mul, mul_pow]
  -- (↑g)^m ≠ 1 in ZMod p (from g^m ≠ 1 as a unit)
  have hne : (↑g : ZMod p) ^ m ≠ 1 := by
    intro h
    apply hgm
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    exact h
  -- ((↑g)^m - 1) * S = 0 from key, and (↑g)^m - 1 ≠ 0, so S = 0
  have h0 : ((↑g : ZMod p) ^ m - 1) * S = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact key
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)

/-
## Section 2: C(p-1, k) ≡ (-1)^k (mod p)

descFactorial(p-1, k) = (p-1)(p-2)···(p-k) ≡ (-1)(-2)···(-k) = (-1)^k · k! in ZMod p.
Since C(p-1,k) = descFactorial(p-1,k)/k! and k! is a unit in ZMod p: C(p-1,k) ≡ (-1)^k.
-/

lemma choose_pred_neg_one_pow (k : ℕ) (hk : k ≤ p - 1) (hp5 : 5 ≤ p) :
    (Nat.choose (p - 1) k : ZMod p) = (-1) ^ k := by
  suffices h : (k.factorial : ZMod p) * (Nat.choose (p - 1) k : ZMod p) =
    (k.factorial : ZMod p) * (-1) ^ k by
    have hne : (k.factorial : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_zmod_eq_zero_iff_dvd]
      exact fun hdvd => absurd (hp.out.dvd_factorial.mp hdvd) (by omega)
    exact mul_left_cancel₀ hne h
  -- Cast the ℕ identity k! * C(n, k) = n.descFactorial k
  rw [← Nat.cast_mul, Nat.factorial_mul_choose hk]
  -- Now show: ((p-1).descFactorial k : ZMod p) = (k! : ZMod p) * (-1)^k
  rw [mul_comm]
  -- Prove by induction on k
  induction k with
  | zero => simp [Nat.descFactorial]
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    rw [ih (by omega)]
    -- Need: (p - 1 - k : ℕ) cast to ZMod p equals -(k + 1 : ℕ)
    have h_sum : (p - 1 - k) + (k + 1) = p := by omega
    have : ((p - 1 - k : ℕ) : ZMod p) = -((k + 1 : ℕ) : ZMod p) := by
      have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self_eq_zero
      have h_add : ((p - 1 - k : ℕ) : ZMod p) + ((k + 1 : ℕ) : ZMod p) = 0 := by
        rw [← Nat.cast_add, h_sum, hp0]
      exact eq_neg_of_add_eq_zero_left h_add
    rw [this]; ring

/-
## Section 3: Key Identity and Divisibility

k · C(n,k) = n · C(n-1, k-1)  ⟹  k · (C(p,k)/p) = C(p-1,k-1)
In ZMod p: (k : ZMod p) · (bₖ : ZMod p) = (-1)^(k-1), so bₖ² ≡ 1/k² ≡ k² (mod p).
Sum vanishes by power sum lemma (m = 2, (p-1) ∤ 2 for p ≥ 5).
-/

/-- k · C(n,k) = n · C(n-1, k-1) for 1 ≤ k ≤ n.
    From (n+1)·C(n,k) = C(n+1,k+1)·(k+1) with n ↦ n-1, k ↦ k-1. -/
lemma mul_choose_eq (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    k * Nat.choose n k = n * Nat.choose (n - 1) (k - 1) := by
  have h := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
  rw [show (n - 1) + 1 = n from by omega, show (k - 1) + 1 = k from by omega] at h
  linarith

/-- k · bₖ = C(p-1, k-1) where bₖ = C(p,k)/p. -/
lemma mul_b_eq (hp' : Nat.Prime p) (k : ℕ) (hk0 : 1 ≤ k) (hkp : k < p) :
    k * (Nat.choose p k / p) = Nat.choose (p - 1) (k - 1) := by
  have h_dvd : p ∣ Nat.choose p k := by apply hp'.dvd_choose <;> omega
  have h_id : k * Nat.choose p k = p * Nat.choose (p - 1) (k - 1) :=
    mul_choose_eq p k hk0 (by omega)
  obtain ⟨bk, hbk⟩ := h_dvd
  rw [hbk] at h_id
  rw [hbk, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
  exact mul_left_cancel₀ (by omega : (p : ℕ) ≠ 0) (by linarith)

-- Per-element identity: bₖ² ≡ k⁻² in ZMod p
private lemma b_sq_eq_inv_sq (hp' : Nat.Prime p) (h5 : 5 ≤ p) (k : ℕ)
    (hk : k ∈ Finset.Ico 1 p) :
    ((Nat.choose p k / p : ℕ) : ZMod p) ^ 2 = ((k : ℕ) : ZMod p)⁻¹ ^ 2 := by
  have hm := Finset.mem_Ico.mp hk
  have hk_ne : ((k : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have h_mul := mul_b_eq p hp' k (by omega) (by omega)
  have h_choose := choose_pred_neg_one_pow p (k - 1) (by omega) h5
  have h_zmod : ((k : ℕ) : ZMod p) * ((Nat.choose p k / p : ℕ) : ZMod p) =
      (-1) ^ (k - 1) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) h_mul ▸ h_choose
  have h_b : ((Nat.choose p k / p : ℕ) : ZMod p) = (-1) ^ (k - 1) * ((k : ℕ) : ZMod p)⁻¹ := by
    rw [← h_zmod, mul_comm, mul_assoc, mul_inv_cancel₀ hk_ne, mul_one]
  rw [h_b, mul_pow, ← pow_mul, show (k - 1) * 2 = 2 * (k - 1) from by ring]
  simp [neg_one_sq, one_pow, pow_mul, one_mul]

/-- The key divisibility: p | Σ_{k ∈ Ico 1 p} (C(p,k)/p)² for prime p ≥ 5. -/
lemma p_dvd_sum_b_sq (hp' : Nat.Prime p) (h5 : 5 ≤ p) :
    (p : ℕ) ∣ ∑ k ∈ Finset.Ico 1 p, (Nat.choose p k / p) ^ 2 := by
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
  push_cast
  -- Each bₖ² = k⁻² in ZMod p
  have h_eq : ∑ k ∈ Finset.Ico 1 p, ((Nat.choose p k / p : ℕ) : ZMod p) ^ 2 =
      ∑ k ∈ Finset.Ico 1 p, ((k : ℕ) : ZMod p)⁻¹ ^ 2 :=
    Finset.sum_congr rfl (fun k hk => b_sq_eq_inv_sq p hp' h5 k hk)
  rw [h_eq]
  -- Use Fermat: a⁻¹ = a^(p-2) for a ≠ 0 in ZMod p, so k⁻² = k^(2(p-2))
  have h_ne : ∀ k ∈ Finset.Ico 1 p, ((k : ℕ) : ZMod p) ≠ 0 := by
    intro k hk; rw [Ne, ZMod.natCast_zmod_eq_zero_iff_dvd]
    have := Finset.mem_Ico.mp hk
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have h_fermat : ∑ k ∈ Finset.Ico 1 p, ((k : ℕ) : ZMod p)⁻¹ ^ 2 =
      ∑ k ∈ Finset.Ico 1 p, ((k : ℕ) : ZMod p) ^ (2 * (p - 2)) := by
    apply Finset.sum_congr rfl; intro k hk
    rw [inv_pow, ← pow_mul]
    congr 1
    -- a⁻¹ = a^(p-2) via Fermat's little theorem
    have hflt := ZMod.pow_card_sub_one_eq_one (h_ne k hk)
    rw [ZMod.card p] at hflt
    have : ((k : ℕ) : ZMod p) * ((k : ℕ) : ZMod p) ^ (p - 2) = 1 := by
      rw [← pow_succ, show p - 2 + 1 = p - 1 from by omega, hflt]
    calc ((k : ℕ) : ZMod p)⁻¹
        = ((k : ℕ) : ZMod p)⁻¹ * 1 := (mul_one _).symm
      _ = ((k : ℕ) : ZMod p)⁻¹ * (((k : ℕ) : ZMod p) * ((k : ℕ) : ZMod p) ^ (p - 2)) := by
            rw [this]
      _ = ((k : ℕ) : ZMod p) ^ (p - 2) := by
            rw [← mul_assoc, inv_mul_cancel₀ (h_ne k hk), one_mul]
  rw [h_fermat]
  -- Relate Ico sum to units sum via bijection Units.mk0
  have h_bij : ∑ k ∈ Finset.Ico 1 p, ((k : ℕ) : ZMod p) ^ (2 * (p - 2)) =
      ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ (2 * (p - 2)) := by
    symm
    apply Finset.sum_nbij' (fun x _ => (x : ZMod p).val) (fun k hk =>
      Units.mk0 ((k : ℕ) : ZMod p) (h_ne k hk))
    · intro x _; exact Finset.mem_Ico.mpr
        ⟨Nat.pos_of_ne_zero (ZMod.val_ne_zero.mpr (Units.ne_zero x)), ZMod.val_lt _⟩
    · intro _ _; exact Finset.mem_univ _
    · intro x _; ext; simp [ZMod.natCast_zmod_val]
    · intro k hk; simp [ZMod.val_natCast_of_lt (show k < p from (Finset.mem_Ico.mp hk).2)]
    · intro x _; simp [ZMod.natCast_zmod_val]
  rw [h_bij]
  -- Apply sum_units_pow_eq_zero with m = 2(p-2)
  -- Need: (p-1) ∤ 2(p-2). Since p ≥ 5: 2(p-2) = 2p-4, and
  -- 2p-4 = (p-1) + (p-3), so 2(p-2) mod (p-1) = p-3 ≠ 0.
  exact sum_units_pow_eq_zero p (2 * (p - 2)) (by omega) (by omega)

/-
## Section 4: Wolstenholme's Theorem
-/

/-- C(2p-1, p-1) -/
def centralBinomial (p : ℕ) : ℕ := Nat.choose (2 * p - 1) (p - 1)

/-- Vandermonde: C(2p,p) = Σ C(p,k)². -/
lemma vandermonde :
    Nat.choose (2 * p) p =
    ∑ k ∈ Finset.range (p + 1), (Nat.choose p k) ^ 2 := by
  rw [show 2 * p = p + p from by ring, Nat.add_choose_eq,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => Nat.choose p i * Nat.choose p j) p]
  exact Finset.sum_congr rfl fun k hk => by
    rw [Nat.choose_symm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), sq]

/-- C(2p,p) = 2 + Σ_{k=1}^{p-1} C(p,k)² for p ≥ 3. -/
lemma vandermonde_decomp (h3 : 3 ≤ p) :
    Nat.choose (2 * p) p =
    2 + ∑ k ∈ Finset.Ico 1 p, (Nat.choose p k) ^ 2 := by
  rw [vandermonde p]
  rw [Finset.sum_range_succ, Nat.choose_self, one_pow]
  have h0 : (0 : ℕ) ∈ Finset.range p := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ h0]
  have : (Finset.range p).erase 0 = Finset.Ico 1 p := by
    ext k; simp [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this]; simp [Nat.choose_zero_right]; ring

/-- C(2p,p) = 2 · C(2p-1, p-1). -/
lemma choose_double_eq (hp1 : 1 ≤ p) :
    Nat.choose (2 * p) p = 2 * centralBinomial p := by
  unfold centralBinomial
  have hpascal := Nat.choose_succ_succ (2 * p - 1) (p - 1)
  simp only [Nat.succ_eq_add_one, show 2 * p - 1 + 1 = 2 * p from by omega,
             show p - 1 + 1 = p from by omega] at hpascal
  have hsymm : Nat.choose (2 * p - 1) p = Nat.choose (2 * p - 1) (p - 1) := by
    rw [← Nat.choose_symm (show p ≤ 2 * p - 1 from by omega),
        show 2 * p - 1 - p = p - 1 from by omega]
  linarith

/-- Factor p² from middle terms. -/
lemma middle_sum_factor (hp' : Nat.Prime p) :
    ∑ k ∈ Finset.Ico 1 p, (Nat.choose p k) ^ 2 =
    p ^ 2 * ∑ k ∈ Finset.Ico 1 p, (Nat.choose p k / p) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hm := Finset.mem_Ico.mp hk
  have hdvd : p ∣ Nat.choose p k := by apply hp'.dvd_choose <;> omega
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Nat.mul_div_cancel_left _ (by omega : 0 < p)]; ring

/-- p³ | Σ_{k=1}^{p-1} C(p,k)². -/
lemma middle_sum_dvd_p_cubed (hp' : Nat.Prime p) (h5 : 5 ≤ p) :
    p ^ 3 ∣ ∑ k ∈ Finset.Ico 1 p, (Nat.choose p k) ^ 2 := by
  rw [middle_sum_factor p hp', show p ^ 3 = p ^ 2 * p from by ring]
  exact Nat.mul_dvd_mul_left _ (p_dvd_sum_b_sq p hp' h5)

/-- C(2p,p) ≡ 2 (mod p³) for prime p ≥ 5. -/
lemma choose_two_p_mod_cubed (hp' : Nat.Prime p) (h5 : 5 ≤ p) :
    Nat.choose (2 * p) p % (p ^ 3) = 2 := by
  rw [vandermonde_decomp p (by omega)]
  obtain ⟨c, hc⟩ := middle_sum_dvd_p_cubed p hp' h5
  rw [hc, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  calc 2 < 5 ^ 3 := by norm_num
    _ ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3

/-- 2 is coprime to p³ for odd prime p. -/
lemma coprime_two_p_cubed (hp' : Nat.Prime p) (h5 : 5 ≤ p) :
    Nat.Coprime 2 (p ^ 3) :=
  Nat.Coprime.pow_right _ (Nat.coprime_comm.mpr
    (Nat.coprime_two_right.mpr (hp'.odd_of_ne_two (by omega))))

/-- **Wolstenholme's theorem**: C(2p-1, p-1) ≡ 1 (mod p³) for prime p ≥ 5. -/
theorem wolstenholme (hp' : Nat.Prime p) (h5 : 5 ≤ p) :
    centralBinomial p % (p ^ 3) = 1 := by
  have hpos : 0 < centralBinomial p := by
    unfold centralBinomial; exact Nat.choose_pos (by omega)
  have hmod : 2 * centralBinomial p % (p ^ 3) = 2 := by
    rw [← choose_double_eq p (by omega)]; exact choose_two_p_mod_cubed p hp' h5
  have hdvd : p ^ 3 ∣ 2 * (centralBinomial p - 1) := by
    have hq := Nat.div_add_mod (2 * centralBinomial p) (p ^ 3)
    rw [hmod] at hq; exact ⟨2 * centralBinomial p / p ^ 3, by omega⟩
  have hdvd1 : p ^ 3 ∣ (centralBinomial p - 1) :=
    (coprime_two_p_cubed p hp' h5).symm.dvd_of_dvd_mul_left hdvd
  obtain ⟨q, hq⟩ := hdvd1
  have ha : centralBinomial p = p ^ 3 * q + 1 := by omega
  rw [ha, show p ^ 3 * q + 1 = 1 + p ^ 3 * q from by ring, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  calc 1 < 5 ^ 3 := by norm_num
    _ ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3

/-
## Section 5: Wolstenholme Primes

A Wolstenholme prime satisfies C(2p-1,p-1) ≡ 1 (mod p⁴).
Only 16843 and 2124679 are known; both are ≡ 3 (mod 4).
-/

/-- A Wolstenholme prime: C(2p-1,p-1) ≡ 1 (mod p⁴). -/
def IsWolstenholmePrime (p : ℕ) : Prop :=
  p.Prime ∧ 5 ≤ p ∧ centralBinomial p % (p ^ 4) = 1

/-- Every Wolstenholme prime satisfies Wolstenholme's theorem. -/
theorem wolstenholme_prime_satisfies (hw : IsWolstenholmePrime p) :
    centralBinomial p % (p ^ 3) = 1 :=
  wolstenholme p hw.1 hw.2.1

/-- Open question: Does a Wolstenholme prime p ≡ 1 (mod 4) exist?
    The known Wolstenholme primes (16843, 2124679) are both ≡ 3 (mod 4). -/
axiom wolstenholme_prime_mod4_question :
  (∃ p, IsWolstenholmePrime p ∧ p % 4 = 1) ∨
  (∀ p, IsWolstenholmePrime p → p % 4 = 3)

end Wolstenholme
