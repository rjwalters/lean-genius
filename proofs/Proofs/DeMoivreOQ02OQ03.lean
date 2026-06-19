import Mathlib

/-
# De Moivre OQ-02-03: Minimax Property of Chebyshev Polynomials

## Research Question

Among all *monic* real polynomials of degree `n ≥ 1`, the monic Chebyshev
polynomial
  Mₙ(x) = Tₙ(x) / 2^(n-1)
has the smallest sup-norm on `[-1, 1]`, and that minimal value is `2^(1-n)`.
This is the classical Chebyshev equioscillation / minimax theorem.

Mathlib's `Mathlib/RingTheory/Polynomial/Chebyshev.lean` lists this as an
explicit TODO ("Prove minimax properties of Chebyshev polynomials"), and also
lacks the degree / leading-coefficient facts for `Tₙ`.  This file builds that
missing infrastructure from the De Moivre identity `Tₙ(cos θ) = cos (n θ)` and
the two-term recurrence `T_{n+2} = 2 X T_{n+1} - Tₙ`, and assembles the
achievability half of the minimax theorem: the monic Chebyshev polynomial is
monic of degree `n`, has sup-norm `2^(1-n)` on `[-1,1]`, and equioscillates
between `±2^(1-n)` at the `n+1` extreme nodes.

## Results

Analysis core (from De Moivre):
* `chebyshev_abs_eval_le_one` : `|Tₙ(x)| ≤ 1` for `x ∈ [-1,1]`.
* `chebyshev_eval_node`       : `Tₙ(cos(kπ/n)) = (-1)^k` — equioscillation at the
  `n+1` Chebyshev extreme nodes.

Degree infrastructure (absent from Mathlib):
* `chebyshev_natDegree`       : `natDegree (Tₙ) = n`.
* `chebyshev_leadingCoeff`    : `leadingCoeff (Tₙ) = 2^(n-1)` for `n ≥ 1`.

Monic normalization and the achievability half of the minimax:
* `monicChebyshev`            : the monic polynomial `Tₙ / 2^(n-1)`.
* `monicChebyshev_monic`      : it is monic of degree `n`.
* `monicChebyshev_abs_le`     : its sup-norm on `[-1,1]` is `≤ 2^(1-n)`.
* `monicChebyshev_eval_node`  : it equioscillates between `±2^(1-n)`.
-/

open Polynomial Polynomial.Chebyshev Real

namespace DeMoivreOQ0203

/-! ## Part I: The sup-norm bound and equioscillation (analysis core) -/

/-- On `[-1,1]`, every Chebyshev polynomial of the first kind is bounded by `1`
in absolute value: the De Moivre identity `Tₙ(cos θ) = cos (n θ)` puts the graph
inside the equioscillation envelope. -/
theorem chebyshev_abs_eval_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(T ℝ (n : ℤ)).eval x| ≤ 1 := by
  obtain ⟨h1, h2⟩ := hx
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos h1 h2
  rw [← hcos, T_real_cos]
  exact abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- Equioscillation: at the `n+1` extreme nodes `xₖ = cos(kπ/n)` the Chebyshev
polynomial attains its extreme values with alternating sign,
`Tₙ(cos(kπ/n)) = (-1)^k`. -/
theorem chebyshev_eval_node (n k : ℕ) (hn : 0 < n) :
    (T ℝ (n : ℤ)).eval (Real.cos (k * π / n)) = (-1) ^ k := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [T_real_cos]
  have harg : ((n : ℤ) : ℝ) * (k * π / n) = (k : ℝ) * π := by
    push_cast
    field_simp
    try ring
  rw [harg, Real.cos_nat_mul_pi]

/-- The bound is sharp at the endpoint: `Tₙ(1) = 1`. -/
theorem chebyshev_eval_one (n : ℕ) : (T ℝ (n : ℤ)).eval 1 = 1 := by
  rw [T_eval_one]

/-! ## Part II: Degree and leading coefficient of `Tₙ` (infrastructure) -/

/-- One recurrence step `T_{n+2} = 2 X T_{n+1} - Tₙ`: given `deg a = d`,
`lead a = c ≠ 0` and `deg b ≤ d`, the polynomial `2 X a - b` has degree `d + 1`
and leading coefficient `2 c`. -/
private theorem deg_lead_recurrence_step (a b : ℝ[X]) (d : ℕ) (c : ℝ)
    (hca : c ≠ 0) (hda : a.natDegree = d) (hla : a.leadingCoeff = c)
    (hdb : b.natDegree ≤ d) :
    (2 * X * a - b).natDegree = d + 1 ∧ (2 * X * a - b).leadingCoeff = 2 * c := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h, leadingCoeff_zero] at hla; exact hca hla.symm
  have h2C : (2 : ℝ[X]) = C 2 := by rw [C_ofNat]
  have hnd2X : ((2 : ℝ[X]) * X).natDegree = 1 := by
    rw [h2C]; exact natDegree_C_mul_X 2 (by norm_num)
  have hlc2X : ((2 : ℝ[X]) * X).leadingCoeff = 2 := by
    rw [h2C]; exact leadingCoeff_C_mul_X 2
  have h2X0 : (2 : ℝ[X]) * X ≠ 0 := by
    rw [← leadingCoeff_ne_zero, hlc2X]; norm_num
  have hndM : ((2 : ℝ[X]) * X * a).natDegree = d + 1 := by
    rw [natDegree_mul h2X0 ha0, hnd2X, hda]; omega
  have hlcM : ((2 : ℝ[X]) * X * a).leadingCoeff = 2 * c := by
    rw [leadingCoeff_mul, hlc2X, hla]
  have hMne : (2 : ℝ[X]) * X * a ≠ 0 := by
    rw [← leadingCoeff_ne_zero, hlcM]; exact mul_ne_zero two_ne_zero hca
  have hdeglt : b.degree < ((2 : ℝ[X]) * X * a).degree := by
    rw [degree_eq_natDegree hMne, hndM]
    calc b.degree ≤ (b.natDegree : WithBot ℕ) := degree_le_natDegree
      _ ≤ (d : WithBot ℕ) := by exact_mod_cast hdb
      _ < ((d + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self d
  refine ⟨?_, ?_⟩
  · rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [hndM]; omega), hndM]
  · rw [leadingCoeff_sub_of_degree_lt hdeglt, hlcM]

/-- Paired degree/leading-coefficient statement for `T_{n+1}` and `T_{n+2}`,
proved by a single induction driven by the two-term recurrence. -/
private theorem chebyshev_deg_lead_pair : ∀ n : ℕ,
    ((T ℝ ((n : ℤ) + 1)).natDegree = n + 1 ∧
      (T ℝ ((n : ℤ) + 1)).leadingCoeff = 2 ^ n) ∧
    ((T ℝ ((n : ℤ) + 2)).natDegree = n + 2 ∧
      (T ℝ ((n : ℤ) + 2)).leadingCoeff = 2 ^ (n + 1)) := by
  intro n
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_add]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [T_one, natDegree_X]
    · rw [T_one, leadingCoeff_X, pow_zero]
    · rw [T_two]; compute_degree!
    · rw [T_two,
        show (2 * X ^ 2 - 1 : ℝ[X]) = C (-1) + C 2 * X ^ 2 from by
          rw [C_ofNat, C_neg, C_1]; ring,
        leadingCoeff_add_of_degree_lt, leadingCoeff_C_mul_X_pow]
      · norm_num
      · rw [degree_C_mul_X_pow 2 (two_ne_zero)]
        exact lt_of_le_of_lt degree_C_le (by norm_num)
  | succ k ih =>
    obtain ⟨hd1, _⟩ := ih.1
    obtain ⟨hd2, hl2⟩ := ih.2
    have idx1 : ((↑(k + 1) : ℤ) + 1) = (k : ℤ) + 2 := by push_cast; ring
    have idx2 : ((↑(k + 1) : ℤ) + 2) = (k : ℤ) + 3 := by push_cast; ring
    have hrec : T ℝ ((k : ℤ) + 3) =
        2 * X * T ℝ ((k : ℤ) + 2) - T ℝ ((k : ℤ) + 1) := by
      have h := T_add_two ℝ ((k : ℤ) + 1)
      have e : ((k : ℤ) + 1 + 2) = (k : ℤ) + 3 := by ring
      have e' : ((k : ℤ) + 1 + 1) = (k : ℤ) + 2 := by ring
      rw [e, e'] at h; exact h
    have step := deg_lead_recurrence_step (T ℝ ((k : ℤ) + 2)) (T ℝ ((k : ℤ) + 1))
      (k + 2) (2 ^ (k + 1)) (pow_ne_zero _ two_ne_zero) hd2 hl2 (by rw [hd1]; omega)
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [idx1]; exact hd2
    · rw [idx1]; exact hl2
    · rw [idx2, hrec, step.1]
    · rw [idx2, hrec, step.2]; ring

/-- `Tₙ` has degree exactly `n`. -/
theorem chebyshev_natDegree (n : ℕ) : (T ℝ (n : ℤ)).natDegree = n := by
  cases n with
  | zero => simp [T_zero]
  | succ m =>
    have h := (chebyshev_deg_lead_pair m).1.1
    have hidx : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hidx] at h; exact h

/-- `Tₙ` has leading coefficient `2^(n-1)` for `n ≥ 1`. -/
theorem chebyshev_leadingCoeff (n : ℕ) (hn : 0 < n) :
    (T ℝ (n : ℤ)).leadingCoeff = 2 ^ (n - 1) := by
  cases n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ m =>
    have h := (chebyshev_deg_lead_pair m).1.2
    have hidx : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hidx] at h
    simpa using h

/-! ## Part III: The monic Chebyshev polynomial and the achievability half -/

/-- The monic Chebyshev polynomial `Mₙ = Tₙ / 2^(n-1)`. -/
noncomputable def monicChebyshev (n : ℕ) : ℝ[X] :=
  C ((2 : ℝ) ^ (n - 1))⁻¹ * T ℝ (n : ℤ)

/-- `Mₙ` is monic. -/
theorem monicChebyshev_monic (n : ℕ) (hn : 0 < n) : (monicChebyshev n).Monic := by
  rw [Monic.def, monicChebyshev, leadingCoeff_mul, leadingCoeff_C,
    chebyshev_leadingCoeff n hn, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)]

/-- `Mₙ` has degree `n`. -/
theorem monicChebyshev_natDegree (n : ℕ) :
    (monicChebyshev n).natDegree = n := by
  rw [monicChebyshev, natDegree_C_mul (inv_ne_zero (pow_ne_zero _ two_ne_zero)),
    chebyshev_natDegree]

/-- Sup-norm bound: `|Mₙ(x)| ≤ 2^(1-n)` on `[-1,1]`. -/
theorem monicChebyshev_abs_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(monicChebyshev n).eval x| ≤ ((2 : ℝ) ^ (n - 1))⁻¹ := by
  rw [monicChebyshev, eval_mul, eval_C, abs_mul, abs_of_pos (by positivity)]
  calc ((2 : ℝ) ^ (n - 1))⁻¹ * |(T ℝ (n : ℤ)).eval x|
      ≤ ((2 : ℝ) ^ (n - 1))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (chebyshev_abs_eval_le_one n hx) (by positivity)
    _ = ((2 : ℝ) ^ (n - 1))⁻¹ := mul_one _

/-- Equioscillation of the monic polynomial: `Mₙ(cos(kπ/n)) = (-1)^k · 2^(1-n)`. -/
theorem monicChebyshev_eval_node (n k : ℕ) (hn : 0 < n) :
    (monicChebyshev n).eval (Real.cos (k * π / n)) =
      (-1) ^ k * ((2 : ℝ) ^ (n - 1))⁻¹ := by
  rw [monicChebyshev, eval_mul, eval_C, chebyshev_eval_node n k hn]; ring

end DeMoivreOQ0203
