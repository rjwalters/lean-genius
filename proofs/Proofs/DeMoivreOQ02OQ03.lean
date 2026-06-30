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
between `±2^(1-n)` at the `n+1` extreme nodes.  It then proves the optimality
(lower-bound) half by the classical equioscillation argument, giving the full
minimax theorem `chebyshev_minimax`.

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

Optimality (lower-bound) half and the full theorem:
* `monicChebyshev_minimax`    : every monic degree-`n` `p` has `|p| ≥ 2^(1-n)`
  somewhere on `[-1,1]` (equioscillation + IVT root-count argument).
* `chebyshev_minimax`         : the full minimax theorem (achievability ∧ optimality).
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
        show (2 * X ^ 2 - 1 : ℝ[X]) = Polynomial.C (-1) + Polynomial.C 2 * X ^ 2 from by
          rw [C_ofNat, Polynomial.C_neg, Polynomial.C_1]; ring,
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

/-! ## Part IV: The optimality (lower-bound) half of the minimax theorem

The deep direction: *no* monic polynomial of degree `n` can have sup-norm on
`[-1,1]` smaller than `Mₙ`'s value `2^(1-n)`.  The proof is the classical
equioscillation argument.  If a monic `p` of degree `n` had `‖p‖∞ < 2^(1-n)`,
then `q = Mₙ - p` would inherit the sign of `Mₙ` at each of the `n+1` extreme
nodes `cos(kπ/n)` (strict alternation), so by the intermediate value theorem `q`
would have a root strictly between every pair of consecutive nodes — `n` distinct
roots.  But `q` is a difference of two monic degree-`n` polynomials, hence has
degree `< n`; a nonzero polynomial of degree `< n` cannot have `n` roots. -/

/-- Strict monotonicity of the Chebyshev extreme nodes `cos(kπ/n)`: over
`0 ≤ k ≤ n` they strictly decrease in `k`. -/
private theorem node_strict_anti (n : ℕ) (hn : 0 < n) {i j : ℕ} (hj : j ≤ n)
    (hij : i < j) : Real.cos (j * π / n) < Real.cos (i * π / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  have hi_le : (i : ℝ) ≤ n := by exact_mod_cast (le_of_lt (lt_of_lt_of_le hij hj))
  have hj_le : (j : ℝ) ≤ n := by exact_mod_cast hj
  apply Real.strictAntiOn_cos
  · refine ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg i) hpi.le) hn'.le, ?_⟩
    rw [div_le_iff₀ hn']; nlinarith [hpi, hi_le]
  · refine ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg j) hpi.le) hn'.le, ?_⟩
    rw [div_le_iff₀ hn']; nlinarith [hpi, hj_le]
  · rw [div_lt_div_iff_of_pos_right hn']
    have hij' : (i : ℝ) < j := by exact_mod_cast hij
    nlinarith [hpi]

/-- Non-strict (antitone) version of `node_strict_anti`. -/
private theorem node_anti (n : ℕ) (hn : 0 < n) {i j : ℕ} (hj : j ≤ n)
    (hij : i ≤ j) : Real.cos (j * π / n) ≤ Real.cos (i * π / n) := by
  rcases eq_or_lt_of_le hij with h | h
  · exact le_of_eq (by rw [h])
  · exact (node_strict_anti n hn hj h).le

set_option maxHeartbeats 800000 in
/-- **Optimality (lower-bound) half of the Chebyshev minimax theorem.**
Every monic real polynomial of degree `n ≥ 1` attains absolute value at least
`2^(1-n)` somewhere on `[-1,1]`; equivalently, its sup-norm there is `≥ 2^(1-n)`,
so it cannot beat the monic Chebyshev polynomial. -/
theorem monicChebyshev_minimax (p : ℝ[X]) (hp : p.Monic) (n : ℕ) (hn : 0 < n)
    (hpdeg : p.natDegree = n) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1, ((2 : ℝ) ^ (n - 1))⁻¹ ≤ |p.eval x| := by
  classical
  by_contra hcon
  push_neg at hcon
  set M : ℝ := ((2 : ℝ) ^ (n - 1))⁻¹ with hM_def
  have hMpos : 0 < M := by rw [hM_def]; positivity
  set q : ℝ[X] := monicChebyshev n - p with hq_def
  -- Strict sign alternation of `q` at the extreme nodes: `(-1)^k · q(cos kπ/n) > 0`.
  have halt : ∀ k : ℕ, k ≤ n → 0 < (-1 : ℝ) ^ k * q.eval (Real.cos (k * π / n)) := by
    intro k hk
    have hmem : Real.cos (k * π / n) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hev : q.eval (Real.cos (k * π / n)) = (-1) ^ k * M - p.eval (Real.cos (k * π / n)) := by
      rw [hq_def, eval_sub, monicChebyshev_eval_node n k hn, ← hM_def]
    have hsq : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨k, by ring⟩
    have hpb : (-1 : ℝ) ^ k * p.eval (Real.cos (k * π / n)) < M := by
      calc (-1 : ℝ) ^ k * p.eval (Real.cos (k * π / n))
          ≤ |(-1 : ℝ) ^ k * p.eval (Real.cos (k * π / n))| := le_abs_self _
        _ = |p.eval (Real.cos (k * π / n))| := by rw [abs_mul]; simp [abs_pow]
        _ < M := hcon _ hmem
    have hcalc : (-1 : ℝ) ^ k * q.eval (Real.cos (k * π / n))
        = ((-1) ^ k * (-1) ^ k) * M - (-1) ^ k * p.eval (Real.cos (k * π / n)) := by
      rw [hev]; ring
    rw [hcalc, hsq, one_mul]; linarith
  -- `q ≠ 0`: it is strictly positive at the `k = 0` node.
  have hq_ne : q ≠ 0 := by
    intro h
    have h0 := halt 0 (Nat.zero_le n)
    rw [h] at h0; simp at h0
  -- `q` has degree `< n` (difference of two monic degree-`n` polynomials).
  have hdeg : q.natDegree < n := by
    have hpne : p ≠ 0 := hp.ne_zero
    have hMcne : monicChebyshev n ≠ 0 := (monicChebyshev_monic n hn).ne_zero
    have hdegM : (monicChebyshev n).degree = (n : WithBot ℕ) := by
      rw [degree_eq_natDegree hMcne, monicChebyshev_natDegree]
    have hdegp : p.degree = (n : WithBot ℕ) := by
      rw [degree_eq_natDegree hpne, hpdeg]
    have hlc : (monicChebyshev n).leadingCoeff = p.leadingCoeff := by
      rw [Monic.def.1 (monicChebyshev_monic n hn), Monic.def.1 hp]
    have hsub : (monicChebyshev n - p).degree < (monicChebyshev n).degree :=
      degree_sub_lt (by rw [hdegM, hdegp]) hMcne hlc
    rw [hdegM, ← hq_def] at hsub
    exact (natDegree_lt_iff_degree_lt hq_ne).mpr hsub
  -- For each consecutive pair of nodes, `q` has a root strictly between them.
  have hroot : ∀ k : Fin n, ∃ r, Real.cos ((k.val + 1) * π / n) < r ∧
      r < Real.cos (k.val * π / n) ∧ q.eval r = 0 := by
    intro k
    have hkn : k.val < n := k.isLt
    have hk1_le : k.val + 1 ≤ n := hkn
    have hlt : Real.cos ((k.val + 1) * π / n) < Real.cos (k.val * π / n) := by
      have h := node_strict_anti n hn hk1_le (Nat.lt_succ_self k.val)
      rwa [Nat.cast_add, Nat.cast_one] at h
    have s0 := halt k.val (le_of_lt hkn)
    have s1 := halt (k.val + 1) hk1_le
    rw [Nat.cast_add, Nat.cast_one] at s1
    have hne0 : q.eval (Real.cos (k.val * π / n)) ≠ 0 := by
      intro h; rw [h, mul_zero] at s0; exact lt_irrefl 0 s0
    have hne1 : q.eval (Real.cos ((k.val + 1) * π / n)) ≠ 0 := by
      intro h; rw [h, mul_zero] at s1; exact lt_irrefl 0 s1
    have hmem0 : (0 : ℝ) ∈ Set.uIcc (q.eval (Real.cos ((k.val + 1) * π / n)))
        (q.eval (Real.cos (k.val * π / n))) := by
      rcases Nat.even_or_odd k.val with he | ho
      · have e0 : (-1 : ℝ) ^ k.val = 1 := he.neg_one_pow
        have e1 : (-1 : ℝ) ^ (k.val + 1) = -1 := by rw [pow_succ, e0]; ring
        rw [e0, one_mul] at s0; rw [e1] at s1
        exact Set.mem_uIcc_of_le (by linarith) (by linarith)
      · have e0 : (-1 : ℝ) ^ k.val = -1 := ho.neg_one_pow
        have e1 : (-1 : ℝ) ^ (k.val + 1) = 1 := by rw [pow_succ, e0]; ring
        rw [e0] at s0; rw [e1, one_mul] at s1
        exact Set.mem_uIcc_of_ge (by linarith) (by linarith)
    have hcont : ContinuousOn (fun x => q.eval x)
        (Set.uIcc (Real.cos ((k.val + 1) * π / n)) (Real.cos (k.val * π / n))) :=
      (Polynomial.continuous q).continuousOn
    obtain ⟨r, hr_mem, hr_eq⟩ := intermediate_value_uIcc hcont hmem0
    rw [Set.uIcc_of_le hlt.le] at hr_mem
    obtain ⟨hr1, hr2⟩ := hr_mem
    refine ⟨r, ?_, ?_, hr_eq⟩
    · rcases eq_or_lt_of_le hr1 with h | h
      · rw [← h] at hr_eq; exact absurd hr_eq hne1
      · exact h
    · rcases eq_or_lt_of_le hr2 with h | h
      · rw [h] at hr_eq; exact absurd hr_eq hne0
      · exact h
  -- Collect one root per interval into an injective family `f : Fin n → ℝ`.
  let f : Fin n → ℝ := fun k => Classical.choose (hroot k)
  have hf : ∀ k : Fin n, Real.cos ((k.val + 1) * π / n) < f k ∧
      f k < Real.cos (k.val * π / n) ∧ q.eval (f k) = 0 :=
    fun k => Classical.choose_spec (hroot k)
  have hf_root : ∀ k : Fin n, f k ∈ q.roots.toFinset := by
    intro k; rw [Multiset.mem_toFinset, mem_roots']; exact ⟨hq_ne, (hf k).2.2⟩
  have hf_inj : Function.Injective f := by
    have hanti : StrictAnti f := by
      intro a b hab
      have hab' : a.val < b.val := hab
      have hb1 : f b < Real.cos (b.val * π / n) := (hf b).2.1
      have ha0 : Real.cos ((a.val + 1) * π / n) < f a := (hf a).1
      have hstep : Real.cos (b.val * π / n) ≤ Real.cos ((a.val + 1) * π / n) := by
        have h := node_anti n hn (le_of_lt b.isLt) (show a.val + 1 ≤ b.val by omega)
        rwa [Nat.cast_add, Nat.cast_one] at h
      linarith
    exact hanti.injective
  -- `n` distinct roots, but `q ≠ 0` has at most `natDegree q < n` roots.
  have hcard : (Finset.univ.image f).card = n := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  have hsubset : Finset.univ.image f ⊆ q.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    exact hf_root k
  have hle : n ≤ q.natDegree :=
    calc n = (Finset.univ.image f).card := hcard.symm
      _ ≤ q.roots.toFinset.card := Finset.card_le_card hsubset
      _ ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
      _ ≤ q.natDegree := card_roots' q
  omega

/-- **Chebyshev minimax theorem (full statement).** Among monic real polynomials
of degree `n ≥ 1`, the monic Chebyshev polynomial `Mₙ` minimizes the sup-norm on
`[-1,1]` and the minimal value is exactly `2^(1-n)`: `Mₙ` stays within `2^(1-n)`
everywhere (achievability), while every monic degree-`n` polynomial reaches at
least `2^(1-n)` somewhere (optimality). -/
theorem chebyshev_minimax (n : ℕ) (hn : 0 < n) :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(monicChebyshev n).eval x| ≤ ((2 : ℝ) ^ (n - 1))⁻¹) ∧
      (∀ p : ℝ[X], p.Monic → p.natDegree = n →
        ∃ x ∈ Set.Icc (-1 : ℝ) 1, ((2 : ℝ) ^ (n - 1))⁻¹ ≤ |p.eval x|) :=
  ⟨fun _ hx => monicChebyshev_abs_le n hx,
    fun p hp hpd => monicChebyshev_minimax p hp n hn hpd⟩

end DeMoivreOQ0203
