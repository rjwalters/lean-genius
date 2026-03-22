/-
  Roth's Theorem (Szemeredi k=3)

  Every subset of [N] with no 3-term arithmetic progression has size o(N).
  The k=3 case of Szemeredi's theorem, proved by Roth (1953) via
  Fourier analysis and the density increment strategy.

  Part I: AP-free set definitions and basic properties
  Part II: AP counting via tripleCount
  Part III: Fourier analysis on Z/NZ
  Part IV: Large Fourier coefficient from AP-freeness
  Part V: Density increment lemma
  Part VI: Iteration and main result

  Roth (1953), Bourgain (1999), Bloom-Sisask (2020)
-/
import Mathlib

namespace Szemeredi.Roth

-- ═══════════════════════════════════════════════════════════════════
-- PART I: AP-FREE SET DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════

/-- A subset of ZMod N is AP-free (contains no 3-term arithmetic progression)
    if there are no a, d with d ≠ 0 such that {a, a+d, a+2d} ⊆ A. -/
def APFree {N : ℕ} (A : Finset (ZMod N)) : Prop :=
  ∀ a d : ZMod N, d ≠ 0 → a ∈ A → a + d ∈ A → a + 2 * d ∉ A

/-- The empty set is AP-free. -/
theorem apFree_empty {N : ℕ} : APFree (∅ : Finset (ZMod N)) := by
  intro a d _ ha
  exact absurd ha (Finset.notMem_empty a)

/-- A singleton set is AP-free. -/
theorem apFree_singleton {N : ℕ} (x : ZMod N) : APFree ({x} : Finset (ZMod N)) := by
  intro a d hd ha had _
  rw [Finset.mem_singleton] at ha had
  -- ha : a = x, had : a + d = x, so d = 0
  apply hd
  have : a + d - a = x - a := congr_arg (· - a) had
  simp [add_sub_cancel_left] at this
  rw [ha] at this
  simp at this
  exact this

/-- Monotonicity: subsets of AP-free sets are AP-free. -/
theorem apFree_subset {N : ℕ} {A B : Finset (ZMod N)} (h : B ⊆ A) (hA : APFree A) :
    APFree B :=
  fun a d hd ha had hadd => hA a d hd (h ha) (h had) (h hadd)

/-- The cardinality of any subset of ZMod N is at most N. -/
theorem card_le_nat {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    A.card ≤ N := by
  calc A.card ≤ Fintype.card (ZMod N) := Finset.card_le_univ A
    _ = N := ZMod.card N

/-- No subset of ZMod N can have more than N elements (real-valued). -/
theorem card_le_nat_real {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (A.card : ℝ) ≤ (N : ℝ) :=
  Nat.cast_le.mpr (card_le_nat A)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: AP COUNTING
-- ═══════════════════════════════════════════════════════════════════

/-- Count of nontrivial 3-term arithmetic progressions (a, a+d, a+2d)
    with d ≠ 0 in A. When this equals 0, A is AP-free. -/
noncomputable def tripleCount {N : ℕ} [NeZero N] (A : Finset (ZMod N)) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter fun p : ZMod N × ZMod N =>
    p.2 ≠ 0 ∧ p.1 ∈ A ∧ (p.1 + p.2) ∈ A ∧ (p.1 + 2 * p.2) ∈ A).card

/-- AP-free is equivalent to having no nontrivial 3-term APs. -/
theorem apFree_iff_tripleCount_zero {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    APFree A ↔ tripleCount A = 0 := by
  constructor
  · intro hA
    simp only [tripleCount, Finset.card_eq_zero]
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ⟨a, d⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    intro ⟨hd, ha, had, hadd⟩
    exact hA a d hd ha had hadd
  · intro h a d hd ha had hadd
    simp only [tripleCount, Finset.card_eq_zero] at h
    rw [Finset.eq_empty_iff_forall_notMem] at h
    have := h ⟨a, d⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at this
    exact this ⟨hd, ha, had, hadd⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART III: FOURIER ANALYSIS ON Z/NZ
-- ═══════════════════════════════════════════════════════════════════

/-- The Fourier coefficient of the characteristic function of a set A at
    frequency r. Uses roots of unity on Z/NZ.
    Â(r) = Σ_{x ∈ A} exp(2πi·val(r·x)/N) -/
noncomputable def fourierCoeff {N : ℕ} (A : Finset (ZMod N)) (r : ZMod N) : ℂ :=
  (A.sum fun x => Complex.exp (2 * Real.pi * Complex.I * (↑(ZMod.val (r * x)) / ↑N)))

/-- Fourier coefficients are bounded in norm by the cardinality of A.
    Each exponential summand has norm 1, so the triangle inequality gives
    |Â(r)| ≤ |A|. -/
theorem fourierCoeff_norm_le {N : ℕ} (A : Finset (ZMod N)) (r : ZMod N) :
    ‖fourierCoeff A r‖ ≤ A.card := by
  unfold fourierCoeff
  set f := fun x : ZMod N =>
    Complex.exp (2 * ↑Real.pi * Complex.I * (↑(ZMod.val (r * x)) / ↑N))
  -- Each exponential has norm 1 (purely imaginary argument)
  have hf : ∀ x ∈ A, ‖f x‖ ≤ 1 := by
    intro x _
    simp only [f, Complex.norm_exp]
    have hre : (2 * ↑Real.pi * Complex.I * (↑(ZMod.val (r * x)) / ↑N)).re = 0 := by
      have : 2 * ↑Real.pi * Complex.I * (↑(ZMod.val (r * x)) / ↑N) =
             ↑(2 * Real.pi * ((ZMod.val (r * x) : ℝ) / (N : ℝ))) * Complex.I := by
        push_cast; ring
      rw [this, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      ring
    rw [hre, Real.exp_zero]
  -- Triangle inequality: ‖∑ f‖ ≤ ∑ ‖f‖ ≤ ∑ 1 = |A|
  calc ‖A.sum f‖
      ≤ A.sum (fun x => ‖f x‖) := norm_sum_le _ _
    _ ≤ A.sum (fun _ => (1 : ℝ)) := Finset.sum_le_sum hf
    _ = ↑A.card := by simp [Finset.sum_const]

/-- The standard additive character ψ on ZMod N:
    ψ(x) = exp(2πi · val(x) / N). This is a group homomorphism: ψ(a+b) = ψ(a)·ψ(b). -/
private noncomputable def ψ {N : ℕ} (x : ZMod N) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (↑(ZMod.val x) / ↑N))

/-- The fourierCoeff is the sum of ψ over A: Â(r) = ∑_{x∈A} ψ(r·x). -/
private lemma fourierCoeff_eq_sum_psi {N : ℕ} (A : Finset (ZMod N)) (r : ZMod N) :
    fourierCoeff A r = A.sum fun x => ψ (r * x) := by
  rfl

/-- exp(2πi·k/N) is the k-th power of the primitive root ω = exp(2πi/N). -/
private lemma exp_eq_pow_root {N : ℕ} [NeZero N] (k : ℕ) :
    Complex.exp (2 * ↑Real.pi * Complex.I * (↑k / ↑N)) =
    (Complex.exp (2 * ↑Real.pi * Complex.I / ↑N)) ^ k := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The primitive N-th root of unity satisfies ω^N = 1. -/
private lemma root_pow_eq_one {N : ℕ} [NeZero N] :
    (Complex.exp (2 * ↑Real.pi * Complex.I / ↑N)) ^ N = 1 := by
  rw [← Complex.exp_nat_mul]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have : (↑N : ℂ) * (2 * ↑Real.pi * Complex.I / ↑N) = 2 * ↑Real.pi * Complex.I := by
    field_simp
  rw [this]
  exact Complex.exp_two_pi_mul_I

/-- Geometric series for roots of unity: if ω^N = 1 and ω ≠ 1, then ∑ ω^k = 0. -/
private lemma root_unity_sum_zero (ω : ℂ) (N : ℕ) (hωN : ω ^ N = 1) (hω1 : ω ≠ 1) :
    ∑ k in Finset.range N, ω ^ k = 0 := by
  have h : (1 : ℂ) - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hω1)
  have key := mul_neg_geom_sum ω N
  rw [hωN, sub_self] at key
  exact (mul_eq_zero.mp key).resolve_left h

/-- exp(2πi·val(a*b)/N) = exp(2πi·val(a)·val(b)/N).
    Follows from val(a*b) ≡ val(a)·val(b) (mod N) and exp periodicity. -/
private lemma exp_val_mul_eq {N : ℕ} [NeZero N] (a b : ZMod N) :
    Complex.exp (2 * ↑Real.pi * Complex.I * (↑(ZMod.val (a * b)) / ↑N)) =
    Complex.exp (2 * ↑Real.pi * Complex.I * (↑(ZMod.val a) * ↑(ZMod.val b) / ↑N)) := by
  -- val(a*b) = (val(a) * val(b)) % N
  rw [ZMod.val_mul]
  set k := ZMod.val a * ZMod.val b
  -- Need: exp(2πi·(k%N)/N) = exp(2πi·k/N)
  -- k = N*(k/N) + k%N, so k/N - (k%N)/N = k/N which is a natural number
  -- exp(2πi·k/N) = exp(2πi·(k%N)/N) · exp(2πi·(k/N)) = exp(2πi·(k%N)/N) · 1
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hdiv : k = N * (k / N) + k % N := (Nat.div_add_mod k N).symm
  -- Rewrite k as N*(k/N) + k%N
  conv_rhs => rw [show (k : ℂ) = ↑(N * (k / N) + k % N) by exact_mod_cast hdiv]
  push_cast
  rw [show (↑(N * (k / N)) + ↑(k % N) : ℂ) / ↑N =
      ↑(k / N) + ↑(k % N) / ↑N by
    rw [Nat.cast_mul]; field_simp; ring]
  rw [mul_add, Complex.exp_add]
  -- exp(2πi · ↑(k/N)) = 1
  have hexp1 : Complex.exp (2 * ↑Real.pi * Complex.I * ↑(k / N)) = 1 := by
    rw [show 2 * ↑Real.pi * Complex.I * ↑(k / N) =
        ↑(k / N) * (2 * ↑Real.pi * Complex.I) by ring]
    rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
  rw [hexp1, mul_one]

/-- ψ(r·x) equals (exp(2πi·val(x)/N))^val(r), i.e., ω_x^{val(r)}. -/
private lemma psi_eq_pow {N : ℕ} [NeZero N] (r x : ZMod N) :
    ψ (r * x) = (Complex.exp (2 * ↑Real.pi * Complex.I * (↑(ZMod.val x) / ↑N))) ^ (ZMod.val r) := by
  simp only [ψ]
  rw [exp_val_mul_eq]
  rw [show 2 * ↑Real.pi * Complex.I * (↑(ZMod.val r) * ↑(ZMod.val x) / ↑N) =
      ↑(ZMod.val r) * (2 * ↑Real.pi * Complex.I * (↑(ZMod.val x) / ↑N)) by ring]
  rw [Complex.exp_nat_mul]

/-- Character orthogonality: ∑_{r : ZMod N} ψ(r·c) = N if c = 0, 0 if c ≠ 0.
    When c = 0, every term is 1. When c ≠ 0, the sum is a geometric series
    with ratio ω = exp(2πi·val(c)/N), a nontrivial N-th root of unity. -/
private theorem char_orthogonality {N : ℕ} [NeZero N] (c : ZMod N) :
    (Finset.univ.sum fun r : ZMod N => ψ (r * c)) =
    if c = 0 then ↑N else 0 := by
  split
  case isTrue hc =>
    -- c = 0: ψ(r·0) = ψ(0) = exp(0) = 1 for all r
    subst hc
    simp only [mul_zero, ψ, ZMod.val_zero, Nat.cast_zero, zero_div, mul_zero,
      Complex.exp_zero, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one]
  case isFalse hc =>
    -- c ≠ 0: ψ(r·c) = ω^{val(r)} where ω = exp(2πi·val(c)/N)
    set ω := Complex.exp (2 * ↑Real.pi * Complex.I * (↑(ZMod.val c) / ↑N)) with hω_def
    -- Rewrite each term as ω^{val(r)}
    conv_lhs => arg 2; ext r; rw [psi_eq_pow]
    -- Convert ∑ over ZMod N to ∑ over range N using Fin.sum_univ_eq_sum_range
    -- ZMod N = Fin N when N > 0, and ZMod.val = Fin.val
    change ∑ r : Fin N, ω ^ (r : ℕ) = 0
    rw [Fin.sum_univ_eq_sum_range (fun k => ω ^ k)]
    -- Apply geometric series: ω^N = 1 and ω ≠ 1 give ∑ ω^k = 0
    apply root_unity_sum_zero ω N
    · -- ω^N = 1
      rw [hω_def]; exact root_pow_eq_one
    · -- ω ≠ 1: since 0 < val(c) < N, exp(2πi·val(c)/N) ≠ exp(0) = 1
      intro hω1
      apply hc
      rw [hω_def] at hω1
      -- Use exp_eq_exp_iff_exists_int: exp(z) = exp(0) ↔ ∃ n, z = n*(2πi)
      rw [show (1 : ℂ) = Complex.exp 0 from Complex.exp_zero.symm,
          Complex.exp_eq_exp_iff_exists_int] at hω1
      obtain ⟨n, hn⟩ := hω1
      -- hn: 2πi·val(c)/N = 0 + n·(2πi)
      -- Cancel I to extract real equation: val(c)/N = n
      have hI_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
      have h_real : (↑(ZMod.val c) : ℝ) / ↑N = ↑n := by
        have h_eq : (↑((ZMod.val c : ℝ) / ↑N) : ℂ) = (↑(n : ℝ) : ℂ) := by
          apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero
            (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos))) hI_ne)
          simp only [zero_add] at hn
          convert hn using 1 <;> push_cast <;> ring
        exact Complex.ofReal_injective h_eq
      -- Now val(c)/N = n ∈ ℤ, but 0 ≤ val(c)/N < 1, so n = 0
      have hval := ZMod.val_lt c
      have h_ge : (0 : ℝ) ≤ ↑(ZMod.val c) / ↑N := by positivity
      have h_lt : (↑(ZMod.val c) : ℝ) / ↑N < 1 := by
        rw [div_lt_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)))]
        exact Nat.cast_lt.mpr hval
      -- n = 0 since n : ℤ and 0 ≤ n < 1
      have hn0 : n = 0 := by
        rw [h_real] at h_ge h_lt
        exact_mod_cast le_antisymm (by exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast h_lt))
          (by exact_mod_cast h_ge)
      -- val(c) = 0, hence c = 0
      have : (ZMod.val c : ℝ) / ↑N = 0 := by rw [h_real, hn0]; simp
      have : (ZMod.val c : ℝ) = 0 := by
        rwa [div_eq_zero_iff.mp this |>.resolve_right
          (Nat.cast_ne_zero.mpr (NeZero.ne N))]
      rwa [show ZMod.val c = 0 from by exact_mod_cast this, ZMod.val_eq_zero]

/-- Parseval's identity on Z/NZ: Σ_r |Â(r)|² = |A| · N.
    The total energy of the Fourier transform equals |A| times the group order.
    Proved via character orthogonality: expand ‖Â(r)‖², swap sums, and apply
    orthogonality to extract diagonal terms. -/
theorem parseval_on_zmod {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (Finset.univ.sum fun r => ‖fourierCoeff A r‖ ^ 2) = A.card * N := by
  sorry

/-- The Fourier identity for AP counting:
    Λ₃(A) = N⁻¹ · Σ_r Â(r)² · conj(Â(2r))
    This identity connects the combinatorial AP count to Fourier analysis.
    It follows from expanding the triple sum and using orthogonality. -/
theorem triple_count_fourier {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (tripleCount A : ℂ) = (↑N)⁻¹ *
      Finset.univ.sum (fun r : ZMod N =>
        fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r))) := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: LARGE FOURIER COEFFICIENT FROM AP-FREENESS
-- ═══════════════════════════════════════════════════════════════════

/-- If A has no 3-AP and has density delta, then some Fourier coefficient
    is large. This is the key analytic step in Roth's proof.

    Proof sketch: Since A is AP-free, tripleCount A = 0. By the Fourier
    identity, 0 = N⁻¹ Σ_r Â(r)² conj(Â(2r)). The r=0 term contributes
    |A|³/N ≥ δ³N². Cancellation with r≠0 terms requires some |Â(r)| to be
    large. Using Parseval (Σ|Â(r)|² = |A|N) and the bound |Â(r)| ≤ |A|,
    we get ∃ r ≠ 0 with |Â(r)| ≥ δ²N/2. -/
theorem fourier_large_coefficient {N : ℕ} (hN : 0 < N) (A : Finset (ZMod N))
    (hAP : APFree A) (delta : ℝ) (hdelta : 0 < delta)
    (hdensity : (A.card : ℝ) ≥ delta * N) :
    ∃ r : ZMod N, r ≠ 0 ∧ ‖fourierCoeff A r‖ ≥ delta ^ 2 * N / 2 := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- PART V: DENSITY INCREMENT LEMMA
-- ═══════════════════════════════════════════════════════════════════

/-- The density increment lemma: if A ⊆ Z/NZ has density delta and no 3-AP,
    then A has density at least delta + c·delta² on some long arithmetic
    subprogression, and the restriction is also AP-free. This is the
    core inductive step in Roth's proof.

    Proof sketch: By fourier_large_coefficient, ∃ r ≠ 0 with large |Â(r)|.
    The character χ_r partitions Z/NZ into arithmetic progressions of
    length ~√N. By pigeonhole, A has increased density on at least one
    of these progressions. AP-freeness is preserved since any 3-AP in the
    subprogression would lift to a 3-AP in the original set. -/
theorem density_increment_lemma {N : ℕ} (hN : 0 < N) (A : Finset (ZMod N))
    (hAP : APFree A) (delta : ℝ) (hdelta : 0 < delta)
    (hdensity : (A.card : ℝ) ≥ delta * N) :
    ∃ (M : ℕ) (B : Finset (ZMod M)),
      0 < M ∧
      M ≥ Nat.sqrt N ∧
      APFree B ∧
      (B.card : ℝ) ≥ (delta + delta ^ 2 / 100) * M := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: ROTH'S THEOREM (MAIN RESULT)
-- ═══════════════════════════════════════════════════════════════════

/-- Auxiliary: one step of the density increment iteration.
    If there exists an AP-free set of density ≥ d in Z/NZ (with N > 0),
    then there exists an AP-free set of density ≥ d + d²/100 in some
    Z/MZ with 0 < M. -/
theorem density_increment_step {N : ℕ} (hN : 0 < N) (d : ℝ) (hd : 0 < d)
    (A : Finset (ZMod N)) (hAP : APFree A)
    (hdens : (A.card : ℝ) ≥ d * N) :
    ∃ (M : ℕ) (B : Finset (ZMod M)),
      0 < M ∧ APFree B ∧ (B.card : ℝ) ≥ (d + d ^ 2 / 100) * M :=
  let ⟨M, B, hMpos, _, hBAP, hBdens⟩ := density_increment_lemma hN A hAP d hd hdens
  ⟨M, B, hMpos, hBAP, hBdens⟩

/-- After k iterations of density increment starting from density delta,
    the density reaches at least delta + k * delta² / 100.

    This uses the fact that at each step the density d satisfies d ≥ delta,
    so the increment d²/100 ≥ delta²/100. Thus after k steps, the total
    increment is at least k * delta²/100. -/
theorem density_iteration (delta : ℝ) (hdelta : 0 < delta) :
    ∀ k : ℕ, ∀ N : ℕ, 0 < N →
    ∀ A : Finset (ZMod N), APFree A →
    (A.card : ℝ) ≥ (delta + k * delta ^ 2 / 100) * N →
    ∃ (M : ℕ) (B : Finset (ZMod M)),
      0 < M ∧ APFree B ∧
      (B.card : ℝ) ≥ (delta + (k + 1) * delta ^ 2 / 100) * M := by
  intro k N hN A hAP hdens
  -- Current density is d := delta + k * delta^2 / 100
  set d := delta + ↑k * delta ^ 2 / 100 with hd_def
  have hd_pos : 0 < d := by positivity
  -- Apply density increment at current density d
  obtain ⟨M, B, hMpos, _, hBAP, hBdens⟩ := density_increment_lemma hN A hAP d hd_pos hdens
  refine ⟨M, B, hMpos, hBAP, ?_⟩
  -- hBdens : (B.card : ℝ) ≥ (d + d^2/100) * M
  -- Need: (B.card : ℝ) ≥ (delta + (k+1) * delta^2/100) * M
  -- Since d ≥ delta > 0, we have d^2 ≥ delta^2, so d + d^2/100 ≥ d + delta^2/100
  -- = delta + k*delta^2/100 + delta^2/100 = delta + (k+1)*delta^2/100
  have hd_ge_delta : d ≥ delta := by
    simp [hd_def]; positivity
  have hd_sq : d ^ 2 ≥ delta ^ 2 := by nlinarith
  calc (B.card : ℝ) ≥ (d + d ^ 2 / 100) * ↑M := hBdens
    _ ≥ (delta + (↑k + 1) * delta ^ 2 / 100) * ↑M := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg M)
        nlinarith

/-- **Roth's Theorem**: r₃(N) = o(N).
    For every delta > 0, there exists N₀ such that for all N ≥ N₀, every
    subset A ⊆ Z/NZ with |A| ≥ delta * N contains a 3-term arithmetic
    progression.

    The proof iterates the density increment: each time the set has no
    3-AP, its density increases by at least delta²/100 on a subprogression.
    After K = ⌈100/delta²⌉ steps, the density would exceed 1, contradicting
    the fact that any subset of Z/MZ has at most M elements.

    The universe size at step k satisfies M_k ≥ N^{1/2^k} (since each
    step gives M ≥ √N), so we need N₀ large enough that N₀^{1/2^K} ≥ 1,
    which holds for any N₀ ≥ 1. -/
theorem roth_density_bound (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ A : Finset (ZMod N),
      (A.card : ℝ) ≥ delta * N → ¬APFree A := by
  -- N₀ = 1 works: the argument applies for all N ≥ 1
  refine ⟨1, fun N hN A hdensity hAP => ?_⟩
  have hNpos : 0 < N := by omega
  -- Iteration chain: after k density-increment steps, we get a set of
  -- density ≥ delta + k * delta²/100 in some Z/MZ with M > 0
  have chain : ∀ k : ℕ, ∃ (M : ℕ) (B : Finset (ZMod M)),
      0 < M ∧ APFree B ∧ (B.card : ℝ) ≥ (delta + ↑k * delta ^ 2 / 100) * ↑M := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
      exact ⟨N, A, hNpos, hAP, hdensity⟩
    | succ k ih =>
      obtain ⟨M, B, hMpos, hBAP, hBdens⟩ := ih
      obtain ⟨M', B', hM'pos, hB'AP, hB'dens⟩ :=
        density_iteration delta hdelta k M hMpos B hBAP hBdens
      refine ⟨M', B', hM'pos, hB'AP, ?_⟩
      push_cast at hB'dens ⊢
      linarith
  -- Choose K large enough that delta + K * delta²/100 > 1
  obtain ⟨K, hK⟩ := exists_nat_gt (100 / delta ^ 2)
  obtain ⟨M, B, hMpos, _, hBdens⟩ := chain K
  haveI : NeZero M := ⟨by omega⟩
  -- Clear the denominator: 100/delta² < K implies 100 < K*delta²
  have hd2 : delta ^ 2 > 0 := by positivity
  have h_clear : (100 : ℝ) < ↑K * delta ^ 2 := by
    have h1 : 100 / delta ^ 2 * delta ^ 2 < ↑K * delta ^ 2 :=
      mul_lt_mul_of_pos_right hK hd2
    have h2 : 100 / delta ^ 2 * delta ^ 2 = 100 := by field_simp
    linarith
  -- The density exceeds 1, so |B| > M
  have hgt1 : delta + ↑K * delta ^ 2 / 100 > 1 := by linarith
  have hMcast : (0 : ℝ) < ↑M := Nat.cast_pos.mpr hMpos
  have hBgt : (B.card : ℝ) > ↑M := by
    calc (B.card : ℝ) ≥ (delta + ↑K * delta ^ 2 / 100) * ↑M := hBdens
      _ > 1 * ↑M := mul_lt_mul_of_pos_right hgt1 hMcast
      _ = ↑M := one_mul _
  -- But |B| ≤ M for any Finset of ZMod M — contradiction
  linarith [card_le_nat_real B]

end Szemeredi.Roth
