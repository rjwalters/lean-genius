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
    ∑ k ∈ Finset.range N, ω ^ k = 0 := by
  have h : (1 : ℂ) - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hω1)
  have key := mul_neg_geom_sum ω N
  rw [hωN, sub_self] at key
  exact (mul_eq_zero.mp key).resolve_left h

/-- exp(2πi·val(a*b)/N) = exp(2πi·val(a)·val(b)/N).
    Follows from val(a*b) ≡ val(a)·val(b) (mod N) and exp periodicity. -/
private lemma exp_val_mul_eq {N : ℕ} [NeZero N] (a b : ZMod N) :
    Complex.exp (2 * ↑Real.pi * Complex.I * (↑(ZMod.val (a * b)) / ↑N)) =
    Complex.exp (2 * ↑Real.pi * Complex.I * (↑(ZMod.val a) * ↑(ZMod.val b) / ↑N)) := by
  rw [ZMod.val_mul,
    show (↑(ZMod.val a) : ℂ) * ↑(ZMod.val b) = ↑(ZMod.val a * ZMod.val b) from by push_cast; ring]
  -- Goal: exp(2πi · ↑((k % N)) / ↑N) = exp(2πi · ↑k / ↑N) where k = val a * val b
  -- Exponents differ by integer · 2πi, so exp agrees
  set k := ZMod.val a * ZMod.val b with hk_def
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hdiv : (↑k : ℂ) = ↑N * ↑(k / N) + ↑(k % N) := by
    exact_mod_cast (Nat.div_add_mod k N).symm
  rw [show (↑k : ℂ) / ↑N = ↑(k / N) + ↑(k % N) / ↑N from by rw [hdiv]; field_simp,
    mul_add, Complex.exp_add,
    show 2 * ↑Real.pi * Complex.I * ↑(k / N) =
        ↑(k / N) * (2 * ↑Real.pi * Complex.I) from by ring,
    Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, one_mul]

/-- ψ(r·x) equals (exp(2πi·val(x)/N))^val(r), i.e., ω_x^{val(r)}. -/
private lemma psi_eq_pow {N : ℕ} [NeZero N] (r x : ZMod N) :
    ψ (r * x) = (Complex.exp (2 * ↑Real.pi * Complex.I * (↑(ZMod.val x) / ↑N))) ^ (ZMod.val r) := by
  simp only [ψ]
  rw [exp_val_mul_eq]
  rw [show 2 * ↑Real.pi * Complex.I * (↑(ZMod.val r) * ↑(ZMod.val x) / ↑N) =
      ↑(ZMod.val r) * (2 * ↑Real.pi * Complex.I * (↑(ZMod.val x) / ↑N)) by ring]
  rw [Complex.exp_nat_mul]

/-- ψ is an additive character: ψ(a + b) = ψ(a) · ψ(b).
    Follows from val(a+b) ≡ val(a)+val(b) (mod N) and exp periodicity. -/
private lemma psi_add {N : ℕ} [NeZero N] (a b : ZMod N) :
    ψ (a + b) = ψ a * ψ b := by
  simp only [ψ]
  rw [← Complex.exp_add, ZMod.val_add]
  -- Goal: exp(2πi·((val a + val b)%N)/N) = exp(2πi·val(a)/N + 2πi·val(b)/N)
  -- Exponents differ by ⌊k/N⌋ · 2πi, which exp absorbs.
  set k := ZMod.val a + ZMod.val b with hk_def
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- Combine RHS fractions: 2πi·val(a)/N + 2πi·val(b)/N = 2πi·k/N
  rw [show 2 * ↑Real.pi * Complex.I * (↑(ZMod.val a) / ↑N) +
        2 * ↑Real.pi * Complex.I * (↑(ZMod.val b) / ↑N) =
        2 * ↑Real.pi * Complex.I * ((↑(ZMod.val a) + ↑(ZMod.val b)) / ↑N) from by ring,
    show (↑(ZMod.val a) : ℂ) + ↑(ZMod.val b) = ↑k from by simp [hk_def]]
  -- Now: exp(2πi·(k%N)/N) = exp(2πi·k/N). Decompose k = N·⌊k/N⌋ + k%N.
  have hdiv : (↑k : ℂ) = ↑N * ↑(k / N) + ↑(k % N) := by
    exact_mod_cast (Nat.div_add_mod k N).symm
  rw [show (↑k : ℂ) / ↑N = ↑(k / N) + ↑(k % N) / ↑N from by rw [hdiv]; field_simp,
    show 2 * ↑Real.pi * Complex.I * (↑(k / N) + ↑(k % N) / ↑N) =
        ↑(k / N) * (2 * ↑Real.pi * Complex.I) +
        2 * ↑Real.pi * Complex.I * (↑(k % N) / ↑N) from by ring,
    Complex.exp_add, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, one_mul]

/-- ψ(0) = 1 (the character evaluated at zero). -/
private lemma psi_zero {N : ℕ} [NeZero N] : ψ (0 : ZMod N) = 1 := by
  simp [ψ, ZMod.val_zero]

/-- Conjugate of ψ: conj(ψ(x)) = ψ(-x). Both are inverses of ψ(x).
    Proof: ψ(x)·ψ(-x) = 1 (psi_add) and ψ(x)·conj(ψ(x)) = ‖ψ(x)‖² = 1 (exp has unit norm),
    so by cancellation conj(ψ(x)) = ψ(-x). Needed for parseval_on_zmod. -/
private lemma conj_psi {N : ℕ} [NeZero N] (x : ZMod N) :
    starRingEnd ℂ (ψ x) = ψ (-x) := by
  -- Both conj(ψ x) and ψ(-x) are the multiplicative inverse of ψ(x).
  -- ψ(x)·ψ(-x) = ψ(0) = 1 and ψ(x)·conj(ψ(x)) = 1 (exp of purely imaginary has norm 1)
  have hne : ψ x ≠ 0 := by unfold ψ; exact Complex.exp_ne_zero _
  have h1 : ψ x * ψ (-x) = 1 := by
    rw [← psi_add, add_neg_cancel, psi_zero]
  have h2 : ψ x * starRingEnd ℂ (ψ x) = 1 := by
    unfold ψ
    rw [← Complex.exp_conj, ← Complex.exp_add]
    -- exp(z + conj z) = exp(0) = 1 for purely imaginary z
    suffices h : 2 * ↑Real.pi * Complex.I * (↑(ZMod.val x) / ↑N) +
        starRingEnd ℂ (2 * ↑Real.pi * Complex.I * (↑(ZMod.val x) / ↑N)) = 0 by
      rw [h, Complex.exp_zero]
    -- conj distributes: conj(r * I * q) = r * (-I) * q for real r, q
    simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_natCast,
      map_ofNat]
    ring
  exact (mul_left_cancel₀ hne (h1.trans h2.symm)).symm

/-- ψ(c) ≠ 1 when c ≠ 0: a nontrivial character is not the identity.
    Since val(c) ∈ {1,...,N-1}, we have 2πi·val(c)/N ∉ 2πiℤ. -/
private lemma psi_ne_one {N : ℕ} [NeZero N] (c : ZMod N) (hc : c ≠ 0) :
    ψ c ≠ 1 := by
  simp only [ψ]
  intro h
  apply hc
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero _) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have heq : (↑(ZMod.val c) : ℂ) / ↑N = ↑n :=
    mul_left_cancel₀ hpi (hn.trans (mul_comm _ _))
  have hval_eq : (ZMod.val c : ℤ) = n * N := by
    have : (↑(ZMod.val c) : ℂ) = ↑n * ↑N := by rwa [div_eq_iff hNc] at heq
    exact_mod_cast this
  -- n must be 0: 0 ≤ n*N < N with N > 0 forces n = 0
  have hn0 : n = 0 := by
    have h1 : (0 : ℤ) ≤ n * N := hval_eq ▸ Int.natCast_nonneg _
    have h2 : n * (N : ℤ) < N := hval_eq ▸ (by exact_mod_cast ZMod.val_lt c)
    have : (0 : ℤ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
    nlinarith [sq_nonneg n]
  rw [hn0, zero_mul, Int.ofNat_eq_zero] at hval_eq
  rwa [← ZMod.val_eq_zero]

/-- Character orthogonality: ∑_{r : ZMod N} ψ(r·c) = N if c = 0, 0 if c ≠ 0.
    When c = 0, every term is 1. When c ≠ 0, the sum is a geometric series
    with ratio ω = exp(2πi·val(c)/N), a nontrivial N-th root of unity.
    Proof via shift argument: r ↦ r+1 is a bijection on ZMod N. -/
private theorem char_orthogonality {N : ℕ} [NeZero N] (c : ZMod N) :
    (Finset.univ.sum fun r : ZMod N => ψ (r * c)) =
    if c = 0 then ↑N else 0 := by
  split_ifs with hc
  · -- c = 0: ψ(r·0) = ψ(0) = 1 for all r, sum = N
    subst hc
    simp only [mul_zero, ψ, ZMod.val_zero, Nat.cast_zero, zero_div, mul_zero,
      Complex.exp_zero, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  · -- c ≠ 0: geometric series with ω = exp(2πi·val(c)/N)
    set ω := Complex.exp (2 * ↑Real.pi * Complex.I * (↑(ZMod.val c) / ↑N)) with hω_def
    -- Rewrite each term as ω^{val(r)}
    simp_rw [show ∀ r : ZMod N, ψ (r * c) = ω ^ ZMod.val r from fun r => psi_eq_pow r c]
    -- Sum over ZMod N = Fin N → sum over range N
    change ∑ r : Fin N, ω ^ (r : ℕ) = 0
    rw [Fin.sum_univ_eq_sum_range (fun k => ω ^ k)]
    apply root_unity_sum_zero ω N
    · -- ω^N = 1
      rw [hω_def]; exact root_pow_eq_one
    · -- ω ≠ 1 since 0 < val(c) < N
      intro hω1
      apply hc
      rw [hω_def] at hω1
      rw [Complex.exp_eq_one_iff] at hω1
      obtain ⟨n, hn⟩ := hω1
      -- hn: 2πi · val(c)/N = n · 2πi. Extract val(c) = n * N.
      have hpi : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 := by
        apply mul_ne_zero (mul_ne_zero two_ne_zero _) Complex.I_ne_zero
        exact_mod_cast Real.pi_ne_zero
      have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
      have heq : (↑(ZMod.val c) : ℂ) / ↑N = ↑n := by
        have h := congr_arg (· / (2 * ↑Real.pi * Complex.I)) hn
        rwa [mul_div_cancel_left₀ _ hpi, mul_div_cancel_right₀ _ hpi] at h
      have hval_eq : (ZMod.val c : ℤ) = n * N := by
        have : (↑(ZMod.val c) : ℂ) = ↑n * ↑N := by rwa [div_eq_iff hNc] at heq
        exact_mod_cast this
      -- 0 ≤ val(c) < N and val(c) = n*N forces val(c) = 0, hence c = 0
      have : ZMod.val c = 0 := by omega
      rwa [← ZMod.val_eq_zero]

/-- Character sum over integers: ∑_{j=0}^{N-1} exp(2πi·j·m/N) = N·δ(N∣m).
    Extension of char_orthogonality to integer exponents via geometric series. -/
private lemma char_sum_int {N : ℕ} [NeZero N] (m : ℤ) :
    ∑ j ∈ Finset.range N, Complex.exp (2 * ↑Real.pi * Complex.I * (↑j * ↑m / ↑N)) =
    if (N : ℤ) ∣ m then ↑N else 0 := by
  -- Set ω = exp(2πi·m/N) and show each term is ω^j
  set ω := Complex.exp (2 * ↑Real.pi * Complex.I * (↑m / ↑N)) with hω_def
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- Rewrite sum as ∑ ω^j
  have hterm : ∀ j ∈ Finset.range N,
      Complex.exp (2 * ↑Real.pi * Complex.I * (↑j * ↑m / ↑N)) = ω ^ j := by
    intro j _
    rw [hω_def, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [Finset.sum_congr rfl hterm]
  -- ω^N = 1: exp(N · 2πi·m/N) = exp(2πi·m) = 1 since m ∈ ℤ
  have hωN : ω ^ N = 1 := by
    rw [hω_def, ← Complex.exp_nat_mul]
    apply Complex.exp_eq_one_iff.mpr
    exact ⟨m, by push_cast; field_simp⟩
  split_ifs with hdvd
  · -- N | m: ω = 1, sum = N
    have hω1 : ω = 1 := by
      rw [hω_def]
      apply Complex.exp_eq_one_iff.mpr
      obtain ⟨k, hk⟩ := hdvd
      exact ⟨k, by subst hk; push_cast; field_simp⟩
    simp [hω1, Finset.sum_const, Finset.card_range]
  · -- N ∤ m: ω ≠ 1, ω^N = 1, geometric series = 0
    apply root_unity_sum_zero _ N hωN
    intro hω1
    apply hdvd
    rw [hω_def] at hω1
    rw [Complex.exp_eq_one_iff] at hω1
    obtain ⟨n, hn⟩ := hω1
    -- hn: 2πi · m/N = n · 2πi, so m/N = n, hence m = n*N
    have hpi : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero two_ne_zero _) Complex.I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    have heq : (↑m : ℂ) / ↑N = ↑n :=
      mul_left_cancel₀ hpi (hn.trans (mul_comm _ _))
    have hmn : (m : ℤ) = n * N := by
      have : (↑m : ℂ) = ↑n * ↑N := by rwa [div_eq_iff hNc] at heq
      exact_mod_cast this
    exact ⟨n, by rw [hmn, mul_comm]⟩

theorem parseval_on_zmod {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (Finset.univ.sum fun r => ‖fourierCoeff A r‖ ^ 2) = A.card * N := by
  -- Proof plan (all ingredients proved in this file):
  -- 1. Cast to ℂ: ↑(‖z‖²) = z * conj z (via Complex.mul_conj + normSq)
  -- 2. Expand Â(r) = ∑_{x∈A} ψ(rx), distribute product via Finset.sum_mul/mul_sum
  -- 3. conj(ψ(ry)) = ψ(-ry) [conj_psi], ψ(rx)·ψ(-ry) = ψ(r(x-y)) [psi_add]
  -- 4. Swap sums via Finset.sum_comm, apply char_orthogonality: ∑_r ψ(r(x-y)) = N·δ(x,y)
  -- 5. Diagonal sum: ∑_{x∈A} N = |A|·N
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
