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
  rw [← Complex.exp_nat_mul]; congr 1; ring

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
  simp only [ψ, ← Complex.exp_add]
  -- Combine RHS: 2πi·val(a)/N + 2πi·val(b)/N = 2πi·(val(a)+val(b))/N
  rw [show 2 * ↑Real.pi * Complex.I * (↑(ZMod.val a) / ↑N) +
      2 * ↑Real.pi * Complex.I * (↑(ZMod.val b) / ↑N) =
      2 * ↑Real.pi * Complex.I * ((↑(ZMod.val a) + ↑(ZMod.val b)) / ↑N) from by ring]
  -- LHS has val(a+b) = (val(a)+val(b)) % N; exponents agree mod 2πi
  rw [ZMod.val_add,
    show (↑(ZMod.val a) : ℂ) + ↑(ZMod.val b) = ↑(ZMod.val a + ZMod.val b) from by push_cast; ring]
  set k := ZMod.val a + ZMod.val b
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
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

/-- ψ(c) ≠ 1 when c ≠ 0: a nontrivial character is not the identity.
    Since val(c) ∈ {1,...,N-1}, we have 2πi·val(c)/N ∉ 2πiℤ. -/
private lemma psi_ne_one {N : ℕ} [NeZero N] (c : ZMod N) (hc : c ≠ 0) :
    ψ c ≠ 1 := by
  simp only [ψ]
  -- val(c) ∈ {1,...,N-1} when c ≠ 0
  have hval_pos : 0 < ZMod.val c := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    exact hc (by rwa [ZMod.val_eq_zero] at h)
  have hval_lt : ZMod.val c < N := ZMod.val_lt c
  -- exp(2πi·val(c)/N) = 1 iff val(c)/N ∈ ℤ, but 0 < val(c)/N < 1
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  -- hn : 2πi * val(c)/N = 2πi * n
  have hpi : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero _ _) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- From hn: val(c)/N = n (as complex numbers)
  have heq : (↑(ZMod.val c) : ℂ) / ↑N = ↑n :=
    mul_left_cancel₀ hpi (by rw [hn]; ring)
  have heq_nat : (ZMod.val c : ℤ) = n * N := by
    have h := heq; rw [div_eq_iff hN] at h; exact_mod_cast h
  have hN_pos : (0 : ℤ) < ↑N := by exact_mod_cast (NeZero.pos N)
  have hvc_pos : (0 : ℤ) < ↑(ZMod.val c) := by exact_mod_cast hval_pos
  have hvc_lt : (↑(ZMod.val c) : ℤ) < ↑N := by exact_mod_cast hval_lt
  rcases le_or_gt n 0 with hn | hn
  · linarith [mul_nonpos_of_nonpos_of_nonneg hn hN_pos.le]
  · linarith [mul_le_mul_of_nonneg_right (show 1 ≤ n by omega) hN_pos.le]

/-- ψ has norm 1: each value lies on the unit circle. -/
private lemma psi_norm {N : ℕ} [NeZero N] (a : ZMod N) : ‖ψ a‖ = 1 := by
  simp only [ψ, Complex.norm_exp]
  have hre : (2 * ↑Real.pi * Complex.I * (↑(ZMod.val a) / ↑N)).re = 0 := by
    have : 2 * ↑Real.pi * Complex.I * (↑(ZMod.val a) / ↑N) =
           ↑(2 * Real.pi * ((ZMod.val a : ℝ) / (N : ℝ))) * Complex.I := by
      push_cast; ring
    rw [this, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    ring
  rw [hre, Real.exp_zero]

/-- Complex conjugate of ψ: conj(ψ(a)) = ψ(-a).
    On the unit circle, conjugation equals inversion. -/
private lemma conj_psi {N : ℕ} [NeZero N] (a : ZMod N) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  have hne : ψ a ≠ 0 := Complex.exp_ne_zero _
  have h1 : ψ a * ψ (-a) = 1 := by rw [← psi_add, add_neg_cancel, psi_zero]
  have h2 : ψ a * starRingEnd ℂ (ψ a) = 1 := by
    rw [Complex.mul_conj, ← Complex.ofReal_one]; congr 1
    -- normSq(ψ a) = ‖ψ a‖² = 1² = 1
    rw [Complex.normSq_eq_norm_sq, psi_norm, one_pow]
  exact mul_left_cancel₀ hne (h2.trans h1.symm)

/-- Character orthogonality: ∑_{r : ZMod N} ψ(r·c) = N if c = 0, 0 if c ≠ 0.
    When c = 0, every term is 1. When c ≠ 0, the sum is a geometric series
    with ratio ω = exp(2πi·val(c)/N), a nontrivial N-th root of unity.
    Proof via shift argument: r ↦ r+1 is a bijection on ZMod N. -/
private theorem char_orthogonality {N : ℕ} [NeZero N] (c : ZMod N) :
    (Finset.univ.sum fun r : ZMod N => ψ (r * c)) =
    if c = 0 then ↑N else 0 := by
  split_ifs with hc
  · -- c = 0: each term is ψ(0) = 1, sum = N
    subst hc
    simp only [mul_zero, psi_zero, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, mul_one]
  · -- c ≠ 0: shift argument. S = ψ(c) · S and ψ(c) ≠ 1, so S = 0.
    set S := Finset.univ.sum fun r : ZMod N => ψ (r * c) with hS_def
    -- Step 1: ψ(c) · S = S
    have hshift : ψ c * S = S := by
      rw [hS_def, Finset.mul_sum]
      -- ψ(c) · ψ(r·c) = ψ(c + r·c) = ψ((r+1)·c)
      have hstep : ∀ r : ZMod N, ψ c * ψ (r * c) = ψ ((r + 1) * c) := by
        intro r; rw [← psi_add c (r * c), show c + r * c = (r + 1) * c from by ring]
      simp_rw [hstep]
      -- Reindex: sum over r of f(r+1) = sum over r of f(r)
      rw [show (Finset.univ.sum fun r : ZMod N => ψ ((r + 1) * c)) =
          Finset.univ.sum fun r : ZMod N => ψ (r * c) from by
        apply Finset.sum_equiv (Equiv.addRight (1 : ZMod N))
        · intro r; simp
        · intro r _; congr 1]
    -- Step 2: ψ(c) ≠ 1
    have hψ := psi_ne_one c hc
    -- Step 3: (ψ(c) - 1) · S = 0, and ψ(c) - 1 ≠ 0, so S = 0
    have h0 : (ψ c - 1) * S = 0 := by rw [sub_mul, one_mul, hshift, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hψ)

/-- exp(n * 2πi) = 1 for any integer n. -/
private lemma exp_int_mul_two_pi_I (n : ℤ) :
    Complex.exp (↑n * (2 * ↑Real.pi * Complex.I)) = 1 :=
  Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩

/-- Character sum over integers: ∑_{j=0}^{N-1} exp(2πi·j·m/N) = N·δ(N∣m).
    Extension of char_orthogonality to integer exponents via geometric series. -/
private lemma char_sum_int {N : ℕ} [NeZero N] (m : ℤ) :
    ∑ j ∈ Finset.range N, Complex.exp (2 * ↑Real.pi * Complex.I * (↑j * ↑m / ↑N)) =
    if (N : ℤ) ∣ m then ↑N else 0 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- Set ω = exp(2πi·m/N) and rewrite each term as ω^j
  set ω := Complex.exp (2 * ↑Real.pi * Complex.I * (↑m / ↑N)) with hω_def
  have hterm : ∀ j : ℕ,
      Complex.exp (2 * ↑Real.pi * Complex.I * (↑j * ↑m / ↑N)) = ω ^ j := by
    intro j
    change Complex.exp (2 * ↑Real.pi * Complex.I * (↑j * ↑m / ↑N)) =
      (Complex.exp (2 * ↑Real.pi * Complex.I * (↑m / ↑N))) ^ j
    rw [← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [hterm]
  -- ω^N = 1: exp(N · 2πi·m/N) = exp(m · 2πi) = 1
  have hωN : ω ^ N = 1 := by
    rw [hω_def, ← Complex.exp_nat_mul]
    rw [show (↑N : ℂ) * (2 * ↑Real.pi * Complex.I * (↑m / ↑N)) =
        ↑m * (2 * ↑Real.pi * Complex.I) from by field_simp]
    exact exp_int_mul_two_pi_I m
  split_ifs with hdvd
  · -- N ∣ m: ω = 1, sum = N
    have hω1 : ω = 1 := by
      obtain ⟨k, hk⟩ := hdvd
      show Complex.exp (2 * ↑Real.pi * Complex.I * (↑m / ↑N)) = 1
      rw [hk, show (↑(↑N * k) : ℂ) / ↑N = ↑k from by push_cast; field_simp]
      rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ↑k =
          ↑k * (2 * ↑Real.pi * Complex.I) from by ring]
      exact exp_int_mul_two_pi_I k
    simp [hω1]
  · -- N ∤ m: ω ≠ 1, geometric series gives 0
    have hω1 : ω ≠ 1 := by
      intro h; apply hdvd
      rw [hω_def, Complex.exp_eq_one_iff] at h
      obtain ⟨k, hk⟩ := h
      have hpi : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
          Complex.I_ne_zero
      have heq : (↑m : ℂ) / ↑N = ↑k := mul_left_cancel₀ hpi (by rw [hk]; ring)
      have h := heq; rw [div_eq_iff hN] at h
      exact ⟨k, by rw [mul_comm] at h; exact_mod_cast h⟩
    exact root_unity_sum_zero ω N hωN hω1

theorem parseval_on_zmod {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (Finset.univ.sum fun r => ‖fourierCoeff A r‖ ^ 2) = A.card * N := by
  -- Prove complex identity: ∑_r Â(r) · conj(Â(r)) = |A| · N
  suffices hC : Finset.univ.sum (fun r : ZMod N =>
      fourierCoeff A r * starRingEnd ℂ (fourierCoeff A r)) =
      ↑A.card * (↑N : ℂ) by
    -- Derive real identity from complex one
    -- ‖z‖² = normSq(z) = (z * conj z).re
    have hnorm : ∀ z : ℂ, ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := by
      intro z
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    simp_rw [hnorm]
    -- Sum of .re = .re of sum (re is additive)
    have sum_re : ∀ (s : Finset (ZMod N)) (f : ZMod N → ℂ),
        s.sum (fun r => (f r).re) = (s.sum f).re := by
      intro s f
      exact (map_sum
        (⟨⟨Complex.re, Complex.zero_re⟩, fun _ _ => Complex.add_re _ _⟩ : ℂ →+ ℝ) f s).symm
    rw [sum_re, hC]; simp
  -- Expand fourierCoeff as ψ sums
  simp_rw [fourierCoeff_eq_sum_psi, map_sum (starRingEnd ℂ), conj_psi]
  -- Expand product of sums into double sum
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  -- Combine ψ(rx) · ψ(-ry) = ψ(r(x-y)) via psi_add
  simp_rw [← psi_add]
  simp_rw [show ∀ r x y : ZMod N, r * x + -(r * y) = r * (x - y) from
    fun _ _ _ => by ring]
  -- Swap sums: ∑_r ∑_x ∑_y → ∑_x ∑_y ∑_r
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext; rw [Finset.sum_comm]
  -- Apply char_orthogonality: ∑_r ψ(r(x-y)) = N·δ(x,y)
  have horth : ∀ x y : ZMod N,
      Finset.univ.sum (fun r => ψ (r * (x - y))) = if x = y then ↑N else 0 := by
    intro x y
    have h := char_orthogonality (x - y)
    simp only [sub_eq_zero] at h; exact h
  simp_rw [horth]
  -- Simplify diagonal: ∑_x ∑_y δ(x,y)·N = ∑_x N = |A|·N
  -- Inner sum: ∑_{y∈A} (if x=y then N else 0) = if x∈A then N else 0
  have inner : ∀ x, (A.sum fun y => if x = y then (↑N : ℂ) else 0) =
      if x ∈ A then ↑N else 0 := fun x => Finset.sum_ite_eq A x (fun _ => (↑N : ℂ))
  simp_rw [inner]
  -- Since x ranges over A, each condition x ∈ A is true
  rw [Finset.sum_congr rfl (fun x hx => if_pos hx), Finset.sum_const]; ring

/-- Each Fourier term Â(r)²·conj(Â(2r)) expands as a triple sum of ψ values. -/
private lemma fourier_term_expand {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (r : ZMod N) :
    fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r)) =
    A.sum fun x => A.sum fun z => A.sum fun y => ψ (r * (x + z - 2 * y)) := by
  simp only [fourierCoeff_eq_sum_psi, sq, map_sum (starRingEnd ℂ), conj_psi]
  -- Work from the RHS: unfold ψ product, then fold sums
  symm
  simp_rw [show ∀ (x z y : ZMod N), ψ (r * (x + z - 2 * y)) =
      ψ (r * x) * (ψ (r * z) * ψ (-(2 * r * y))) from
    fun x z y => by
      rw [show r * (x + z - 2 * y) = r * x + (r * z + -(2 * r * y)) from by ring]
      rw [psi_add, psi_add]]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [← mul_assoc]

/-- Combinatorial identity: the double sum counting AP triples (x,y) ∈ A×A
    with 2y−x ∈ A equals tripleCount(A) + |A|.
    When y=x: 2x−x = x ∈ A (always), contributing |A| triples.
    When y≠x: setting d=y−x gives d≠0, a=x∈A, a+d=y∈A, a+2d=2y−x∈A. -/
private lemma ap_pair_count {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (↑(tripleCount A) : ℂ) + ↑A.card =
    A.sum fun x => A.sum fun y => if 2 * y - x ∈ A then (1 : ℂ) else 0 := by
  -- Split inner sum at y=x: f(x) + ∑_{y≠x} f(y)
  have split : ∀ x ∈ A,
      (A.sum fun y => if 2 * y - x ∈ A then (1 : ℂ) else 0) =
      1 + ((A.erase x).sum fun y => if 2 * y - x ∈ A then (1 : ℂ) else 0) := by
    intro x hx
    rw [← Finset.add_sum_erase A _ hx]
    simp [show 2 * x - x = x from by ring, hx]
  rw [Finset.sum_congr rfl split, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Goal: ↑(tripleCount A) + ↑A.card = ↑A.card + ∑_{x∈A} ∑_{y∈A\{x}} [2y-x∈A]
  rw [add_comm]
  congr 1
  -- Remaining: ↑(tripleCount A) = ∑_{x∈A} ∑_{y∈A\{x}} [2y-x∈A ? 1 : 0]
  -- Both sides count {(a,d) : d≠0, a∈A, a+d∈A, a+2d∈A}
  -- Step 1: Show both sides equal ↑T.card where T = (A×A).filter(p.1≠p.2 ∧ 2p.2-p.1∈A)
  set T := (A ×ˢ A).filter (fun p : ZMod N × ZMod N => p.1 ≠ p.2 ∧ 2 * p.2 - p.1 ∈ A)
  -- The sum = ↑T.card
  suffices hsum : (∑ x ∈ A, ∑ y ∈ A.erase x,
      if 2 * y - x ∈ A then (1 : ℂ) else 0) = ↑T.card by
    rw [hsum]
    -- tripleCount A = T.card via bijection (a,d) ↦ (a, a+d)
    congr 1
    unfold tripleCount
    apply Finset.card_nbij (fun (p : ZMod N × ZMod N) => (p.1, p.1 + p.2))
    · -- maps into T
      intro ⟨a, d⟩ hmem
      have hm := (Finset.mem_filter.mp hmem).2
      -- hm : d ≠ 0 ∧ a ∈ A ∧ (a + d) ∈ A ∧ (a + 2 * d) ∈ A
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm.2.1, hm.2.2.1⟩, ?_, ?_⟩
      · intro heq; exact hm.1 (by linear_combination -heq)
      · convert hm.2.2.2 using 1; ring
    · -- injective
      intro ⟨a₁, d₁⟩ _ ⟨a₂, d₂⟩ _ h
      have h := Prod.mk.inj h
      exact Prod.ext h.1 (by linear_combination h.2 - h.1)
    · -- surjective
      intro ⟨x, y⟩ hmem
      have hm := Finset.mem_filter.mp hmem
      have hxy := Finset.mem_product.mp hm.1
      exact ⟨(x, y - x), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
         sub_ne_zero.mpr (Ne.symm hm.2.1),
         hxy.1, by convert hxy.2 using 1; ring,
         by convert hm.2.2 using 1; ring⟩,
        Prod.ext rfl (show x + (y - x) = y from by ring)⟩
  -- Prove sum = ↑T.card by converting ite sum to filter cardinality
  simp only [T, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  -- Use fiberwise counting: T decomposes into fibers over Prod.fst
  norm_cast
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := A) (fun ⟨a, _⟩ h => (Finset.mem_product.mp
      (Finset.mem_filter.mp h).1).1)]
  apply Finset.sum_congr rfl
  intro x hx
  -- Show: ((A.erase x).filter Q(x)).card = (T.filter (p.fst = x)).card
  apply Finset.card_nbij (fun (y : ZMod N) => ((x, y) : ZMod N × ZMod N))
  · intro y hy
    have hf := Finset.mem_filter.mp hy
    have he := Finset.mem_erase.mp hf.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx, he.2⟩, Ne.symm he.1, hf.2⟩, rfl⟩
  · intro _ _ _ _ h; exact (Prod.mk.inj h).2
  · intro ⟨a, b⟩ hmem
    have hf := Finset.mem_filter.mp hmem
    have ht := Finset.mem_filter.mp hf.1
    have hp := Finset.mem_product.mp ht.1
    have ha := hf.2; subst ha  -- substitute a = x
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
      ⟨Ne.symm ht.2.1, hp.2⟩, ht.2.2⟩,
      rfl⟩

/-- The Fourier identity for AP counting:
    tripleCount(A) + |A| = N⁻¹ · Σ_r Â(r)² · conj(Â(2r))
    Proof: Fourier expand, swap sums, apply character orthogonality,
    then count the combinatorial triples. -/
theorem triple_count_fourier {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (tripleCount A : ℂ) + ↑A.card = (↑N)⁻¹ *
      Finset.univ.sum (fun r : ZMod N =>
        fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r))) := by
  have hN : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [eq_comm, inv_mul_eq_div, div_eq_iff hN, eq_comm]
  -- Step 1: Expand each Fourier term as triple ψ sum
  simp_rw [fourier_term_expand]
  -- Step 2: Swap sums to bring r innermost
  rw [Finset.sum_comm]
  conv_rhs => arg 2; ext; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext; arg 2; ext; rw [Finset.sum_comm]
  -- Step 3: Apply character orthogonality: ∑_r ψ(r·c) = N·δ(c,0)
  simp_rw [char_orthogonality]
  -- Step 4: Swap z and y to make z the innermost, then eliminate z
  conv_rhs => arg 2; ext; rw [Finset.sum_comm]
  simp_rw [show ∀ (x y z : ZMod N), (x + z - 2 * y = 0) ↔ (z = 2 * y - x) from
    fun x y z => ⟨fun h => by linear_combination h, fun h => by subst h; ring⟩]
  simp_rw [Finset.sum_ite_eq']
  -- Step 5: Combinatorial identity
  -- Goal: (↑(tripleCount A) + ↑A.card) * ↑N =
  --   ∑_{x∈A} ∑_{y∈A} (if 2y-x ∈ A then ↑N else 0)
  -- Factor out N and reduce to a counting argument
  simp_rw [show ∀ (P : Prop) [Decidable P],
      (if P then (↑N : ℂ) else 0) = ↑N * (if P then (1 : ℂ) else 0) from
      fun P _ => by split_ifs <;> simp]
  simp_rw [← Finset.mul_sum]
  rw [mul_comm]
  congr 1
  -- Combinatorial identity: count (x,y)∈A×A with 2y-x∈A = tripleCount + |A|
  exact ap_pair_count A

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: LARGE FOURIER COEFFICIENT FROM AP-FREENESS
-- ═══════════════════════════════════════════════════════════════════

/-- In ZMod N, the nonzero kernel of multiplication by 2 has at most one element.
    If 2a = 0 and 2b = 0 with a,b ≠ 0, then a = b.
    Proof: 2·val(a) ≡ 0 (mod N) with 0 < val(a) < N forces val(a) = N/2. -/
private lemma two_mul_zero_unique {N : ℕ} [NeZero N]
    {a b : ZMod N} (ha : a ≠ 0) (hb : b ≠ 0)
    (h2a : 2 * a = 0) (h2b : 2 * b = 0) : a = b := by
  have hva_pos : 0 < ZMod.val a := by
    rwa [Nat.pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]
  have hvb_pos : 0 < ZMod.val b := by
    rwa [Nat.pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]
  have hva_lt : ZMod.val a < N := ZMod.val_lt a
  have hvb_lt : ZMod.val b < N := ZMod.val_lt b
  -- From 2*a = 0: (val a + val a) % N = 0, so val a + val a = N
  -- (the only multiple of N in [2, 2N-2])
  have hmoda : (ZMod.val a + ZMod.val a) % N = 0 := by
    have h := congr_arg ZMod.val (show a + a = 0 from by rw [← two_mul]; exact h2a)
    rwa [ZMod.val_add, ZMod.val_zero] at h
  have ha2 : ZMod.val a + ZMod.val a = N := by
    have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmoda
    have : 0 < k := by nlinarith
    have : k ≤ 1 := by nlinarith [show ZMod.val a + ZMod.val a < 2 * N from by omega]
    have : k = 1 := by omega
    subst this; linarith
  have hmodb : (ZMod.val b + ZMod.val b) % N = 0 := by
    have h := congr_arg ZMod.val (show b + b = 0 from by rw [← two_mul]; exact h2b)
    rwa [ZMod.val_add, ZMod.val_zero] at h
  have hb2 : ZMod.val b + ZMod.val b = N := by
    have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmodb
    have : 0 < k := by nlinarith
    have : k ≤ 1 := by nlinarith [show ZMod.val b + ZMod.val b < 2 * N from by omega]
    have : k = 1 := by omega
    subst this; linarith
  -- val a = val b (both equal N/2), hence a = b
  have hval_eq : ZMod.val a = ZMod.val b := by omega
  exact (ZMod.val_injective N) hval_eq

/-- Fourier coefficient at 0 equals the set cardinality: Â(0) = |A|. -/
private lemma fourierCoeff_zero' {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    fourierCoeff A 0 = ↑A.card := by
  simp only [fourierCoeff, zero_mul, ZMod.val_zero, Nat.cast_zero, zero_div, mul_zero,
    Complex.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- AP-free sets cannot be all of ZMod N for N ≥ 2. -/
private theorem apFree_card_lt {N : ℕ} [NeZero N] (hN2 : 1 < N) (A : Finset (ZMod N))
    (hAP : APFree A) : A.card < N := by
  by_contra h
  push_neg at h
  have hfull : A = Finset.univ := by
    apply Finset.eq_univ_of_card
    have := Finset.card_le_univ A
    rw [ZMod.card] at this ⊢; omega
  have h0 : (0 : ZMod N) ∈ A := hfull ▸ Finset.mem_univ _
  have h1 : (1 : ZMod N) ∈ A := hfull ▸ Finset.mem_univ _
  have h2 : (0 + 2 * 1 : ZMod N) ∈ A := hfull ▸ Finset.mem_univ _
  have h1_ne : (1 : ZMod N) ≠ 0 := by
    intro heq
    have h1cast : ((1 : ℕ) : ZMod N) = 0 := by norm_cast
    rw [ZMod.natCast_eq_zero_iff] at h1cast
    exact absurd (Nat.le_of_dvd (by omega) h1cast) (by omega)
  have h1' : (0 + 1 : ZMod N) ∈ A := by rwa [zero_add]
  exact hAP 0 1 h1_ne h0 h1' h2

/-- Parseval for nonzero frequencies: Σ_{r≠0} ‖Â(r)‖² = |A|·N - |A|². -/
private theorem parseval_nonzero {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖fourierCoeff A r‖ ^ 2) =
    A.card * N - A.card ^ 2 := by
  have hfull := parseval_on_zmod A
  have hsplit := Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ (0 : ZMod N))
    (fun r : ZMod N => ‖fourierCoeff A r‖ ^ 2)
  rw [hsplit] at hfull
  have h0 : ‖fourierCoeff A 0‖ ^ 2 = A.card ^ 2 := by
    rw [fourierCoeff_zero']; simp [Complex.norm_natCast]
  linarith

/-- If A has no 3-AP and has density delta, then some Fourier coefficient
    is large. This is the key analytic step in Roth's proof.

    Case 1 (δ²N < 2): Parseval pigeonhole gives max ≥ 1 > δ²N/2.
    Case 2 (δ²N ≥ 2): By contradiction using the Fourier identity
    and AM-GM bound. -/
theorem fourier_large_coefficient {N : ℕ} (hN : 1 < N) (A : Finset (ZMod N))
    (hAP : APFree A) (delta : ℝ) (hdelta : 0 < delta)
    (hdensity : (A.card : ℝ) ≥ delta * N) :
    ∃ r : ZMod N, r ≠ 0 ∧ ‖fourierCoeff A r‖ ≥ delta ^ 2 * N / 2 := by
  haveI : NeZero N := ⟨by omega⟩
  set n := A.card with hn_def
  have hNr : (N : ℝ) > 0 := by positivity
  have hn_pos : (n : ℝ) > 0 := by linarith [mul_pos hdelta hNr]
  have hn_nat_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h] at hn_pos
    · exact h
  have hn_lt : n < N := apFree_card_lt hN A hAP
  set T := Finset.univ \ {(0 : ZMod N)} with hT_def
  have hT_card : T.card = N - 1 := by
    rw [hT_def, show Finset.univ \ {(0 : ZMod N)} = Finset.univ.erase 0 from
      Finset.sdiff_singleton_eq_erase _ _,
      Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
  have hT_nonempty : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    rw [hT_def] at h
    have hsub : Finset.univ ⊆ ({(0 : ZMod N)} : Finset (ZMod N)) :=
      Finset.sdiff_eq_empty_iff_subset.mp h
    have hcard : Fintype.card (ZMod N) ≤ 1 := by
      rw [← Finset.card_univ]; exact le_trans (Finset.card_le_card hsub) (by simp)
    rw [ZMod.card] at hcard; omega
  have hparseval_eq : T.sum (fun r => ‖fourierCoeff A r‖ ^ 2) = (n : ℝ) * (N - n) := by
    have := parseval_nonzero A
    have hn_le_N : (n : ℝ) ≤ N := by exact_mod_cast hn_lt.le
    nlinarith
  -- n(N-n) ≥ N-1 since n ∈ {1,...,N-1}
  have hn_prod_ge : (n : ℝ) * (N - n) ≥ N - 1 := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn_nat_pos
    have h2 : (1 : ℝ) ≤ N - n := by
      have : n + 1 ≤ N := hn_lt
      have : (↑(n + 1) : ℝ) ≤ ↑N := Nat.cast_le.mpr this
      push_cast at this; linarith
    nlinarith
  by_cases hcase : delta ^ 2 * ↑N < 2
  · -- CASE 1: δ²N < 2, so δ²N/2 < 1. Parseval pigeonhole gives max ≥ 1.
    -- Σ_{r∈T} ‖Â(r)‖² ≥ N-1. T has N-1 elements. So ∃ r, ‖Â(r)‖² ≥ 1.
    have hbound : delta ^ 2 * ↑N / 2 < 1 := by linarith
    have hmax : ∃ r ∈ T, ‖fourierCoeff A r‖ ^ 2 ≥ 1 := by
      by_contra h; push_neg at h
      have hsum_lt : T.sum (fun r => ‖fourierCoeff A r‖ ^ 2) < ↑T.card := by
        obtain ⟨w, hw⟩ := hT_nonempty
        calc T.sum _ < T.sum (fun _ => (1 : ℝ)) :=
              Finset.sum_lt_sum (fun r hr => le_of_lt (h r hr))
                ⟨w, hw, h _ hw⟩
          _ = ↑T.card := by simp [Finset.sum_const, nsmul_eq_mul]
      rw [hT_card, hparseval_eq, show (↑(N - 1 : ℕ) : ℝ) = ↑N - 1 from by
        rw [Nat.cast_sub (by omega : 1 ≤ N)]; push_cast; ring] at hsum_lt
      linarith
    obtain ⟨r, hr, hrge⟩ := hmax
    exact ⟨r, by intro h; subst h; simp [hT_def] at hr,
      by nlinarith [norm_nonneg (fourierCoeff A r)]⟩
  · -- CASE 2: δ²N ≥ 2. By contradiction using Fourier identity + AM-GM.
    push_neg at hcase
    by_contra hall; push_neg at hall
    -- hall : ∀ r ≠ 0, ‖Â(r)‖ < δ²N/2
    -- From AP-free: nN = n³ + S where S = Σ_{r≠0} Â(r)²·conj(Â(2r))
    have htc : tripleCount A = 0 := (apFree_iff_tripleCount_zero A).mp hAP
    have hfourier := triple_count_fourier A
    rw [htc, Nat.cast_zero, zero_add] at hfourier
    have hNc : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have hsum_eq : Finset.univ.sum (fun r : ZMod N =>
        fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r))) = ↑n * ↑N := by
      -- hfourier : ↑n = (↑N)⁻¹ * sum, so sum = ↑n * ↑N
      set S' := Finset.univ.sum (fun r : ZMod N =>
        fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r)))
      show S' = ↑n * ↑N
      have h1 : (↑N : ℂ) * ↑n = S' := by
        rw [hfourier, ← mul_assoc, mul_inv_cancel₀ hNc, one_mul]
      rw [mul_comm] at h1; exact h1.symm
    have h0term : fourierCoeff A 0 ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * 0)) =
        (↑n : ℂ) ^ 3 := by
      simp only [mul_zero, fourierCoeff_zero', map_natCast]; ring
    have hsplit := Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ (0 : ZMod N))
      (fun r : ZMod N => fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r)))
    rw [hsplit, h0term] at hsum_eq
    -- S = nN - n³
    set S := T.sum (fun r => fourierCoeff A r ^ 2 *
      starRingEnd ℂ (fourierCoeff A (2 * r)))
    have hS_val : S = ↑n * ↑N - (↑n : ℂ) ^ 3 := by
      -- hsum_eq : (↑n)^3 + S = ↑n * ↑N (after rewrites)
      linear_combination hsum_eq
    -- n² > N (from δ²N ≥ 2 and n ≥ δN)
    have hn2_gt : (n : ℝ) ^ 2 > N := by nlinarith [sq_nonneg (n - delta * N)]
    -- ‖S‖ = |nN - n³| = n(n²-N) > 0
    have hS_norm_eq : ‖S‖ = (n : ℝ) * ((n : ℝ) ^ 2 - N) := by
      rw [hS_val]
      rw [show (↑n : ℂ) * ↑N - (↑n : ℂ) ^ 3 =
          -((↑n : ℂ) * ((↑n : ℂ) ^ 2 - ↑N)) from by ring]
      rw [norm_neg, Complex.norm_mul, Complex.norm_natCast]
      congr 1
      rw [show (↑n : ℂ) ^ 2 - (↑N : ℂ) = (↑((n : ℝ) ^ 2 - (N : ℝ)) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < (n : ℝ) ^ 2 - ↑N)]
    -- Derive n²-N < δ²N²/2 by splitting the Fourier sum into terms where
    -- 2r ≠ 0 (bounded by hypothesis+Parseval) and 2r = 0 (at most one term).
    have key : (n : ℝ) ^ 2 - ↑N < delta ^ 2 * ↑N ^ 2 / 2 := by
      -- Set B = δ²N/2 (the hypothetical upper bound on all ‖Â(r)‖)
      set B := delta ^ 2 * (↑N : ℝ) / 2 with hB_def
      have hB_pos : 0 < B := by positivity
      -- Key: n > B (since n ≥ δN and B = δ²N/2 < δN when δ < 2)
      have hn_gt_B : (↑n : ℝ) > B := by
        -- n ≥ δN > δ²N/2 = B because δ < 1 (from n < N and n ≥ δN)
        have hd_lt_1 : delta < 1 := by
          have : (↑n : ℝ) < ↑N := by exact_mod_cast hn_lt
          nlinarith
        nlinarith [sq_nonneg (1 - delta)]
      -- Step 1: ‖S‖ ≤ Σ_T ‖Â(r)‖² · ‖Â(2r)‖
      set g := fun r : ZMod N => ‖fourierCoeff A r‖ ^ 2 * ‖fourierCoeff A (2 * r)‖
      have hS_le_sum : ‖S‖ ≤ T.sum g := by
        calc ‖S‖ ≤ T.sum (fun r =>
              ‖fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r))‖) :=
              norm_sum_le T _
          _ = T.sum g := by
              congr 1; ext r
              rw [norm_mul, norm_pow]; congr 1
              exact RCLike.norm_conj _
      -- Step 2: Split T = T₁ ∪ T₂ where T₂ = {r ∈ T : 2r = 0}
      set T₁ := T.filter (fun r : ZMod N => (2 : ZMod N) * r ≠ 0)
      set T₂ := T.filter (fun r : ZMod N => ¬((2 : ZMod N) * r ≠ 0))
      have hT_split : T.sum g = T₁.sum g + T₂.sum g :=
        (Finset.sum_filter_add_sum_filter_not T (fun r => (2 : ZMod N) * r ≠ 0) g).symm
      -- Step 3: T₂ has ≤ 1 element (kernel of ×2, minus {0})
      have hT2_le1 : T₂.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        have ha' := Finset.mem_filter.mp ha
        have hb' := Finset.mem_filter.mp hb
        have ha_in_T := ha'.1
        have hb_in_T := hb'.1
        have h2a : (2 : ZMod N) * a = 0 := not_not.mp ha'.2
        have h2b : (2 : ZMod N) * b = 0 := not_not.mp hb'.2
        have ha_ne : a ≠ 0 := by
          rw [hT_def, Finset.mem_sdiff, Finset.mem_singleton] at ha_in_T
          exact ha_in_T.2
        have hb_ne : b ≠ 0 := by
          rw [hT_def, Finset.mem_sdiff, Finset.mem_singleton] at hb_in_T
          exact hb_in_T.2
        exact two_mul_zero_unique ha_ne hb_ne h2a h2b
      -- Step 4: Bound T₁ sum ≤ B · n(N-n) [use hall on 2r ≠ 0]
      have hT1_le : T₁.sum g ≤ B * ((↑n : ℝ) * (↑N - ↑n)) := by
        calc T₁.sum g
            ≤ T₁.sum (fun r => ‖fourierCoeff A r‖ ^ 2 * B) := by
              apply Finset.sum_le_sum; intro r hr
              exact mul_le_mul_of_nonneg_left
                (le_of_lt (hall (2 * r) (Finset.mem_filter.mp hr).2)) (sq_nonneg _)
          _ = B * T₁.sum (fun r => ‖fourierCoeff A r‖ ^ 2) := by
              simp_rw [mul_comm _ B]; exact (Finset.mul_sum T₁ _ B).symm
          _ ≤ B * ((↑n : ℝ) * (↑N - ↑n)) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hB_pos)
              calc T₁.sum (fun r => ‖fourierCoeff A r‖ ^ 2)
                  ≤ T.sum (fun r => ‖fourierCoeff A r‖ ^ 2) :=
                    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                      (fun r _ _ => sq_nonneg _)
                _ = (↑n : ℝ) * (↑N - ↑n) := hparseval_eq
      -- Step 5: Bound T₂ sum ≤ B² · n [2r=0 so ‖Â(2r)‖=n; ‖Â(r)‖<B; ≤1 term]
      have hT2_le : T₂.sum g ≤ B ^ 2 * ↑n := by
        calc T₂.sum g
            ≤ T₂.sum (fun _ => B ^ 2 * (↑n : ℝ)) := by
              apply Finset.sum_le_sum; intro r hr
              have hr' := Finset.mem_filter.mp hr
              have h2r : (2 : ZMod N) * r = 0 := not_not.mp hr'.2
              have hr_ne : r ≠ 0 := by
                have := hr'.1; rw [hT_def, Finset.mem_sdiff, Finset.mem_singleton] at this
                exact this.2
              -- ‖Â(2r)‖ = ‖Â(0)‖ = n (since 2r = 0)
              have hA2r : ‖fourierCoeff A ((2 : ZMod N) * r)‖ = ↑n := by
                rw [h2r, fourierCoeff_zero', Complex.norm_natCast]
              -- ‖Â(r)‖² ≤ B²
              have hAr_sq : ‖fourierCoeff A r‖ ^ 2 ≤ B ^ 2 :=
                sq_le_sq' (by linarith [norm_nonneg (fourierCoeff A r)])
                  (le_of_lt (hall r hr_ne))
              calc g r = ‖fourierCoeff A r‖ ^ 2 * ‖fourierCoeff A (2 * r)‖ := rfl
                _ = ‖fourierCoeff A r‖ ^ 2 * ↑n := by rw [hA2r]
                _ ≤ B ^ 2 * ↑n := mul_le_mul_of_nonneg_right hAr_sq (by positivity)
          _ = ↑T₂.card * (B ^ 2 * (↑n : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 1 * (B ^ 2 * (↑n : ℝ)) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hT2_le1) (by positivity)
          _ = B ^ 2 * ↑n := one_mul _
      -- Step 6: n(n²-N) ≤ B·n(N-n) + B²·n < B·n·N, hence n²-N < B·N = δ²N²/2
      have h_total : ↑n * ((↑n : ℝ) ^ 2 - ↑N) ≤ B * (↑n * (↑N - ↑n)) + B ^ 2 * ↑n := by
        calc ↑n * ((↑n : ℝ) ^ 2 - ↑N) = ‖S‖ := hS_norm_eq.symm
          _ ≤ T.sum g := hS_le_sum
          _ = T₁.sum g + T₂.sum g := hT_split
          _ ≤ B * (↑n * (↑N - ↑n)) + B ^ 2 * ↑n := add_le_add hT1_le hT2_le
      -- B²·n < B·n² (since B < n), so total < B·n·N, giving n²-N < B·N
      nlinarith [mul_pos hB_pos (mul_pos (show (0 : ℝ) < ↑n from by positivity)
        (sub_pos.mpr hn_gt_B))]
    -- But n ≥ δN, so n² ≥ δ²N²
    have hn2_ge : (n : ℝ) ^ 2 ≥ delta ^ 2 * N ^ 2 := by
      nlinarith [sq_nonneg ((↑n : ℝ) - delta * ↑N)]
    -- δ²N² - N < δ²N²/2 and δ²N ≥ 2 → δ²N²/2 ≥ N, contradiction
    have hcaseN : delta ^ 2 * (↑N : ℝ) ^ 2 / 2 ≥ ↑N := by
      have h1 := mul_le_mul_of_nonneg_right hcase (show (0 : ℝ) ≤ ↑N from by positivity)
      -- h1 : 2 * ↑N ≤ delta ^ 2 * ↑N * ↑N
      have h2 : delta ^ 2 * (↑N : ℝ) * ↑N = delta ^ 2 * ↑N ^ 2 := by ring
      linarith
    linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART V: DENSITY INCREMENT INFRASTRUCTURE
-- ═══════════════════════════════════════════════════════════════════

/-- **Counting lemma**: For N ≥ 3, any AP-free subset of Z/NZ has at most 2N/3
    elements. The argument: for d = 1, the triples {a, a+1, a+2} cover Z/NZ.
    Each missing element destroys at most 2 such "good" starting points.
    If |A| > 2N/3, then some triple {a, a+1, a+2} ⊆ A, contradicting AP-free.

    Formally: T = {a ∈ A : a+1 ∈ A ∧ a+2 ∈ A}. Elements of A \ T either miss
    a+1 or a+2 from A. Each "missing" set has size ≤ N - |A| (by injection
    into the complement). So |A \ T| ≤ 2(N - |A|), giving |T| ≥ 3|A| - 2N. -/
private theorem apFree_card_le_two_thirds {N : ℕ} [NeZero N] (hN3 : 2 < N)
    (A : Finset (ZMod N)) (hAP : APFree A) :
    3 * A.card ≤ 2 * N := by
  by_contra h_big
  push_neg at h_big
  -- h_big : 3 * A.card > 2 * N, i.e., A.card > 2N/3
  -- Define T = {a ∈ A : a+1 ∈ A ∧ a+2 ∈ A}
  set T := A.filter (fun a => a + 1 ∈ A ∧ a + 2 * 1 ∈ A) with hT_def
  -- The "bad" sets: B1 = {a ∈ A : a+1 ∉ A}, B2 = {a ∈ A : a+2 ∉ A}
  set B1 := A.filter (fun a => a + 1 ∉ A) with hB1_def
  set B2 := A.filter (fun a => a + 2 * 1 ∉ A) with hB2_def
  -- Each bad set has card ≤ N - A.card via injection into complement
  have hcompl_card : (Finset.univ \ A).card = N - A.card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    rw [Finset.card_univ, ZMod.card] at h; omega
  have hB1_le : B1.card ≤ N - A.card := by
    rw [← hcompl_card]
    apply Finset.card_le_card_of_injOn (fun a => a + 1)
      (fun a ha => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩)
      (fun a _ b _ h => add_right_cancel h)
  have hB2_le : B2.card ≤ N - A.card := by
    rw [← hcompl_card]
    apply Finset.card_le_card_of_injOn (fun a => a + 2 * 1)
      (fun a ha => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩)
      (fun a _ b _ h => add_right_cancel h)
  -- A \ T ⊆ B1 ∪ B2 (if a ∈ A but not in T, then a+1 ∉ A or a+2 ∉ A)
  have hAT_sub : A \ T ⊆ B1 ∪ B2 := by
    intro a ha
    have haA := (Finset.mem_sdiff.mp ha).1
    have haT := (Finset.mem_sdiff.mp ha).2
    rw [hT_def, Finset.mem_filter] at haT
    push_neg at haT
    have h_miss := haT haA
    by_cases h_a1 : a + 1 ∈ A
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haA, h_miss h_a1⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haA, h_a1⟩)
  -- |T| ≥ 3|A| - 2N > 0
  have hcard_le : A.card ≤ N := card_le_nat A
  have hT_sub_A : T ⊆ A := Finset.filter_subset _ _
  have h_split : (A \ T).card + T.card = A.card :=
    Finset.card_sdiff_add_card_eq_card hT_sub_A
  have h_bad : (A \ T).card ≤ B1.card + B2.card :=
    le_trans (Finset.card_le_card hAT_sub) (Finset.card_union_le B1 B2)
  have h_AT_le : (A \ T).card ≤ 2 * (N - A.card) := by omega
  have hT_card : T.card ≥ 3 * A.card - 2 * N := by omega
  -- T is nonempty
  have hT_nonempty : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty; rw [h_empty, Finset.card_empty] at hT_card; omega
  -- Extract witness: a ∈ A with a+1 ∈ A and a+2 ∈ A
  obtain ⟨a, ha⟩ := hT_nonempty
  have ha' := Finset.mem_filter.mp ha
  -- This is a 3-AP with d = 1 ≠ 0, contradicting APFree
  have hd_ne : (1 : ZMod N) ≠ 0 := by
    intro h
    have h1 : ((1 : ℕ) : ZMod N) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
  exact hAP a 1 hd_ne ha'.1 ha'.2.1 ha'.2.2

/-- Corollary: AP-free density is bounded away from 1 for N ≥ 3. -/
private theorem apFree_density_bound {N : ℕ} [NeZero N] (hN3 : 2 < N)
    (A : Finset (ZMod N)) (hAP : APFree A) :
    (A.card : ℝ) ≤ 2 * N / 3 := by
  have h := apFree_card_le_two_thirds hN3 A hAP
  have : 3 * (A.card : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast h
  linarith

/-- Restriction of A to a coset of the subgroup generated by g ∣ N.
    For g dividing N, coset j has elements {j + k·g : k = 0,...,N/g-1}.
    The restriction maps each such element to k ∈ ZMod (N/g). -/
noncomputable def cosetRestrict {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (g : ℕ) (hg : 0 < g) (hgN : g ∣ N) (j : ℕ) (hj : j < g) :
    Finset (ZMod (N / g)) :=
  haveI : NeZero (N / g) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hgN) hg).ne'⟩
  Finset.univ.filter fun k : ZMod (N / g) =>
    (↑j + ↑(ZMod.val k) * ↑g : ZMod N) ∈ A

/-- AP-freeness transfers from Z_N to Z_{N/g} via coset restriction.
    A 3-AP {c, c+d, c+2d} in Z_{N/g} maps to {j+cg, j+(c+d)g, j+(c+2d)g}
    in Z_N, which is a 3-AP with common difference dg. Since g(N/g) = N ≡ 0,
    the map preserves modular arithmetic. -/
private theorem apFree_coset_restrict {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (hAP : APFree A) (g : ℕ) (hg : 0 < g) (hgN : g ∣ N) (j : ℕ) (hj : j < g) :
    APFree (cosetRestrict A g hg hgN j hj) := by
  haveI : NeZero (N / g) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hgN) hg).ne'⟩
  set M := N / g with hM_def
  have hMg : M * g = N := Nat.div_mul_cancel hgN
  intro c d hd hc hcd h2cd
  -- c, c+d, c+2d ∈ cosetRestrict means j + val(·)*g ∈ A
  simp only [cosetRestrict, Finset.mem_filter, Finset.mem_univ, true_and] at hc hcd h2cd
  -- Key: val(a+b)*g ≡ (val a + val b)*g (mod N) because val_add gives mod M and M*g = N
  have val_mul_g_add : ∀ (a b : ZMod M),
      (↑(ZMod.val (a + b)) * ↑g : ZMod N) =
      ↑(ZMod.val a) * ↑g + ↑(ZMod.val b) * ↑g := by
    intro a b
    rw [ZMod.val_add]
    set x := ZMod.val a + ZMod.val b
    -- Reduce both sides to single Nat.cast expressions
    rw [show (↑(x % M) * (↑g : ZMod N)) = (↑(x % M * g) : ZMod N) from by
          rw [Nat.cast_mul],
      show (↑(ZMod.val a) * (↑g : ZMod N) + ↑(ZMod.val b) * ↑g) = (↑(x * g) : ZMod N) from by
          rw [Nat.cast_mul, Nat.cast_add]; ring]
    -- x*g = x%M*g + x/M*N, so they're equal in ZMod N
    symm
    conv_lhs => rw [show x * g = x % M * g + x / M * N from by
      calc x * g = (M * (x / M) + x % M) * g := by congr 1; linarith [Nat.div_add_mod x M]
        _ = x / M * (M * g) + x % M * g := by ring
        _ = x / M * N + x % M * g := by rw [hMg]
        _ = x % M * g + x / M * N := by ring]
    simp only [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero (ZMod N) N, mul_zero, add_zero]
  -- The images form a 3-AP: φ(c+d) = φ(c) + val(d)*g, φ(c+2d) = φ(c) + 2*val(d)*g
  have hcd_eq : (↑j + ↑(ZMod.val (c + d)) * ↑g : ZMod N) =
      (↑j + ↑(ZMod.val c) * ↑g) + ↑(ZMod.val d) * ↑g := by
    rw [val_mul_g_add]; ring
  have h2cd_eq : (↑j + ↑(ZMod.val (c + 2 * d)) * ↑g : ZMod N) =
      (↑j + ↑(ZMod.val c) * ↑g) + 2 * (↑(ZMod.val d) * ↑g) := by
    rw [show c + 2 * d = c + d + d from by ring, val_mul_g_add, val_mul_g_add]; ring
  -- The common difference val(d)*g is nonzero in Z_N
  -- Since d ≠ 0: val(d) ∈ {1,...,M-1}, so val(d)*g ∈ {g,...,(M-1)*g} ⊂ {1,...,N-1}
  have hd_ne_N : (↑(ZMod.val d) * ↑g : ZMod N) ≠ 0 := by
    intro h
    have hval_pos : 0 < ZMod.val d := by
      rwa [Nat.pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]
    have hprod_pos : 0 < ZMod.val d * g := Nat.mul_pos hval_pos hg
    have hprod_lt : ZMod.val d * g < N := by
      calc ZMod.val d * g < M * g := Nat.mul_lt_mul_of_pos_right (ZMod.val_lt d) hg
        _ = N := hMg
    have h_cast : ((ZMod.val d * g : ℕ) : ZMod N) = 0 := by push_cast at h ⊢; exact h
    rw [ZMod.natCast_eq_zero_iff] at h_cast
    exact absurd (Nat.le_of_dvd hprod_pos h_cast) (by omega)
  -- Apply APFree to get contradiction
  exact hAP (↑j + ↑(ZMod.val c) * ↑g) (↑(ZMod.val d) * ↑g) hd_ne_N
    hc (hcd_eq ▸ hcd) (h2cd_eq ▸ h2cd)

/-- Coset cardinality helper for clean summation over Fin g. -/
private noncomputable def cosetCardFin {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (g : ℕ) (hg : 0 < g) (hgN : g ∣ N) (j : Fin g) : ℕ :=
  (cosetRestrict A g hg hgN j.val j.isLt).card

/-- `↑(ZMod.val x) = x` in `ZMod N`. -/
private lemma natCast_zmod_val' {N : ℕ} [NeZero N] (x : ZMod N) :
    (↑(ZMod.val x) : ZMod N) = x := ZMod.natCast_zmod_val x

/-- Each coset has the same cardinality as the corresponding fiber of the
    coset index function `x ↦ val(x) % g`. -/
private lemma coset_fiber_card_eq {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (g : ℕ) (hg : 0 < g) (hgN : g ∣ N) (j : ℕ) (hj : j < g) :
    let M := N / g
    let idx : ZMod N → Fin g := fun x => ⟨ZMod.val x % g, Nat.mod_lt _ hg⟩
    cosetCardFin A g hg hgN ⟨j, hj⟩ = (A.filter (fun x => idx x = ⟨j, hj⟩)).card := by
  intro M idx
  have hMg : M * g = N := Nat.div_mul_cancel hgN
  have hM_pos : 0 < M := Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hgN) hg
  haveI : NeZero M := ⟨by omega⟩
  have hval_range : ∀ (k : ZMod M), j + ZMod.val k * g < N := by
    intro k; nlinarith [ZMod.val_lt k]
  simp only [cosetCardFin, cosetRestrict]
  apply Finset.card_nbij (fun k : ZMod M => (↑j + ↑(ZMod.val k) * ↑g : ZMod N))
  · -- Maps coset into fiber
    intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    refine ⟨hk, ?_⟩
    show idx (↑j + ↑(ZMod.val k) * ↑g : ZMod N) = ⟨j, hj⟩; ext
    show ZMod.val (↑j + ↑(ZMod.val k) * ↑g : ZMod N) % g = j
    have hcast_k : (↑j + ↑(ZMod.val k) * ↑g : ZMod N) =
        (↑(j + ZMod.val k * g) : ZMod N) := by
      rw [Nat.cast_add, Nat.cast_mul]
    rw [hcast_k, ZMod.val_natCast, Nat.mod_eq_of_lt (hval_range k),
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  · -- Injective
    intro a₁ ha₁ a₂ ha₂ heq
    suffices ZMod.val a₁ = ZMod.val a₂ from (ZMod.val_injective M) this
    -- heq : ↑j + ↑(ZMod.val a₁) * ↑g = ↑j + ↑(ZMod.val a₂) * ↑g in ZMod N
    have hmul_eq : (↑(ZMod.val a₁) * ↑g : ZMod N) = ↑(ZMod.val a₂) * ↑g :=
      add_left_cancel heq
    -- Lift to ℕ: both products < N, so they're equal as naturals
    have hprod_eq : ZMod.val a₁ * g = ZMod.val a₂ * g := by
      have h1 : ZMod.val a₁ * g < N := by nlinarith [ZMod.val_lt a₁, hMg]
      have h2 : ZMod.val a₂ * g < N := by nlinarith [ZMod.val_lt a₂, hMg]
      have hmul_cast : (↑(ZMod.val a₁ * g) : ZMod N) = ↑(ZMod.val a₂ * g) := by
        rw [Nat.cast_mul, Nat.cast_mul]; exact hmul_eq
      have h := ZMod.val_natCast_of_lt h1
      have h' := ZMod.val_natCast_of_lt h2
      have := congr_arg ZMod.val hmul_cast
      rw [h, h'] at this; exact this
    exact Nat.eq_of_mul_eq_mul_right hg hprod_eq
  · -- Surjective
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx
    have hmod : ZMod.val x % g = j := by
      have := congr_arg Fin.val hx.2; exact this
    have hdiv : ZMod.val x / g < M :=
      Nat.div_lt_of_lt_mul (by linarith [ZMod.val_lt x, hMg])
    have hval_k : ZMod.val (↑(ZMod.val x / g) : ZMod M) = ZMod.val x / g :=
      by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hdiv]
    have hrecomp : j + ZMod.val x / g * g = ZMod.val x := by
      rw [← hmod, mul_comm (ZMod.val x / g) g]; exact Nat.mod_add_div (ZMod.val x) g
    have himage : (↑j + ↑(ZMod.val (↑(ZMod.val x / g) : ZMod M)) * ↑g : ZMod N) = x := by
      rw [hval_k]
      have : (↑j + ↑(ZMod.val x / g) * ↑g : ZMod N) =
          (↑(j + ZMod.val x / g * g) : ZMod N) := by rw [Nat.cast_add, Nat.cast_mul]
      rw [this, hrecomp, natCast_zmod_val']
    exact ⟨↑(ZMod.val x / g), by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [himage]; exact hx.1, himage⟩

/-- Partition: sum of coset cardinalities = |A|. -/
private lemma coset_partition_sum {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (g : ℕ) (hg : 0 < g) (hgN : g ∣ N) :
    ∑ j : Fin g, (cosetCardFin A g hg hgN j : ℝ) = ↑A.card := by
  suffices h : ∑ j : Fin g, cosetCardFin A g hg hgN j = A.card by exact_mod_cast h
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun x : ZMod N => (⟨ZMod.val x % g, Nat.mod_lt _ hg⟩ : Fin g))
    (fun _ _ => Finset.mem_univ _)]
  exact Finset.sum_congr rfl (fun ⟨j, hj⟩ _ => coset_fiber_card_eq A g hg hgN j hj)

/-- Fourier decomposition via compatible cosets. -/
private lemma fourier_coset_decomp {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (g : ℕ) (hg : 0 < g) (hgN : g ∣ N)
    (r : ZMod N) (hcompat : (N / g) ∣ ZMod.val r) :
    fourierCoeff A r =
    ∑ j : Fin g, ↑(cosetCardFin A g hg hgN j) * ψ (r * (↑j.val : ZMod N)) := by
  set M := N / g with hM_def
  have hMg : M * g = N := Nat.div_mul_cancel hgN
  have hM_pos : 0 < M := Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hgN) hg
  haveI : NeZero M := ⟨by omega⟩
  -- Key: r * ↑g = 0 in ZMod N (from compatibility condition)
  have hrg : r * (↑g : ZMod N) = 0 := by
    obtain ⟨q, hq⟩ := hcompat
    have : (↑(ZMod.val r * g) : ZMod N) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact ⟨q, by rw [hq]; calc M * q * g = q * (M * g) := by ring
        _ = q * N := by rw [hMg]
        _ = N * q := by ring⟩
    rwa [show (↑(ZMod.val r * g) : ZMod N) = r * ↑g from by
      rw [Nat.cast_mul, natCast_zmod_val']] at this
  -- ψ is constant on cosets: ψ(r*x) = ψ(r*j) when val(x) % g = j
  have hpsi_const : ∀ (x : ZMod N) (j : ℕ), ZMod.val x % g = j →
      ψ (r * x) = ψ (r * (↑j : ZMod N)) := by
    intro x j hmod
    have hdiv : ZMod.val x / g < M :=
      Nat.div_lt_of_lt_mul (by linarith [ZMod.val_lt x, hMg])
    have hx_eq : x = (↑j : ZMod N) + ↑(ZMod.val x / g) * ↑g := by
      have hcast : (↑j : ZMod N) + ↑(ZMod.val x / g) * ↑g =
          (↑(j + ZMod.val x / g * g) : ZMod N) := by rw [Nat.cast_add, Nat.cast_mul]
      rw [hcast, show j + ZMod.val x / g * g = ZMod.val x from by
          rw [← hmod, mul_comm]; exact Nat.mod_add_div (ZMod.val x) g,
        natCast_zmod_val']
    rw [hx_eq]; congr 1
    calc r * ((↑j : ZMod N) + ↑(ZMod.val x / g) * ↑g)
        = r * ↑j + ↑(ZMod.val x / g) * (r * ↑g) := by ring
      _ = r * ↑j := by rw [hrg, mul_zero, add_zero]
  -- Partition the Fourier sum by coset index
  set idx : ZMod N → Fin g := fun x => ⟨ZMod.val x % g, Nat.mod_lt _ hg⟩ with hidx
  rw [fourierCoeff_eq_sum_psi,
    show (A.sum fun x => ψ (r * x)) =
        ∑ j : Fin g, ∑ x ∈ A.filter (fun x => idx x = j), ψ (r * x) from
      (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm]
  apply Finset.sum_congr rfl; intro ⟨j, hj⟩ _
  -- In fiber j: ψ(r*x) = ψ(r*↑j) for all x, so sum = count * ψ(r*↑j)
  rw [Finset.sum_congr rfl (fun x hx => hpsi_const x j (congr_arg Fin.val
    (Finset.mem_filter.mp hx).2)),
    Finset.sum_const, nsmul_eq_mul]
  -- Fiber cardinality = cosetCardFin (reuse helper)
  exact_mod_cast congrArg (· * ψ (r * (↑j : ZMod N)))
    (congrArg Nat.cast (coset_fiber_card_eq A g hg hgN j hj).symm)

/-- Character sum over compatible cosets vanishes. -/
private lemma char_sum_cosets_zero {N : ℕ} [NeZero N] (g : ℕ) (_hg : 0 < g) (hgN : g ∣ N)
    (r : ZMod N) (hr : r ≠ 0) (hcompat : (N / g) ∣ ZMod.val r) :
    ∑ j : Fin g, ψ (r * (↑j.val : ZMod N)) = 0 := by
  set ω := ψ r with hω_def
  have hterm : ∀ j : Fin g, ψ (r * (↑j.val : ZMod N)) = ω ^ j.val := by
    intro ⟨j, hj⟩; simp only
    induction j with
    | zero => simp [Nat.cast_zero, mul_zero, psi_zero, pow_zero]
    | succ k ih =>
      rw [pow_succ, ← ih (by omega)]
      rw [show (↑(k + 1) : ZMod N) = (↑k : ZMod N) + 1 from by rw [Nat.cast_add, Nat.cast_one]]
      rw [mul_add, mul_one, psi_add]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range]
  have hωg : ω ^ g = 1 := by
    rw [hω_def]; simp only [ψ, ← Complex.exp_nat_mul]
    obtain ⟨q, hq⟩ := hcompat
    have hN_ne : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have hkey : g * ZMod.val r = N * q := by
      rw [hq]; calc g * (N / g * q) = N / g * g * q := by ring
        _ = N * q := by rw [Nat.div_mul_cancel hgN]
    rw [show (↑g : ℂ) * (2 * ↑Real.pi * Complex.I * (↑(ZMod.val r) / ↑N)) =
      ↑(g * ZMod.val r) / ↑N * (2 * ↑Real.pi * Complex.I) from by push_cast; ring,
      show (↑(g * ZMod.val r) : ℂ) = ↑(N * q) from by exact_mod_cast hkey,
      show (↑(N * q) : ℂ) / ↑N = ↑q from by push_cast; field_simp]
    exact exp_int_mul_two_pi_I q
  exact root_unity_sum_zero ω g hωg (hω_def ▸ psi_ne_one r hr)

/-- Coset pigeonhole: with a compatible large Fourier coefficient, some coset
    has density ≥ δ + δ²/4. Decomposes Â(r) by cosets, uses vanishing
    character sum, applies triangle inequality + pigeonhole.

    Â(r) = Σ (f_j - m)·ψ(rj), |Â(r)| ≤ Σ|f_j - m| ≥ δ²N/2.
    Σ(f_j - m) = 0 ⟹ Σ(f_j - m)⁺ ≥ δ²N/4.
    max(f_j) ≥ m + δ²N/(4g) = m + δ²M/4 where M = N/g. -/
private theorem coset_density_increment {N : ℕ} [NeZero N] (hN : 1 < N)
    (A : Finset (ZMod N)) (_hAP : APFree A) (delta : ℝ) (hdelta : 0 < delta)
    (hdensity : (A.card : ℝ) ≥ delta * N) (g : ℕ) (hg : 0 < g) (hgN : g ∣ N)
    (r : ZMod N) (hr : r ≠ 0) (hlarge : ‖fourierCoeff A r‖ ≥ delta ^ 2 * N / 2)
    (hcompat : (N / g) ∣ ZMod.val r) :
    ∃ (j : ℕ) (hj : j < g),
      ((cosetRestrict A g hg hgN j hj).card : ℝ) ≥
        (delta + delta ^ 2 / 4) * (N / g : ℝ) := by
  set M := N / g with hM_def
  have hMg : M * g = N := Nat.div_mul_cancel hgN
  have hM_pos : 0 < M := Nat.div_pos (Nat.le_of_dvd (by omega) hgN) hg
  haveI : NeZero M := ⟨by omega⟩
  set f := cosetCardFin A g hg hgN with hf_def
  set m : ℝ := ↑A.card / ↑g with hm_def
  have hg_pos_real : (0 : ℝ) < ↑g := Nat.cast_pos.mpr hg
  have hg_ne : (↑g : ℝ) ≠ 0 := ne_of_gt hg_pos_real
  -- Mean bound: m ≥ δM
  have hm_ge : m ≥ delta * ↑M := by
    rw [hm_def, ge_iff_le, le_div_iff₀ hg_pos_real]
    calc delta * ↑M * ↑g = delta * (↑M * ↑g) := by ring
      _ = delta * ↑N := by rw [show (↑M : ℝ) * ↑g = ↑N from by exact_mod_cast hMg]
      _ ≤ ↑A.card := hdensity
  -- Pigeonhole: ∃ j, f_j ≥ m + δ²N/(4g)
  -- Uses: Fourier decomp + char sum zero + triangle ineq + deviation analysis
  have hpart := coset_partition_sum A g hg hgN
  obtain ⟨j_star, _, hj_max⟩ : ∃ j : Fin g, j ∈ Finset.univ ∧
      ↑(f j) - m ≥ delta ^ 2 * ↑N / (4 * ↑g) := by
    -- By contradiction: suppose no coset has large enough deviation
    by_contra hno; push_neg at hno
    set c := delta ^ 2 * ↑N / (4 * ↑g) with hc_def
    have hc_pos : 0 < c := by positivity
    have hdev : ∀ j : Fin g, (↑(f j) : ℝ) - m < c := fun j => hno j (Finset.mem_univ _)
    -- Zero-sum: ∑ (f_j - m) = 0
    have hzs : ∑ j : Fin g, ((↑(f j) : ℝ) - m) = 0 := by
      have h1 := hpart
      have h2 : ↑g * m = ↑A.card := by rw [hm_def]; field_simp
      have h3 : ∑ _ : Fin g, m = ↑g * m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp_rw [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      linarith
    -- Fourier analysis: Â(r) = ∑ (f_j - m) * ψ(r*j)
    have hFD := fourier_coset_decomp A g hg hgN r hcompat
    have hCS := char_sum_cosets_zero g hg hgN r hr hcompat
    have hFourier_eq : fourierCoeff A r =
        ∑ j : Fin g, ((↑(f j) : ℂ) - ↑m) * ψ (r * (↑j.val : ZMod N)) := by
      rw [hFD]; simp only [← hf_def]
      simp_rw [show ∀ j : Fin g, (↑(f j) : ℂ) * ψ (r * ↑j.val) =
        ((↑(f j) : ℂ) - ↑m + ↑m) * ψ (r * ↑j.val) from fun j => by ring]
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [show ∑ j : Fin g, (↑m : ℂ) * ψ (r * ↑j.val) =
          ↑m * ∑ j : Fin g, ψ (r * ↑j.val) from (Finset.mul_sum ..).symm,
        hCS, mul_zero, add_zero]
    -- |ψ(a)| = 1
    have hpsi_norm : ∀ a : ZMod N, ‖ψ a‖ = 1 := by
      intro a; simp only [ψ, Complex.norm_exp]
      rw [show (2 * ↑Real.pi * Complex.I * (↑(ZMod.val a) / ↑N)).re = 0 from by
        rw [show 2 * ↑Real.pi * Complex.I * (↑(ZMod.val a) / ↑N) =
            ↑(2 * Real.pi * (↑(ZMod.val a) / ↑N)) * Complex.I from by push_cast; ring,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]; ring, Real.exp_zero]
    -- Lower bound: ∑ |f_j - m| ≥ δ²N/2 (triangle inequality)
    have habs_lb : delta ^ 2 * ↑N / 2 ≤ ∑ j : Fin g, |(↑(f j) : ℝ) - m| := by
      calc delta ^ 2 * ↑N / 2
          ≤ ‖fourierCoeff A r‖ := hlarge
        _ ≤ ∑ j : Fin g, ‖((↑(f j) : ℂ) - ↑m) * ψ (r * ↑j.val)‖ := by
            rw [hFourier_eq]; exact norm_sum_le _ _
        _ = ∑ j : Fin g, |(↑(f j) : ℝ) - m| := by
            congr 1; ext j
            rw [Complex.norm_mul, hpsi_norm, mul_one]
            rw [show (↑(f j) : ℂ) - (↑m : ℂ) = (↑((↑(f j) : ℝ) - m) : ℂ) from by push_cast; ring]
            exact Complex.norm_real _
    -- Upper bound from by_contra + zero-sum: ∑ |f_j - m| < δ²N/2
    -- Key identity: |a| = max(a, 0) + max(-a, 0) and a = max(a,0) - max(-a,0)
    -- Combined with zero-sum: ∑ |f-m| = 2 * ∑ max(f-m, 0)
    set a := fun j : Fin g => (↑(f j) : ℝ) - m
    -- Each max(a j, 0) < c
    have hmax_bound : ∀ j : Fin g, max (a j) 0 < c := by
      intro j; exact max_lt (hdev j) hc_pos
    -- ∑ max(a, 0) < gc by pigeonhole
    have hsum_max : ∑ j : Fin g, max (a j) 0 < ↑g * c := by
      calc ∑ j, max (a j) 0
          < ∑ _ : Fin g, c := Finset.sum_lt_sum
            (fun j _ => le_of_lt (hmax_bound j))
            ⟨⟨0, hg⟩, Finset.mem_univ _, hmax_bound ⟨0, hg⟩⟩
        _ = ↑g * c := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- ∑ |a| = 2 * ∑ max(a, 0) from zero-sum
    have habs_eq_twice : ∑ j : Fin g, |a j| = 2 * ∑ j : Fin g, max (a j) 0 := by
      -- Key identities for reals
      have habs_decomp : ∀ x : ℝ, |x| = max x 0 + max (-x) 0 := by
        intro x; rcases le_or_gt 0 x with h | h
        · simp [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
        · rw [abs_of_neg h]; simp [max_eq_right (le_of_lt h),
            max_eq_left (neg_nonneg.mpr (le_of_lt h))]
      have ha_decomp : ∀ x : ℝ, x = max x 0 - max (-x) 0 := by
        intro x; rcases le_or_gt 0 x with h | h
        · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
        · simp [max_eq_right (le_of_lt h), max_eq_left (neg_nonneg.mpr (le_of_lt h))]
      -- ∑ |a| = ∑ max(a,0) + ∑ max(-a,0)
      simp_rw [habs_decomp, Finset.sum_add_distrib]
      -- From zero-sum: ∑ max(a,0) = ∑ max(-a,0)
      have hmax_eq : ∑ j : Fin g, max (a j) 0 = ∑ j, max (-(a j)) 0 := by
        have h1 : ∑ j : Fin g, a j = ∑ j, (max (a j) 0 - max (-(a j)) 0) :=
          Finset.sum_congr rfl (fun j _ => ha_decomp (a j))
        have h2 : ∑ j : Fin g, (max (a j) 0 - max (-(a j)) 0) =
            ∑ j, max (a j) 0 - ∑ j, max (-(a j)) 0 := by
          simp_rw [sub_eq_add_neg]; rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
        linarith
      linarith
    -- Combine: ∑ |f-m| < 2gc = δ²N/2
    have hgc_eq : ↑g * c = delta ^ 2 * ↑N / 4 := by rw [hc_def]; field_simp
    linarith
  refine ⟨j_star.val, j_star.isLt, ?_⟩
  have hj_bound : ↑(f j_star) ≥ m + delta ^ 2 * ↑N / (4 * ↑g) := by linarith
  show (↑(cosetRestrict A g hg hgN j_star.val j_star.isLt).card : ℝ) ≥
    (delta + delta ^ 2 / 4) * (↑N / ↑g)
  change ↑(f j_star) ≥ (delta + delta ^ 2 / 4) * (↑N / ↑g)
  -- Multiply through by g to clear denominators
  suffices h : ↑(f j_star) * ↑g ≥ (delta + delta ^ 2 / 4) * ↑N by
    rw [ge_iff_le, ← sub_nonneg]
    have : ↑(f j_star) - (delta + delta ^ 2 / 4) * (↑N / ↑g) =
      (↑(f j_star) * ↑g - (delta + delta ^ 2 / 4) * ↑N) / ↑g := by field_simp
    rw [this]; exact div_nonneg (by linarith) (le_of_lt hg_pos_real)
  have h1 : ↑(f j_star) * ↑g ≥ (m + delta ^ 2 * ↑N / (4 * ↑g)) * ↑g :=
    mul_le_mul_of_nonneg_right hj_bound (le_of_lt hg_pos_real)
  have hm_mul : m * ↑g = ↑A.card := by rw [hm_def]; exact div_mul_cancel₀ _ hg_ne
  have h2 : (m + delta ^ 2 * ↑N / (4 * ↑g)) * ↑g = ↑A.card + delta ^ 2 * ↑N / 4 := by
    field_simp; nlinarith
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART V-B: DENSITY INCREMENT LEMMA
-- ═══════════════════════════════════════════════════════════════════

/-- The density increment lemma: if A ⊆ Z/NZ (with N ≥ 2) has density delta
    and no 3-AP, then A has density at least delta + c·delta² on some arithmetic
    subprogression in Z/MZ with 0 < M < N, and the restriction is AP-free.

    The strict descent M < N is crucial for the main theorem: it ensures
    the iteration terminates after at most N steps, giving room for the
    density to exceed 1 and yield a contradiction.

    Proof: By fourier_large_coefficient, ∃ r ≠ 0 with |Â(r)| ≥ δ²N/2.
    Take g = N/gcd(val(r), N) as compatible coset step for χ_r.
    Then M = gcd(val(r), N) < N since val(r) ∈ {1,...,N-1}.
    Apply coset_density_increment + apFree_coset_restrict. -/
theorem density_increment_lemma {N : ℕ} (hN : 1 < N) (A : Finset (ZMod N))
    (hAP : APFree A) (delta : ℝ) (hdelta : 0 < delta)
    (hdensity : (A.card : ℝ) ≥ delta * N) :
    ∃ (M : ℕ) (B : Finset (ZMod M)),
      0 < M ∧ M < N ∧
      APFree B ∧
      (B.card : ℝ) ≥ (delta + delta ^ 2 / 100) * M := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨r, hr, hfourier⟩ := fourier_large_coefficient hN A hAP delta hdelta hdensity
  set d := Nat.gcd (ZMod.val r) N
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right (NeZero.ne N))
  have hdN : d ∣ N := Nat.gcd_dvd_right _ _
  have hd_dvd_r : d ∣ ZMod.val r := Nat.gcd_dvd_left _ _
  -- d = gcd(val(r), N) < N because val(r) ∈ {1,...,N-1}
  have hval_pos : 0 < ZMod.val r := by
    rw [Nat.pos_iff_ne_zero]; intro h
    exact hr (by rwa [ZMod.val_eq_zero] at h)
  have hd_lt_N : d < N :=
    lt_of_le_of_lt (Nat.gcd_le_left N hval_pos) (ZMod.val_lt r)
  set g := N / d
  have hg_pos : 0 < g := Nat.div_pos (Nat.le_of_dvd (by omega) hdN) hd_pos
  -- g ≥ 2 since d | N and d < N (so g = N/d ≥ 2)
  have hg_ge_two : 2 ≤ g := by
    by_contra h; push_neg at h
    -- g ≤ 1 and g > 0 → g = 1
    have hg1 : g = 1 := by omega
    -- N/d * d = N, and N/d = g = 1, so d = N, contradicting d < N
    have hgd : N / d * d = N := Nat.div_mul_cancel hdN
    rw [show N / d = g from rfl, hg1, one_mul] at hgd
    omega
  have hgN : g ∣ N := Nat.div_dvd_of_dvd hdN
  have hNg_eq : N / g = d := Nat.div_div_self hdN (by omega)
  have hcompat : (N / g) ∣ ZMod.val r := hNg_eq ▸ hd_dvd_r
  obtain ⟨j, hj, hdense⟩ := coset_density_increment hN A hAP delta hdelta hdensity
    g hg_pos hgN r hr hfourier hcompat
  have hM_pos : 0 < N / g := Nat.div_pos (Nat.le_of_dvd (by omega) hgN) hg_pos
  -- M = N/g = d < N
  have hM_lt_N : N / g < N := hNg_eq ▸ hd_lt_N
  have hMreal : (↑(N / g) : ℝ) = ↑N / ↑g :=
    Nat.cast_div hgN (Nat.cast_ne_zero.mpr (by omega))
  refine ⟨N / g, cosetRestrict A g hg_pos hgN j hj, hM_pos, hM_lt_N,
    apFree_coset_restrict A hAP g hg_pos hgN j hj, ?_⟩
  rw [hMreal]
  calc (↑(cosetRestrict A g hg_pos hgN j hj).card : ℝ)
      ≥ (delta + delta ^ 2 / 4) * (↑N / ↑g) := hdense
    _ ≥ (delta + delta ^ 2 / 100) * (↑N / ↑g) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg delta]

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: ROTH'S THEOREM (MAIN RESULT)
-- ═══════════════════════════════════════════════════════════════════

/-- APFree in ZMod N implies ThreeAPFree when mapped to ℕ via ZMod.val.

    A 3-AP {a, b, c} in ℕ (with a + c = 2b) lifts to a 3-AP in ZMod N
    since val(x) + val(z) = 2·val(y) in ℕ implies x + z = 2y in ZMod N
    (both sides are < 2N, so the natural equation implies the modular one). -/
private theorem apFree_imp_threeAPFree_val {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (hAP : APFree A) : ThreeAPFree (Finset.image ZMod.val A : Set ℕ) := by
  intro a ha b hb c hc habc
  -- a, b, c ∈ A.image ZMod.val, so a = val(x), b = val(y), c = val(z) for x, y, z ∈ A
  rw [Finset.coe_image] at ha hb hc
  obtain ⟨x, hxA, rfl⟩ := ha
  obtain ⟨y, hyA, rfl⟩ := hb
  obtain ⟨z, hzA, rfl⟩ := hc
  -- habc : val(x) + val(z) = val(y) + val(y) in ℕ
  -- This implies x + z = 2y in ZMod N (cast both sides)
  by_contra hne
  have hxy : x ≠ y := by
    intro h; exact hne (congr_arg ZMod.val h)
  have hd : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  -- Cast habc to ZMod N: ↑(val x + val z) = ↑(val y + val y)
  have hmod : x + z = y + y := by
    have h1 : (↑(ZMod.val x + ZMod.val z) : ZMod N) = (↑(ZMod.val y + ZMod.val y) : ZMod N) :=
      congr_arg Nat.cast habc
    simp only [Nat.cast_add, ZMod.natCast_zmod_val] at h1
    exact h1
  -- z = x + 2(y - x) in ZMod N
  have hz_eq : z = x + 2 * (y - x) := by linear_combination hmod
  have hy_eq : y = x + (y - x) := by ring
  exact hAP x (y - x) hd hxA (hy_eq ▸ hyA) (hz_eq ▸ hzA)

/-- **Roth's Theorem**: r₃(N) = o(N).
    For every delta > 0, there exists N₀ such that for all N ≥ N₀, every
    subset A ⊆ Z/NZ with |A| ≥ delta * N contains a 3-term arithmetic
    progression.

    This proof uses Mathlib's Roth theorem (via the corners theorem chain:
    Regularity Lemma → Triangle Removal → Corners → Roth) applied to the
    image of A under ZMod.val : ZMod N → ℕ. The custom Fourier-analytic
    density increment machinery (Parts I-V) provides the coset-based
    density increment lemma as an independently verified result. -/
theorem roth_density_bound (delta : ℝ) (hdelta : 0 < delta) (_hdelta1 : delta ≤ 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ A : Finset (ZMod N),
      (A.card : ℝ) ≥ delta * N → ¬APFree A := by
  -- Use Mathlib's Roth theorem via corners theorem chain
  use cornersTheoremBound (delta / 3) + 1
  intro N hN A hdensity hAP
  haveI : NeZero N := ⟨by
    intro h; subst h; simp at hdensity; linarith⟩
  -- Map A to ℕ via ZMod.val
  set S := Finset.image ZMod.val A with hS_def
  -- S ⊆ Finset.range N
  have hS_sub : S ⊆ Finset.range N := by
    intro x hx
    rw [hS_def, Finset.mem_image] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  -- |S| = |A| (ZMod.val is injective)
  have hS_card : S.card = A.card := by
    rw [hS_def]
    exact Finset.card_image_of_injective A (ZMod.val_injective N)
  -- |S| ≥ delta * N
  have hS_dens : (S.card : ℝ) ≥ delta * ↑N := by
    rw [hS_card]; exact hdensity
  -- ThreeAPFree S (from APFree A)
  have hS_free : ThreeAPFree (S : Set ℕ) := apFree_imp_threeAPFree_val A hAP
  -- Apply Mathlib's roth_3ap_theorem_nat
  have hN_bound : cornersTheoremBound (delta / 3) ≤ N := by omega
  exact roth_3ap_theorem_nat delta hdelta hN_bound S hS_sub hS_dens hS_free

end Szemeredi.Roth
