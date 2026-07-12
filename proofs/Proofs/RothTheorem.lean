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

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: SÁRKÖZY SQUARE-DIFFERENCE FOURIER IDENTITY
-- ═══════════════════════════════════════════════════════════════════

/-- The quadratic Gauss sum `G(r) = Σ_{n ∈ ℤ/Nℤ} ψ(r·n²)`. -/
noncomputable def sqGaussSum {N : ℕ} [NeZero N] (r : ZMod N) : ℂ :=
  Finset.univ.sum fun n : ZMod N => ψ (r * n ^ 2)

/-- The square-difference count `SD(A) = #{(x, n) : x ∈ A, x + n² ∈ A}`. -/
noncomputable def sqDiffCount {N : ℕ} [NeZero N] (A : Finset (ZMod N)) : ℕ :=
  ((A ×ˢ (Finset.univ : Finset (ZMod N))).filter
    (fun p : ZMod N × ZMod N => p.1 + p.2 ^ 2 ∈ A)).card

/-- Principal Gauss sum: `G(0) = N` (every term is ψ(0) = 1). -/
theorem sqGaussSum_zero {N : ℕ} [NeZero N] : sqGaussSum (0 : ZMod N) = ↑N := by
  simp only [sqGaussSum, zero_mul, psi_zero, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, mul_one]

/-- `SD(A)` as a double sum of indicators over `A × ℤ/Nℤ`. -/
private lemma sqDiffCount_eq_sum {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (sqDiffCount A : ℂ) =
      A.sum fun x => Finset.univ.sum fun n : ZMod N =>
        if x + n ^ 2 ∈ A then (1 : ℂ) else 0 := by
  unfold sqDiffCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  split_ifs <;> simp

/-- Each summand `‖Â(r)‖²·G(r) = Â(r)·conj(Â(r))·G(r)` expands as a triple ψ sum. -/
private lemma sq_term_expand {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (r : ZMod N) :
    fourierCoeff A r * starRingEnd ℂ (fourierCoeff A r) * sqGaussSum r =
    A.sum fun x => A.sum fun y => Finset.univ.sum fun n : ZMod N =>
      ψ (r * (x - y + n ^ 2)) := by
  simp only [fourierCoeff_eq_sum_psi, sqGaussSum, map_sum (starRingEnd ℂ), conj_psi]
  symm
  simp_rw [show ∀ (x y n : ZMod N), ψ (r * (x - y + n ^ 2)) =
      ψ (r * x) * (ψ (-(r * y)) * ψ (r * n ^ 2)) from
    fun x y n => by
      rw [show r * (x - y + n ^ 2) = r * x + (-(r * y) + r * n ^ 2) from by ring]
      rw [psi_add, psi_add]]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [← mul_assoc]

/-- **Sárközy square-difference Fourier identity (complex form).** -/
theorem sqDiffCount_fourier_complex {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (sqDiffCount A : ℂ) * N =
    Finset.univ.sum fun r : ZMod N =>
      fourierCoeff A r * starRingEnd ℂ (fourierCoeff A r) * sqGaussSum r := by
  -- Expand each Fourier term as a triple ψ sum
  simp_rw [sq_term_expand]
  -- Bring the r-sum innermost
  rw [Finset.sum_comm]
  conv_rhs => arg 2; ext; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext; arg 2; ext; rw [Finset.sum_comm]
  -- Character orthogonality collapses the r-sum
  simp_rw [char_orthogonality]
  -- Swap y and n so the y-sum (which the equation determines) is innermost
  conv_rhs => arg 2; ext; rw [Finset.sum_comm]
  simp_rw [show ∀ (x n y : ZMod N), (x - y + n ^ 2 = 0) ↔ (y = x + n ^ 2) from
    fun x n y => ⟨fun h => by linear_combination -h, fun h => by subst h; ring⟩]
  simp_rw [Finset.sum_ite_eq']
  -- Factor out N and match the combinatorial count
  simp_rw [show ∀ (P : Prop) [Decidable P],
      (if P then (↑N : ℂ) else 0) = ↑N * (if P then (1 : ℂ) else 0) from
      fun P _ => by split_ifs <;> simp]
  simp_rw [← Finset.mul_sum]
  rw [sqDiffCount_eq_sum]; ring

/-- **Sárközy square-difference Fourier identity.** -/
theorem sqDiffCount_fourier {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (sqDiffCount A : ℂ) = (↑N)⁻¹ *
      Finset.univ.sum (fun r : ZMod N =>
        (↑(‖fourierCoeff A r‖ ^ 2) : ℂ) * sqGaussSum r) := by
  have hN : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [eq_comm, inv_mul_eq_div, div_eq_iff hN, eq_comm, sqDiffCount_fourier_complex A]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Circle-method principal-term extraction for the square-difference count.**
Peeling the `r = 0` frequency off the verified `sqDiffCount_fourier` identity
isolates the expected main term `|A|²`:
    SD(A) = |A|² + N⁻¹ · Σ_{r ≠ 0} ‖Â(r)‖² · G(r).
The `r = 0` summand is `‖Â(0)‖²·G(0) = |A|²·N` (since `Â(0) = |A|` and the
quadratic Gauss sum `G(0) = N`), and the outer `N⁻¹` cancels that `N`, leaving
`|A|²` plus the nonzero-frequency error term.  This is the exact form the circle
method bounds (via `|G(r)| ≲ √N` and Parseval) to prove Sárközy's theorem, and
mirrors the merged 3-AP principal-term split. -/
theorem sqDiffCount_fourier_main {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (sqDiffCount A : ℂ) = (↑A.card) ^ 2 + (↑N)⁻¹ *
      (Finset.univ \ {(0 : ZMod N)}).sum (fun r : ZMod N =>
        (↑(‖fourierCoeff A r‖ ^ 2) : ℂ) * sqGaussSum r) := by
  have hN : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- Split the r = 0 frequency off the full sum.  The explicit summand argument to
  -- `sum_eq_add_sum_diff_singleton` is essential: leaving it to be inferred forces a
  -- higher-order unification against the whole Fourier sum that blows up elaboration.
  have hsplit := Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ (0 : ZMod N))
    (fun r : ZMod N => (↑(‖fourierCoeff A r‖ ^ 2) : ℂ) * sqGaussSum r)
  rw [sqDiffCount_fourier A, hsplit]
  -- Evaluate the r = 0 term: ‖Â(0)‖²·G(0) = |A|²·N.
  simp only [sqGaussSum_zero, fourierCoeff_zero', Complex.norm_natCast, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  field_simp

/-- **Circle-method error bound for the square-difference count.**  Given a
uniform bound `‖G(r)‖ ≤ M` on the quadratic Gauss sum over the nonzero
frequencies, the square-difference count `SD(A)` differs from its expected main
term `|A|²` by at most

    ‖SD(A) − |A|²‖  ≤  N⁻¹ · M · (|A|·N − |A|²).

This is the exact analytic reduction the circle method performs for Sárközy's
theorem: it isolates *all* the arithmetic content into the single Gauss-sum
magnitude bound `M`.  Combining `sqDiffCount_fourier_main` (the principal-term
split) with the triangle inequality and `parseval_nonzero`
(`Σ_{r≠0} ‖Â(r)‖² = |A|·N − |A|²`), the error is controlled with no further
input.  The hypothesis `hG` is precisely the classical estimate `|G(r)| ≤ √(2N)`
(so `M = √(2N)`), whose formalization for general composite `N` is the one
remaining ingredient; abstracting it as `M` keeps this reduction fully
machine-checked and 0-axiom. -/
theorem sqDiff_error_le {N : ℕ} [NeZero N] (A : Finset (ZMod N)) {M : ℝ}
    (hG : ∀ r : ZMod N, r ≠ 0 → ‖sqGaussSum r‖ ≤ M) :
    ‖(sqDiffCount A : ℂ) - (↑A.card) ^ 2‖
      ≤ (↑N)⁻¹ * (M * (↑A.card * ↑N - (↑A.card) ^ 2)) := by
  -- Isolate the error term as `N⁻¹ · Σ_{r≠0} ‖Â(r)‖²·G(r)`.
  have hsub : (sqDiffCount A : ℂ) - (↑A.card) ^ 2
      = (↑N)⁻¹ * (Finset.univ \ {(0 : ZMod N)}).sum
          (fun r => (↑(‖fourierCoeff A r‖ ^ 2) : ℂ) * sqGaussSum r) := by
    rw [sqDiffCount_fourier_main A]; ring
  rw [hsub, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- Triangle inequality + Gauss bound + Parseval on the nonzero frequencies.
  calc ‖(Finset.univ \ {(0 : ZMod N)}).sum
            (fun r => (↑(‖fourierCoeff A r‖ ^ 2) : ℂ) * sqGaussSum r)‖
      ≤ (Finset.univ \ {(0 : ZMod N)}).sum
            (fun r => ‖(↑(‖fourierCoeff A r‖ ^ 2) : ℂ) * sqGaussSum r‖) :=
        norm_sum_le _ _
    _ = (Finset.univ \ {(0 : ZMod N)}).sum
            (fun r => ‖fourierCoeff A r‖ ^ 2 * ‖sqGaussSum r‖) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ (Finset.univ \ {(0 : ZMod N)}).sum
            (fun r => ‖fourierCoeff A r‖ ^ 2 * M) := by
        refine Finset.sum_le_sum (fun r hr => ?_)
        have hrne : r ≠ 0 := by
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hr; exact hr.2
        exact mul_le_mul_of_nonneg_left (hG r hrne) (by positivity)
    _ = (Finset.univ \ {(0 : ZMod N)}).sum
            (fun r => ‖fourierCoeff A r‖ ^ 2) * M := by
        rw [← Finset.sum_mul]
    _ = M * (↑A.card * ↑N - (↑A.card) ^ 2) := by
        rw [parseval_nonzero A]; ring

/-- **Circle-method lower bound for the square-difference count (real form).**
The two-sided bound `sqDiff_error_le` immediately gives a one-sided *lower* bound
on the (nonnegative real) count `SD(A)`:

    SD(A)  ≥  |A|² − N⁻¹ · M · (|A|·N − |A|²).

This is the operative direction for Sárközy's theorem: it guarantees that the
square-difference count stays close to its `|A|²` main term, so a dense set is
*forced* to contain many square differences.  Both `SD(A)` and `|A|²` are real,
so the complex norm in `sqDiff_error_le` is just the absolute value, and the
lower half of `|x| ≤ c` supplies the bound. -/
theorem sqDiffCount_ge {N : ℕ} [NeZero N] (A : Finset (ZMod N)) {M : ℝ}
    (hG : ∀ r : ZMod N, r ≠ 0 → ‖sqGaussSum r‖ ≤ M) :
    (A.card : ℝ) ^ 2 - (↑N)⁻¹ * (M * (↑A.card * ↑N - (↑A.card) ^ 2))
      ≤ (sqDiffCount A : ℝ) := by
  have h := sqDiff_error_le A hG
  have key : |(sqDiffCount A : ℝ) - (A.card : ℝ) ^ 2|
      ≤ (↑N)⁻¹ * (M * (↑A.card * ↑N - (↑A.card) ^ 2)) := by
    have e : ‖(sqDiffCount A : ℂ) - (↑A.card) ^ 2‖
        = |(sqDiffCount A : ℝ) - (A.card : ℝ) ^ 2| := by
      rw [show (sqDiffCount A : ℂ) - (↑A.card) ^ 2
            = (((sqDiffCount A : ℝ) - (A.card : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rwa [e] at h
  linarith [(abs_le.mp key).1]

/-- **Square-difference-free sets have few solutions.**  If `A` contains no
*nontrivial* square difference — no `x ∈ A` and `n` with `n² ≠ 0` and
`x + n² ∈ A` — then every `(x, n)` counted by `SD(A)` must have `n² = 0`, so

    SD(A)  ≤  |A| · #{n : n² = 0}.

The only pairs surviving the `SD(A)` filter are the trivial ones `(x, n)` with
`n² = 0` (for which `x + n² = x ∈ A` automatically); the freeness hypothesis
kills every pair with `n² ≠ 0`.  The `#{n : n² = 0}` factor is `1` when `N` is
squarefree (only `n = 0`) and larger otherwise. -/
theorem sqDiffCount_le_of_free {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    sqDiffCount A ≤ A.card * (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card := by
  unfold sqDiffCount
  calc ((A ×ˢ (Finset.univ : Finset (ZMod N))).filter
          (fun p : ZMod N × ZMod N => p.1 + p.2 ^ 2 ∈ A)).card
      ≤ (A ×ˢ (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0))).card := by
        refine Finset.card_le_card (fun p hp => ?_)
        rw [Finset.mem_filter, Finset.mem_product] at hp
        obtain ⟨⟨hx, _⟩, hin⟩ := hp
        rw [Finset.mem_product, Finset.mem_filter]
        refine ⟨hx, Finset.mem_univ _, ?_⟩
        by_contra hne
        exact hfree p.1 hx p.2 hne hin
    _ = A.card * (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card :=
        Finset.card_product _ _

/-- **Sárközy density inequality (conditional on the Gauss-sum bound `M`).**
Combining the circle-method lower bound `sqDiffCount_ge` with the
square-difference-free upper bound `sqDiffCount_le_of_free` pins the size of any
square-difference-free `A ⊆ ℤ/Nℤ`:

    |A|²  ≤  |A| · #{n : n² = 0}  +  N⁻¹ · M · (|A|·N − |A|²).

This is the finite Sárközy statement in fully abstracted form.  With the
classical quadratic Gauss-sum bound `M = √(2N)` and `N` squarefree
(`#{n : n² = 0} = 1`), the right side is `|A| + √(2N)·|A|·(N − |A|)/N ≲ |A|·√N`,
forcing `|A| ≲ √N`, i.e. density `|A|/N → 0` — Sárközy's theorem.  Every step is
0-axiom; the single remaining analytic input is the magnitude bound `M`. -/
theorem sqDiffFree_density_bound {N : ℕ} [NeZero N] (A : Finset (ZMod N)) {M : ℝ}
    (hG : ∀ r : ZMod N, r ≠ 0 → ‖sqGaussSum r‖ ≤ M)
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) ^ 2
      ≤ (A.card : ℝ) * (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card
        + (↑N)⁻¹ * (M * (↑A.card * ↑N - (↑A.card) ^ 2)) := by
  have hlow := sqDiffCount_ge A hG
  have hupp : (sqDiffCount A : ℝ)
      ≤ (A.card : ℝ) * (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card := by
    exact_mod_cast sqDiffCount_le_of_free A hfree
  linarith

/-!
## Part VII: Weyl-differencing magnitude of the quadratic Gauss sum

The abstract circle-method reduction (`sqDiffFree_density_bound`) leaves a single
analytic input: a magnitude bound `‖G(r)‖ ≤ M` on the quadratic Gauss sum
`G(r) = Σ_n ψ(r·n²)` for nonzero frequencies `r`.  The classical route to that
bound is **Weyl differencing**: squaring `G(r)` and reindexing `m = n + h` turns
the double character sum into a *linear* one in `n`, which `char_orthogonality`
collapses.  The result is the exact squared-magnitude identity

    ‖G(r)‖² = N · Σ_{h : 2rh = 0} ψ(−r·h²),

reducing the magnitude of a genuinely *quadratic* exponential sum to a sum over
the (small) kernel `{h : 2rh = 0}`.  Two consequences follow immediately:

  * `sqGaussSum_normSq_le` — the bound `‖G(r)‖² ≤ N · #{h : 2rh = 0}` (triangle
    inequality, each `‖ψ‖ = 1`), pinning the sole remaining quantity in the
    Sárközy density bound to the *cardinality of the kernel*;
  * `sqGaussSum_normSq_eq_of_kernel_trivial` — the exact evaluation
    `‖G(r)‖² = N` (so `‖G(r)‖ = √N`) whenever the kernel is trivial (e.g. `N`
    odd and `2r` a unit) — the classical quadratic Gauss-sum magnitude in the
    accessible regime.

All 0-axiom.  This is the concrete first step of the one remaining input: it
identifies the kernel count `#{h : 2rh = 0}` (a `gcd(2r, N)` quantity) as exactly
what controls `‖G(r)‖`, replacing the black-box `√(2N)` with a structured estimate.
-/

/-- **Weyl-differencing squared-magnitude identity.**  Squaring the quadratic
    Gauss sum and reindexing `m = n + h` linearises the phase in `n`:

    `G(r) · conj(G(r)) = N · Σ_{h : 2rh = 0} ψ(−r·h²)`.

    The inner `n`-sum `Σ_n ψ((−2rh)·n)` is a *linear* character sum, collapsed by
    `char_orthogonality` to `N·[2rh = 0]`; only the diagonal frequencies `2rh = 0`
    survive, each weighted by the residual quadratic phase `ψ(−r·h²)`. -/
theorem sqGaussSum_mul_conj {N : ℕ} [NeZero N] (r : ZMod N) :
    sqGaussSum r * starRingEnd ℂ (sqGaussSum r)
      = (N : ℂ) * (Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0)).sum
          (fun h => ψ (-(r * h ^ 2))) := by
  -- Expand `G · conj G` as a product of ψ-sums and merge each pair into one ψ.
  simp only [sqGaussSum, map_sum (starRingEnd ℂ), conj_psi]
  rw [Finset.sum_mul_sum]
  simp_rw [← psi_add]
  -- Reindex the inner `m`-sum by `m = n + h` (a bijection of `ZMod N`).
  rw [show (Finset.univ.sum (fun n : ZMod N =>
        Finset.univ.sum (fun m : ZMod N => ψ (r * n ^ 2 + -(r * m ^ 2)))))
      = (Finset.univ.sum (fun n : ZMod N =>
        Finset.univ.sum (fun h : ZMod N => ψ (r * n ^ 2 + -(r * (n + h) ^ 2))))) from by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    exact (Finset.sum_equiv (Equiv.addLeft n) (fun h => by simp) (fun h _ => rfl)).symm]
  -- The merged phase `r(n² − (n+h)²)` is linear in `n`: `(−2rh)·n − r·h²`.
  simp_rw [show ∀ n h : ZMod N, ψ (r * n ^ 2 + -(r * (n + h) ^ 2))
        = ψ (n * (-(2 * r * h))) * ψ (-(r * h ^ 2)) from
    fun n h => by
      rw [show r * n ^ 2 + -(r * (n + h) ^ 2) = n * (-(2 * r * h)) + (-(r * h ^ 2)) from by ring,
        psi_add]]
  -- Bring the `n`-sum innermost and factor the `n`-independent phase out.
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  -- Character orthogonality: `Σ_n ψ((−2rh)·n) = N·[2rh = 0]`.
  simp_rw [char_orthogonality, neg_eq_zero]
  -- Collapse the resulting `if` to a sum over the kernel and factor out `N`.
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]

/-- **Magnitude bound via the kernel count.**  From the Weyl identity, the triangle
    inequality and `‖ψ‖ = 1` give `‖G(r)‖² ≤ N · #{h : 2rh = 0}`.  The sole quantity
    controlling the quadratic Gauss sum is thus the size of the kernel `{h : 2rh = 0}`
    — a `gcd(2r, N)` count — a structured replacement for the black-box `√(2N)`. -/
theorem sqGaussSum_normSq_le {N : ℕ} [NeZero N] (r : ZMod N) :
    ‖sqGaussSum r‖ ^ 2
      ≤ (N : ℝ) * ((Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0)).card : ℝ) := by
  have hGsq : (↑(‖sqGaussSum r‖ ^ 2) : ℂ)
      = (N : ℂ) * (Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0)).sum
          (fun h => ψ (-(r * h ^ 2))) := by
    rw [← sqGaussSum_mul_conj r, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hnn : (0 : ℝ) ≤ ‖sqGaussSum r‖ ^ 2 := sq_nonneg _
  have hnorm : ‖sqGaussSum r‖ ^ 2
      = ‖(N : ℂ) * (Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0)).sum
          (fun h => ψ (-(r * h ^ 2)))‖ := by
    have h := congrArg norm hGsq
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn] at h
  rw [hnorm, norm_mul, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  calc ‖(Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0)).sum
            (fun h => ψ (-(r * h ^ 2)))‖
      ≤ (Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0)).sum
          (fun h => ‖ψ (-(r * h ^ 2))‖) := norm_sum_le _ _
    _ = (Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0)).sum (fun _ => (1 : ℝ)) :=
        Finset.sum_congr rfl (fun h _ => psi_norm _)
    _ = ((Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Exact magnitude in the accessible regime.**  When the kernel `{h : 2rh = 0}`
    is trivial — e.g. `N` odd and `2r` a unit — only `h = 0` survives in the Weyl
    identity, giving the classical exact evaluation `‖G(r)‖² = N`, i.e. `‖G(r)‖ = √N`.
    This is the quadratic Gauss-sum magnitude that, supplied as `M = √N` into
    `sqDiffFree_density_bound`, yields Sárközy's density bound outright. -/
theorem sqGaussSum_normSq_eq_of_kernel_trivial {N : ℕ} [NeZero N] (r : ZMod N)
    (hker : ∀ h : ZMod N, 2 * r * h = 0 → h = 0) :
    ‖sqGaussSum r‖ ^ 2 = (N : ℝ) := by
  have hfilter : (Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0)) = {0} := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hker h, fun hh => by rw [hh]; ring⟩
  have hid := sqGaussSum_mul_conj r
  rw [hfilter, Finset.sum_singleton,
    show (-(r * (0 : ZMod N) ^ 2)) = 0 from by ring, psi_zero, mul_one] at hid
  have hGsq : (↑(‖sqGaussSum r‖ ^ 2) : ℂ) = sqGaussSum r * starRingEnd ℂ (sqGaussSum r) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hid] at hGsq
  exact_mod_cast hGsq

/-- **Unit frequencies have trivial kernel.**  If `2r` is a unit in `ZMod N`, then the only
    solution of `2r·h = 0` is `h = 0`: left-multiply by `(2r)⁻¹`.  This is the checkable
    hypothesis feeding `sqGaussSum_normSq_eq_of_kernel_trivial` — it replaces the abstract
    "kernel trivial" side condition with the concrete unit condition on the frequency `2r`. -/
theorem kernel_trivial_of_isUnit {N : ℕ} [NeZero N] {r : ZMod N} (hu : IsUnit (2 * r)) :
    ∀ h : ZMod N, 2 * r * h = 0 → h = 0 := by
  intro h hh
  obtain ⟨u, hu_eq⟩ := hu
  have hz : (↑(u⁻¹) : ZMod N) * (2 * r * h) = 0 := by rw [hh, mul_zero]
  rw [← hu_eq, ← mul_assoc, Units.inv_mul, one_mul] at hz
  exact hz

/-- **Exact Gauss-sum magnitude at unit frequencies.**  Whenever `2r` is a unit in `ZMod N`,
    the quadratic Gauss sum has `‖G(r)‖² = N` — the classical `√N` magnitude, now with an
    explicitly checkable hypothesis (no abstract kernel condition). -/
theorem sqGaussSum_normSq_eq_of_isUnit {N : ℕ} [NeZero N] {r : ZMod N} (hu : IsUnit (2 * r)) :
    ‖sqGaussSum r‖ ^ 2 = (N : ℝ) :=
  sqGaussSum_normSq_eq_of_kernel_trivial r (kernel_trivial_of_isUnit hu)

/-- **`‖G(r)‖ = √N` at unit frequencies.**  The square-root form of
    `sqGaussSum_normSq_eq_of_isUnit`: this is exactly the value `M = √N` that, supplied to
    `sqDiffFree_density_bound`, discharges its magnitude hypothesis on the unit frequencies. -/
theorem sqGaussSum_norm_eq_sqrt_of_isUnit {N : ℕ} [NeZero N] {r : ZMod N} (hu : IsUnit (2 * r)) :
    ‖sqGaussSum r‖ = Real.sqrt N := by
  have h := sqGaussSum_normSq_eq_of_isUnit hu
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- **Odd-modulus regime.**  For `N` odd and any unit frequency `r`, `2r` is a unit (since `2`
    is a unit mod an odd `N`), so `‖G(r)‖ = √N`.  This is the clean accessible case: on the
    units of `ZMod N` (`N` odd) every quadratic Gauss sum has magnitude exactly `√N`. -/
theorem sqGaussSum_norm_eq_sqrt_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) {r : ZMod N}
    (hr : IsUnit r) : ‖sqGaussSum r‖ = Real.sqrt N := by
  have h2 : IsUnit (2 : ZMod N) := by
    have hcast : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_cast
    rw [← hcast, ZMod.isUnit_iff_coprime]
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hodd
    have hnd : ¬ (2 ∣ N) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
  exact sqGaussSum_norm_eq_sqrt_of_isUnit (h2.mul hr)

/-- **Odd-prime regime.**  When `N` is an odd prime, `ZMod N` is a field, so *every*
    nonzero frequency `r` is a unit; combined with the oddness of `N` (which makes `2`
    a unit) this gives the exact Gauss-sum magnitude `‖G(r)‖ = √N` at all `r ≠ 0`.
    This is the fully checkable, hypothesis-free-per-frequency form: no unit condition on
    `r` is imposed — nonzero suffices, because a prime modulus turns `ZMod N` into a field. -/
theorem sqGaussSum_norm_eq_sqrt_of_prime {N : ℕ} [NeZero N] (hp : N.Prime) (hN2 : N ≠ 2)
    {r : ZMod N} (hr : r ≠ 0) : ‖sqGaussSum r‖ = Real.sqrt N := by
  haveI := Fact.mk hp
  exact sqGaussSum_norm_eq_sqrt_of_odd (hp.odd_of_ne_two hN2) (isUnit_iff_ne_zero.mpr hr)

/-- **Sárközy square-difference density bound for odd-prime moduli (unconditional).**

    The capstone of Part VII in the prime case: for `N` an odd prime and any
    square-difference-free set `A ⊆ ZMod N` (no `x, x + n²` both in `A` with `n² ≠ 0`),

      `|A|² ≤ |A|·#{n : n² = 0} + N⁻¹·(√N·(|A|·N − |A|²))`.

    Every nonzero frequency in a prime field is a unit, so the Weyl-differencing magnitude
    `sqGaussSum_norm_eq_sqrt_of_prime` supplies the *uniform* bound `‖G(r)‖ = √N` for all
    `r ≠ 0`, discharging the sole analytic hypothesis of the abstract circle-method
    reduction `sqDiffFree_density_bound` with `M = √N`.  No kernel-count / `gcd` estimate is
    needed — that is only required for composite `N`, where distinct frequencies can have
    nontrivial kernel `{h : 2rh = 0}`.  0 axioms. -/
theorem sqDiffFree_density_bound_of_prime {N : ℕ} [NeZero N] (hp : N.Prime) (hN2 : N ≠ 2)
    (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) ^ 2
      ≤ (A.card : ℝ) * (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card
        + (↑N)⁻¹ * (Real.sqrt N * (↑A.card * ↑N - (↑A.card) ^ 2)) :=
  sqDiffFree_density_bound A
    (fun _ hr => le_of_eq (sqGaussSum_norm_eq_sqrt_of_prime hp hN2 hr)) hfree

/-! ### Composite modulus: the Weyl kernel count is a gcd

For a prime modulus every nonzero frequency is a unit, so `sqDiffFree_density_bound_of_prime`
closes the Sárközy density estimate with `M = √N`. For a *composite* `N` a nonzero
frequency `r` can fail to be a unit, and then the Weyl-differencing kernel
`{h : 2rh = 0}` — the sole remaining input to `sqGaussSum_normSq_le` — is nontrivial.
This subsection evaluates that kernel exactly: the number of solutions of a linear
equation `c·h = 0` in `ZMod N` is `gcd(c.val, N)`, which upgrades `sqGaussSum_normSq_le`
to the explicit magnitude bound `‖G(r)‖² ≤ N · gcd((2r).val, N)`. At unit frequencies
`gcd = 1`, recovering `‖G(r)‖² ≤ N` (with equality, `sqGaussSum_normSq_eq_of_isUnit`). -/

/-- **The kernel count of a linear equation in `ZMod N` is a gcd.** The number of
solutions `h ∈ ZMod N` of `c · h = 0` equals `gcd(c.val, N)`:

`#{h : ZMod N | c · h = 0} = gcd(c.val, N)`.

Multiplication-by-`c` is the additive endomorphism `AddMonoidHom.mulLeft c`; its range is
the cyclic subgroup `zmultiples c`, of order `addOrderOf c = N / gcd(c.val, N)`
(`ZMod.addOrderOf_coe`, `Nat.card_zmultiples`). Hence by rank–nullity for finite additive
groups (`AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup` composed with
`QuotientAddGroup.quotientKerEquivRange`), the kernel has order `N / (N / gcd) = gcd(c.val, N)`.
This is the finite-group kernel-cardinality input flagged for the composite-`N` regime. -/
theorem kernel_card_eq_gcd {N : ℕ} [NeZero N] (c : ZMod N) :
    (Finset.univ.filter (fun h : ZMod N => c * h = 0)).card = Nat.gcd c.val N := by
  classical
  set f : ZMod N →+ ZMod N := AddMonoidHom.mulLeft c with hf
  have hfapp : ∀ x, f x = c * x := fun x => rfl
  have hmem : ∀ h : ZMod N, h ∈ f.ker ↔ c * h = 0 := by
    intro h; rw [AddMonoidHom.mem_ker, hfapp]
  -- (1) the filter is the kernel, so its card is `Nat.card f.ker`
  have hcard_filter :
      (Finset.univ.filter (fun h : ZMod N => c * h = 0)).card = Nat.card f.ker := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    apply Finset.filter_congr
    intro x _
    exact (hmem x).symm
  -- (2) the range is the cyclic subgroup generated by `c`
  have hrange : f.range = AddSubgroup.zmultiples c := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      have hcx : f x = x.val • c := by
        rw [hfapp, nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id, mul_comm c x]
      rw [hcx]
      exact nsmul_mem (AddSubgroup.mem_zmultiples c) x.val
    · rw [AddSubgroup.zmultiples_le]
      exact ⟨1, by rw [hfapp, mul_one]⟩
  have hrange_card : Nat.card f.range = addOrderOf c := by
    rw [hrange, Nat.card_zmultiples]
  -- (3) the cyclic order is `N / gcd(c.val, N)`
  have hc : (↑(c.val) : ZMod N) = c := by rw [ZMod.natCast_val, ZMod.cast_id]
  have haddord : addOrderOf c = N / Nat.gcd c.val N := by
    conv_lhs => rw [← hc]
    rw [ZMod.addOrderOf_coe c.val (NeZero.ne N), Nat.gcd_comm N c.val]
  -- (4) rank–nullity `N = card(range) * card(ker)`, then divide
  have hrn : Nat.card (ZMod N) = Nat.card (ZMod N ⧸ f.ker) * Nat.card f.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have hquot : Nat.card (ZMod N ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  have hcardZ : Nat.card (ZMod N) = N := by rw [Nat.card_eq_fintype_card, ZMod.card]
  set g := Nat.gcd c.val N with hg
  have hgdvd : g ∣ N := Nat.gcd_dvd_right c.val N
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hkey : N = (N / g) * Nat.card f.ker := by
    have h := hrn
    rw [hcardZ, hquot, hrange_card, haddord] at h
    exact h
  have hdivpos : 0 < N / g :=
    Nat.div_pos (Nat.le_of_dvd hNpos hgdvd) (Nat.gcd_pos_of_pos_right c.val hNpos)
  have hcancel : (N / g) * Nat.card f.ker = (N / g) * g := by
    rw [← hkey, Nat.div_mul_cancel hgdvd]
  rw [hcard_filter, Nat.eq_of_mul_eq_mul_left hdivpos hcancel]

/-- **Explicit Weyl magnitude bound at a composite modulus.** Combining the kernel count
`kernel_card_eq_gcd` (at `c = 2r`) with the Weyl-differencing bound `sqGaussSum_normSq_le`,
the quadratic Gauss sum satisfies

`‖G(r)‖² ≤ N · gcd((2r).val, N)`.

This is the composite-`N` replacement for the black-box `√(2N)`: the magnitude is
controlled by the concrete arithmetic quantity `gcd(2r, N)`. At unit frequencies the gcd
is `1`, recovering `‖G(r)‖² ≤ N`; this is the uniform input `M = max_{r≠0} √(N·gcd(2r,N))`
needed to discharge `sqDiffFree_density_bound` for general (composite) `N`. -/
theorem sqGaussSum_normSq_le_gcd {N : ℕ} [NeZero N] (r : ZMod N) :
    ‖sqGaussSum r‖ ^ 2 ≤ (N : ℝ) * (Nat.gcd (2 * r).val N : ℝ) := by
  have h := sqGaussSum_normSq_le r
  rwa [kernel_card_eq_gcd (2 * r)] at h

/-- **`‖G(r)‖ ≤ √(N · gcd(2r, N))`.**  The square-root form of `sqGaussSum_normSq_le_gcd`,
    giving the pointwise magnitude of the quadratic Gauss sum directly as
    `√(N · gcd((2r).val, N))`.  At unit frequencies (`gcd = 1`) this is the familiar `√N`;
    the extra factor `√(gcd(2r, N))` measures exactly how the composite structure of `N`
    can inflate the sum at non-unit frequencies. -/
theorem sqGaussSum_norm_le_sqrt_gcd {N : ℕ} [NeZero N] (r : ZMod N) :
    ‖sqGaussSum r‖ ≤ Real.sqrt ((N : ℝ) * (Nat.gcd (2 * r).val N : ℝ)) := by
  have hmono := Real.sqrt_le_sqrt (sqGaussSum_normSq_le_gcd r)
  rwa [Real.sqrt_sq (norm_nonneg _)] at hmono

/-!
## Part XV: L²-averaged circle-method bound (Cauchy–Schwarz, composite `N`)

The pointwise density bound `sqDiffFree_density_bound` needs a *uniform*
Gauss-sum bound `M = max_{r≠0} ‖G(r)‖`.  For composite `N` this maximum is
genuinely large: `‖G(r)‖ = √(N·gcd(2r,N))` reaches `Θ(N)` at high-gcd
frequencies (e.g. the `2`-torsion), so the sup-form bound is too weak to give
`o(N)` density.

The circle-method error is really the sum `Σ_{r≠0} ‖Â(r)‖²·G(r)`, and only its
*root-mean-square* over the Gauss sum matters.  Cauchy–Schwarz replaces the
supremum `max ‖G(r)‖` with the second moment `√(Σ_{r≠0} ‖G(r)‖²)` — a genuine
average, far smaller than `(#freqs)·max²` when `‖G‖` is spread out (which it is:
`Σ_r ‖G(r)‖² = N·Σ_r gcd(2r,N)` concentrates).  This converts the last analytic
obstruction (evaluating a quadratic Gauss sum, which needs reciprocity not in
Mathlib) into the **elementary arithmetic estimate** `Σ_{r≠0} gcd((2r).val, N) =
o(N²)`.
-/

/-- **L²-averaged circle-method error bound (Cauchy–Schwarz form).**  Bounds the
square-difference count's deviation from its `|A|²` main term by the *root-mean-
square* of the Gauss sum rather than its supremum:

    ‖SD(A) − |A|²‖  ≤  N⁻¹ · |A| · √(|A|N − |A|²) · √(Σ_{r≠0} ‖G(r)‖²).

Proof: the error is `N⁻¹·Σ_{r≠0} ‖Â(r)‖²·G(r)` (`sqDiffCount_fourier_main`);
pull one factor `‖Â(r)‖ ≤ |A|` (`fourierCoeff_norm_le`) out of `‖Â(r)‖²`, then
Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`) on the residual
`Σ ‖Â(r)‖·‖G(r)‖` against Parseval (`Σ_{r≠0}‖Â(r)‖² = |A|N − |A|²`).  Strictly
sharper than `sqDiff_error_le` whenever the Gauss sum is spread out, which is the
composite-`N` regime. -/
theorem sqDiff_error_le_l2 {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    ‖(sqDiffCount A : ℂ) - (↑A.card) ^ 2‖
      ≤ (↑N)⁻¹ * (↑A.card * (Real.sqrt (↑A.card * ↑N - (↑A.card) ^ 2)
          * Real.sqrt ((Finset.univ \ {(0 : ZMod N)}).sum
              (fun r => ‖sqGaussSum r‖ ^ 2)))) := by
  have hsub : (sqDiffCount A : ℂ) - (↑A.card) ^ 2
      = (↑N)⁻¹ * (Finset.univ \ {(0 : ZMod N)}).sum
          (fun r => (↑(‖fourierCoeff A r‖ ^ 2) : ℂ) * sqGaussSum r) := by
    rw [sqDiffCount_fourier_main A]; ring
  rw [hsub, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set T := Finset.univ \ {(0 : ZMod N)} with hT
  -- Cauchy–Schwarz: `Σ ‖Â‖·‖G‖ ≤ √(Σ‖Â‖²)·√(Σ‖G‖²)`.
  have hCS : T.sum (fun r => ‖fourierCoeff A r‖ * ‖sqGaussSum r‖)
      ≤ Real.sqrt (T.sum (fun r => ‖fourierCoeff A r‖ ^ 2))
          * Real.sqrt (T.sum (fun r => ‖sqGaussSum r‖ ^ 2)) := by
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq T
      (fun r => ‖fourierCoeff A r‖) (fun r => ‖sqGaussSum r‖)
    have hnn : 0 ≤ T.sum (fun r => ‖fourierCoeff A r‖ * ‖sqGaussSum r‖) :=
      Finset.sum_nonneg (fun r _ => by positivity)
    calc T.sum (fun r => ‖fourierCoeff A r‖ * ‖sqGaussSum r‖)
        = Real.sqrt ((T.sum (fun r => ‖fourierCoeff A r‖ * ‖sqGaussSum r‖)) ^ 2) := by
          rw [Real.sqrt_sq hnn]
      _ ≤ Real.sqrt ((T.sum (fun r => ‖fourierCoeff A r‖ ^ 2))
              * (T.sum (fun r => ‖sqGaussSum r‖ ^ 2))) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (T.sum (fun r => ‖fourierCoeff A r‖ ^ 2))
              * Real.sqrt (T.sum (fun r => ‖sqGaussSum r‖ ^ 2)) :=
          Real.sqrt_mul (Finset.sum_nonneg (fun r _ => by positivity)) _
  calc ‖T.sum (fun r => (↑(‖fourierCoeff A r‖ ^ 2) : ℂ) * sqGaussSum r)‖
      ≤ T.sum (fun r => ‖(↑(‖fourierCoeff A r‖ ^ 2) : ℂ) * sqGaussSum r‖) := norm_sum_le _ _
    _ = T.sum (fun r => ‖fourierCoeff A r‖ ^ 2 * ‖sqGaussSum r‖) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ T.sum (fun r => (↑A.card : ℝ) * (‖fourierCoeff A r‖ * ‖sqGaussSum r‖)) := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        have hb := fourierCoeff_norm_le A r
        have hrw : ‖fourierCoeff A r‖ ^ 2 * ‖sqGaussSum r‖
            = ‖fourierCoeff A r‖ * (‖fourierCoeff A r‖ * ‖sqGaussSum r‖) := by ring
        rw [hrw]
        exact mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (↑A.card : ℝ) * T.sum (fun r => ‖fourierCoeff A r‖ * ‖sqGaussSum r‖) := by
        rw [← Finset.mul_sum]
    _ ≤ (↑A.card : ℝ) * (Real.sqrt (T.sum (fun r => ‖fourierCoeff A r‖ ^ 2))
            * Real.sqrt (T.sum (fun r => ‖sqGaussSum r‖ ^ 2))) := by
        exact mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = (↑A.card : ℝ) * (Real.sqrt (↑A.card * ↑N - (↑A.card) ^ 2)
            * Real.sqrt (T.sum (fun r => ‖sqGaussSum r‖ ^ 2))) := by
        rw [parseval_nonzero A]

/-- **Second moment ≤ kernel-gcd sum.**  Summing the per-frequency bound
`‖G(r)‖² ≤ N·gcd((2r).val, N)` (`sqGaussSum_normSq_le_gcd`) over the nonzero
frequencies bounds the root-mean-square in `sqDiff_error_le_l2` by an elementary
divisor sum:

    Σ_{r≠0} ‖G(r)‖²  ≤  N · Σ_{r≠0} gcd((2r).val, N).

This pins the *sole* remaining input to the composite-`N` Sárközy bound to a
purely arithmetic estimate on `Σ_r gcd((2r).val, N)` — no Gauss-sum reciprocity
required. -/
theorem sqGaussSum_normSq_sum_le_gcd_sum {N : ℕ} [NeZero N] :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ 2)
      ≤ (N : ℝ) * (Finset.univ \ {(0 : ZMod N)}).sum
          (fun r => (Nat.gcd (2 * r).val N : ℝ)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun r _ => sqGaussSum_normSq_le_gcd r)

/-- **L²-averaged Sárközy density inequality (unconditional).**  Combining the
Cauchy–Schwarz error bound `sqDiff_error_le_l2` (one-sided, via `|·|`) with the
square-difference-free upper bound `sqDiffCount_le_of_free` gives, for any
square-difference-free `A ⊆ ℤ/Nℤ`,

    |A|²  ≤  |A|·#{n : n² = 0}  +  N⁻¹·|A|·√(|A|N − |A|²)·√(Σ_{r≠0} ‖G(r)‖²).

Unlike `sqDiffFree_density_bound`, the Gauss-sum input is the *second moment*
`Σ_{r≠0}‖G(r)‖²` (an average), not the pointwise maximum.  Chained with
`sqGaussSum_normSq_sum_le_gcd_sum` (`Σ‖G‖² ≤ N·Σgcd`), the last analytic
ingredient becomes the elementary bound `Σ_{r≠0} gcd((2r).val,N) = o(N²)`. -/
theorem sqDiffFree_density_bound_l2 {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) ^ 2
      ≤ (A.card : ℝ) * (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card
        + (↑N)⁻¹ * (↑A.card * (Real.sqrt (↑A.card * ↑N - (↑A.card) ^ 2)
            * Real.sqrt ((Finset.univ \ {(0 : ZMod N)}).sum
                (fun r => ‖sqGaussSum r‖ ^ 2)))) := by
  have herr := sqDiff_error_le_l2 A
  have key : |(sqDiffCount A : ℝ) - (A.card : ℝ) ^ 2|
      ≤ (↑N)⁻¹ * (↑A.card * (Real.sqrt (↑A.card * ↑N - (↑A.card) ^ 2)
          * Real.sqrt ((Finset.univ \ {(0 : ZMod N)}).sum
              (fun r => ‖sqGaussSum r‖ ^ 2)))) := by
    have e : ‖(sqDiffCount A : ℂ) - (↑A.card) ^ 2‖
        = |(sqDiffCount A : ℝ) - (A.card : ℝ) ^ 2| := by
      rw [show (sqDiffCount A : ℂ) - (↑A.card) ^ 2
            = (((sqDiffCount A : ℝ) - (A.card : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rwa [e] at herr
  have hupp : (sqDiffCount A : ℝ)
      ≤ (A.card : ℝ) * (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card := by
    exact_mod_cast sqDiffCount_le_of_free A hfree
  linarith [(abs_le.mp key).1]

/-- A proper divisor is at most half: if `0 < m < N` then `2 · gcd(m, N) ≤ N`.  The gcd
    divides `N` and is at most `m < N`, hence a *proper* divisor, so `N / gcd ≥ 2`. -/
private theorem two_mul_gcd_le {m N : ℕ} (hpos : 0 < m) (hlt : m < N) :
    2 * Nat.gcd m N ≤ N := by
  set d := Nat.gcd m N with hd
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le m) hlt
  have hdvd : d ∣ N := Nat.gcd_dvd_right m N
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hNpos
  have hdlt : d < N := lt_of_le_of_lt (Nat.gcd_le_left N hpos) hlt
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    by_contra h
    push_neg at h
    interval_cases k
    · simp at hk; omega
    · simp at hk; omega
  calc 2 * d ≤ k * d := Nat.mul_le_mul_right d hk2
    _ = d * k := Nat.mul_comm k d
    _ = N := hk.symm

/-- **Sub-maximal magnitude off the `2`-torsion.**  Whenever `2r ≠ 0`, the frequency
    `(2r).val` is a nonzero residue `< N`, so its gcd with `N` is a *proper* divisor and
    `sqGaussSum_normSq_le_gcd` sharpens to

    `‖G(r)‖² ≤ N² / 2`,  i.e.  `‖G(r)‖ ≤ N / √2`.

    This is the first *uniform* bound covering non-unit frequencies: it shows the quadratic
    Gauss sum is strictly sub-maximal (`< N`) at every frequency except the trivial `2`-torsion
    `{r : 2r = 0}`.  (At a `2`-torsion `r ≠ 0` — only possible for even `N` — the kernel is all
    of `ZMod N` and `‖G(r)‖` can reach the full `N`.) -/
theorem sqGaussSum_normSq_le_half_of_two_mul_ne {N : ℕ} [NeZero N] {r : ZMod N}
    (hr : 2 * r ≠ 0) : ‖sqGaussSum r‖ ^ 2 ≤ (N : ℝ) ^ 2 / 2 := by
  have hpos : 0 < (2 * r).val := ZMod.val_pos.mpr hr
  have hlt : (2 * r).val < N := ZMod.val_lt (2 * r)
  have hnat : 2 * Nat.gcd (2 * r).val N ≤ N := two_mul_gcd_le hpos hlt
  have hgle : (Nat.gcd (2 * r).val N : ℝ) ≤ (N : ℝ) / 2 := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this; linarith
  have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc ‖sqGaussSum r‖ ^ 2 ≤ (N : ℝ) * (Nat.gcd (2 * r).val N : ℝ) := sqGaussSum_normSq_le_gcd r
    _ ≤ (N : ℝ) * ((N : ℝ) / 2) := mul_le_mul_of_nonneg_left hgle hNnn
    _ = (N : ℝ) ^ 2 / 2 := by ring

/-- **Uniform sub-maximal magnitude at odd moduli.**  For `N` odd, `2` is a unit, so `2r = 0`
    forces `r = 0`; hence *every* nonzero frequency has `2r ≠ 0` and inherits the sub-maximal
    bound `‖G(r)‖² ≤ N² / 2`.  Unlike the exact `√N` evaluation, this needs no unit hypothesis on
    `r` itself — it holds at the non-unit nonzero frequencies of a composite odd `N` too. -/
theorem sqGaussSum_normSq_le_half_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) {r : ZMod N}
    (hr : r ≠ 0) : ‖sqGaussSum r‖ ^ 2 ≤ (N : ℝ) ^ 2 / 2 := by
  apply sqGaussSum_normSq_le_half_of_two_mul_ne
  have h2 : IsUnit (2 : ZMod N) := by
    have hcast : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_cast
    rw [← hcast, ZMod.isUnit_iff_coprime]
    have hnd : ¬ (2 ∣ N) := by rw [Nat.dvd_iff_mod_eq_zero, Nat.odd_iff.mp hodd]; omega
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
  intro h
  obtain ⟨u, hu⟩ := h2
  have hz : (↑u⁻¹ : ZMod N) * (2 * r) = 0 := by rw [h, mul_zero]
  rw [← hu, ← mul_assoc, Units.inv_mul, one_mul] at hz
  exact hr hz

/-- **`‖G(r)‖ ≤ N / √2` at odd moduli.**  Square-root form of `sqGaussSum_normSq_le_half_of_odd`:
    the uniform magnitude bound `‖G(r)‖ ≤ √(N²/2)` valid at every nonzero frequency of an odd
    modulus, supplying a *single* `M` for `sqDiffFree_density_bound` over all odd `N`. -/
theorem sqGaussSum_norm_le_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) {r : ZMod N} (hr : r ≠ 0) :
    ‖sqGaussSum r‖ ≤ Real.sqrt ((N : ℝ) ^ 2 / 2) := by
  have hmono := Real.sqrt_le_sqrt (sqGaussSum_normSq_le_half_of_odd hodd hr)
  rwa [Real.sqrt_sq (norm_nonneg _)] at hmono

/-- **Square-difference density bound at odd moduli (unconditional in `N`).**  The uniform
    sub-maximal magnitude `‖G(r)‖ ≤ √(N²/2)` discharges the analytic hypothesis of
    `sqDiffFree_density_bound` with `M = N/√2` for *every* odd `N` — composite included — extending
    the prime-modulus capstone `sqDiffFree_density_bound_of_prime` past the field case.

    Honesty note: `M = N/√2` is of the same order as `N`, so — unlike the prime case's `M = √N` —
    this does **not** by itself force `|A| = o(N)`.  It is a genuine unconditional statement for all
    odd moduli, but quantitatively weak; a nontrivial odd-composite Sárközy density still needs the
    residual-phase cancellation in `Σ_{h : 2rh=0} ψ(−rh²)` (a smaller Gauss sum) that the triangle
    inequality in `sqGaussSum_normSq_le` discards. -/
theorem sqDiffFree_density_bound_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) ^ 2
      ≤ (A.card : ℝ) * (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card
        + (↑N)⁻¹ * (Real.sqrt ((N : ℝ) ^ 2 / 2) * (↑A.card * ↑N - (↑A.card) ^ 2)) :=
  sqDiffFree_density_bound A (fun _ hr => sqGaussSum_norm_le_of_odd hodd hr) hfree

/-!
## Part VIII: The two-torsion dichotomy

All of the magnitude machinery so far (`sqGaussSum_normSq_le_gcd`,
`sqGaussSum_normSq_le_half_of_two_mul_ne`) becomes *vacuous* at a two-torsion
frequency `2r = 0`: there the kernel `{h : 2rh = 0}` is the whole of `ZMod N`, so
`gcd((2r).val, N) = N` and the bound degrades to the trivial `‖G(r)‖ ≤ N`.  These
are precisely the frequencies the earlier results could not reach (they all needed
`2r` a unit, or `2r ≠ 0`).

The Weyl identity nonetheless pins them down *exactly*.  When `2r = 0` the residual
phase sum `Σ_{h : 2rh=0} ψ(−r·h²)` runs over **all** of `ZMod N` and equals
`conj(G(r))`, so the identity `G(r)·conj(G(r)) = N·conj(G(r))` factors as
`conj(G(r))·(G(r) − N) = 0`.  Over the integral domain `ℂ` this forces a clean
**dichotomy**: a two-torsion quadratic Gauss sum is either *fully cancelled*
(`G(r) = 0`) or *fully coherent* (`G(r) = N`) — never anything strictly between.
The intermediate magnitudes `0 < ‖G(r)‖ < N` that the trivial kernel bound leaves
open are all impossible.
-/

/-- The conjugate quadratic Gauss sum is the Gauss sum with a negated phase:
    `conj(G(r)) = Σ_h ψ(−r·h²)`.  Immediate from `conj_psi` (`conj(ψ a) = ψ(−a)`). -/
private lemma conj_sqGaussSum {N : ℕ} [NeZero N] (r : ZMod N) :
    starRingEnd ℂ (sqGaussSum r)
      = Finset.univ.sum (fun h : ZMod N => ψ (-(r * h ^ 2))) := by
  simp only [sqGaussSum, map_sum (starRingEnd ℂ), conj_psi]

/-- **Weyl identity at a two-torsion frequency.**  When `2r = 0` the kernel
    `{h : 2rh = 0}` is all of `ZMod N`, so the residual phase sum collapses to
    `conj(G(r))` and the Weyl identity reads `G(r)·conj(G(r)) = N·conj(G(r))`. -/
theorem sqGaussSum_mul_conj_of_two_mul_eq_zero {N : ℕ} [NeZero N] {r : ZMod N}
    (hr : 2 * r = 0) :
    sqGaussSum r * starRingEnd ℂ (sqGaussSum r)
      = (N : ℂ) * starRingEnd ℂ (sqGaussSum r) := by
  have hfilter : (Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro h _
    rw [hr, zero_mul]
  rw [sqGaussSum_mul_conj r, hfilter, conj_sqGaussSum r]

/-- **The two-torsion dichotomy.**  A quadratic Gauss sum at a two-torsion frequency
    (`2r = 0`) is either `0` or `N` — nothing strictly in between.  Factoring the
    Weyl identity `G(r)·conj(G(r)) = N·conj(G(r))` as `conj(G(r))·(G(r) − N) = 0`
    over the integral domain `ℂ`.  This pins down exactly the frequencies at which
    the kernel-count magnitude bounds are vacuous (they give only `‖G(r)‖ ≤ N`). -/
theorem sqGaussSum_eq_zero_or_eq_natCast_of_two_mul_eq_zero {N : ℕ} [NeZero N]
    {r : ZMod N} (hr : 2 * r = 0) :
    sqGaussSum r = 0 ∨ sqGaussSum r = (N : ℂ) := by
  have hid := sqGaussSum_mul_conj_of_two_mul_eq_zero hr
  have hfac : starRingEnd ℂ (sqGaussSum r) * (sqGaussSum r - (N : ℂ)) = 0 := by
    linear_combination hid
  rcases mul_eq_zero.mp hfac with hz | hz
  · left
    have h := congrArg (starRingEnd ℂ) hz
    simpa using h
  · right
    exact sub_eq_zero.mp hz

/-- **Magnitude dichotomy at two-torsion frequencies.**  The norm form of the
    dichotomy: at a two-torsion frequency `‖G(r)‖` is either `0` or `N`, so the only
    magnitudes attainable are the two extremes.  Contrast with the *unit*-frequency
    value `‖G(r)‖ = √N` (`sqGaussSum_norm_eq_sqrt_of_isUnit`): the two regimes are
    completely disjoint. -/
theorem sqGaussSum_norm_eq_zero_or_eq_natCast_of_two_mul_eq_zero {N : ℕ} [NeZero N]
    {r : ZMod N} (hr : 2 * r = 0) :
    ‖sqGaussSum r‖ = 0 ∨ ‖sqGaussSum r‖ = (N : ℝ) := by
  rcases sqGaussSum_eq_zero_or_eq_natCast_of_two_mul_eq_zero hr with h | h
  · left; rw [h, norm_zero]
  · right; rw [h, Complex.norm_natCast]

/-! ### Part VIII (cont.): the two-torsion branch is *always* the zero branch

The dichotomy `sqGaussSum_eq_zero_or_eq_natCast_of_two_mul_eq_zero` leaves open
*which* branch (`0` or `N`) a given two-torsion frequency lands in.  The next
theorem decides it completely: away from `r = 0`, the branch is **always** `0`.
Equivalently, the "fully coherent" value `G(r) = N` occurs at a two-torsion
frequency only at `r = 0` (where `G(0) = N` by `sqGaussSum_zero`); every *nonzero*
two-torsion frequency is fully cancelled.

The mechanism is a one-line shift.  At a two-torsion frequency `2r = 0` the mixed
term of `(n+1)²` disappears: `r·(n+1)² = r·n² + (2r)·n + r = r·n² + r`.  Hence the
`n ↦ n+1` reindexing of the Gauss sum multiplies every term by the *constant*
phase `ψ(r)`, giving `G(r) = ψ(r)·G(r)`.  Since `r ≠ 0` makes `ψ(r) ≠ 1`
(`psi_ne_one`), the only solution is `G(r) = 0`.

This is strictly stronger than the flagged sub-goal (the canonical even-modulus
element `r = N/2`, where `G(N/2) = Σ_n (−1)^n = 0`): it covers the whole
two-torsion subgroup at once, for every modulus `N`.  It does **not** yield the
`o(N)` Sárközy density bound — that still needs the residual-phase recursion at
frequencies with `2r ≠ 0`, which this argument does not touch.
-/

/-- **Nonzero two-torsion quadratic Gauss sums vanish.**  At any *nonzero*
    two-torsion frequency (`2r = 0`, `r ≠ 0`) the quadratic Gauss sum is fully
    cancelled: `G(r) = 0`.  This resolves the two-torsion dichotomy
    (`sqGaussSum_eq_zero_or_eq_natCast_of_two_mul_eq_zero`): the coherent branch
    `G(r) = N` never occurs for `r ≠ 0`, only at `r = 0`.

    Proof: since `2r = 0`, the mixed term of `(n+1)²` drops,
    `r·(n+1)² = r·n² + (2r)·n + r = r·n² + r`, so `ψ(r(n+1)²) = ψ(r n²)·ψ(r)`.
    Reindexing the sum by the bijection `n ↦ n+1` gives `G(r) = ψ(r)·G(r)`; as
    `r ≠ 0` forces `ψ(r) ≠ 1`, this forces `G(r) = 0`. -/
theorem sqGaussSum_eq_zero_of_two_mul_eq_zero {N : ℕ} [NeZero N] {r : ZMod N}
    (hr2 : 2 * r = 0) (hr0 : r ≠ 0) :
    sqGaussSum r = 0 := by
  -- Each shifted term factors off the constant phase ψ(r), using (2r)·n = 0.
  have hstep : ∀ n : ZMod N, ψ (r * (n + 1) ^ 2) = ψ (r * n ^ 2) * ψ r := by
    intro n
    rw [← psi_add]
    congr 1
    have hz : 2 * r * n = 0 := by rw [hr2, zero_mul]
    linear_combination hz
  -- Reindex n ↦ n+1 (a bijection of ZMod N): ∑ ψ(r(n+1)²) = ∑ ψ(r n²) = G(r).
  have hreindex :
      (Finset.univ.sum fun n : ZMod N => ψ (r * (n + 1) ^ 2)) = sqGaussSum r := by
    rw [sqGaussSum]
    apply Finset.sum_equiv (Equiv.addRight (1 : ZMod N))
    · intro n; simp
    · intro n _; rfl
  -- Combine the two evaluations of the shifted sum: G(r) = G(r)·ψ(r).
  have hfix : sqGaussSum r = sqGaussSum r * ψ r := by
    calc sqGaussSum r
        = Finset.univ.sum fun n : ZMod N => ψ (r * (n + 1) ^ 2) := hreindex.symm
      _ = Finset.univ.sum fun n : ZMod N => ψ (r * n ^ 2) * ψ r :=
            Finset.sum_congr rfl (fun n _ => hstep n)
      _ = (Finset.univ.sum fun n : ZMod N => ψ (r * n ^ 2)) * ψ r := by
            rw [← Finset.sum_mul]
      _ = sqGaussSum r * ψ r := by rw [sqGaussSum]
  -- ψ(r) ≠ 1 for r ≠ 0, so G(r)·(1 − ψ(r)) = 0 forces G(r) = 0.
  have hψ : ψ r ≠ 1 := psi_ne_one r hr0
  have hzero : sqGaussSum r * (1 - ψ r) = 0 := by linear_combination hfix
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hψ

/-- **Norm form.**  Every nonzero two-torsion quadratic Gauss sum has norm `0`. -/
theorem sqGaussSum_norm_eq_zero_of_two_mul_eq_zero {N : ℕ} [NeZero N] {r : ZMod N}
    (hr2 : 2 * r = 0) (hr0 : r ≠ 0) :
    ‖sqGaussSum r‖ = 0 := by
  rw [sqGaussSum_eq_zero_of_two_mul_eq_zero hr2 hr0, norm_zero]

/-! ### Part IX: the general shift-vanishing criterion

The one-line shift behind `sqGaussSum_eq_zero_of_two_mul_eq_zero` never used the
shift amount `1` in any essential way.  Reindexing the Gauss sum by `n ↦ n + t`
for an **arbitrary** `t : ZMod N` gives
`r·(n + t)² = r·n² + (2rt)·n + r·t²`, so as soon as `2rt = 0` the mixed term drops
and every term picks up the same constant phase `ψ(r·t²)`:
`G(r) = ψ(r·t²)·G(r)`.  If additionally `r·t² ≠ 0` then `ψ(r·t²) ≠ 1`, forcing
`G(r) = 0`.  The two-torsion result is exactly the `t = 1` instance
(`2r·1 = 2r = 0`, `r·1² = r ≠ 0`).

This is *strictly* stronger: it vanishes many frequencies that are **not**
two-torsion.  A concrete witness is `N = 24`, `r = 4`, `t = 3`: here
`2·4·3 = 24 = 0` and `4·3² = 36 = 12 ≠ 0` in `ℤ/24ℤ`, so `G(4) = 0` even though
`2·4 = 8 ≠ 0` (so the two-torsion theorem says nothing about `r = 4`).  The
mechanism is that `2rt = 0` forces `rt` into the two-torsion subgroup `{0, N/2}`;
the criterion fires precisely when `rt = N/2` with `t` odd, which — over a modulus
with a nontrivial odd part — reaches `r`'s outside the two-torsion subgroup.

Like its special case this remains a *pointwise* vanishing statement and does not
touch the `o(N)` Sárközy density bound, which needs the residual-phase recursion
at the frequencies this criterion leaves untouched (those with no admissible
shift `t`). -/

/-- **General shift-vanishing criterion for quadratic Gauss sums.**  If some shift
    `t` kills the linear term (`2·r·t = 0`) while keeping the constant phase
    nontrivial (`r·t² ≠ 0`), then the Gauss sum vanishes: `G(r) = 0`.

    Reindexing `n ↦ n + t` (a bijection of `ZMod N`) sends
    `ψ(r·(n+t)²) = ψ(r·n²)·ψ(r·t²)` once `2rt = 0`, so `G(r) = ψ(r·t²)·G(r)`; the
    hypothesis `r·t² ≠ 0` makes `ψ(r·t²) ≠ 1`, forcing `G(r) = 0`.  Generalizes
    `sqGaussSum_eq_zero_of_two_mul_eq_zero` (the `t = 1` case) and reaches
    non-two-torsion frequencies (see `sqGaussSum_four_eq_zero_mod_24`). -/
theorem sqGaussSum_eq_zero_of_shift {N : ℕ} [NeZero N] {r t : ZMod N}
    (h2 : 2 * r * t = 0) (hrt : r * t ^ 2 ≠ 0) :
    sqGaussSum r = 0 := by
  -- Each shifted term factors off the constant phase ψ(r·t²), using (2rt)·n = 0.
  have hstep : ∀ n : ZMod N, ψ (r * (n + t) ^ 2) = ψ (r * n ^ 2) * ψ (r * t ^ 2) := by
    intro n
    rw [← psi_add]
    congr 1
    have hz : 2 * r * t * n = 0 := by rw [h2, zero_mul]
    linear_combination hz
  -- Reindex n ↦ n+t (a bijection of ZMod N): ∑ ψ(r(n+t)²) = ∑ ψ(r n²) = G(r).
  have hreindex :
      (Finset.univ.sum fun n : ZMod N => ψ (r * (n + t) ^ 2)) = sqGaussSum r := by
    rw [sqGaussSum]
    apply Finset.sum_equiv (Equiv.addRight t)
    · intro n; simp
    · intro n _; rfl
  -- Combine the two evaluations of the shifted sum: G(r) = G(r)·ψ(r·t²).
  have hfix : sqGaussSum r = sqGaussSum r * ψ (r * t ^ 2) := by
    calc sqGaussSum r
        = Finset.univ.sum fun n : ZMod N => ψ (r * (n + t) ^ 2) := hreindex.symm
      _ = Finset.univ.sum fun n : ZMod N => ψ (r * n ^ 2) * ψ (r * t ^ 2) :=
            Finset.sum_congr rfl (fun n _ => hstep n)
      _ = (Finset.univ.sum fun n : ZMod N => ψ (r * n ^ 2)) * ψ (r * t ^ 2) := by
            rw [← Finset.sum_mul]
      _ = sqGaussSum r * ψ (r * t ^ 2) := by rw [sqGaussSum]
  -- ψ(r·t²) ≠ 1, so G(r)·(1 − ψ(r·t²)) = 0 forces G(r) = 0.
  have hψ : ψ (r * t ^ 2) ≠ 1 := psi_ne_one _ hrt
  have hzero : sqGaussSum r * (1 - ψ (r * t ^ 2)) = 0 := by linear_combination hfix
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hψ

/-- **Norm form of the shift criterion.**  Under an admissible shift the Gauss sum
    has norm `0`. -/
theorem sqGaussSum_norm_eq_zero_of_shift {N : ℕ} [NeZero N] {r t : ZMod N}
    (h2 : 2 * r * t = 0) (hrt : r * t ^ 2 ≠ 0) :
    ‖sqGaussSum r‖ = 0 := by
  rw [sqGaussSum_eq_zero_of_shift h2 hrt, norm_zero]

/-- The two-torsion vanishing theorem is the `t = 1` instance of the shift
    criterion.  (Recorded as a sanity check that `sqGaussSum_eq_zero_of_shift`
    subsumes `sqGaussSum_eq_zero_of_two_mul_eq_zero`.) -/
example {N : ℕ} [NeZero N] {r : ZMod N} (hr2 : 2 * r = 0) (hr0 : r ≠ 0) :
    sqGaussSum r = 0 :=
  sqGaussSum_eq_zero_of_shift (t := 1) (by rw [mul_one]; exact hr2) (by rwa [one_pow, mul_one])

/-- **A non-two-torsion vanishing frequency.**  In `ℤ/24ℤ` the frequency `r = 4`
    is *not* two-torsion (`2·4 = 8 ≠ 0`), yet its quadratic Gauss sum vanishes,
    `G(4) = 0`, via the shift `t = 3`: `2·4·3 = 24 = 0` while `4·3² = 12 ≠ 0`.
    This exhibits `sqGaussSum_eq_zero_of_shift` reaching strictly past the
    two-torsion subgroup. -/
theorem sqGaussSum_four_eq_zero_mod_24 : sqGaussSum (4 : ZMod 24) = 0 :=
  sqGaussSum_eq_zero_of_shift (t := 3) (by decide) (by decide)

/-!
## Part XI: Uniform sub-maximal magnitude at every modulus

The two-torsion vanishing theorem (`sqGaussSum_eq_zero_of_two_mul_eq_zero`) closes
the one gap that forced the Part VII magnitude bounds to assume `Odd N`.  The
off-two-torsion bound `sqGaussSum_normSq_le_half_of_two_mul_ne` already gives
`‖G(r)‖² ≤ N²/2` whenever `2r ≠ 0`; the only frequencies it could not reach were
the two-torsion ones `2r = 0`, where the kernel is all of `ZMod N` and the gcd
bound degrades to the trivial `‖G(r)‖ ≤ N`.  But a *nonzero* two-torsion frequency
has `G(r) = 0` outright, so it satisfies the same `N²/2` bound with room to spare.

Splitting on `2r = 0` therefore removes the oddness hypothesis entirely: at **every**
modulus `N`, every nonzero frequency obeys `‖G(r)‖ ≤ N/√2`.  This supplies the single
magnitude `M = N/√2` to `sqDiffFree_density_bound` unconditionally in `N`, superseding
`sqDiffFree_density_bound_of_odd` (which needed `Odd N`) and the field-only
`sqDiffFree_density_bound_of_prime`.

Honesty note: `M = N/√2` is still of order `N`, so — exactly as in the odd case — it
does **not** by itself force `|A| = o(N)`.  The point here is the removal of a
hypothesis, not a quantitative sharpening: the unconditional Sárközy density for all
moduli still needs the residual-phase cancellation in `Σ_{h : 2rh=0} ψ(−rh²)` that the
triangle inequality in `sqGaussSum_normSq_le` discards. -/

/-- **Uniform sub-maximal magnitude at every modulus.**  For *any* `N` and any nonzero
    frequency `r`, `‖G(r)‖² ≤ N²/2`.  Split on the two-torsion: if `2r = 0` then `r ≠ 0`
    forces `G(r) = 0` (`sqGaussSum_eq_zero_of_two_mul_eq_zero`), so the bound holds with
    the left side `0`; otherwise `sqGaussSum_normSq_le_half_of_two_mul_ne` applies.  Drops
    the `Odd N` hypothesis of `sqGaussSum_normSq_le_half_of_odd`. -/
theorem sqGaussSum_normSq_le_half_of_ne_zero {N : ℕ} [NeZero N] {r : ZMod N}
    (hr : r ≠ 0) : ‖sqGaussSum r‖ ^ 2 ≤ (N : ℝ) ^ 2 / 2 := by
  rcases eq_or_ne (2 * r) 0 with h2 | h2
  · rw [sqGaussSum_norm_eq_zero_of_two_mul_eq_zero h2 hr]
    have hpos : (0 : ℝ) ≤ (N : ℝ) ^ 2 / 2 := by positivity
    simpa using hpos
  · exact sqGaussSum_normSq_le_half_of_two_mul_ne h2

/-- **`‖G(r)‖ ≤ N / √2` at every modulus.**  Square-root form of
    `sqGaussSum_normSq_le_half_of_ne_zero`, supplying a *single* magnitude `M = √(N²/2)`
    for `sqDiffFree_density_bound` over all `N`.  Supersedes `sqGaussSum_norm_le_of_odd`
    by dropping the `Odd N` hypothesis. -/
theorem sqGaussSum_norm_le_of_ne_zero {N : ℕ} [NeZero N] {r : ZMod N} (hr : r ≠ 0) :
    ‖sqGaussSum r‖ ≤ Real.sqrt ((N : ℝ) ^ 2 / 2) := by
  have hmono := Real.sqrt_le_sqrt (sqGaussSum_normSq_le_half_of_ne_zero hr)
  rwa [Real.sqrt_sq (norm_nonneg _)] at hmono

/-- **Square-difference density bound at every modulus (unconditional in `N`).**  The
    uniform magnitude `‖G(r)‖ ≤ √(N²/2)` discharges the analytic hypothesis of
    `sqDiffFree_density_bound` with `M = N/√2` for *every* `N` — even moduli included —
    extending `sqDiffFree_density_bound_of_odd` past the oddness restriction.

    Honesty note: `M = N/√2` is of the same order as `N`, so this does **not** by itself
    force `|A| = o(N)`; it is a genuine unconditional statement for all moduli but
    quantitatively weak, for the same reason as the odd case. -/
theorem sqDiffFree_density_bound_of_ne_zero {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) ^ 2
      ≤ (A.card : ℝ) * (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card
        + (↑N)⁻¹ * (Real.sqrt ((N : ℝ) ^ 2 / 2) * (↑A.card * ↑N - (↑A.card) ^ 2)) :=
  sqDiffFree_density_bound A (fun _ hr => sqGaussSum_norm_le_of_ne_zero hr) hfree

/-!
## Part XII: An effective (search-free) vanishing criterion

The shift criterion `sqGaussSum_eq_zero_of_shift` is *existential*: it certifies
`G(r) = 0` given **some** shift `t` with `2rt = 0` and `rt² ≠ 0`, but leaves open
how to find such a `t` (the `N = 24`, `r = 4` witness `t = 3` was produced by
hand).  The kernel `{t : 2rt = 0}` is the cyclic subgroup of `ZMod N` annihilating
`2r`; it has order `g := gcd((2r).val, N)` and is generated by the single element

  `t₀ := (N / g : ZMod N)`.

So there is a **canonical** shift to test, and the entire admissible family is
`{k · t₀ : k}`.  Because the constant phase is quadratic in the shift,
`r·(k·t₀)² = k²·(r·t₀²)`, the whole family's phases are scalar multiples of the
*one* phase `r·t₀²`.  Two consequences:

* **Effectiveness.**  `G(r) = 0` as soon as the single closed-form quantity
  `r·t₀²` is nonzero — one `gcd` and one modular multiplication, no search
  (`sqGaussSum_eq_zero_of_gcd_shift`).  This is `decide`-able at any concrete
  modulus, and it *automatically* recovers the hand-found witnesses: `t₀ = 1` at a
  two-torsion frequency, and `t₀ = 3` for `N = 24`, `r = 4`.

* **Optimality of the canonical test.**  If `r·t₀² = 0`, then `r·t² = 0` for every
  admissible `t = k·t₀`, so the shift criterion fires for *no* shift at all
  (`gcd_shift_phase_smul`).  The canonical test is therefore not just *a* test but
  *the* test for this whole method — a frequency is reached by some shift iff it is
  reached by `t₀`.

Honesty note: turning the last "iff" into a formal statement needs the kernel
cyclicity `{t : 2rt = 0} = ⟨t₀⟩` (every admissible `t` is a scalar multiple of
`t₀`), which is stated below only as the prose fact `gcd_shift_phase_smul` covers
the `⟨t₀⟩ ⊆ kernel` direction of; the reverse containment is the remaining gap.  As
with all of Parts VIII–XI this stays pointwise and does not by itself sharpen the
`o(N)` Sárközy density. -/

/-- The canonical kernel generator `t₀ = N / gcd((2r).val, N)` annihilates `2r`:
    `2r · t₀ = 0`.  Writing `(2r).val = g·a` and `N = g·b` (so `N/g = b`), the
    product `(2r).val · (N/g) = a·N ≡ 0`, and `2r` is the cast of its own `val`. -/
private theorem two_mul_kernel_gen_eq_zero {N : ℕ} [NeZero N] (r : ZMod N) :
    2 * r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) = 0 := by
  set g := Nat.gcd (2 * r).val N with hg
  have hgv : g ∣ (2 * r).val := Nat.gcd_dvd_left _ _
  have hgN : g ∣ N := Nat.gcd_dvd_right _ _
  obtain ⟨a, ha⟩ := hgv                                -- (2*r).val = g * a
  -- Cast the val-factorisation into `ZMod N`: `2r = (g:ZMod N)·(a:ZMod N)`.
  have h2r : (2 * r) = (g : ZMod N) * (a : ZMod N) := by
    rw [← Nat.cast_mul, ← ha, ZMod.natCast_zmod_val]
  -- The generator kills `g`: `(g:ZMod N)·t₀ = (g·(N/g) : ZMod N) = (N : ZMod N) = 0`.
  have hgt : (g : ZMod N) * ((N / g : ℕ) : ZMod N) = 0 := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hgN, ZMod.natCast_self]
  calc 2 * r * ((N / g : ℕ) : ZMod N)
      = (a : ZMod N) * ((g : ZMod N) * ((N / g : ℕ) : ZMod N)) := by rw [h2r]; ring
    _ = 0 := by rw [hgt, mul_zero]

/-- **Effective vanishing criterion.**  With the canonical shift
    `t₀ = N / gcd((2r).val, N)` (the kernel generator), the *single* closed-form
    condition `r · t₀² ≠ 0` already forces `G(r) = 0`.  No search over shifts is
    needed: `t₀` annihilates `2r` by `two_mul_kernel_gen_eq_zero`, so this is the
    `t = t₀` instance of `sqGaussSum_eq_zero_of_shift`.  The hypothesis is a finite
    `gcd`-plus-multiplication computation, hence `decide`-able at any concrete
    modulus. -/
theorem sqGaussSum_eq_zero_of_gcd_shift {N : ℕ} [NeZero N] {r : ZMod N}
    (hr : r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) ^ 2 ≠ 0) :
    sqGaussSum r = 0 :=
  sqGaussSum_eq_zero_of_shift (two_mul_kernel_gen_eq_zero r) hr

/-- **Norm form** of the effective criterion. -/
theorem sqGaussSum_norm_eq_zero_of_gcd_shift {N : ℕ} [NeZero N] {r : ZMod N}
    (hr : r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) ^ 2 ≠ 0) :
    ‖sqGaussSum r‖ = 0 := by
  rw [sqGaussSum_eq_zero_of_gcd_shift hr, norm_zero]

/-- **Scalar multiples share the canonical phase (up to a square factor).**  Every
    admissible shift is a scalar multiple `k · t₀` of the canonical generator, and
    its constant phase is `r·(k t₀)² = k²·(r t₀²)`.  Hence if the canonical phase
    `r·t₀²` vanishes, so does every scalar multiple's — the shift criterion fires
    for a scalar multiple of `t₀` iff it fires for `t₀` itself.  (Combined with the
    kernel cyclicity `{t : 2rt = 0} = ⟨t₀⟩`, this would upgrade
    `sqGaussSum_eq_zero_of_gcd_shift` to an exact characterization of the
    shift-reachable vanishing set.) -/
theorem gcd_shift_phase_smul {N : ℕ} [NeZero N] (r k : ZMod N) :
    r * (k * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N)) ^ 2
      = k ^ 2 * (r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) ^ 2) := by
  ring

/-- The effective criterion recovers the two-torsion vanishing theorem: when
    `2r = 0` the gcd is `N`, so `t₀ = N/N = 1` and the test reduces to `r ≠ 0`. -/
example {N : ℕ} [NeZero N] {r : ZMod N} (hr2 : 2 * r = 0) (hr0 : r ≠ 0) :
    sqGaussSum r = 0 := by
  apply sqGaussSum_eq_zero_of_gcd_shift
  have hval : (2 * r).val = 0 := by rw [hr2]; simp
  rw [hval, Nat.gcd_zero_left, Nat.div_self (NeZero.pos N), Nat.cast_one, one_pow, mul_one]
  exact hr0

/-- The effective criterion decides the non-two-torsion witness `G(4) = 0` in
    `ℤ/24ℤ` *without* supplying a shift: the canonical `t₀ = 24 / gcd(8, 24) = 3`
    is computed by `decide` from `r = 4` alone. -/
example : sqGaussSum (4 : ZMod 24) = 0 :=
  sqGaussSum_eq_zero_of_gcd_shift (by decide)

/-! ### Part XIII — exact iff-characterization of the shift-reachable vanishing set

The effective criterion `sqGaussSum_eq_zero_of_gcd_shift` gives one implication: the
canonical phase `r·t₀² ≠ 0` (with `t₀ = N / gcd((2r).val, N)`) *forces* `G(r) = 0`.
The converse question is whether the *existence* of any vanishing shift already
implies the canonical test fires.  It does, and the missing input is the reverse
kernel containment `{t : 2rt = 0} ⊆ ⟨t₀⟩`: every annihilator of `2r` is a scalar
multiple of the canonical generator `t₀`.  Combined with the forward containment
`⟨t₀⟩ ⊆ kernel` (`two_mul_kernel_gen_eq_zero`) this pins the kernel *exactly* as the
cyclic subgroup `⟨t₀⟩`, and upgrades the criterion to the exact characterisation
`(∃ shift t : 2rt = 0 ∧ r·t² ≠ 0) ↔ r·t₀² ≠ 0`.  The right-hand side is a single
decidable `gcd`-plus-multiplication test, so this decides membership in the
shift-reachable vanishing set at any concrete frequency — and, dually, isolates the
*residual* frequencies `r·t₀² = 0` where no shift works and the residual-phase
recursion `S(r) = Σ_{h:2rh=0} ψ(−r h²)` is genuinely required for an `o(N)` bound.

As throughout Parts VIII–XII this stays pointwise; it sharpens *which* frequencies
the shift method decides, not the Sárközy density itself. -/

/-- **Reverse kernel containment** `{t : c·t = 0} ⊆ ⟨t₀⟩`.  Every annihilator `t` of a
    ring element `c : ZMod N` is a scalar multiple of the canonical cyclic generator
    `t₀ = N / gcd(c.val, N)`.  Proof: `c·t = 0` casts to `N ∣ c.val·t.val`; writing
    `c.val = g·a`, `N = g·b` with `g = gcd(c.val, N)` and `Coprime a b`, this gives
    `b ∣ a·t.val`, hence `b ∣ t.val` by coprimality, so `t = (t.val/b)·t₀`. -/
private theorem kernel_eq_smul_gen {N : ℕ} [NeZero N] (c t : ZMod N)
    (ht : c * t = 0) :
    ∃ k : ZMod N, t = k * ((N / Nat.gcd c.val N : ℕ) : ZMod N) := by
  set g := Nat.gcd c.val N with hg
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right c.val hNpos
  have hgc : g ∣ c.val := Nat.gcd_dvd_left c.val N
  have hgN : g ∣ N := Nat.gcd_dvd_right c.val N
  -- casts of vals
  have hcv : (c.val : ZMod N) = c := by rw [ZMod.natCast_val, ZMod.cast_id]
  have htv : (t.val : ZMod N) = t := by rw [ZMod.natCast_val, ZMod.cast_id]
  -- `c*t = 0` ⟹ `N ∣ c.val * t.val`
  have hzero : ((c.val * t.val : ℕ) : ZMod N) = 0 := by rw [Nat.cast_mul, hcv, htv, ht]
  have hdvd : N ∣ c.val * t.val := by
    rwa [ZMod.natCast_eq_zero_iff] at hzero
  -- factor `c.val` and `N` by `g`, with coprime cofactors
  set a := c.val / g with ha
  set b := N / g with hb
  have hcval : g * a = c.val := Nat.mul_div_cancel' hgc
  have hNval : g * b = N := Nat.mul_div_cancel' hgN
  have hcop : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hgpos
  -- descend the divisibility to `b ∣ t.val`
  have hdvd' : g * b ∣ g * (a * t.val) := by
    rw [hNval, ← mul_assoc, hcval]; exact hdvd
  have hbat : b ∣ a * t.val := Nat.dvd_of_mul_dvd_mul_left hgpos hdvd'
  have hbt : b ∣ t.val := (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left hbat
  obtain ⟨k, hk⟩ := hbt                               -- t.val = b * k
  refine ⟨(k : ZMod N), ?_⟩
  have ht' : t = ((b * k : ℕ) : ZMod N) := by rw [← htv, hk]
  rw [ht', Nat.cast_mul]
  ring

/-- **Kernel membership iff.**  `t` annihilates `2r` exactly when it is a scalar
    multiple of the canonical generator `t₀ = N / gcd((2r).val, N)`; i.e. the
    annihilator kernel `{t : 2rt = 0}` is precisely the cyclic subgroup `⟨t₀⟩`.
    Forward is `kernel_eq_smul_gen`; reverse is `two_mul_kernel_gen_eq_zero`. -/
theorem two_mul_eq_zero_iff_smul_gen {N : ℕ} [NeZero N] (r t : ZMod N) :
    2 * r * t = 0 ↔
      ∃ k : ZMod N, t = k * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) := by
  constructor
  · intro ht
    exact kernel_eq_smul_gen (2 * r) t ht
  · rintro ⟨k, rfl⟩
    have hcomm :
        2 * r * (k * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N))
          = k * (2 * r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N)) := by ring
    rw [hcomm, two_mul_kernel_gen_eq_zero, mul_zero]

/-- **Exact characterisation of the shift-reachable vanishing set.**  A shift `t`
    with `2rt = 0 ∧ r·t² ≠ 0` (which forces `G(r) = 0` by `sqGaussSum_eq_zero_of_shift`)
    *exists* iff the single canonical phase `r·t₀²` is nonzero.  Forward: any such `t`
    is `k·t₀` (reverse kernel containment), and `r·t² = k²·(r·t₀²)` by
    `gcd_shift_phase_smul`, so `r·t₀² = 0` would force `r·t² = 0`.  Reverse: `t₀`
    itself is the witness (`two_mul_kernel_gen_eq_zero`).  The right-hand side is a
    decidable closed-form test. -/
theorem exists_vanishing_shift_iff {N : ℕ} [NeZero N] (r : ZMod N) :
    (∃ t : ZMod N, 2 * r * t = 0 ∧ r * t ^ 2 ≠ 0) ↔
      r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) ^ 2 ≠ 0 := by
  constructor
  · rintro ⟨t, ht2, htne⟩
    obtain ⟨k, hk⟩ := kernel_eq_smul_gen (2 * r) t ht2
    intro hcontra
    apply htne
    rw [hk, gcd_shift_phase_smul, hcontra, mul_zero]
  · intro hne
    exact ⟨_, two_mul_kernel_gen_eq_zero r, hne⟩

/-- **Vanishing via the shift method is decidable and iff the canonical test.**  If
    the canonical phase test fires (`r·t₀² ≠ 0`) then `G(r) = 0`; conversely, whenever
    *some* shift makes `G(r)` provably vanish through `sqGaussSum_eq_zero_of_shift`,
    the canonical test already detects it.  Concretely, the shift method certifies
    `G(r) = 0` iff `r·t₀² ≠ 0`. -/
theorem sqGaussSum_eq_zero_of_exists_shift {N : ℕ} [NeZero N] {r : ZMod N}
    (h : ∃ t : ZMod N, 2 * r * t = 0 ∧ r * t ^ 2 ≠ 0) :
    sqGaussSum r = 0 :=
  sqGaussSum_eq_zero_of_gcd_shift ((exists_vanishing_shift_iff r).mp h)


/-! ### Part XIV — the residual case is maximal: exact decidable vanishing characterization

Part XIII isolates the *residual* frequencies `r·t₀² = 0` (with
`t₀ = N / gcd((2r).val, N)`) as exactly those the shift method cannot reach.  Here we
*evaluate* the quadratic Gauss sum on precisely those frequencies and find it is
**maximal**, never zero.  The mechanism is the reverse kernel containment
`kernel_eq_smul_gen`: every kernel element is `h = k·t₀`, so on the residual set its
residual phase is `r·h² = k²·(r·t₀²) = 0`, i.e. `ψ(−r·h²) = 1` for *every* `h` in the
kernel.  The Weyl residual sum `Σ_{h:2rh=0} ψ(−r·h²)` therefore collapses to the full
kernel count `g = gcd((2r).val, N)`, giving

    ‖G(r)‖² = N · g,

the largest value permitted by `sqGaussSum_normSq_le_gcd` — hence `G(r) ≠ 0`.

Combined with the shift criterion (`r·t₀² ≠ 0 ⟹ G(r) = 0`,
`sqGaussSum_eq_zero_of_gcd_shift`) this closes the characterisation to an exact,
decidable **iff**:

    G(r) = 0  ↔  r·t₀² ≠ 0.

So the single closed-form quantity `r·t₀²` (one `gcd`, one modular multiply) *decides*
quadratic-Gauss-sum vanishing at every frequency, with **no** residual open input — and
the shift method (`sqGaussSum_eq_zero_iff_exists_shift`) is *complete*: it certifies
every vanishing.  This resolves the Part XIII residual gap: the `o(N)` Sárközy
obstruction is **not** pointwise vanishing (now fully decided) but the cancellation
among the *non-vanishing* magnitudes `‖G(r)‖ = √(N·gcd(2r,N))`. -/

/-- In the residual case `r·t₀² = 0`, every residual phase is trivial: any kernel
    element `h` (i.e. `2rh = 0`) satisfies `r·h² = 0`.  Indeed `h = k·t₀` by the reverse
    kernel containment `kernel_eq_smul_gen`, so `r·h² = k²·(r·t₀²) = 0`. -/
private theorem residual_phase_zero_of_gcd_phase_zero {N : ℕ} [NeZero N] {r : ZMod N}
    (hphase : r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) ^ 2 = 0)
    {h : ZMod N} (hh : 2 * r * h = 0) : r * h ^ 2 = 0 := by
  obtain ⟨k, hk⟩ := kernel_eq_smul_gen (2 * r) h hh
  rw [hk, gcd_shift_phase_smul, hphase, mul_zero]

/-- **Residual sum is the full kernel count in the residual case.**  When `r·t₀² = 0`
    every term of the Weyl residual sum is `ψ(0) = 1`, so
    `Σ_{h:2rh=0} ψ(−r·h²) = #{h : 2rh = 0}`. -/
private theorem residual_sum_eq_card_of_gcd_phase_zero {N : ℕ} [NeZero N] {r : ZMod N}
    (hphase : r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) ^ 2 = 0) :
    (Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0)).sum (fun h => ψ (-(r * h ^ 2)))
      = ((Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0)).card : ℂ) := by
  have hterm : ∀ h ∈ Finset.univ.filter (fun h : ZMod N => 2 * r * h = 0),
      ψ (-(r * h ^ 2)) = 1 := by
    intro h hh
    have hz : r * h ^ 2 = 0 :=
      residual_phase_zero_of_gcd_phase_zero hphase (Finset.mem_filter.mp hh).2
    rw [hz, neg_zero, psi_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Maximal magnitude in the residual case.**  If `r·t₀² = 0` then
    `‖G(r)‖² = N · gcd((2r).val, N)` — the maximum allowed by `sqGaussSum_normSq_le_gcd`.
    Every residual phase is trivial, so the Weyl residual sum is the full kernel count `g`. -/
theorem sqGaussSum_normSq_eq_gcd_of_gcd_phase_zero {N : ℕ} [NeZero N] {r : ZMod N}
    (hphase : r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) ^ 2 = 0) :
    ‖sqGaussSum r‖ ^ 2 = (N : ℝ) * (Nat.gcd (2 * r).val N : ℝ) := by
  have hid := sqGaussSum_mul_conj r
  rw [residual_sum_eq_card_of_gcd_phase_zero hphase, kernel_card_eq_gcd (2 * r)] at hid
  have hGsq : (↑(‖sqGaussSum r‖ ^ 2) : ℂ) = sqGaussSum r * starRingEnd ℂ (sqGaussSum r) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hid] at hGsq
  exact_mod_cast hGsq

/-- **The residual case never vanishes.**  If `r·t₀² = 0` then `‖G(r)‖² = N·g > 0`, so
    `G(r) ≠ 0`.  This is the exact converse of `sqGaussSum_eq_zero_of_gcd_shift`. -/
theorem sqGaussSum_ne_zero_of_gcd_phase_zero {N : ℕ} [NeZero N] {r : ZMod N}
    (hphase : r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) ^ 2 = 0) :
    sqGaussSum r ≠ 0 := by
  intro h0
  have hpos : (0 : ℝ) < (N : ℝ) * (Nat.gcd (2 * r).val N : ℝ) := by
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hg : (0 : ℝ) < (Nat.gcd (2 * r).val N : ℝ) := by
      exact_mod_cast Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hmag := sqGaussSum_normSq_eq_gcd_of_gcd_phase_zero hphase
  rw [h0, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hmag
  exact (ne_of_lt hpos) hmag

/-- **Exact decidable vanishing characterisation.**  The quadratic Gauss sum vanishes at
    frequency `r` *iff* the single canonical phase `r·t₀²` (with
    `t₀ = N / gcd((2r).val, N)`) is nonzero:

        `G(r) = 0  ↔  r · (N / gcd((2r).val, N))² ≠ 0`.

    Backward is the shift criterion `sqGaussSum_eq_zero_of_gcd_shift`; forward is the
    residual maximality `sqGaussSum_ne_zero_of_gcd_phase_zero` (if the phase is `0`,
    `‖G(r)‖² = N·g > 0`).  A closed-form `gcd`-plus-multiply test — `decide`-able at any
    concrete modulus — completely deciding quadratic-Gauss-sum vanishing. -/
theorem sqGaussSum_eq_zero_iff_gcd_shift {N : ℕ} [NeZero N] (r : ZMod N) :
    sqGaussSum r = 0 ↔ r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) ^ 2 ≠ 0 := by
  constructor
  · intro h0
    by_contra hphase
    exact sqGaussSum_ne_zero_of_gcd_phase_zero hphase h0
  · exact sqGaussSum_eq_zero_of_gcd_shift

/-- **Vanishing iff some shift certifies it (completeness of the shift method).**  Chaining
    the exact characterisation with the shift-reachability iff `exists_vanishing_shift_iff`,
    `G(r) = 0` holds *exactly* when some shift `t` satisfies the vanishing hypotheses
    `2rt = 0 ∧ r·t² ≠ 0`.  The elementary shift method therefore certifies *every* vanishing
    of the quadratic Gauss sum — there is no undetected vanishing frequency. -/
theorem sqGaussSum_eq_zero_iff_exists_shift {N : ℕ} [NeZero N] (r : ZMod N) :
    sqGaussSum r = 0 ↔ ∃ t : ZMod N, 2 * r * t = 0 ∧ r * t ^ 2 ≠ 0 := by
  rw [sqGaussSum_eq_zero_iff_gcd_shift r]
  exact (exists_vanishing_shift_iff r).symm

/-- The exact characterisation decides the concrete witnesses with no shift supplied:
    `G(4) = 0` in `ℤ/24ℤ` (canonical phase `4·3² = 12 ≠ 0` fires the vanishing branch). -/
example : sqGaussSum (4 : ZMod 24) = 0 :=
  (sqGaussSum_eq_zero_iff_gcd_shift 4).mpr (by decide)

/-- Dually, the exact characterisation *certifies non-vanishing*: `G(2) ≠ 0` in `ℤ/8ℤ`,
    a residual frequency (`2·2² = 8 ≡ 0`) where the maximal magnitude `‖G(2)‖² = 8·4 = 32`
    forbids vanishing — the shift method's blind spot is genuinely a non-vanishing one. -/
example : sqGaussSum (2 : ZMod 8) ≠ 0 :=
  sqGaussSum_ne_zero_of_gcd_phase_zero (by decide)

/-!
### Part XVI — The elementary gcd-sum input is subquadratic (`o(N²)`)

Part XV reduced the composite-`N` circle-method density bound to a purely
arithmetic estimate on `Σ_{r≠0} gcd((2r).val, N)`.  This subsection discharges
that estimate unconditionally, with *no* Gauss-sum reciprocity, via Pillai's
divisor-sum identity and the elementary divisor bound `d(N) ≤ 2√N`:

    Σ_{r<N} gcd(N,r) = Σ_{d∣N} d·φ(N/d) ≤ N·d(N) ≤ 2·N·⌊√N⌋ = o(N²),

and hence, after the `r ↦ 2r` doubling bound `gcd(2x,N) ≤ 2·gcd(x,N)`,

    Σ_{r≠0} gcd((2r).val, N) ≤ 4·N·⌊√N⌋,    Σ_{r≠0} ‖G(r)‖² ≤ 4·N²·⌊√N⌋.
-/

/-- **Pillai's gcd-sum identity.**  Summing `gcd N r` over a complete residue
system `r ∈ {0,…,N-1}` groups the terms by the divisor `d = gcd N r ∣ N`; the
fiber `{r < N : gcd N r = d}` has exactly `φ(N/d)` elements
(`Nat.totient_div_of_dvd`), so `Σ_{r<N} gcd(N,r) = Σ_{d∣N} d·φ(N/d)`. -/
theorem gcd_sum_pillai (N : ℕ) :
    ∑ r ∈ Finset.range N, Nat.gcd N r = ∑ d ∈ N.divisors, d * Nat.totient (N / d) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Finset.sum_fiberwise_of_maps_to (t := N.divisors) (g := fun r => Nat.gcd N r)
      (f := fun r => Nat.gcd N r) ?_]
  · refine Finset.sum_congr rfl fun d hd => ?_
    have hdvd : d ∣ N := Nat.dvd_of_mem_divisors hd
    have hcard : (Finset.filter (fun r => Nat.gcd N r = d) (Finset.range N)).card
        = Nat.totient (N / d) := (Nat.totient_div_of_dvd hdvd).symm
    calc ∑ r ∈ Finset.filter (fun r => Nat.gcd N r = d) (Finset.range N), Nat.gcd N r
        = ∑ _r ∈ Finset.filter (fun r => Nat.gcd N r = d) (Finset.range N), d := by
          refine Finset.sum_congr rfl fun r hr => (Finset.mem_filter.mp hr).2
      _ = (Finset.filter (fun r => Nat.gcd N r = d) (Finset.range N)).card * d := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = d * Nat.totient (N / d) := by rw [hcard, Nat.mul_comm]
  · intro r _
    rw [Nat.mem_divisors]
    exact ⟨Nat.gcd_dvd_left N r, hN.ne'⟩

/-- **Elementary upper bound.**  Since `φ(N/d) ≤ N/d` and `d·(N/d) = N` for `d ∣ N`,
every Pillai term is `≤ N`, so `Σ_{r<N} gcd(N,r) ≤ N·d(N)`. -/
theorem gcd_sum_le_card_divisors_mul (N : ℕ) :
    ∑ r ∈ Finset.range N, Nat.gcd N r ≤ N * N.divisors.card := by
  rw [gcd_sum_pillai, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  have hdvd : d ∣ N := Nat.dvd_of_mem_divisors hd
  have hle : d * Nat.totient (N / d) ≤ d * (N / d) :=
    Nat.mul_le_mul_left d (Nat.totient_le _)
  calc d * Nat.totient (N / d) ≤ d * (N / d) := hle
    _ = N := Nat.mul_div_cancel' hdvd
    _ = N * 1 := (Nat.mul_one N).symm

/-- **Divisor-count bound.**  Divisors of `N` pair up as `(d, N/d)`; the smaller
member of each pair is `≤ √N`, and the reflection `d ↦ N/d` injects the large
divisors into the small ones, so `d(N) = #{d ∣ N} ≤ 2·⌊√N⌋`. -/
theorem card_divisors_le_two_mul_sqrt (N : ℕ) :
    N.divisors.card ≤ 2 * Nat.sqrt N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set s := Nat.sqrt N with hs
  set A := N.divisors.filter (fun d => d ≤ s) with hA
  set B := N.divisors.filter (fun d => ¬ d ≤ s) with hB
  have hsplit : A.card + B.card = N.divisors.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  have hAle : A.card ≤ s := by
    calc A.card ≤ (Finset.Icc 1 s).card := by
          apply Finset.card_le_card
          intro d hd
          rw [hA, Finset.mem_filter] at hd
          rw [Finset.mem_Icc]
          exact ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩
      _ = s := by rw [Nat.card_Icc]; omega
  have hBle : B.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun d => N / d)
    · intro d hd
      simp only [Finset.mem_coe, hB, Finset.mem_filter] at hd
      obtain ⟨hdD, hdgt⟩ := hd
      have hddvd : d ∣ N := Nat.dvd_of_mem_divisors hdD
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hdD
      have hdgt' : s + 1 ≤ d := by omega
      simp only [Finset.mem_coe, hA, Finset.mem_filter]
      refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hddvd, hN.ne'⟩, ?_⟩
      have hlt : N / d < s + 1 := by
        rw [Nat.div_lt_iff_lt_mul hdpos]
        calc N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
          _ ≤ (s + 1) * d := by gcongr
      omega
    · intro d1 h1 d2 h2 heq
      simp only [Finset.mem_coe, hB, Finset.mem_filter] at h1 h2
      have hd1 : d1 ∣ N := Nat.dvd_of_mem_divisors h1.1
      have hd2 : d2 ∣ N := Nat.dvd_of_mem_divisors h2.1
      have e1 : N / (N / d1) = d1 := Nat.div_div_self hd1 hN.ne'
      have e2 : N / (N / d2) = d2 := Nat.div_div_self hd2 hN.ne'
      have heq' : N / d1 = N / d2 := heq
      rw [← e1, ← e2, heq']
  omega

/-- **Subquadratic gcd sum.**  Combining Pillai's identity `Σ gcd ≤ N·d(N)` with
`d(N) ≤ 2√N` gives `Σ_{r<N} gcd(N,r) ≤ 2·N·⌊√N⌋`, which is `o(N²)`. -/
theorem gcd_sum_le_two_mul_N_mul_sqrt (N : ℕ) :
    ∑ r ∈ Finset.range N, Nat.gcd N r ≤ 2 * N * Nat.sqrt N := by
  calc ∑ r ∈ Finset.range N, Nat.gcd N r
      ≤ N * N.divisors.card := gcd_sum_le_card_divisors_mul N
    _ ≤ N * (2 * Nat.sqrt N) := Nat.mul_le_mul_left N (card_divisors_le_two_mul_sqrt N)
    _ = 2 * N * Nat.sqrt N := by ring

/-- `ZMod.val` is a bijection `ZMod N → {0,…,N-1}`, transporting the gcd sum. -/
theorem gcd_val_sum_eq_range {N : ℕ} [NeZero N] :
    ∑ s : ZMod N, Nat.gcd (ZMod.val s) N = ∑ k ∈ Finset.range N, Nat.gcd k N := by
  apply Finset.sum_nbij' (i := fun s : ZMod N => ZMod.val s) (j := fun k : ℕ => (k : ZMod N))
  · intro s _; simp only [Finset.mem_range]; exact ZMod.val_lt s
  · intro k _; exact Finset.mem_univ _
  · intro s _; exact ZMod.natCast_zmod_val s
  · intro k hk; simp only [Finset.mem_range] at hk; exact ZMod.val_natCast_of_lt hk
  · intro s _; rfl

/-- `gcd(2x, N) ≤ 2·gcd(x, N)`: a common divisor of `2x` and `N` divides `2N`,
so it divides `gcd(2x,2N) = 2·gcd(x,N)`. -/
theorem gcd_two_mul_le {x N : ℕ} (hN : 0 < N) :
    Nat.gcd (2 * x) N ≤ 2 * Nat.gcd x N := by
  have hdvd : Nat.gcd (2 * x) N ∣ 2 * Nat.gcd x N := by
    rw [← Nat.gcd_mul_left 2 x N]
    exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
      ((Nat.gcd_dvd_right (2 * x) N).trans (dvd_mul_left N 2))
  have hpos : 0 < 2 * Nat.gcd x N := by
    have := Nat.gcd_pos_of_pos_right x hN; omega
  exact Nat.le_of_dvd hpos hdvd

/-- Pointwise doubling bound in `ZMod N`: `gcd((2r).val, N) ≤ 2·gcd(r.val, N)`,
since `(2r).val ≡ 2·r.val [MOD N]` and gcd is `mod N`-invariant. -/
theorem gcd_two_val_le {N : ℕ} [NeZero N] (r : ZMod N) :
    Nat.gcd (2 * r).val N ≤ 2 * Nat.gcd r.val N := by
  have hpos : 0 < N := NeZero.pos N
  have hcast : (2 * r : ZMod N) = ((2 * r.val : ℕ) : ZMod N) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
  have hval : (2 * r).val = (2 * r.val) % N := by
    rw [hcast, ZMod.val_natCast]
  rw [hval]
  have hmod : Nat.gcd ((2 * r.val) % N) N = Nat.gcd (2 * r.val) N := by
    rw [← Nat.gcd_rec N (2 * r.val), Nat.gcd_comm]
  rw [hmod]
  exact gcd_two_mul_le hpos

/-- **Second-moment gcd input, fully evaluated.**  The frequency sum controlling
the composite-`N` circle-method bound is subquadratic (`o(N²)`):

    Σ_{r≠0} gcd((2r).val, N) ≤ 4·N·⌊√N⌋. -/
theorem gcd_two_shift_sum_le {N : ℕ} [NeZero N] :
    ∑ r ∈ (Finset.univ \ {(0 : ZMod N)}), Nat.gcd (2 * r).val N ≤ 4 * N * Nat.sqrt N := by
  calc ∑ r ∈ (Finset.univ \ {(0 : ZMod N)}), Nat.gcd (2 * r).val N
      ≤ ∑ r : ZMod N, Nat.gcd (2 * r).val N :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ ∑ r : ZMod N, 2 * Nat.gcd r.val N :=
        Finset.sum_le_sum (fun r _ => gcd_two_val_le r)
    _ = 2 * ∑ r : ZMod N, Nat.gcd r.val N := by rw [Finset.mul_sum]
    _ = 2 * ∑ k ∈ Finset.range N, Nat.gcd k N := by rw [gcd_val_sum_eq_range]
    _ = 2 * ∑ k ∈ Finset.range N, Nat.gcd N k := by
        rw [Finset.sum_congr rfl (fun k _ => Nat.gcd_comm k N)]
    _ ≤ 2 * (2 * N * Nat.sqrt N) :=
        Nat.mul_le_mul_left 2 (gcd_sum_le_two_mul_N_mul_sqrt N)
    _ = 4 * N * Nat.sqrt N := by ring

/-- **Explicit unconditional second moment.**  Feeding the subquadratic gcd bound
`gcd_two_shift_sum_le` into `sqGaussSum_normSq_sum_le_gcd_sum` (`Σ‖G‖² ≤ N·Σgcd`)
gives an explicit `o(N³)` second moment for *every* modulus `N`, with no odd/prime
restriction and no Gauss-sum reciprocity:

    Σ_{r≠0} ‖G(r)‖² ≤ 4·N²·⌊√N⌋.

Chained with the L²-averaged density bound `sqDiffFree_density_bound_l2`, this makes
the composite-`N` circle-method error term fully explicit and unconditional. -/
theorem sqGaussSum_normSq_sum_le_sqrt {N : ℕ} [NeZero N] :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ 2)
      ≤ 4 * (N : ℝ) ^ 2 * Nat.sqrt N := by
  have hcast : (Finset.univ \ {(0 : ZMod N)}).sum (fun r => (Nat.gcd (2 * r).val N : ℝ))
      ≤ ((4 * N * Nat.sqrt N : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast gcd_two_shift_sum_le
  calc (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ 2)
      ≤ (N : ℝ) * (Finset.univ \ {(0 : ZMod N)}).sum
          (fun r => (Nat.gcd (2 * r).val N : ℝ)) := sqGaussSum_normSq_sum_le_gcd_sum
    _ ≤ (N : ℝ) * ((4 * N * Nat.sqrt N : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg N)
    _ = 4 * (N : ℝ) ^ 2 * Nat.sqrt N := by push_cast; ring

/-! ### Part XVII — Exact second moment at a prime modulus: the L² direction is capped

Parts XV–XVI drive the composite-`N` circle-method error through an *upper* bound
on the second moment `Σ_{r≠0} ‖G(r)‖²` (culminating in `≤ 4N²⌊√N⌋`).  A natural
hope is that this second moment is `o(N²)`, which would push the L²-averaged
density bound `sqDiffFree_density_bound_l2` down to the `o(N)` Sárközy density.

This subsection proves that hope is **false**: at an odd-prime modulus the second
moment is computed *exactly* and equals `N² − N = Θ(N²)`.  So the L²-averaged
direction can never reach `o(N²)`, and the per-frequency `√N` cancellation it
averages away must instead be used *pointwise* — exactly what
`sqDiffFree_density_bound_of_prime` does.  This is an honest cap on Parts XV–XVI,
not a further tightening of them.
-/

/-- **Exact second moment at an odd-prime modulus (Plancherel identity).**
For `N` an odd prime, `ZMod N` is a field, so every nonzero frequency `r` is a
unit and `2r` is a unit (`2` is a unit mod an odd prime).  Hence `‖G(r)‖² = N`
*exactly* at each of the `N − 1` nonzero frequencies:

    Σ_{r≠0} ‖G(r)‖² = (N − 1)·N = N² − N.

This is an exact equality — simultaneously an upper *and a lower* bound — so it
shows the `o(N²)` second-moment target implicit in the L²-averaged circle method
(Parts XV–XVI) is unreachable: the second moment is `Θ(N²)`, never `o(N²)`. -/
theorem sqGaussSum_normSq_sum_eq_of_prime {N : ℕ} [NeZero N] (hp : N.Prime) (hN2 : N ≠ 2) :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ 2) = (N : ℝ) ^ 2 - N := by
  haveI := Fact.mk hp
  have h2 : IsUnit (2 : ZMod N) := by
    have hcast : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_cast
    rw [← hcast, ZMod.isUnit_iff_coprime]
    have hmod : N % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hN2)
    have hnd : ¬ (2 ∣ N) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
  have hconst : ∀ r ∈ (Finset.univ \ {(0 : ZMod N)}), ‖sqGaussSum r‖ ^ 2 = (N : ℝ) := by
    intro r hr
    have hr0 : r ≠ 0 := Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hr).2
    exact sqGaussSum_normSq_eq_of_isUnit (h2.mul (isUnit_iff_ne_zero.mpr hr0))
  have hcard : (Finset.univ \ {(0 : ZMod N)}).card = N - 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Finset.card_singleton,
      ZMod.card]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, nsmul_eq_mul]
  have hN1 : 1 ≤ N := hp.pos
  rw [Nat.cast_sub hN1]
  push_cast
  ring

/-- **The L²-averaged minor-arc factor does not decay (prime modulus).**
`√(Σ_{r≠0} ‖G(r)‖²) ≥ N − 1`, so the second-moment input to the L²-averaged
density bound `sqDiffFree_density_bound_l2` is `Θ(N)` at a prime modulus and
cannot furnish the `o(N)` Sárközy density on its own — only the pointwise `√N`
magnitude (`sqDiffFree_density_bound_of_prime`) can. -/
theorem sqGaussSum_l2_factor_ge_of_prime {N : ℕ} [NeZero N] (hp : N.Prime) (hN2 : N ≠ 2) :
    (N : ℝ) - 1 ≤
      Real.sqrt ((Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ 2)) := by
  rw [sqGaussSum_normSq_sum_eq_of_prime hp hN2]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hp.pos
  have h0 : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have hsq : ((N : ℝ) - 1) ^ 2 ≤ (N : ℝ) ^ 2 - N := by nlinarith
  calc (N : ℝ) - 1 = Real.sqrt (((N : ℝ) - 1) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt ((N : ℝ) ^ 2 - N) := Real.sqrt_le_sqrt hsq

/-! ### Part XVIII — The quantitative Sárközy cardinality bound at a prime modulus

Parts VII–XVII assemble the circle-method *inequality*
`|A|² ≤ |A|·#{n²=0} + N⁻¹·M·(|A|·N − |A|²)` (`sqDiffFree_density_bound`) and
discharge its sole analytic input `M` at a prime with the exact Weyl magnitude
`‖G(r)‖ = √N` (`sqDiffFree_density_bound_of_prime`).  What was still missing is
the step that turns that quadratic inequality into the statement a reader wants:
the **explicit cardinality bound**.  Solving the inequality for `|A|` — where the
`−N⁻¹·M·|A|²` term (the gain a crude `M·|A|` bound throws away) is exactly what
sharpens the estimate — collapses it to

    |A| ≤ √N.

This is the sharp-up-to-constant quantitative Sárközy theorem for
square-difference-free sets in the prime field `ℤ/Nℤ`: such a set has at most `√N`
elements, hence density `|A|/N ≤ 1/√N → 0`.  Equivalently it is the classical
**independence-number bound `α(Paley) ≤ √p`** for the Paley graph (whose edges join
`x, y` with `x − y` a nonzero square): a square-difference-free set is exactly an
independent set, and the same quadratic-Gauss-sum / eigenvalue input caps it at
`√p`.  This is the honest capstone of the prime branch — the pointwise `√N`
magnitude is precisely strong enough to yield `o(N)` density, unlike the `Θ(N)`
second-moment (Part XVII) or `N/√2` sup-norm (Part XI) routes, which cannot. -/

/-- **Quantitative Sárközy at a prime modulus: `|A| ≤ √N`.**  For an odd prime `N`,
    any square-difference-free `A ⊆ ℤ/Nℤ` (no `x, x + n²` both in `A` with `n² ≠ 0`)
    satisfies `|A| ≤ √N`.  This solves the circle-method inequality
    `sqDiffFree_density_bound_of_prime` for `|A|`: with the exact prime magnitude
    `M = √N` and `#{n : n² = 0} = 1` (a field has no nonzero nilpotents), the
    inequality `|A|²·(1 + 1/√N) ≤ |A|·(1 + √N)` divides down to `|A| ≤ √N`.  This is
    the independence-number bound `α(Paley graph) ≤ √p`.  0 axioms. -/
theorem sqDiffFree_card_le_sqrt_of_prime {N : ℕ} [NeZero N] (hp : N.Prime) (hN2 : N ≠ 2)
    (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) ≤ Real.sqrt N := by
  haveI := Fact.mk hp
  -- (1) A prime field has exactly one square root of `0`, namely `0`.
  have hc1 : (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card = 1 := by
    have hset : (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)) = {0} := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact sq_eq_zero_iff.mp h
      · rintro rfl; ring
    rw [hset, Finset.card_singleton]
  -- (2) The circle-method inequality with `M = √N` and the count `#{n²=0} = 1`.
  have hden := sqDiffFree_density_bound_of_prime hp hN2 A hfree
  rw [hc1] at hden
  push_cast at hden
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hp.pos
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  set a : ℝ := (A.card : ℝ) with ha
  set t : ℝ := Real.sqrt N with ht
  have htpos : (0 : ℝ) < t := Real.sqrt_pos.mpr hNpos
  have hts : t ^ 2 = N := Real.sq_sqrt (le_of_lt hNpos)
  have ha0 : (0 : ℝ) ≤ a := by positivity
  -- (3) Clear `N⁻¹` by multiplying through by `N`, then substitute `N = (√N)²`.
  have hmulN := mul_le_mul_of_nonneg_right hden (le_of_lt hNpos)
  have hexp : (a * 1 + (N : ℝ)⁻¹ * (t * (a * N - a ^ 2))) * N
      = a * N + t * (a * N - a ^ 2) := by
    field_simp
  have key : a ^ 2 * (N : ℝ) ≤ a * N + t * (a * N - a ^ 2) := by
    rw [hexp] at hmulN; exact hmulN
  have keyS : a ^ 2 * t ^ 2 ≤ a * t ^ 2 + t * (a * t ^ 2 - a ^ 2) := by
    rw [hts]; exact key
  -- (4) `a·t·(1+t)·(a − t) ≤ 0` with `a·t·(1+t) > 0` forces `a ≤ t`.
  rcases eq_or_lt_of_le ha0 with h0 | hapos
  · rw [← h0]; exact le_of_lt htpos
  · have hp3 : (0 : ℝ) < a * t * (1 + t) := mul_pos (mul_pos hapos htpos) (by linarith)
    nlinarith [keyS, hp3, hapos, htpos]

/-- **Square-difference-free density decay at a prime modulus: `|A|/N ≤ 1/√N`.**
    The immediate density consequence of the cardinality bound
    `sqDiffFree_card_le_sqrt_of_prime`: a square-difference-free set in the prime
    field `ℤ/Nℤ` has density at most `(√N)⁻¹`, which tends to `0` as `N → ∞`.  This
    is Sárközy's `o(1)` density conclusion, made fully explicit and unconditional in
    the prime case. -/
theorem sqDiffFree_density_le_of_prime {N : ℕ} [NeZero N] (hp : N.Prime) (hN2 : N ≠ 2)
    (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) / N ≤ (Real.sqrt N)⁻¹ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hp.pos
  set t : ℝ := Real.sqrt N with ht
  have htpos : (0 : ℝ) < t := Real.sqrt_pos.mpr hNpos
  have hts : t * t = N := Real.mul_self_sqrt (le_of_lt hNpos)
  have h : (A.card : ℝ) ≤ t := sqDiffFree_card_le_sqrt_of_prime hp hN2 A hfree
  rw [div_le_iff₀ hNpos, ← hts, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt htpos), one_mul]
  exact h

/-! ### Part XIX — The master explicit cardinality bound (any Weyl sup-norm `M`)

Parts VII–XVIII derive, for *every* modulus, the circle-method **inequality**
`|A|² ≤ |A|·c + N⁻¹·M·(|A|·N − |A|²)` (`sqDiffFree_density_bound`, with
`c = #{n : n² = 0}` and any Weyl sup-norm `M ≥ ‖G(r)‖`) and, at a prime, solve it
*by hand* for `|A| ≤ √N` (`sqDiffFree_card_le_sqrt_of_prime`).  That final
"solve the quadratic for `|A|`" step is not special to the prime value `M = √N`:
for **any** admissible sup-norm `M ≥ 0` the same algebra collapses to one closed form

    |A|·(N + M) ≤ N·(c + M),     i.e.   |A| ≤ N·(c + M)/(N + M).

This section extracts that step as a standalone lemma (`sqDiffFree_card_le_of_supNorm`)
plus its division form, then reads off two instances:

  * the **sharp prime bound** `√N` (`M = √N`, `c = 1`): the master lemma *is* the
    prime capstone — `sqDiffFree_card_le_sqrt_of_prime_via_master` is one substitution;
  * the first **explicit all-`N` cardinality bound**, with the unconditional sup-norm
    `M = N/√2` (`sqDiffFree_card_le_of_ne_zero`): honest but quantitatively weak
    (`N + N/√2 = Θ(N)`, so it does **not** force `|A| = o(N)`), the cardinality-level
    counterpart of the density inequality `sqDiffFree_density_bound_of_ne_zero`.

The value is *reusability*: any future sharper sup-norm `M = o(N)` on a class of
moduli plugs straight into `sqDiffFree_card_le_of_supNorm` to yield `|A| = o(N)`
Sárközy on that class with no further algebra.  0 axioms. -/

/-- **Master explicit cardinality bound from a Weyl sup-norm.**  If every nonzero
    frequency satisfies `‖G(r)‖ ≤ M` (with `M ≥ 0`) and `A` is square-difference-free,
    then solving the circle-method inequality `sqDiffFree_density_bound` for `|A|`
    gives the closed form

    `|A|·(N + M) ≤ N·(#{n : n² = 0} + M)`.

    The `−N⁻¹·M·|A|²` term a crude `M·|A|` bound throws away is exactly the gain that
    makes the right-hand side sub-`M`.  Dividing by `N + M > 0` gives
    `|A| ≤ N·(c + M)/(N + M)` (`sqDiffFree_card_le_of_supNorm_div`).  Substituting
    `M = √N`, `c = 1` collapses the bound to `√N`, recovering the prime capstone. -/
theorem sqDiffFree_card_le_of_supNorm {N : ℕ} [NeZero N] {M : ℝ} (hM : 0 ≤ M)
    (A : Finset (ZMod N))
    (hG : ∀ r : ZMod N, r ≠ 0 → ‖sqGaussSum r‖ ≤ M)
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) * ((N : ℝ) + M)
      ≤ (N : ℝ) * (((Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card : ℝ) + M) := by
  have hden := sqDiffFree_density_bound A hG hfree
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set a : ℝ := (A.card : ℝ) with ha
  set c : ℝ := ((Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card : ℝ) with hc
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hc0 : (0 : ℝ) ≤ c := by positivity
  -- Clear `N⁻¹` by multiplying the inequality through by `N`.
  have hmulN := mul_le_mul_of_nonneg_right hden (le_of_lt hNpos)
  have hexp : (a * c + (N : ℝ)⁻¹ * (M * (a * N - a ^ 2))) * N
      = a * c * N + M * (a * N - a ^ 2) := by field_simp
  have key : a ^ 2 * N ≤ a * c * N + M * (a * N - a ^ 2) := by
    rw [hexp] at hmulN; exact hmulN
  -- Rearrange to `a²·(N+M) ≤ a·(N·(c+M))`, then cancel one factor of `a`.
  have hbase : a ^ 2 * ((N : ℝ) + M) ≤ a * ((N : ℝ) * (c + M)) := by nlinarith [key]
  rcases eq_or_lt_of_le ha0 with h0 | hapos
  · rw [← h0, zero_mul]
    exact mul_nonneg (le_of_lt hNpos) (by linarith)
  · nlinarith [hbase, hapos]

/-- **Division form of the master cardinality bound: `|A| ≤ N·(c + M)/(N + M)`.**
    The explicit closed-form solution of the circle-method inequality for any Weyl
    sup-norm `M ≥ 0`. -/
theorem sqDiffFree_card_le_of_supNorm_div {N : ℕ} [NeZero N] {M : ℝ} (hM : 0 ≤ M)
    (A : Finset (ZMod N))
    (hG : ∀ r : ZMod N, r ≠ 0 → ‖sqGaussSum r‖ ≤ M)
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ)
      ≤ (N : ℝ) * (((Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card : ℝ) + M)
          / ((N : ℝ) + M) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNM : (0 : ℝ) < (N : ℝ) + M := by linarith
  rw [le_div_iff₀ hNM]
  exact sqDiffFree_card_le_of_supNorm hM A hG hfree

/-- **The master lemma subsumes the prime capstone `|A| ≤ √N`.**  Instantiating
    `sqDiffFree_card_le_of_supNorm` at the exact prime magnitude `M = √N` and the
    field count `c = 1` (a prime field has a unique square root of `0`) collapses the
    right-hand side `N·(1 + √N)/(N + √N)` to `√N`.  This re-derives
    `sqDiffFree_card_le_sqrt_of_prime` through the general lemma — evidence the
    abstraction is faithful and sharp. -/
theorem sqDiffFree_card_le_sqrt_of_prime_via_master {N : ℕ} [NeZero N] (hp : N.Prime)
    (hN2 : N ≠ 2) (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) ≤ Real.sqrt N := by
  haveI := Fact.mk hp
  have hc1 : (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card = 1 := by
    have hset : (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)) = {0} := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => sq_eq_zero_iff.mp h, fun h => by rw [h]; ring⟩
    rw [hset, Finset.card_singleton]
  have hmaster := sqDiffFree_card_le_of_supNorm (Real.sqrt_nonneg (N : ℝ)) A
    (fun _ hr => le_of_eq (sqGaussSum_norm_eq_sqrt_of_prime hp hN2 hr)) hfree
  rw [hc1] at hmaster
  push_cast at hmaster
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hp.pos
  set a : ℝ := (A.card : ℝ) with ha
  set t : ℝ := Real.sqrt N with ht
  have htpos : (0 : ℝ) < t := Real.sqrt_pos.mpr hNpos
  have hts : t ^ 2 = N := Real.sq_sqrt (le_of_lt hNpos)
  -- `hmaster : a·(N + t) ≤ N·(1 + t)`; substitute `N = t²` and cancel `t·(t+1) > 0`.
  rw [← hts] at hmaster
  have hfac : a * (t * (t + 1)) ≤ t * (t * (t + 1)) := by nlinarith [hmaster]
  exact le_of_mul_le_mul_right hfac (mul_pos htpos (by linarith))

/-- **Explicit cardinality bound at every modulus (unconditional in `N`).**  The
    master lemma fed by the all-`N` Weyl sup-norm `M = √(N²/2) = N/√2`
    (`sqGaussSum_norm_le_of_ne_zero`): a square-difference-free `A ⊆ ℤ/Nℤ` satisfies

    `|A|·(N + N/√2) ≤ N·(#{n : n² = 0} + N/√2)`.

    This is the first explicit *cardinality*-level statement valid for all moduli
    (the composite branch had only the density inequality
    `sqDiffFree_density_bound_of_ne_zero`).  Honesty note: `N/√2 = Θ(N)`, so both
    sides are `Θ(N²)` and this does **not** give `|A| = o(N)`; a sharper sub-`N`
    sup-norm on a class of moduli would, via `sqDiffFree_card_le_of_supNorm`. -/
theorem sqDiffFree_card_le_of_ne_zero {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) * ((N : ℝ) + Real.sqrt ((N : ℝ) ^ 2 / 2))
      ≤ (N : ℝ) * (((Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card : ℝ)
          + Real.sqrt ((N : ℝ) ^ 2 / 2)) :=
  sqDiffFree_card_le_of_supNorm (Real.sqrt_nonneg _) A
    (fun _ hr => sqGaussSum_norm_le_of_ne_zero hr) hfree

/-! ### Part XX — Exact second moment at *every* odd modulus (Plancherel via Pillai)

Part XVII computed the second moment `Σ_{r≠0} ‖G(r)‖²` *exactly* at an odd **prime**
modulus (`= N² − N`), using that a prime turns `ZMod N` into a field so every nonzero
frequency is a unit and `‖G(r)‖² = N` exactly.  This subsection removes the primality
hypothesis: at *any* odd modulus the residual Weyl phase is trivial (`2` is a unit, so
`2rh = 0 ⟹ rh = 0 ⟹ rh² = 0`), giving the exact per-frequency magnitude
`‖G(r)‖² = N·gcd((2r).val, N)`.  Summing and reindexing by the bijection `r ↦ 2r`
(again `2` a unit) collapses the frequency gcd-sum to Pillai's divisor sum:

    Σ_{r≠0} ‖G(r)‖² = N · (Σ_{k<N} gcd(N,k) − N) = N · (Σ_{d∣N} d·φ(N/d) − N).

At `N = p` prime this is `N·((2p−1) − p) = p² − p`, recovering Part XVII.  This is an
exact equality for *all* odd `N`, so it simultaneously sharpens the Part XVI upper
bound `≤ 4N²⌊√N⌋` and extends the Part XVII `Θ(N²)` cap on the L²-averaged circle
method from primes to every odd modulus. -/

/-- **Exact per-frequency magnitude at an odd modulus.**  For `N` odd, `2` is a unit in
`ZMod N`; the kernel generator `t₀ = N/gcd((2r).val, N)` satisfies `2r·t₀ = 0`
(`two_mul_kernel_gen_eq_zero`), so cancelling the unit `2` gives `r·t₀ = 0` and hence the
canonical residual phase `r·t₀² = 0`.  Feeding this into
`sqGaussSum_normSq_eq_gcd_of_gcd_phase_zero` yields the maximal (uncancelled) value

    `‖G(r)‖² = N · gcd((2r).val, N)`

at *every* frequency `r` (including `r = 0`, where both sides are `N²`). -/
theorem sqGaussSum_normSq_eq_gcd_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (r : ZMod N) :
    ‖sqGaussSum r‖ ^ 2 = (N : ℝ) * (Nat.gcd (2 * r).val N : ℝ) := by
  apply sqGaussSum_normSq_eq_gcd_of_gcd_phase_zero
  have h2 : IsUnit (2 : ZMod N) := by
    have hcast : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_cast
    rw [← hcast, ZMod.isUnit_iff_coprime]
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hodd
    have hnd : ¬ (2 ∣ N) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
  have hk : (2 : ZMod N) * (r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N)) = 0 := by
    rw [← mul_assoc]; exact two_mul_kernel_gen_eq_zero r
  have hrt : r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) = 0 := (h2.mul_right_eq_zero).mp hk
  have hexp : r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) ^ 2
      = (r * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N))
          * ((N / Nat.gcd (2 * r).val N : ℕ) : ZMod N) := by ring
  rw [hexp, hrt, zero_mul]

/-- **Second moment as an exact frequency gcd-sum (odd modulus).**  Summing the exact
per-frequency magnitude `sqGaussSum_normSq_eq_gcd_of_odd` over the nonzero frequencies
turns the second moment into an *equality* (not the Part XV inequality
`sqGaussSum_normSq_sum_le_gcd_sum`):

    Σ_{r≠0} ‖G(r)‖² = N · Σ_{r≠0} gcd((2r).val, N). -/
theorem sqGaussSum_normSq_sum_eq_gcd_sum_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ 2)
      = (N : ℝ) * (Finset.univ \ {(0 : ZMod N)}).sum
          (fun r => (Nat.gcd (2 * r).val N : ℝ)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => sqGaussSum_normSq_eq_gcd_of_odd hodd r)

/-- **Doubling reindex (odd modulus).**  For `N` odd, `2` is a unit, so `r ↦ 2r` is a
bijection of `ZMod N`.  Reindexing the frequency gcd-sum along it and transporting
`ZMod.val` to a range sum (`gcd_val_sum_eq_range`) gives

    Σ_{r : ZMod N} gcd((2r).val, N) = Σ_{k<N} gcd(N, k). -/
theorem gcd_two_shift_full_sum_eq_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    ∑ r : ZMod N, Nat.gcd (2 * r).val N = ∑ k ∈ Finset.range N, Nat.gcd N k := by
  have h2 : IsUnit (2 : ZMod N) := by
    have hcast : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_cast
    rw [← hcast, ZMod.isUnit_iff_coprime]
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hodd
    have hnd : ¬ (2 ∣ N) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
  obtain ⟨u, hu⟩ := h2
  have hbij : Function.Bijective (fun r : ZMod N => 2 * r) := by
    apply Function.bijective_iff_has_inverse.mpr
    refine ⟨fun s => (↑u⁻¹ : ZMod N) * s, ?_, ?_⟩
    · intro r
      show (↑u⁻¹ : ZMod N) * (2 * r) = r
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    · intro s
      show 2 * ((↑u⁻¹ : ZMod N) * s) = s
      rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  calc ∑ r : ZMod N, Nat.gcd (2 * r).val N
      = ∑ s : ZMod N, Nat.gcd s.val N := hbij.sum_comp (fun s => Nat.gcd s.val N)
    _ = ∑ k ∈ Finset.range N, Nat.gcd k N := gcd_val_sum_eq_range
    _ = ∑ k ∈ Finset.range N, Nat.gcd N k :=
        Finset.sum_congr rfl (fun k _ => Nat.gcd_comm k N)

/-- **Nonzero-frequency gcd-sum (odd modulus).**  Splitting off the `r = 0` term
(`gcd((2·0).val, N) = gcd(0, N) = N`) from `gcd_two_shift_full_sum_eq_of_odd`:

    (Σ_{r≠0} gcd((2r).val, N)) + N = Σ_{k<N} gcd(N, k). -/
theorem gcd_two_shift_sum_nonzero_add_eq_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    (∑ r ∈ (Finset.univ \ {(0 : ZMod N)}), Nat.gcd (2 * r).val N) + N
      = ∑ k ∈ Finset.range N, Nat.gcd N k := by
  have hfull := gcd_two_shift_full_sum_eq_of_odd hodd
  have h0 : Nat.gcd (2 * (0 : ZMod N)).val N = N := by
    rw [mul_zero, ZMod.val_zero, Nat.gcd_zero_left]
  have hsplit : (∑ r ∈ (Finset.univ \ {(0 : ZMod N)}), Nat.gcd (2 * r).val N)
      + Nat.gcd (2 * (0 : ZMod N)).val N = ∑ r : ZMod N, Nat.gcd (2 * r).val N := by
    rw [← Finset.erase_eq]
    exact Finset.sum_erase_add Finset.univ _ (Finset.mem_univ 0)
  rw [h0] at hsplit
  rw [hsplit, hfull]

/-- **Exact second moment at any odd modulus (range form).**  Combining the exact
frequency gcd-sum (`sqGaussSum_normSq_sum_eq_gcd_sum_of_odd`) with the doubling reindex
(`gcd_two_shift_sum_nonzero_add_eq_of_odd`):

    Σ_{r≠0} ‖G(r)‖² = N · (Σ_{k<N} gcd(N, k) − N).

This is an exact equality (upper *and* lower bound) valid for every odd `N`, generalizing
the prime-only Part XVII. -/
theorem sqGaussSum_normSq_sum_eq_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ 2)
      = (N : ℝ) * (((∑ k ∈ Finset.range N, Nat.gcd N k : ℕ) : ℝ) - N) := by
  rw [sqGaussSum_normSq_sum_eq_gcd_sum_of_odd hodd]
  congr 1
  rw [← Nat.cast_sum]
  have hnat := gcd_two_shift_sum_nonzero_add_eq_of_odd hodd
  have hR : ((∑ r ∈ (Finset.univ \ {(0 : ZMod N)}), Nat.gcd (2 * r).val N : ℕ) : ℝ)
      + (N : ℝ) = ((∑ k ∈ Finset.range N, Nat.gcd N k : ℕ) : ℝ) := by exact_mod_cast hnat
  linarith

/-- **Exact second moment at any odd modulus (Pillai divisor form).**  Rewriting the
range gcd-sum through Pillai's identity `gcd_sum_pillai`:

    Σ_{r≠0} ‖G(r)‖² = N · (Σ_{d∣N} d·φ(N/d) − N).

The closed Plancherel evaluation of the quadratic-Gauss second moment for all odd `N`.
At an odd prime `p` the divisors are `{1, p}` and `Σ_{d∣p} d·φ(p/d) = (p−1) + p = 2p−1`,
so the right side is `p·((2p−1) − p) = p² − p`, exactly `sqGaussSum_normSq_sum_eq_of_prime`. -/
theorem sqGaussSum_normSq_sum_eq_divisors_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ 2)
      = (N : ℝ) * (((∑ d ∈ N.divisors, d * Nat.totient (N / d) : ℕ) : ℝ) - N) := by
  rw [sqGaussSum_normSq_sum_eq_of_odd hodd, gcd_sum_pillai N]

end Szemeredi.Roth

