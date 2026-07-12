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

/-! ### Part XXI — The odd-modulus second moment is `Θ(N²)`: the L² cap for *every* odd `N`

Part XVII computed the second moment *exactly* at an odd **prime** and derived the L²-cap
`√(Σ_{r≠0}‖G(r)‖²) ≥ N−1` (`sqGaussSum_l2_factor_ge_of_prime`), proving the L²-averaged
circle-method route cannot furnish the `o(N)` Sárközy density at primes.  Part XX made the
second moment an exact Pillai divisor sum for *all* odd `N*.  Here we extract the matching
**lower** bound at every odd modulus.

The Pillai function `P(N) = Σ_{d∣N} d·φ(N/d)` always contains the two extreme divisor terms
`d = 1` (contributing `1·φ(N) = φ(N)`) and `d = N` (contributing `N·φ(1) = N`), so
`P(N) ≥ N + φ(N)` and hence `P(N) − N ≥ φ(N)`.  Feeding this into the Part XX equality
`Σ_{r≠0}‖G(r)‖² = N·(P(N) − N)` gives

    Σ_{r≠0} ‖G(r)‖² ≥ N·φ(N)      (odd `N > 1`).

At an odd prime `p` this is `p·(p−1) = p² − p`, which *coincides* with the exact prime value
`sqGaussSum_normSq_sum_eq_of_prime`, so the bound is sharp at primes.  For odd `N` with a
bounded number of prime factors `φ(N) = Θ(N)`, so the second moment is `Θ(N²)` and the
L²-averaged density route is capped at every such modulus — exactly the Part XVII obstruction,
now removed from the primality hypothesis. -/

/-- **Pillai's divisor sum dominates `N + φ(N)`.**  For `N > 1` the divisors `1` and `N` are
distinct members of `N.divisors`; their Pillai terms are `1·φ(N/1) = φ(N)` and
`N·φ(N/N) = N·φ(1) = N`.  As every Pillai term is nonnegative, the full sum dominates this
two-term subsum:

    `N + φ(N) ≤ Σ_{d∣N} d·φ(N/d)`. -/
theorem pillai_ge_add_totient {N : ℕ} (hN : 1 < N) :
    N + Nat.totient N ≤ ∑ d ∈ N.divisors, d * Nat.totient (N / d) := by
  have hN0 : N ≠ 0 := by omega
  have hsub : ({1, N} : Finset ℕ) ⊆ N.divisors := by
    apply Finset.insert_subset
    · exact Nat.one_mem_divisors.mpr hN0
    · rw [Finset.singleton_subset_iff]; exact Nat.mem_divisors_self N hN0
  have hpair : ∑ d ∈ ({1, N} : Finset ℕ), d * Nat.totient (N / d)
      = N + Nat.totient N := by
    rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ N), Nat.div_one,
      Nat.div_self (by omega : 0 < N), Nat.totient_one]
    ring
  calc N + Nat.totient N
      = ∑ d ∈ ({1, N} : Finset ℕ), d * Nat.totient (N / d) := hpair.symm
    _ ≤ ∑ d ∈ N.divisors, d * Nat.totient (N / d) := Finset.sum_le_sum_of_subset hsub

/-- **Second-moment lower bound at any odd modulus.**  Combining the exact Pillai form of
the second moment (`sqGaussSum_normSq_sum_eq_divisors_of_odd`) with `pillai_ge_add_totient`:

    `N·φ(N) ≤ Σ_{r≠0} ‖G(r)‖²`   (odd `N > 1`).

At an odd prime `p` the left side is `p·(p−1) = p² − p`, matching the exact prime value
`sqGaussSum_normSq_sum_eq_of_prime`, so the estimate is sharp. -/
theorem sqGaussSum_normSq_sum_ge_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (hN : 1 < N) :
    (N : ℝ) * (Nat.totient N : ℝ) ≤
      (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ 2) := by
  rw [sqGaussSum_normSq_sum_eq_divisors_of_odd hodd]
  have hpil := pillai_ge_add_totient hN
  have hR : (Nat.totient N : ℝ)
      ≤ ((∑ d ∈ N.divisors, d * Nat.totient (N / d) : ℕ) : ℝ) - N := by
    have hcast : (N : ℝ) + (Nat.totient N : ℝ)
        ≤ ((∑ d ∈ N.divisors, d * Nat.totient (N / d) : ℕ) : ℝ) := by exact_mod_cast hpil
    linarith
  exact mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg N)

/-- **The L²-averaged minor-arc factor does not decay at any odd modulus.**
`√(N·φ(N)) ≤ √(Σ_{r≠0}‖G(r)‖²)`.  This removes the primality hypothesis from
`sqGaussSum_l2_factor_ge_of_prime`: for every odd `N > 1` with a bounded number of prime
factors (`φ(N) = Θ(N)`), the L²-averaged second-moment input to `sqDiffFree_density_bound_l2`
is `Θ(N)`, so it cannot on its own furnish the `o(N)` Sárközy density — only the pointwise
`√N` magnitude route can.  The L² average destroys the per-frequency `√N` cancellation at
every odd modulus, not merely at primes. -/
theorem sqGaussSum_l2_factor_ge_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (hN : 1 < N) :
    Real.sqrt ((N : ℝ) * (Nat.totient N : ℝ)) ≤
      Real.sqrt ((Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ 2)) :=
  Real.sqrt_le_sqrt (sqGaussSum_normSq_sum_ge_of_odd hodd hN)

/-! ### Part XXII — Divisor upper bound: the second moment is `N^{2+o(1)}` (tight bracket)

Part XXI extracted the lower bound `N·φ(N) ≤ Σ_{r≠0}‖G(r)‖²`.  Here we furnish the matching
**upper** bound directly from the exact Pillai form.  Each Pillai term is dominated by `N`:

    d·φ(N/d) ≤ d·(N/d) = N          (since `φ(m) ≤ m` and `d ∣ N`),

so summing over the `d(N) = |N.divisors|` divisors gives `P(N) = Σ_{d∣N} d·φ(N/d) ≤ N·d(N)`,
whence

    Σ_{r≠0} ‖G(r)‖² = N·(P(N) − N) ≤ N²·(d(N) − 1).

Because `d(N) = N^{o(1)}` (the divisor function is subpolynomial), this pins the second moment
to `N^{2+o(1)}`, *sharpening* the crude explicit Part XVI bound `≤ 4N²⌊√N⌋` (order `N^{2.5}`)
to essentially optimal order.  Combined with the Part XXI lower bound `N·φ(N) ≤ Σ‖G‖²` it
brackets the second moment as `N·φ(N) ≤ Σ‖G‖² ≤ N²·(d(N)−1)`, both sides `N^{2+o(1)}`, closing
the order-of-magnitude question and reconfirming that the L²-averaged circle-method route is
`Θ(N²)`-capped at every odd modulus. -/

/-- **Pillai's divisor sum is bounded by `N·d(N)`.**  Each term `d·φ(N/d)` is at most
`d·(N/d) = N` (using `φ(m) ≤ m` and `d ∣ N`), so the full sum over the `|N.divisors|`
divisors is at most `N·|N.divisors|`. -/
theorem pillai_le_mul_card_divisors {N : ℕ} :
    ∑ d ∈ N.divisors, d * Nat.totient (N / d) ≤ N * N.divisors.card := by
  calc ∑ d ∈ N.divisors, d * Nat.totient (N / d)
      ≤ ∑ _d ∈ N.divisors, N := by
        apply Finset.sum_le_sum
        intro d hd
        have hdvd : d ∣ N := Nat.dvd_of_mem_divisors hd
        calc d * Nat.totient (N / d)
            ≤ d * (N / d) := Nat.mul_le_mul (le_refl d) (Nat.totient_le (N / d))
          _ = N := Nat.mul_div_cancel' hdvd
    _ = N * N.divisors.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Second-moment upper bound at any odd modulus.**  Feeding `pillai_le_mul_card_divisors`
into the exact Pillai form `sqGaussSum_normSq_sum_eq_divisors_of_odd`:

    Σ_{r≠0} ‖G(r)‖² ≤ N²·(d(N) − 1).

Since `d(N) = N^{o(1)}`, the second moment is `N^{2+o(1)}`, sharpening the crude Part XVI
bound `≤ 4N²⌊√N⌋` (order `N^{2.5}`) to essentially optimal order.  With the Part XXI lower
bound `N·φ(N) ≤ Σ‖G‖²` this yields the tight bracket `N·φ(N) ≤ Σ‖G‖² ≤ N²·(d(N)−1)`. -/
theorem sqGaussSum_normSq_sum_le_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ 2)
      ≤ (N : ℝ) ^ 2 * ((N.divisors.card : ℝ) - 1) := by
  rw [sqGaussSum_normSq_sum_eq_divisors_of_odd hodd]
  have hcast : ((∑ d ∈ N.divisors, d * Nat.totient (N / d) : ℕ) : ℝ)
      ≤ (N : ℝ) * (N.divisors.card : ℝ) := by
    calc ((∑ d ∈ N.divisors, d * Nat.totient (N / d) : ℕ) : ℝ)
        ≤ ((N * N.divisors.card : ℕ) : ℝ) := by exact_mod_cast pillai_le_mul_card_divisors
      _ = (N : ℝ) * (N.divisors.card : ℝ) := by push_cast; ring
  have hR : ((∑ d ∈ N.divisors, d * Nat.totient (N / d) : ℕ) : ℝ) - N
      ≤ (N : ℝ) * ((N.divisors.card : ℝ) - 1) := by
    have hid : (N : ℝ) * ((N.divisors.card : ℝ) - 1)
        = (N : ℝ) * (N.divisors.card : ℝ) - N := by ring
    rw [hid]; linarith [hcast]
  calc (N : ℝ) * (((∑ d ∈ N.divisors, d * Nat.totient (N / d) : ℕ) : ℝ) - N)
      ≤ (N : ℝ) * ((N : ℝ) * ((N.divisors.card : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg N)
    _ = (N : ℝ) ^ 2 * ((N.divisors.card : ℝ) - 1) := by ring

/-! ### Part XXIII — First moment (L¹): `Σ_{r≠0}‖G(r)‖` is subquadratic (`o(N²)`)

Parts XX–XXII pinned the **second** moment `Σ_{r≠0}‖G(r)‖²` to the exact Pillai sum and
bracketed it as `N·φ(N) ≤ Σ‖G‖² ≤ N²·(d(N)−1)`, i.e. `Θ(N²)` at every odd modulus.  A
reader will naturally ask whether the **first** moment `Σ_{r≠0}‖G(r)‖` — the `L¹` Weyl norm —
is any smaller.  It is: Cauchy–Schwarz against the counting measure over the `N−1` nonzero
frequencies turns the second-moment upper bound into

    (Σ_{r≠0}‖G(r)‖)² ≤ (N−1)·Σ_{r≠0}‖G(r)‖² ≤ (N−1)·N²·(d(N)−1) ≤ N³·(d(N)−1),

so `Σ_{r≠0}‖G(r)‖ ≤ N·√(N·(d(N)−1)) = N^{3/2+o(1)} = o(N²)`.  The first moment is strictly
smaller in order than the second (`N^{3/2+o(1)}` vs `Θ(N²)`), completing the moment hierarchy.

**Honest caveat (why this does not improve the density bound).**  One might hope the `o(N²)`
first moment feeds the circle-method reduction to give `o(N)` density for *every* odd `N`,
breaking the small-`minFac` obstruction.  It does not: Parseval *forces*
`Σ_{r≠0}‖Â(r)‖² = |A|·N − |A|²`, so the residual `Σ_{r≠0}‖Â(r)‖²·‖G(r)‖` can only be pulled
apart as `(max_{r≠0}‖G(r)‖)·Σ‖Â‖²` (the pointwise route, `sqDiffFree_card_le_of_supNorm`) or
via Cauchy–Schwarz as `√(Σ‖Â‖⁴)·√(Σ‖G‖²)` (the `L²` route, `sqDiff_error_le_l2`) — never as
`(something o(N))·Σ_{r≠0}‖G(r)‖`.  So the `L¹` norm, despite being subquadratic, does not enter
the density estimate; the operative quantity remains the *pointwise* magnitude, capped at
`N/√minFac`.  Part XXIII therefore sharpens the *map* of the obstruction (the barrier is
genuinely pointwise/minor-arc, not an `L¹`/`L²` averaging artifact) without moving the density. -/

/-- **Pointwise `L¹` magnitude at an odd modulus.**  Taking the nonnegative square root of the
exact second-moment identity `‖G(r)‖² = N·gcd((2r).val, N)`
(`sqGaussSum_normSq_eq_gcd_of_odd`):

    `‖G(r)‖ = √(N·gcd((2r).val, N))`. -/
theorem sqGaussSum_norm_eq_sqrt_gcd_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (r : ZMod N) :
    ‖sqGaussSum r‖ = Real.sqrt ((N : ℝ) * (Nat.gcd (2 * r).val N : ℝ)) := by
  have h := sqGaussSum_normSq_eq_gcd_of_odd hodd r
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- **First-moment (squared) upper bound at any odd modulus.**  Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq` with the constant weight `1`) over the `N−1` nonzero
frequencies against the Part XXII second-moment bound `Σ‖G‖² ≤ N²·(d(N)−1)`:

    `(Σ_{r≠0} ‖G(r)‖)² ≤ N³·(d(N) − 1)`.

Since `d(N) = N^{o(1)}`, the right side is `N^{3+o(1)}`, so the first moment is `N^{3/2+o(1)}`,
strictly below the second moment's `Θ(N²)`. -/
theorem sqGaussSum_norm_sum_sq_le_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    ((Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖)) ^ 2
      ≤ (N : ℝ) ^ 3 * ((N.divisors.card : ℝ) - 1) := by
  set T := Finset.univ \ {(0 : ZMod N)} with hT
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) (fun r => ‖sqGaussSum r‖)
  simp only [one_mul, one_pow] at hCS
  have hcard_le : T.sum (fun _ => (1 : ℝ)) ≤ (N : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hle : T.card ≤ N := by
      calc T.card ≤ Finset.univ.card := Finset.card_le_card Finset.sdiff_subset
        _ = N := by rw [Finset.card_univ, ZMod.card]
    exact_mod_cast hle
  have h2mom := sqGaussSum_normSq_sum_le_of_odd hodd
  have hmom_nn : 0 ≤ T.sum (fun r => ‖sqGaussSum r‖ ^ 2) :=
    Finset.sum_nonneg (fun r _ => by positivity)
  refine hCS.trans (le_trans (mul_le_mul hcard_le h2mom hmom_nn (Nat.cast_nonneg N)) ?_)
  apply le_of_eq; ring

/-- **First moment is `o(N²)` (radical form).**  Taking the nonnegative square root of
`sqGaussSum_norm_sum_sq_le_of_odd`:

    `Σ_{r≠0} ‖G(r)‖ ≤ N·√(N·(d(N) − 1))`.

As `d(N) = N^{o(1)}`, the bound is `N^{3/2+o(1)} = o(N²)`.  Contrast with the second-moment
lower bound `sqGaussSum_l2_factor_ge_of_odd` (`√(N·φ(N)) ≤ √(Σ‖G‖²)`, order `N`): the `L¹`
Weyl norm is genuinely smaller in order than the `L²` norm at every odd modulus. -/
theorem sqGaussSum_norm_sum_le_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖)
      ≤ (N : ℝ) * Real.sqrt ((N : ℝ) * ((N.divisors.card : ℝ) - 1)) := by
  have hsq := sqGaussSum_norm_sum_sq_le_of_odd hodd
  have hnn : 0 ≤ (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖) :=
    Finset.sum_nonneg (fun r _ => norm_nonneg _)
  rw [← Real.sqrt_sq hnn]
  refine (Real.sqrt_le_sqrt hsq).trans ?_
  rw [show (N : ℝ) ^ 3 * ((N.divisors.card : ℝ) - 1)
      = (N : ℝ) ^ 2 * ((N : ℝ) * ((N.divisors.card : ℝ) - 1)) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-! ### Part XXIV — Exact pointwise maximum of the Weyl coefficient (odd modulus)

Parts X–XXIII bounded the Gauss-sum *moments* (`L¹`, `L²`) and the pointwise magnitude
by inequalities.  Here we pin the **exact maximum** of `‖G(r)‖` over the nonzero
frequencies:

    `max_{r ≠ 0} ‖G(r)‖² = N · (N / minFac N) = N² / minFac N`,

*achieved* at a concrete frequency.  Because `‖G(r)‖² = N · gcd((2r).val, N)`
(`sqGaussSum_normSq_eq_gcd_of_odd`), the maximum is governed by the largest **proper**
divisor of `N`, which is exactly `N / minFac N`.

This turns the informal caveat repeated throughout Parts XI–XXIII ("the sup-norm / Weyl
reduction cannot reach `o(N)` when `N` has a bounded smallest prime factor") into a
**proven no-go**: the density theorem `sqDiffFree_card_le_of_supNorm` needs a bound
`M ≥ ‖G(r)‖` for every `r ≠ 0`, and the *smallest* such `M` is exactly
`N / √(minFac N)`.  For `N = p^k` an odd prime power this is `N / √p = Θ(N)`, useless for
`o(N)`.  Combined with the exact `Θ(N²)` second moment (`sqGaussSum_normSq_sum_eq_of_odd`),
*both* elementary single-frequency reductions are now rigorously exhausted for
bounded-`minFac` moduli — genuine cross-frequency (minor-arc) cancellation is required. -/

/-- **Pointwise gcd is a proper divisor, hence `≤ N / minFac N` (odd modulus).**  For odd
`N > 1` and any nonzero frequency `r`, since `2` is a unit the doubled residue `(2r).val`
is a nonzero element of `{1, …, N-1}`, so `gcd((2r).val, N)` is a *proper* divisor of `N`
and is therefore at most the largest proper divisor `N / minFac N`. -/
theorem gcd_two_val_le_div_minFac_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (hN : 1 < N)
    {r : ZMod N} (hr : r ≠ 0) :
    Nat.gcd (2 * r).val N ≤ N / N.minFac := by
  have h2 : IsUnit (2 : ZMod N) := by
    have hcast : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_cast
    rw [← hcast, ZMod.isUnit_iff_coprime]
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hodd
    have hnd : ¬ (2 ∣ N) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
  have h2r : (2 : ZMod N) * r ≠ 0 := fun hz => hr (h2.mul_right_eq_zero.mp hz)
  set g := Nat.gcd (2 * r).val N with hgdef
  have hgN : g ∣ N := Nat.gcd_dvd_right _ _
  have hval_pos : 0 < (2 * r).val := (ZMod.val_pos).mpr h2r
  have hval_lt : (2 * r).val < N := ZMod.val_lt _
  have hg_le_val : g ≤ (2 * r).val := Nat.le_of_dvd hval_pos (Nat.gcd_dvd_left _ _)
  have hg_lt : g < N := lt_of_le_of_lt hg_le_val hval_lt
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
  have hdivmul : (N / g) * g = N := Nat.div_mul_cancel hgN
  have hcofactor_dvd : (N / g) ∣ N := Nat.div_dvd_of_dvd hgN
  have hq2 : 2 ≤ N / g := by
    have h1 : 1 ≤ N / g := (Nat.one_le_div_iff hg_pos).mpr (le_of_lt hg_lt)
    rcases Nat.eq_or_lt_of_le h1 with heq | hlt
    · exfalso; rw [← heq, one_mul] at hdivmul; omega
    · omega
  have hminfac_le : N.minFac ≤ N / g := Nat.minFac_le_of_dvd hq2 hcofactor_dvd
  rw [Nat.le_div_iff_mul_le (Nat.minFac_pos N)]
  calc g * N.minFac ≤ g * (N / g) := Nat.mul_le_mul (le_refl g) hminfac_le
    _ = (N / g) * g := Nat.mul_comm _ _
    _ = N := hdivmul

/-- **The pointwise maximum `N / minFac N` is achieved (odd modulus).**  Choosing the
frequency `r = 2⁻¹ · (N / minFac N)` gives `(2r).val = N / minFac N`, a divisor of `N`,
so `gcd((2r).val, N) = N / minFac N`.  This is the witness making
`gcd_two_val_le_div_minFac_of_odd` an equality. -/
theorem exists_gcd_two_val_eq_div_minFac_of_odd {N : ℕ} [NeZero N] (hodd : Odd N)
    (hN : 1 < N) :
    ∃ r : ZMod N, r ≠ 0 ∧ Nat.gcd (2 * r).val N = N / N.minFac := by
  have h2 : IsUnit (2 : ZMod N) := by
    have hcast : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_cast
    rw [← hcast, ZMod.isUnit_iff_coprime]
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hodd
    have hnd : ¬ (2 ∣ N) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp h2
  have hmf_dvd : N.minFac ∣ N := Nat.minFac_dvd N
  have hmf_ge2 : 2 ≤ N.minFac := (Nat.minFac_prime (by omega)).two_le
  set d := N / N.minFac with hddef
  have hd_dvd : d ∣ N := Nat.div_dvd_of_dvd hmf_dvd
  have hd_lt : d < N := Nat.div_lt_self (by omega) hmf_ge2
  have hd_pos : 0 < d := Nat.div_pos (Nat.minFac_le (by omega)) (Nat.minFac_pos N)
  set a : ZMod N := (d : ZMod N) with hadef
  have hval_a : a.val = d := by rw [hadef, ZMod.val_natCast_of_lt hd_lt]
  have h2wa : (2 : ZMod N) * (w * a) = a := by rw [← mul_assoc, hw, one_mul]
  refine ⟨w * a, ?_, ?_⟩
  · intro hz
    have ha0 : a = 0 := by rw [hz, mul_zero] at h2wa; exact h2wa.symm
    rw [ha0, ZMod.val_zero] at hval_a
    omega
  · rw [h2wa, hval_a]
    exact Nat.gcd_eq_left hd_dvd

/-- **Exact greatest nonzero Weyl coefficient — squared form (odd modulus).**  Combining
`gcd_two_val_le_div_minFac_of_odd` (upper) with `exists_gcd_two_val_eq_div_minFac_of_odd`
(achieved) and the exact per-frequency magnitude `sqGaussSum_normSq_eq_gcd_of_odd`:

    `IsGreatest {‖G(r)‖² : r ≠ 0} (N · (N / minFac N))`.

So `max_{r≠0} ‖G(r)‖² = N² / minFac N` exactly. -/
theorem sqGaussSum_normSq_isGreatest_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (hN : 1 < N) :
    IsGreatest
      ((fun r : ZMod N => ‖sqGaussSum r‖ ^ 2) ''
        (↑(Finset.univ \ {(0 : ZMod N)}) : Set (ZMod N)))
      ((N : ℝ) * ((N / N.minFac : ℕ) : ℝ)) := by
  constructor
  · obtain ⟨r, hr, hgcd⟩ := exists_gcd_two_val_eq_div_minFac_of_odd hodd hN
    refine ⟨r, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_sdiff]
      exact ⟨Finset.mem_univ r, by simpa using hr⟩
    · dsimp only
      rw [sqGaussSum_normSq_eq_gcd_of_odd hodd r, hgcd]
  · rintro x ⟨r, hrmem, rfl⟩
    rw [Finset.mem_coe, Finset.mem_sdiff] at hrmem
    have hr : r ≠ 0 := by simpa using hrmem.2
    dsimp only
    rw [sqGaussSum_normSq_eq_gcd_of_odd hodd r]
    have hle := gcd_two_val_le_div_minFac_of_odd hodd hN hr
    have hcast : ((Nat.gcd (2 * r).val N : ℕ) : ℝ) ≤ ((N / N.minFac : ℕ) : ℝ) := by
      exact_mod_cast hle
    exact mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg N)

/-- **Exact greatest nonzero Weyl coefficient — norm form (odd modulus).**  The square
root of `sqGaussSum_normSq_isGreatest_of_odd`:

    `IsGreatest {‖G(r)‖ : r ≠ 0} (√(N · (N / minFac N)))`. -/
theorem sqGaussSum_norm_isGreatest_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (hN : 1 < N) :
    IsGreatest
      ((fun r : ZMod N => ‖sqGaussSum r‖) ''
        (↑(Finset.univ \ {(0 : ZMod N)}) : Set (ZMod N)))
      (Real.sqrt ((N : ℝ) * ((N / N.minFac : ℕ) : ℝ))) := by
  constructor
  · obtain ⟨r, hr, hgcd⟩ := exists_gcd_two_val_eq_div_minFac_of_odd hodd hN
    refine ⟨r, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_sdiff]
      exact ⟨Finset.mem_univ r, by simpa using hr⟩
    · dsimp only
      rw [sqGaussSum_norm_eq_sqrt_gcd_of_odd hodd r, hgcd]
  · rintro x ⟨r, hrmem, rfl⟩
    rw [Finset.mem_coe, Finset.mem_sdiff] at hrmem
    have hr : r ≠ 0 := by simpa using hrmem.2
    dsimp only
    rw [sqGaussSum_norm_eq_sqrt_gcd_of_odd hodd r]
    apply Real.sqrt_le_sqrt
    have hle := gcd_two_val_le_div_minFac_of_odd hodd hN hr
    have hcast : ((Nat.gcd (2 * r).val N : ℕ) : ℝ) ≤ ((N / N.minFac : ℕ) : ℝ) := by
      exact_mod_cast hle
    exact mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg N)

/-- **The exact sup-norm floor is `N / √(minFac N)` (odd modulus).**  Rewriting the value
in `sqGaussSum_norm_isGreatest_of_odd` in closed form, using `minFac N ∣ N`:

    `√(N · (N / minFac N)) = N / √(minFac N)`.

Hence the least valid Weyl sup-norm bound for `sqDiffFree_card_le_of_supNorm` is exactly
`N / √(minFac N)`.  For `N` with bounded smallest prime factor `p` (e.g. odd prime powers,
`minFac = p`) this is `Θ(N)` — the sup-norm reduction provably cannot deliver `o(N)`. -/
theorem sqGaussSum_norm_max_value_eq_of_odd {N : ℕ} [NeZero N] (hN : 1 < N) :
    Real.sqrt ((N : ℝ) * ((N / N.minFac : ℕ) : ℝ)) = (N : ℝ) / Real.sqrt (N.minFac) := by
  have hmf_dvd : N.minFac ∣ N := Nat.minFac_dvd N
  have hmf_ne : (N.minFac : ℝ) ≠ 0 := by exact_mod_cast (Nat.minFac_pos N).ne'
  have hcast : ((N / N.minFac : ℕ) : ℝ) = (N : ℝ) / (N.minFac : ℝ) :=
    Nat.cast_div hmf_dvd hmf_ne
  rw [hcast, show (N : ℝ) * ((N : ℝ) / (N.minFac : ℝ)) = (N : ℝ) ^ 2 / (N.minFac : ℝ) by ring,
    Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]

/-! ### Part XXV — The exact spectral level-set distribution of the Weyl coefficient (odd modulus)

Parts XVII–XXIV computed *moments* of the nonzero-frequency Weyl coefficient
`r ↦ ‖G(r)‖²` (max, first/second moments, divisor sums).  Here we compute the underlying
**distribution** those are moments of.  For odd `N` the exact per-frequency magnitude
`‖G(r)‖² = N·gcd((2r).val, N)` (`sqGaussSum_normSq_eq_gcd_of_odd`) is constant on the gcd
level sets, and each level set has a totient count.

Since `r ↦ 2r` is a bijection of `ZMod N` (`2` is a unit for odd `N`) and `s ↦ s.val`
identifies `ZMod N` with `{0,…,N−1}`, the level set of frequencies with
`gcd((2r).val, N) = d` is in bijection with `{k < N : gcd(N, k) = d}`, whose cardinality is
`φ(N/d)` by `Nat.totient_div_of_dvd`.  Thus, for every proper divisor `d ∣ N` (`d < N`):

    #{ r ≠ 0 : ‖G(r)‖² = N·d } = φ(N/d).

This single identity *subsumes* every earlier moment (`Σ_{r≠0}‖G‖² = N·Σ_{d∣N,d<N} d·φ(N/d)`
is Part XX, the max at `d = N/minFac` is Part XXIV).  Its consumer punchline
(`sqGaussSum_max_level_set_card_of_odd`) is that the *maximal* Weyl coefficient is attained at
exactly `minFac(N) − 1` frequencies — the quantitative "few large frequencies" fact that a
major/minor-arc split of the circle method needs. -/

/-- **Exact gcd level-set count (odd modulus).**  For `N` odd and a proper divisor `d ∣ N`
(`d < N`), the number of nonzero frequencies `r` with `gcd((2r).val, N) = d` is exactly the
totient `φ(N/d)`.  Proof: reindex by the bijection `r ↦ 2r` (`2` a unit) composed with
`s ↦ s.val`, landing in `{k < N : gcd(N,k) = d}` whose count is `Nat.totient_div_of_dvd`. -/
theorem sqGaussSum_gcd_level_set_card_of_odd {N : ℕ} [NeZero N] (hodd : Odd N)
    {d : ℕ} (hd : d ∣ N) (hdN : d < N) :
    ((Finset.univ \ {(0 : ZMod N)}).filter
        (fun r => Nat.gcd (2 * r).val N = d)).card = Nat.totient (N / d) := by
  have h2 : IsUnit (2 : ZMod N) := by
    have hcast : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_cast
    rw [← hcast, ZMod.isUnit_iff_coprime]
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hodd
    have hnd : ¬ (2 ∣ N) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp h2   -- hw : 2 * w = 1
  rw [Nat.totient_div_of_dvd hd]
  refine Finset.card_bij (fun r _ => (2 * r).val) ?_ ?_ ?_
  · -- maps into `{k ∈ range N | N.gcd k = d}`
    intro r hr
    rw [Finset.mem_filter] at hr ⊢
    refine ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    rw [Nat.gcd_comm]; exact hr.2
  · -- injective (via `s ↦ s.val` injective, then cancel the unit `2`)
    intro r₁ _ r₂ _ heq
    have hw' : (w : ZMod N) * 2 = 1 := by rw [mul_comm]; exact hw
    have h2r : (2 * r₁ : ZMod N) = 2 * r₂ := ZMod.val_injective N heq
    calc r₁ = (w * 2) * r₁ := by rw [hw', one_mul]
      _ = w * (2 * r₁) := by rw [mul_assoc]
      _ = w * (2 * r₂) := by rw [h2r]
      _ = (w * 2) * r₂ := by rw [mul_assoc]
      _ = r₂ := by rw [hw', one_mul]
  · -- surjective
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hklt, hkgcd⟩ := hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [Nat.gcd_zero_right] at hkgcd
      omega
    set s : ZMod N := (k : ZMod N) with hsdef
    have hsval : s.val = k := by rw [hsdef, ZMod.val_natCast_of_lt hklt]
    have h2ws : (2 : ZMod N) * (w * s) = s := by rw [← mul_assoc, hw, one_mul]
    have hs0 : s ≠ 0 := by
      intro h; rw [h, ZMod.val_zero] at hsval; exact hk0 hsval.symm
    refine ⟨w * s, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_sdiff, Finset.mem_singleton]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hz
        rw [hz, mul_zero] at h2ws
        exact hs0 h2ws.symm
      · rw [h2ws, hsval, Nat.gcd_comm]; exact hkgcd
    · show (2 * (w * s)).val = k
      rw [h2ws, hsval]

/-- **Exact spectral distribution of the Weyl coefficient (odd modulus).**  Restatement of the
gcd level-set count directly in terms of the squared magnitude: for `N` odd and a proper divisor
`d ∣ N`, exactly `φ(N/d)` nonzero frequencies attain `‖G(r)‖² = N·d`.  (Equality of the two
filter sets is `sqGaussSum_normSq_eq_gcd_of_odd` together with cancelling the positive factor
`N`.) -/
theorem sqGaussSum_normSq_level_set_card_of_odd {N : ℕ} [NeZero N] (hodd : Odd N)
    {d : ℕ} (hd : d ∣ N) (hdN : d < N) :
    ((Finset.univ \ {(0 : ZMod N)}).filter
        (fun r => ‖sqGaussSum r‖ ^ 2 = (N : ℝ) * d)).card = Nat.totient (N / d) := by
  rw [← sqGaussSum_gcd_level_set_card_of_odd hodd hd hdN]
  congr 1
  apply Finset.filter_congr
  intro r _
  rw [sqGaussSum_normSq_eq_gcd_of_odd hodd r]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  constructor
  · intro h
    have hcast := mul_left_cancel₀ (ne_of_gt hN0) h
    exact_mod_cast hcast
  · intro h; rw [h]

/-- **The maximal Weyl coefficient is attained at exactly `minFac(N) − 1` frequencies
(odd modulus).**  The unique largest gcd level (`d = N/minFac`, Part XXIV) has count
`φ(N / (N/minFac)) = φ(minFac N) = minFac N − 1`, since `minFac N` is prime.

This is the quantitative "few large frequencies" statement: the `Θ(N)` obstruction to a Weyl
sup-norm reduction (`sqGaussSum_norm_max_value_eq_of_odd`) lives on only `minFac(N) − 1` of the
`N − 1` nonzero frequencies — precisely the major arcs a refined circle-method argument would
isolate and treat separately from the `√N`-sized minor arcs. -/
theorem sqGaussSum_max_level_set_card_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (hN : 1 < N) :
    ((Finset.univ \ {(0 : ZMod N)}).filter
        (fun r => Nat.gcd (2 * r).val N = N / N.minFac)).card = N.minFac - 1 := by
  have hN0 : N ≠ 0 := by omega
  have hmf_dvd : N.minFac ∣ N := Nat.minFac_dvd N
  have hmf_prime : N.minFac.Prime := Nat.minFac_prime (by omega)
  have hmf_ge2 : 2 ≤ N.minFac := hmf_prime.two_le
  set d := N / N.minFac with hddef
  have hd_dvd : d ∣ N := Nat.div_dvd_of_dvd hmf_dvd
  have hd_lt : d < N := Nat.div_lt_self (by omega) hmf_ge2
  rw [sqGaussSum_gcd_level_set_card_of_odd hodd hd_dvd hd_lt, hddef,
    Nat.div_div_self hmf_dvd hN0, Nat.totient_prime hmf_prime]

/-! ### Part XXVI — The spectral partition is exhaustive: the level sets tile the whole spectrum

Part XXV computed the count `φ(N/d)` of each individual gcd level set `{r ≠ 0 : gcd((2r).val,N) = d}`
but left open the *global* question: do these level sets, ranging over the proper divisors `d ∣ N`,
account for **every** nonzero frequency, with none missed or double-counted?  They do, and this
closes the loop on the whole Part XVII–XXV moment tower.

The map `r ↦ gcd((2r).val, N)` sends each nonzero frequency to a *proper* divisor of `N`: it is a
divisor of `N` always, and for `r ≠ 0` it is strictly below `N` because `2r ≠ 0` (as `2` is a unit
for odd `N`), so `0 < (2r).val < N` forces `gcd((2r).val, N) ≤ (2r).val < N`.  Hence the fibers of
this map partition the `N − 1` nonzero frequencies, and `Finset.card_eq_sum_card_fiberwise` with the
per-fiber counts of Part XXV yields the exhaustiveness identity

    Σ_{d ∣ N, d < N} φ(N/d) = N − 1.

This is the spectral incarnation of Gauss's divisor-sum identity `Σ_{d ∣ N} φ(d) = N` (drop the
`d = N` term `φ(1) = 1`): it certifies that the exact distribution of Part XXV is a genuine finite
measure whose total mass is the full nonzero spectrum — nothing lives outside the enumerated levels.
As a structural consequence, the second moment (Part XX) is now an *honest* partition sum
`Σ_{r≠0} ‖G(r)‖² = N · Σ_{d ∣ N, d < N} d · φ(N/d)` (`sqGaussSum_normSq_sum_eq_divisor_sum_of_odd`),
grouping the frequency gcd-sum by its constant value on each level. -/

/-- **Nonzero frequencies land on proper divisors (odd modulus).**  For `N` odd and `r ≠ 0`,
the gcd `gcd((2r).val, N)` is a *proper* divisor of `N`: it always divides `N`, and it is
strictly below `N` because `2` is a unit (odd `N`) so `2r ≠ 0`, giving `0 < (2r).val < N` and
hence `gcd((2r).val, N) ≤ (2r).val < N`.  This is the membership hypothesis that lets the gcd
map fiber the nonzero spectrum over the proper divisors. -/
theorem sqGaussSum_gcd_mem_proper_divisors_of_odd {N : ℕ} [NeZero N] (hodd : Odd N)
    {r : ZMod N} (hr0 : r ≠ 0) :
    Nat.gcd (2 * r).val N ∈ (N.divisors).filter (· < N) := by
  have h2 : IsUnit (2 : ZMod N) := by
    have hcast : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_cast
    rw [← hcast, ZMod.isUnit_iff_coprime]
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hodd
    have hnd : ¬ (2 ∣ N) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
  have h2r : (2 * r : ZMod N) ≠ 0 := by
    intro h
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp h2
    apply hr0
    calc r = (w * 2) * r := by rw [mul_comm w 2, hw, one_mul]
      _ = w * (2 * r) := by rw [mul_assoc]
      _ = w * 0 := by rw [h]
      _ = 0 := mul_zero w
  have hval_pos : 0 < (2 * r).val := by
    rcases Nat.eq_zero_or_pos (2 * r).val with hz | hpos
    · exact absurd (ZMod.val_injective N (by rw [hz, ZMod.val_zero])) h2r
    · exact hpos
  rw [Finset.mem_filter, Nat.mem_divisors]
  refine ⟨⟨Nat.gcd_dvd_right _ _, NeZero.ne N⟩, ?_⟩
  calc Nat.gcd (2 * r).val N ≤ (2 * r).val :=
        Nat.le_of_dvd hval_pos (Nat.gcd_dvd_left _ _)
    _ < N := ZMod.val_lt _

/-- **Exhaustive spectral partition (odd modulus).**  The gcd level sets of the nonzero
frequencies, indexed by the proper divisors `d ∣ N` (`d < N`), partition the entire spectrum:
summing their Part XXV counts `φ(N/d)` recovers the total number `N − 1` of nonzero frequencies.
Proof: the fiber map `r ↦ gcd((2r).val, N)` lands in the proper divisors
(`sqGaussSum_gcd_mem_proper_divisors_of_odd`), so `Finset.card_eq_sum_card_fiberwise` decomposes
`|univ \ {0}| = N − 1` into the per-level counts. -/
theorem sqGaussSum_spectral_partition_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    ((N.divisors).filter (· < N)).sum (fun d => Nat.totient (N / d)) = N - 1 := by
  -- number of nonzero frequencies
  have hcard : (Finset.univ \ ({0} : Finset (ZMod N))).card = N - 1 := by
    rw [show Finset.univ \ ({0} : Finset (ZMod N)) = Finset.univ.erase 0 from
      Finset.sdiff_singleton_eq_erase _ _,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  -- the fiber map `r ↦ gcd((2r).val, N)` lands in the proper divisors
  have hfiber : ∀ r ∈ (Finset.univ \ ({0} : Finset (ZMod N))),
      Nat.gcd (2 * r).val N ∈ (N.divisors).filter (· < N) := fun r hr =>
    sqGaussSum_gcd_mem_proper_divisors_of_odd hodd
      (by rw [Finset.mem_sdiff, Finset.mem_singleton] at hr; exact hr.2)
  rw [← hcard, Finset.card_eq_sum_card_fiberwise
    (f := fun r => Nat.gcd (2 * r).val N)
    (t := (N.divisors).filter (· < N))
    (fun r hr => Finset.mem_coe.mpr (hfiber r (Finset.mem_coe.mp hr)))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  exact (sqGaussSum_gcd_level_set_card_of_odd hodd hd.1.1 hd.2).symm

/-- **Second moment as an honest divisor-partition sum (odd modulus).**  Grouping the exact
frequency gcd-sum `Σ_{r≠0} ‖G(r)‖² = N·Σ_{r≠0} gcd((2r).val,N)` by the constant value the gcd
takes on each level set (Part XXV) turns the second moment into an explicit sum over the proper
divisors:

    Σ_{r≠0} ‖G(r)‖² = N · Σ_{d ∣ N, d < N} d · φ(N/d).

This is the divisor-sum form of the Part XX second moment, obtained purely from the exhaustive
spectral partition: each of the `φ(N/d)` frequencies in level `d` contributes `N·d`. -/
theorem sqGaussSum_normSq_sum_eq_divisor_sum_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ 2)
      = (N : ℝ) * ((N.divisors).filter (· < N)).sum
          (fun d => (d : ℝ) * (Nat.totient (N / d) : ℝ)) := by
  rw [sqGaussSum_normSq_sum_eq_gcd_sum_of_odd hodd]
  congr 1
  have hfiber : ∀ r ∈ (Finset.univ \ ({0} : Finset (ZMod N))),
      Nat.gcd (2 * r).val N ∈ (N.divisors).filter (· < N) := fun r hr =>
    sqGaussSum_gcd_mem_proper_divisors_of_odd hodd
      (by rw [Finset.mem_sdiff, Finset.mem_singleton] at hr; exact hr.2)
  rw [← Finset.sum_fiberwise_of_maps_to hfiber
    (fun r => (Nat.gcd (2 * r).val N : ℝ))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  -- on the fiber `gcd = d`, every summand is the constant `(d : ℝ)`
  rw [Finset.sum_congr rfl (g := fun _ => (d : ℝ))
        (fun r hr => by rw [Finset.mem_filter] at hr; rw [hr.2])]
  rw [Finset.sum_const, sqGaussSum_gcd_level_set_card_of_odd hodd hd.1.1 hd.2,
    nsmul_eq_mul, mul_comm]

/-! ### Part XXVII — The sharp single-scale cardinality bound at odd modulus

Every prior cardinality statement fed the master lemma `sqDiffFree_card_le_of_supNorm`
either the *exact* prime magnitude `M = √N` (`sqDiffFree_card_le_sqrt_of_prime`, primes
only) or the *crude* all-modulus magnitude `M = N/√2` (`sqDiffFree_card_le_of_ne_zero`,
from the lossy "proper divisor `≤ N/2`" estimate).  Neither used the **exact** odd-modulus
Weyl sup-norm `max_{r≠0}‖G(r)‖ = N/√(minFac N)` established in
`sqGaussSum_norm_isGreatest_of_odd` / `sqGaussSum_norm_max_value_eq_of_odd`.

Plugging that exact maximum into the master lemma gives the **sharpest single-scale
cardinality bound the entire circle-method / Weyl line can produce** at odd `N`, with the
provably-optimal constant.  It strictly refines `sqDiffFree_card_le_of_ne_zero`: for odd
`N > 1` one always has `minFac N ≥ 3`, so `N/√(minFac N) ≤ N/√3 < N/√2`.  It also
subsumes the prime capstone as the special case `minFac N = N` (`M = √N`).

Honest scope (the documented no-go, unchanged): this is a *pointwise* sup-norm bound, so it
delivers `|A| = o(N)` **iff** `minFac N → ∞` along the modulus sequence (e.g. `N` prime).
At bounded smallest prime factor — odd prime powers `N = p^a`, `minFac = p` fixed —
`N/√p = Θ(N)` and the bound is genuinely `Θ(N)`; that ceiling is *sharp*, not a proof
artifact, by `sqGaussSum_normSq_isGreatest_of_odd`.  Breaking it needs the multi-scale
density-increment iteration, which is out of Mathlib-4.26 reach. -/

/-- **Sharp single-scale cardinality bound at odd modulus (product form).**  Feeding the
    master lemma the *exact* Weyl sup-norm `M = N/√(minFac N)`
    (`sqGaussSum_norm_max_value_eq_of_odd`, the achieved maximum
    `sqGaussSum_norm_isGreatest_of_odd`): a square-difference-free `A ⊆ ℤ/Nℤ` at odd
    `N > 1` satisfies

    `|A|·(N + N/√(minFac N)) ≤ N·(#{n : n² = 0} + N/√(minFac N))`.

    Strictly sharper than the `N/√2` bound `sqDiffFree_card_le_of_ne_zero` (since odd
    `N > 1 ⟹ minFac N ≥ 3`), and it is the tightest sup-norm the Weyl reduction admits. -/
theorem sqDiffFree_card_le_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (hN : 1 < N)
    (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) * ((N : ℝ) + (N : ℝ) / Real.sqrt (N.minFac))
      ≤ (N : ℝ) * (((Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card : ℝ)
          + (N : ℝ) / Real.sqrt (N.minFac)) := by
  have hval := sqGaussSum_norm_max_value_eq_of_odd (N := N) hN
  have hG : ∀ r : ZMod N, r ≠ 0 → ‖sqGaussSum r‖ ≤ (N : ℝ) / Real.sqrt (N.minFac) := by
    intro r hr
    rw [← hval, sqGaussSum_norm_eq_sqrt_gcd_of_odd hodd r]
    apply Real.sqrt_le_sqrt
    have hle := gcd_two_val_le_div_minFac_of_odd hodd hN hr
    have hcast : ((Nat.gcd (2 * r).val N : ℕ) : ℝ) ≤ ((N / N.minFac : ℕ) : ℝ) := by
      exact_mod_cast hle
    exact mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg N)
  have hM : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (N.minFac) := by positivity
  exact sqDiffFree_card_le_of_supNorm hM A hG hfree

/-- **Sharp single-scale cardinality bound at odd modulus (additive form).**  Cancelling
    the common factor `N + N/√(minFac N) > 0` from the product form
    `sqDiffFree_card_le_of_odd` yields the clean closed inequality

    `|A| ≤ #{n : n² = 0} + N/√(minFac N)`.

    For odd `N` with `minFac N → ∞` and few nilpotent square roots (e.g. squarefree,
    `#{n : n² = 0} = 1`) this is `|A| = o(N)` — the Sárközy density decay on that modulus
    class.  Specialising to a prime `N` gives `|A| ≤ 1 + √N`. -/
theorem sqDiffFree_card_le_add_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (hN : 1 < N)
    (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ)
      ≤ ((Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card : ℝ)
          + (N : ℝ) / Real.sqrt (N.minFac) := by
  have hprod := sqDiffFree_card_le_of_odd hodd hN A hfree
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set a : ℝ := (A.card : ℝ) with ha
  set c : ℝ := ((Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card : ℝ) with hc
  set M : ℝ := (N : ℝ) / Real.sqrt (N.minFac) with hMdef
  have hM : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  have hc0 : (0 : ℝ) ≤ c := by rw [hc]; positivity
  have hNM : (0 : ℝ) < (N : ℝ) + M := by linarith
  -- `a·(N+M) ≤ N·(c+M) ≤ (c+M)·(N+M)`, then cancel the positive factor `N+M`.
  have hstep : (N : ℝ) * (c + M) ≤ (c + M) * ((N : ℝ) + M) := by nlinarith [hM, hc0]
  have hfac : a * ((N : ℝ) + M) ≤ (c + M) * ((N : ℝ) + M) := le_trans hprod hstep
  exact le_of_mul_le_mul_right hfac hNM

/-! ### Part XXVIII — Sharpness at a prime-square modulus: an explicit √N construction

Every prior part bounds `|A|` from *above*.  This part supplies the complementary
*lower* bound at `N = p²`: an explicit square-difference-free set of size exactly
`p = √N`, so the prime upper bound `|A| ≤ √N` (`sqDiffFree_card_le_sqrt_of_prime`,
Part XVIII) is **order-tight** and cannot improve to `o(√N)` at prime-square moduli.
It is the first lower-bound / explicit construction in the file.

The witness is the subgroup `pℤ/p²ℤ = {p·k : 0 ≤ k < p}` of the multiples of `p`.
Its `p` elements have pairwise differences all divisible by `p`, and the *only*
square divisible by `p` in `ℤ/p²ℤ` is `0`: if `p ∣ n²` then `p ∣ n` (p prime), so
`p² ∣ n²`, i.e. `n² = 0`.  Hence no nonzero square is a difference of two elements
— the set is square-difference-free.

Structural note (not formalized): the true maximum at `N = p²` is *larger*,
`p · α(Paley(p)) = Θ(p^{3/2}) = Θ(N^{3/4})`, obtained from a Paley-independent
family of `p`-cosets (two cosets `pℤ` and `d + pℤ` combine into a
square-difference-free set iff `d` is a quadratic non-residue mod `p`).  The
subgroup here is the clean `α ≥ 1` base case; the `√N` it certifies already shows
the pointwise circle-method ceiling `|A| ≤ √N` is tight up to a constant. -/

/-- **Sharpness of the `√N` bound at a prime-square modulus.**  For an odd (indeed
    any) prime `p` and `N = p²`, the subgroup of multiples of `p`,
    `{ p·k : 0 ≤ k < p }`, is square-difference-free and has exactly `p = √N`
    elements.  Hence the maximal square-difference-free set in `ℤ/p²ℤ` has at least
    `√N` elements: the prime upper bound `|A| ≤ √N` (Part XVIII) is order-tight and
    does not shrink at prime-square moduli. -/
theorem exists_sqDiffFree_card_sqrt_of_prime_sq {p : ℕ} (hp : p.Prime) :
    ∃ A : Finset (ZMod (p ^ 2)),
      (∀ x ∈ A, ∀ n : ZMod (p ^ 2), n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) ∧ A.card = p := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
  set f : ℕ → ZMod (p ^ 2) := fun k => ((p * k : ℕ) : ZMod (p ^ 2)) with hf
  refine ⟨(Finset.range p).image f, ?_, ?_⟩
  · -- square-difference-free
    intro x hx n hn hmem
    -- forward membership ⟹ `p ∣ (·).val`
    have key : ∀ y ∈ (Finset.range p).image f, p ∣ (y : ZMod (p ^ 2)).val := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      rw [Finset.mem_range] at hk
      have hlt : p * k < p ^ 2 := by rw [sq]; nlinarith [hp.pos, hk]
      rw [hf, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
      exact Dvd.intro k rfl
    have hpx : p ∣ x.val := key x hx
    have hpxn : p ∣ (x + n ^ 2).val := key _ hmem
    -- `p ∣ (n²).val`
    have hpn2 : p ∣ (n ^ 2).val := by
      have hadd : (x + n ^ 2).val = (x.val + (n ^ 2).val) % p ^ 2 := ZMod.val_add x (n ^ 2)
      rw [hadd] at hpxn
      have hdvd : p ∣ (x.val + (n ^ 2).val) :=
        (Nat.dvd_mod_iff (dvd_pow_self p (by norm_num))).mp hpxn
      exact (Nat.dvd_add_right hpx).mp hdvd
    -- `p ∣ (n²).val ⟹ p² ∣ n.val²  ⟹  n² = 0`
    have hval : (n ^ 2).val = (n.val * n.val) % p ^ 2 := by rw [pow_two n, ZMod.val_mul]
    have hpm2 : p ∣ n.val * n.val := by
      have h1 : p ∣ (n.val * n.val) % p ^ 2 := by rw [← hval]; exact hpn2
      exact (Nat.dvd_mod_iff (dvd_pow_self p (by norm_num))).mp h1
    have hpm : p ∣ n.val := (hp.dvd_mul.mp hpm2).elim id id
    have hp2m : p ^ 2 ∣ n.val * n.val := by
      obtain ⟨s, hs⟩ := hpm; exact ⟨s * s, by rw [hs]; ring⟩
    have hzero : (n ^ 2).val = 0 := by
      rw [hval]; obtain ⟨t, ht⟩ := hp2m; rw [ht, Nat.mul_mod_right]
    exact hn ((ZMod.val_eq_zero _).mp hzero)
  · -- card = p
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    have hva : (f a).val = p * a := by
      rw [hf, ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [sq]; nlinarith [hp.pos, ha])]
    have hvb : (f b).val = p * b := by
      rw [hf, ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [sq]; nlinarith [hp.pos, hb])]
    have : p * a = p * b := by rw [← hva, ← hvb, hab]
    exact Nat.eq_of_mul_eq_mul_left hp.pos this

/-- **`√N`-phrased sharpness corollary.**  Restates
    `exists_sqDiffFree_card_sqrt_of_prime_sq` with the cardinality written as
    `Nat.sqrt (p²)`: at a prime-square modulus `N = p²` there is a
    square-difference-free set of size exactly `⌊√N⌋ = √N`. -/
theorem exists_sqDiffFree_card_eq_sqrt_of_prime_sq {p : ℕ} (hp : p.Prime) :
    ∃ A : Finset (ZMod (p ^ 2)),
      (∀ x ∈ A, ∀ n : ZMod (p ^ 2), n ^ 2 ≠ 0 → x + n ^ 2 ∉ A)
        ∧ A.card = Nat.sqrt (p ^ 2) := by
  obtain ⟨A, hfree, hcard⟩ := exists_sqDiffFree_card_sqrt_of_prime_sq hp
  exact ⟨A, hfree, by rw [hcard, Nat.sqrt_eq']⟩

/-! ### Part XXIX — The `√N` bound is NOT extremal: a two-coset `2√N` construction (`p ≡ 1 mod 4`)

Part XXVIII exhibits the subgroup `pℤ ⊆ ℤ/p²ℤ` (`√N = p` elements) as a
square-difference-free set, making the prime upper bound order-tight.  Is that
subgroup the *largest* square-difference-free set?  No — this part strictly beats
it whenever `p ≡ 1 (mod 4)`, doubling the lower bound to `2p = 2√N`.

Take a quadratic **non-residue** `d` mod `p` and adjoin the coset `d + pℤ`, giving
`A = pℤ ∪ (d + pℤ)`.  Reducing mod `p` (the ring map `φ : ℤ/p²ℤ → ℤ/pℤ`), the two
cosets land on `0` and `d̄`.  For a nonzero square `n²`:

* if `p ∣ n` then `n² = 0` (excluded), so `p ∤ n`, hence `φ n ≠ 0` and `(φ n)²` is
  a nonzero **residue**;
* the pairwise differences of `A` reduce mod `p` to `{0, d̄, −d̄}`.

Because `p ≡ 1 (mod 4)`, `−1` is itself a residue, so `d̄` a non-residue forces
`−d̄` a non-residue too.  A nonzero residue `(φ n)²` therefore never equals `0`,
`d̄`, or `−d̄`: no nonzero square is a difference, so `A` is square-difference-free
with `|A| = 2p`.

`p ≡ 1 (mod 4)` is essential: for `p ≡ 3 (mod 4)` exactly one of `d̄, −d̄` is a
residue for every `d`, so no second coset can be adjoined — the two-coset
improvement is a genuine `p ≡ 1 (mod 4)` phenomenon.  (The true maximum is
`Θ(p^{3/2}) = Θ(N^{3/4})`, a Paley-independent family of `√p` cosets matching the
`N/√minFac = N^{3/4}` single-scale upper bound at `N = p²`; that needs the
Paley-graph independence number, out of Mathlib-4.26 reach.  Two cosets is the
clean unconditional rung above the subgroup, and already shows the subgroup
`pℤ` is *not* extremal.) -/

/-- **The `√N` lower bound is not extremal.**  For a prime `p ≡ 1 (mod 4)` and
    `N = p²`, the union of the subgroup `pℤ` with a shifted coset `d + pℤ`, where
    `d` is a quadratic non-residue mod `p`, is square-difference-free and has
    exactly `2p = 2√N` elements — strictly more than the subgroup's `√N`. -/
theorem exists_sqDiffFree_card_two_mul_sqrt_of_prime_mod_four_one
    {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) :
    ∃ A : Finset (ZMod (p ^ 2)),
      (∀ x ∈ A, ∀ n : ZMod (p ^ 2), n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) ∧ A.card = 2 * p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hpdvd : p ∣ p ^ 2 := ⟨p, (sq p)⟩
  -- reduction map ℤ/p²ℤ → ℤ/pℤ
  set φ : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom hpdvd (ZMod p) with hφ
  -- a quadratic non-residue mod `p`
  obtain ⟨dz, hdz⟩ : ∃ a : ZMod p, ¬ IsSquare a := by
    apply FiniteField.exists_nonsquare
    rw [ZMod.ringChar_zmod_n]; omega
  have hdz0 : dz ≠ 0 := by rintro rfl; exact hdz ⟨0, by ring⟩
  have hneg1 : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  have hnegdz : ¬ IsSquare (-dz) := by
    intro h; exact hdz (by simpa using hneg1.mul h)
  -- integer representative `d` of the non-residue, `0 ≤ d < p`
  set d : ℕ := dz.val with hd
  have hdlt : d < p := ZMod.val_lt dz
  have hdcast : (d : ZMod p) = dz := by rw [hd]; exact ZMod.natCast_zmod_val dz
  -- the two cosets
  set f1 : ℕ → ZMod (p ^ 2) := fun k => ((p * k : ℕ) : ZMod (p ^ 2)) with hf1
  set f2 : ℕ → ZMod (p ^ 2) := fun k => ((d + p * k : ℕ) : ZMod (p ^ 2)) with hf2
  set S1 : Finset (ZMod (p ^ 2)) := (Finset.range p).image f1 with hS1
  set S2 : Finset (ZMod (p ^ 2)) := (Finset.range p).image f2 with hS2
  -- `φ` sends the first coset to `0`, the second to `dz`
  have hφ1 : ∀ y ∈ S1, φ y = 0 := by
    intro y hy
    rw [hS1, Finset.mem_image] at hy
    obtain ⟨k, _, rfl⟩ := hy
    have hmap : φ (f1 k) = ((p * k : ℕ) : ZMod p) := by rw [hf1]; exact map_natCast φ _
    rw [hmap]; push_cast; rw [ZMod.natCast_self]; ring
  have hφ2 : ∀ y ∈ S2, φ y = dz := by
    intro y hy
    rw [hS2, Finset.mem_image] at hy
    obtain ⟨k, _, rfl⟩ := hy
    have hmap : φ (f2 k) = ((d + p * k : ℕ) : ZMod p) := by rw [hf2]; exact map_natCast φ _
    rw [hmap]; push_cast; rw [ZMod.natCast_self, hdcast]; ring
  have hlevel : ∀ y ∈ S1 ∪ S2, φ y = 0 ∨ φ y = dz := by
    intro y hy
    rcases Finset.mem_union.mp hy with h | h
    · exact Or.inl (hφ1 y h)
    · exact Or.inr (hφ2 y h)
  -- `φ n = 0 ⟹ n² = 0`, i.e. `n² ≠ 0 ⟹ φ n ≠ 0`
  have hnzero : ∀ n : ZMod (p ^ 2), φ n = 0 → n ^ 2 = 0 := by
    intro n hn0
    have hφn : φ n = ((n.val : ℕ) : ZMod p) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val n]
      exact map_natCast φ _
    rw [hφn] at hn0
    have hpv : p ∣ n.val := (ZMod.natCast_eq_zero_iff _ _).mp hn0
    obtain ⟨s, hs⟩ := hpv
    have hp2 : p ^ 2 ∣ n.val * n.val := ⟨s * s, by rw [hs]; ring⟩
    have hval : (n ^ 2).val = (n.val * n.val) % p ^ 2 := by rw [pow_two n, ZMod.val_mul]
    have hz : (n ^ 2).val = 0 := by
      rw [hval]; obtain ⟨t, ht⟩ := hp2; rw [ht, Nat.mul_mod_right]
    exact (ZMod.val_eq_zero _).mp hz
  refine ⟨S1 ∪ S2, ?_, ?_⟩
  · -- square-difference-free
    intro x hx n hn hmem
    have hφx := hlevel x hx
    have hφxn := hlevel _ hmem
    have hsplit : φ (x + n ^ 2) = φ x + (φ n) ^ 2 := by rw [map_add, map_pow]
    have hφn0 : φ n ≠ 0 := fun h => hn (hnzero n h)
    have hsq : IsSquare ((φ n) ^ 2) := ⟨φ n, pow_two (φ n)⟩
    have hsqne : (φ n) ^ 2 ≠ 0 := pow_ne_zero 2 hφn0
    rw [hsplit] at hφxn
    rcases hφx with hx0 | hxd <;> rcases hφxn with hxn0 | hxnd
    · rw [hx0, zero_add] at hxn0; exact hsqne hxn0
    · rw [hx0, zero_add] at hxnd; exact hdz (hxnd ▸ hsq)
    · rw [hxd] at hxn0
      have hsval : (φ n) ^ 2 = -dz := by linear_combination hxn0
      exact hnegdz (hsval ▸ hsq)
    · rw [hxd] at hxnd
      have hsval : (φ n) ^ 2 = 0 := by linear_combination hxnd
      exact hsqne hsval
  · -- `|A| = 2p`
    have hinj1 : Set.InjOn f1 (Finset.range p) := by
      intro a ha b hb hab
      rw [Finset.coe_range, Set.mem_Iio] at ha hb
      have hva : (f1 a).val = p * a := by
        rw [hf1, ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [sq]; nlinarith [hp.pos, ha])]
      have hvb : (f1 b).val = p * b := by
        rw [hf1, ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [sq]; nlinarith [hp.pos, hb])]
      have : p * a = p * b := by rw [← hva, ← hvb, hab]
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    have hinj2 : Set.InjOn f2 (Finset.range p) := by
      intro a ha b hb hab
      rw [Finset.coe_range, Set.mem_Iio] at ha hb
      have hlta : d + p * a < p ^ 2 := by
        rw [sq]
        calc d + p * a < p + p * a := by omega
          _ = p * (a + 1) := by ring
          _ ≤ p * p := by gcongr; omega
      have hltb : d + p * b < p ^ 2 := by
        rw [sq]
        calc d + p * b < p + p * b := by omega
          _ = p * (b + 1) := by ring
          _ ≤ p * p := by gcongr; omega
      have hva : (f2 a).val = d + p * a := by rw [hf2, ZMod.val_natCast, Nat.mod_eq_of_lt hlta]
      have hvb : (f2 b).val = d + p * b := by rw [hf2, ZMod.val_natCast, Nat.mod_eq_of_lt hltb]
      have heq : d + p * a = d + p * b := by rw [← hva, ← hvb, hab]
      have : p * a = p * b := by omega
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    have hc1 : S1.card = p := by rw [hS1, Finset.card_image_of_injOn hinj1, Finset.card_range]
    have hc2 : S2.card = p := by rw [hS2, Finset.card_image_of_injOn hinj2, Finset.card_range]
    have hdisj : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      have e1 := hφ1 y hy1
      have e2 := hφ2 y hy2
      rw [e1] at e2
      exact hdz0 e2.symm
    rw [Finset.card_union_eq_card_add_card.mpr hdisj, hc1, hc2]; omega

/-- **The subgroup `pℤ` is strictly sub-extremal at `N = p²` for `p ≡ 1 (mod 4)`.**
    There is a square-difference-free set in `ℤ/p²ℤ` with *more* than `√N = p`
    elements, so the `√N` construction of Part XXVIII is not the maximum. -/
theorem exists_sqDiffFree_card_gt_sqrt_of_prime_mod_four_one
    {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) :
    ∃ A : Finset (ZMod (p ^ 2)),
      (∀ x ∈ A, ∀ n : ZMod (p ^ 2), n ^ 2 ≠ 0 → x + n ^ 2 ∉ A)
        ∧ Nat.sqrt (p ^ 2) < A.card := by
  obtain ⟨A, hfree, hcard⟩ := exists_sqDiffFree_card_two_mul_sqrt_of_prime_mod_four_one hp hp1
  refine ⟨A, hfree, ?_⟩
  rw [hcard, Nat.sqrt_eq']
  have := hp.two_le
  omega

/-! ### Part XXX — the general coset-lift (Paley) construction

Parts XXVIII (`S = {0}`, giving `√N`) and XXIX (`S = {0,d}` with `d` a non-residue and
`p ≡ 1 mod 4`, giving `2√N`) are the `k = 1, 2` cases of a single **multiplicative lift**:
*any* square-difference-free set `S ⊆ ℤ/pℤ` lifts, through the reduction
`φ : ℤ/p²ℤ → ℤ/pℤ`, to the union of cosets `⋃_{s∈S} (s + pℤ)`, which is
square-difference-free in `ℤ/p²ℤ` with exactly `|S|·p` elements.

The mechanism is uniform.  A nonzero square `n²` in `ℤ/p²ℤ` has `p ∤ n` (else `n² = 0`),
so `φ n ≠ 0` and `(φ n)²` is a nonzero square in `ℤ/pℤ`.  If `x` sits in coset `s` and
`x + n²` in coset `t`, then `t = φ(x + n²) = φ x + (φ n)² = s + (φ n)²`, exhibiting the
nonzero square `(φ n)²` as a difference `t − s` of two elements of `S` — impossible when
`S` is square-difference-free.  Distinct cosets are `φ`-separated hence disjoint, so the
cardinality is `|S|·p` on the nose.

This reduces the sharp lower-bound question at `N = p²` to a *pure* combinatorial
quantity: the largest square-difference-free set of residues in `ℤ/pℤ`, i.e. the
independence number of the Paley graph on `𝔽_p`, which is `Θ(√p)` — matching the
single-scale upper bound `N/√minFac = N^{3/4}`.  That extremal count is out of
Mathlib-4.26 reach, but the lift itself is fully machine-checked, and any *concrete*
independent set of residues now yields a concrete lower bound. -/

/-- **General coset-lift (Paley) construction.**  A square-difference-free set `S` in
`ℤ/pℤ` lifts, via the reduction `φ : ℤ/p²ℤ → ℤ/pℤ`, to the union of the cosets
`s + pℤ` over `s ∈ S`, which is square-difference-free in `ℤ/p²ℤ` and has exactly
`|S|·p` elements.  Subsumes Part XXVIII (`S = {0}`) and Part XXIX (`S = {0,d}`); the
extremal case is a Paley-independent residue set of size `√p`, giving `Θ(p^{3/2}) =
Θ(N^{3/4})`. -/
theorem sqDiffFree_lift_prime_sq {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p))
    (hS : ∀ s ∈ S, ∀ n : ZMod p, n ^ 2 ≠ 0 → s + n ^ 2 ∉ S) :
    ∃ A : Finset (ZMod (p ^ 2)),
      (∀ x ∈ A, ∀ n : ZMod (p ^ 2), n ^ 2 ≠ 0 → x + n ^ 2 ∉ A)
        ∧ A.card = S.card * p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hpdvd : p ∣ p ^ 2 := ⟨p, (sq p)⟩
  set φ : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom hpdvd (ZMod p) with hφ
  -- the coset attached to a residue `s`
  set g : ZMod p → ℕ → ZMod (p ^ 2) := fun s k => ((s.val + p * k : ℕ) : ZMod (p ^ 2)) with hg
  set coset : ZMod p → Finset (ZMod (p ^ 2)) := fun s => (Finset.range p).image (g s) with hcoset
  -- `φ` maps the `s`-coset onto `s`
  have hφcoset : ∀ s : ZMod p, ∀ y ∈ coset s, φ y = s := by
    intro s y hy
    rw [hcoset, Finset.mem_image] at hy
    obtain ⟨k, _, rfl⟩ := hy
    have hmap : φ (g s k) = ((s.val + p * k : ℕ) : ZMod p) := by rw [hg]; exact map_natCast φ _
    rw [hmap]; push_cast
    rw [ZMod.natCast_self, ZMod.natCast_zmod_val]; ring
  -- `φ n = 0 ⟹ n² = 0` (so `n² ≠ 0 ⟹ φ n ≠ 0`)
  have hnzero : ∀ n : ZMod (p ^ 2), φ n = 0 → n ^ 2 = 0 := by
    intro n hn0
    have hφn : φ n = ((n.val : ℕ) : ZMod p) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val n]
      exact map_natCast φ _
    rw [hφn] at hn0
    have hpv : p ∣ n.val := (ZMod.natCast_eq_zero_iff _ _).mp hn0
    obtain ⟨s, hs⟩ := hpv
    have hp2 : p ^ 2 ∣ n.val * n.val := ⟨s * s, by rw [hs]; ring⟩
    have hval : (n ^ 2).val = (n.val * n.val) % p ^ 2 := by rw [pow_two n, ZMod.val_mul]
    have hz : (n ^ 2).val = 0 := by
      rw [hval]; obtain ⟨t, ht⟩ := hp2; rw [ht, Nat.mul_mod_right]
    exact (ZMod.val_eq_zero _).mp hz
  -- each coset has exactly `p` elements
  have hcard_coset : ∀ s : ZMod p, (coset s).card = p := by
    intro s
    have hinj : Set.InjOn (g s) (Finset.range p) := by
      intro a ha b hb hab
      rw [Finset.coe_range, Set.mem_Iio] at ha hb
      have hlta : s.val + p * a < p ^ 2 := by
        have := ZMod.val_lt s; rw [sq]
        calc s.val + p * a < p + p * a := by omega
          _ = p * (a + 1) := by ring
          _ ≤ p * p := by gcongr; omega
      have hltb : s.val + p * b < p ^ 2 := by
        have := ZMod.val_lt s; rw [sq]
        calc s.val + p * b < p + p * b := by omega
          _ = p * (b + 1) := by ring
          _ ≤ p * p := by gcongr; omega
      have hva : (g s a).val = s.val + p * a := by rw [hg, ZMod.val_natCast, Nat.mod_eq_of_lt hlta]
      have hvb : (g s b).val = s.val + p * b := by rw [hg, ZMod.val_natCast, Nat.mod_eq_of_lt hltb]
      have heq : s.val + p * a = s.val + p * b := by rw [← hva, ← hvb, hab]
      have : p * a = p * b := by omega
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    rw [hcoset, Finset.card_image_of_injOn hinj, Finset.card_range]
  -- distinct cosets are `φ`-separated, hence disjoint
  have hdisj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint (coset s) (coset t) := by
    intro s _ t _ hst
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    exact hst ((hφcoset s y hy1).symm.trans (hφcoset t y hy2))
  refine ⟨S.biUnion coset, ?_, ?_⟩
  · -- square-difference-free
    intro x hx n hn hmem
    rw [Finset.mem_biUnion] at hx hmem
    obtain ⟨s, hsS, hxs⟩ := hx
    obtain ⟨t, htS, hts⟩ := hmem
    have hφx : φ x = s := hφcoset s x hxs
    have hφt : φ (x + n ^ 2) = t := hφcoset t (x + n ^ 2) hts
    have hφn0 : φ n ≠ 0 := fun h => hn (hnzero n h)
    have hsqne : (φ n) ^ 2 ≠ 0 := pow_ne_zero 2 hφn0
    have hsplit : φ (x + n ^ 2) = s + (φ n) ^ 2 := by rw [map_add, map_pow, hφx]
    rw [hφt] at hsplit
    exact hS s hsS (φ n) hsqne (hsplit ▸ htS)
  · -- cardinality `|S|·p`
    rw [Finset.card_biUnion hdisj]
    simp only [hcard_coset]
    rw [Finset.sum_const, smul_eq_mul]

/-- **A three-coset lift at `N = 169`, showing `2√N` is not extremal either.**
The residues `{0, 2, 7} ⊆ ℤ/13ℤ` are pairwise non-adjacent in the Paley graph
(every nonzero pairwise difference is a quadratic non-residue), i.e. they form a
square-difference-free set.  Lifting through `φ : ℤ/169ℤ → ℤ/13ℤ` yields a
square-difference-free set of `3·13 = 39 = 3√N` elements. -/
theorem exists_sqDiffFree_card_three_mul_sqrt_mod_169 :
    ∃ A : Finset (ZMod (13 ^ 2)),
      (∀ x ∈ A, ∀ n : ZMod (13 ^ 2), n ^ 2 ≠ 0 → x + n ^ 2 ∉ A)
        ∧ A.card = 3 * 13 := by
  have hp : Nat.Prime 13 := by norm_num
  have hS : ∀ s ∈ ({0, 2, 7} : Finset (ZMod 13)), ∀ n : ZMod 13,
      n ^ 2 ≠ 0 → s + n ^ 2 ∉ ({0, 2, 7} : Finset (ZMod 13)) := by decide
  obtain ⟨A, hfree, hcard⟩ := sqDiffFree_lift_prime_sq hp ({0, 2, 7} : Finset (ZMod 13)) hS
  refine ⟨A, hfree, ?_⟩
  rw [hcard]
  have hc : ({0, 2, 7} : Finset (ZMod 13)).card = 3 := by decide
  rw [hc]

/-- **The two-coset lower bound `2√N` is not extremal at `N = 169`.**  The Paley
three-coset set beats it: there is a square-difference-free set in `ℤ/169ℤ` with
strictly more than `2√N = 26` elements. -/
theorem exists_sqDiffFree_card_gt_two_sqrt_mod_169 :
    ∃ A : Finset (ZMod (13 ^ 2)),
      (∀ x ∈ A, ∀ n : ZMod (13 ^ 2), n ^ 2 ≠ 0 → x + n ^ 2 ∉ A)
        ∧ 2 * Nat.sqrt (13 ^ 2) < A.card := by
  obtain ⟨A, hfree, hcard⟩ := exists_sqDiffFree_card_three_mul_sqrt_mod_169
  refine ⟨A, hfree, ?_⟩
  rw [hcard, Nat.sqrt_eq']
  norm_num

/-! ### Part XXXI — the coset-lift is an EXACT correspondence

Part XXX proved one direction: `S` square-difference-free in `ℤ/pℤ` **implies** its
coset-union lift `⋃_{s∈S}(s + pℤ)` is square-difference-free in `ℤ/p²ℤ`.  Here we prove
the **converse**, upgrading the reduction to a genuine iff: the lift is
square-difference-free **iff** the base residue set `S` is.

The converse rests on a membership characterization — `y` lies in the `s`-coset **iff**
`φ y = s`, so each coset is *exactly* the fibre `φ⁻¹{s}`.  Given a square difference
`t = s + m²` inside `S` (`m² ≠ 0` in `ℤ/pℤ`), lift `s` and `m` naturally to `ℤ/p²ℤ`:
`x := (s.val : ℤ/p²ℤ)` sits in the `s`-coset, and `n := (m.val : ℤ/p²ℤ)` has
`(φ n)² = m² ≠ 0`, forcing `n² ≠ 0`.  Then `φ(x + n²) = s + m² = t`, so `x + n²` lands in
the `t`-coset — a square difference inside the lift.  Contrapositive: lift
square-difference-free ⟹ `S` square-difference-free.

Combined with Part XXX and the exact count `|⋃ coset| = |S|·p`, this pins the maximal
**coset-structured** square-difference-free set in `ℤ/p²ℤ` to `p` times the largest
square-difference-free residue set in `ℤ/pℤ` (the Paley independence number), on the nose. -/

/-- **The coset-lift is an exact correspondence.**  For `coset s := {s + pℤ}` realized as
`(range p).image (k ↦ s.val + p·k)` in `ℤ/p²ℤ`, the union `⋃_{s∈S} coset s` is
square-difference-free **iff** `S ⊆ ℤ/pℤ` is square-difference-free.  The `←` direction is
Part XXX (`sqDiffFree_lift_prime_sq`); the `→` direction is new and makes the lower-bound
reduction of Part XXX tight for coset-structured sets. -/
theorem sqDiffFree_lift_prime_sq_iff {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p))
    (coset : ZMod p → Finset (ZMod (p ^ 2)))
    (hcoset : ∀ s, coset s
      = (Finset.range p).image (fun k => ((s.val + p * k : ℕ) : ZMod (p ^ 2)))) :
    (∀ x ∈ S.biUnion coset, ∀ n : ZMod (p ^ 2), n ^ 2 ≠ 0 → x + n ^ 2 ∉ S.biUnion coset)
      ↔ (∀ s ∈ S, ∀ n : ZMod p, n ^ 2 ≠ 0 → s + n ^ 2 ∉ S) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hpdvd : p ∣ p ^ 2 := ⟨p, (sq p)⟩
  set φ : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom hpdvd (ZMod p) with hφ
  -- `φ` restricted to natural lifts is the reduction of the underlying `.val`
  have hφval : ∀ y : ZMod (p ^ 2), φ y = ((y.val : ℕ) : ZMod p) := by
    intro y
    conv_lhs => rw [← ZMod.natCast_zmod_val y]
    exact map_natCast φ _
  -- `φ n = 0 ⟹ n² = 0`
  have hnzero : ∀ n : ZMod (p ^ 2), φ n = 0 → n ^ 2 = 0 := by
    intro n hn0
    rw [hφval] at hn0
    have hpv : p ∣ n.val := (ZMod.natCast_eq_zero_iff _ _).mp hn0
    obtain ⟨s, hs⟩ := hpv
    have hp2 : p ^ 2 ∣ n.val * n.val := ⟨s * s, by rw [hs]; ring⟩
    have hval : (n ^ 2).val = (n.val * n.val) % p ^ 2 := by rw [pow_two n, ZMod.val_mul]
    have hz : (n ^ 2).val = 0 := by
      rw [hval]; obtain ⟨t, ht⟩ := hp2; rw [ht, Nat.mul_mod_right]
    exact (ZMod.val_eq_zero _).mp hz
  -- forward membership: elements of `coset s` reduce to `s`
  have hφcoset : ∀ s : ZMod p, ∀ y ∈ coset s, φ y = s := by
    intro s y hy
    rw [hcoset, Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [Finset.mem_range] at hk
    rw [hφval, ZMod.val_natCast, Nat.mod_eq_of_lt]
    · push_cast; rw [ZMod.natCast_self, ZMod.natCast_zmod_val]; ring
    · have hs := ZMod.val_lt s; rw [sq]
      calc s.val + p * k < p + p * k := Nat.add_lt_add_right hs (p * k)
        _ = p * (k + 1) := by ring
        _ ≤ p * p := by gcongr; omega
  -- reverse membership: the `s`-coset is *exactly* the fibre `φ⁻¹{s}`
  have hmem : ∀ s : ZMod p, ∀ y : ZMod (p ^ 2), φ y = s → y ∈ coset s := by
    intro s y hys
    rw [hcoset, Finset.mem_image]
    refine ⟨y.val / p, ?_, ?_⟩
    · rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hp.pos]
      have hlt : y.val < p ^ 2 := ZMod.val_lt y
      have hpp : p ^ 2 = p * p := sq p
      omega
    · -- `s.val + p·(y.val/p) = y.val`
      have hmod : y.val % p = s.val := by
        have h1 : ((y.val : ℕ) : ZMod p) = s := by rw [← hφval]; exact hys
        have h2 := ZMod.val_natCast (n := p) y.val
        rw [h1] at h2
        omega
      have hdm := Nat.div_add_mod y.val p
      have hval_eq : s.val + p * (y.val / p) = y.val := by omega
      rw [hval_eq, ZMod.natCast_zmod_val]
  constructor
  · -- (→) lift square-difference-free ⟹ `S` square-difference-free
    intro hA s hsS m hm hcontra
    have hple : p ≤ p ^ 2 := by nlinarith [hp.pos]
    -- natural lift of `s` sits in the lift
    set x : ZMod (p ^ 2) := ((s.val : ℕ) : ZMod (p ^ 2)) with hx
    have hsval : s.val < p ^ 2 := lt_of_lt_of_le (ZMod.val_lt s) hple
    have hφx : φ x = s := by
      rw [hx, hφval, ZMod.val_natCast, Nat.mod_eq_of_lt hsval, ZMod.natCast_zmod_val]
    have hxmem : x ∈ S.biUnion coset :=
      Finset.mem_biUnion.mpr ⟨s, hsS, hmem s x hφx⟩
    -- natural lift of `m`
    set n : ZMod (p ^ 2) := ((m.val : ℕ) : ZMod (p ^ 2)) with hn
    have hmval : m.val < p ^ 2 := lt_of_lt_of_le (ZMod.val_lt m) hple
    have hφn : φ n = m := by
      rw [hn, hφval, ZMod.val_natCast, Nat.mod_eq_of_lt hmval, ZMod.natCast_zmod_val]
    have hn2 : n ^ 2 ≠ 0 := by
      intro h
      apply hm
      rw [← hφn, ← map_pow, h, map_zero]
    -- `x + n²` lands in the `t = s + m²` coset
    have hφxn : φ (x + n ^ 2) = s + m ^ 2 := by rw [map_add, map_pow, hφx, hφn]
    have hxnmem : x + n ^ 2 ∈ S.biUnion coset :=
      Finset.mem_biUnion.mpr ⟨s + m ^ 2, hcontra, hmem _ _ hφxn⟩
    exact hA x hxmem n hn2 hxnmem
  · -- (←) `S` square-difference-free ⟹ lift square-difference-free (Part XXX)
    intro hS x hx n hn hmem'
    rw [Finset.mem_biUnion] at hx hmem'
    obtain ⟨s, hsS, hxs⟩ := hx
    obtain ⟨t, htS, hts⟩ := hmem'
    have hφx : φ x = s := hφcoset s x hxs
    have hφt : φ (x + n ^ 2) = t := hφcoset t (x + n ^ 2) hts
    have hφn0 : φ n ≠ 0 := fun h => hn (hnzero n h)
    have hsqne : (φ n) ^ 2 ≠ 0 := pow_ne_zero 2 hφn0
    have hsplit : φ (x + n ^ 2) = s + (φ n) ^ 2 := by rw [map_add, map_pow, hφx]
    rw [hφt] at hsplit
    exact hS s hsS (φ n) hsqne (hsplit ▸ htS)


/-! ### Part XXXII — the EXTREMAL square-difference-free count is super-multiplicative

Parts XXVIII–XXXI produced concrete and coset-structured lower bounds for the maximal
square-difference-free set at a prime-square modulus `N = p²`.  Here we package the
prime→prime² coset lift (`sqDiffFree_lift_prime_sq`, Part XXX) as a clean *structural*
theorem about the **maximum cardinality** of a square-difference-free set, denoted
`maxSqDiffFreeCard N`.  The lift shows this extremal count is super-multiplicative across
the step `p ↦ p²`:

  `maxSqDiffFreeCard (p²) ≥ p · maxSqDiffFreeCard p`.

Equivalently, an *extremal* square-difference-free residue set in `ℤ/pℤ` (the Paley
independence number) lifts on the nose to `p` times as many elements in `ℤ/p²ℤ`.  This turns
the earlier one-off constructions into a single quantified inequality on the extremal
function, and — via the achievement lemma — records that the maximum is genuinely attained. -/

/-- A finite set `A ⊆ ℤ/Nℤ` is **square-difference-free** when no two of its elements differ
by a nonzero square: for every `x ∈ A` and every `n` with `n² ≠ 0`, `x + n² ∉ A`. -/
def IsSqDiffFree {N : ℕ} (A : Finset (ZMod N)) : Prop :=
  ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A

instance instDecidableIsSqDiffFree {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    Decidable (IsSqDiffFree A) :=
  inferInstanceAs (Decidable (∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A))

/-- The **maximum cardinality** of a square-difference-free subset of `ℤ/Nℤ`.  The family of
square-difference-free finsets is a nonempty (it contains `∅`) finite family, so this
supremum is attained (see `exists_isSqDiffFree_card_eq_max`). -/
noncomputable def maxSqDiffFreeCard (N : ℕ) [NeZero N] : ℕ :=
  (Finset.univ.filter fun A : Finset (ZMod N) => IsSqDiffFree A).sup Finset.card

/-- Any square-difference-free set has cardinality at most the extremal count. -/
theorem le_maxSqDiffFreeCard_of_isSqDiffFree {N : ℕ} [NeZero N] {A : Finset (ZMod N)}
    (hA : IsSqDiffFree A) : A.card ≤ maxSqDiffFreeCard N := by
  rw [maxSqDiffFreeCard]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)

/-- The extremal count is **attained**: there is a square-difference-free set whose
cardinality is exactly `maxSqDiffFreeCard N`. -/
theorem exists_isSqDiffFree_card_eq_max (N : ℕ) [NeZero N] :
    ∃ A : Finset (ZMod N), IsSqDiffFree A ∧ A.card = maxSqDiffFreeCard N := by
  have hne : (Finset.univ.filter fun A : Finset (ZMod N) => IsSqDiffFree A).Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro x hx
    exact absurd hx (Finset.notMem_empty x)
  obtain ⟨A, hA, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨A, (Finset.mem_filter.mp hA).2, by rw [maxSqDiffFreeCard]; exact hsup.symm⟩

/-- **The extremal square-difference-free count is super-multiplicative across `p ↦ p²`.**
For a prime `p`, the coset lift of Part XXX carries an extremal square-difference-free
residue set in `ℤ/pℤ` to a square-difference-free set in `ℤ/p²ℤ` of exactly `p` times the
size, so `maxSqDiffFreeCard (p²) ≥ p · maxSqDiffFreeCard p`.  Because the largest
square-difference-free residue set in `ℤ/pℤ` is the Paley independence number `α(p)`, this
reads `maxSqDiffFreeCard (p²) ≥ p · α(p)` — the coset-structured lower bound as a single
inequality on the extremal function. -/
theorem maxSqDiffFreeCard_prime_sq_ge {p : ℕ} (hp : p.Prime) [NeZero p] :
    p * maxSqDiffFreeCard p ≤ maxSqDiffFreeCard (p ^ 2) := by
  obtain ⟨S, hS, hScard⟩ := exists_isSqDiffFree_card_eq_max p
  obtain ⟨A, hAfree, hAcard⟩ := sqDiffFree_lift_prime_sq hp S hS
  calc p * maxSqDiffFreeCard p = S.card * p := by rw [hScard]; ring
    _ = A.card := hAcard.symm
    _ ≤ maxSqDiffFreeCard (p ^ 2) := le_maxSqDiffFreeCard_of_isSqDiffFree hAfree

/-- **Concrete instance of the structural bound at `N = 169`.**  The Paley three-coset set
`{0,2,7} ⊆ ℤ/13ℤ` (square-difference-free, so `maxSqDiffFreeCard 13 ≥ 3`) lifts to a
square-difference-free set of `3·13 = 39` elements, giving `maxSqDiffFreeCard 169 ≥ 39`. -/
theorem le_maxSqDiffFreeCard_mod_169 : 39 ≤ maxSqDiffFreeCard (13 ^ 2) := by
  obtain ⟨A, hAfree, hAcard⟩ := exists_sqDiffFree_card_three_mul_sqrt_mod_169
  have h := le_maxSqDiffFreeCard_of_isSqDiffFree (A := A) hAfree
  rw [hAcard] at h; omega



/-! ### Part XXXIII — the coset lift works at every SQUAREFREE modulus (primality dropped)

Parts XXX–XXXII established the coset lift and the super-multiplicativity of the extremal
square-difference-free count `maxSqDiffFreeCard` across the step `p ↦ p²` **for prime `p`**.
The primality hypothesis can be weakened, but *not* to arbitrary `N`: the lift
`ℤ/Nℤ → ℤ/N²ℤ` through `φ = castHom (N ∣ N²)` is square-difference-free **iff `N` is
squarefree**.  The subtle point is a single reducedness step.  For `x ∈ coset s` and
`x + n²` in the lift with `n² ≠ 0`, one needs `(φ n)² ≠ 0` to feed the base
square-difference-freeness.  Equivalently `ZMod N` must be *reduced* (`y² = 0 → y = 0`),
which holds exactly when `N` is squarefree.  Concretely the lift **fails** at
`N = 4`: `coset 0 = {0,4,8,12} ⊆ ℤ/16ℤ` contains `0` and `4 = 2²` with `2² ≠ 0` in `ℤ/16ℤ`,
a nonzero square difference, because `2 ≠ 0` yet `2² = 0` in `ℤ/4ℤ`.

For squarefree `N` the step `N ∣ a² ⟹ N ∣ a` (`Squarefree.dvd_pow_iff_dvd`) restores the
argument.  We record the general lift and the resulting super-multiplicativity

  `maxSqDiffFreeCard (N²) ≥ N · maxSqDiffFreeCard N`  for every squarefree `N ≥ 1`,

which subsumes the prime case `maxSqDiffFreeCard_prime_sq_ge` and applies at **composite**
squarefree moduli that the prime-square constructions of Parts XXVIII–XXXII cannot reach.
The concrete witness `le_maxSqDiffFreeCard_mod_441` lifts the three-element base set
`{0,2,10} ⊆ ℤ/21ℤ` to a square-difference-free set of `3·21 = 63 = 3√N` elements in the
composite squarefree square `ℤ/441ℤ` (`441 = 21² = 3²·7²`, with `21 = 3·7` squarefree). -/

/-- **`ZMod N` is reduced when `N` is squarefree.**  If `N` is squarefree then `x² = 0`
forces `x = 0` in `ZMod N` — squarefreeness is exactly the absence of nonzero nilpotents. -/
theorem ZMod.sq_eq_zero_iff_eq_zero_of_squarefree {N : ℕ} [NeZero N] (hsf : Squarefree N)
    (x : ZMod N) : x ^ 2 = 0 → x = 0 := by
  intro hx
  have hz : (x.val * x.val) % N = 0 := by
    have h0 : (x ^ 2).val = 0 := (ZMod.val_eq_zero _).mpr hx
    rwa [pow_two x, ZMod.val_mul] at h0
  have hNv : N ∣ x.val := by
    have hNdvd : N ∣ x.val ^ 2 := by rw [pow_two]; exact Nat.dvd_of_mod_eq_zero hz
    exact (hsf.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hNdvd
  exact (ZMod.val_eq_zero x).mp (Nat.eq_zero_of_dvd_of_lt hNv (ZMod.val_lt x))

/-- **The coset lift works at every squarefree modulus.**  For squarefree `N ≥ 1`, a
square-difference-free residue set `S ⊆ ℤ/Nℤ` lifts through `φ : ℤ/N²ℤ → ℤ/Nℤ` to a
square-difference-free set of exactly `|S|·N` elements.  Generalizes
`sqDiffFree_lift_prime_sq` from prime to squarefree moduli; the squarefree hypothesis is
sharp (`ZMod N` must be reduced, cf. the `N = 4` failure discussed above). -/
theorem sqDiffFree_lift_sq_of_squarefree {N : ℕ} [NeZero N] (hsf : Squarefree N)
    (S : Finset (ZMod N))
    (hS : ∀ s ∈ S, ∀ n : ZMod N, n ^ 2 ≠ 0 → s + n ^ 2 ∉ S) :
    ∃ A : Finset (ZMod (N ^ 2)),
      (∀ x ∈ A, ∀ n : ZMod (N ^ 2), n ^ 2 ≠ 0 → x + n ^ 2 ∉ A)
        ∧ A.card = S.card * N := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  haveI : NeZero (N ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne N)⟩
  have hpdvd : N ∣ N ^ 2 := ⟨N, (sq N)⟩
  set φ : ZMod (N ^ 2) →+* ZMod N := ZMod.castHom hpdvd (ZMod N) with hφ
  -- the coset attached to a residue `s`
  set g : ZMod N → ℕ → ZMod (N ^ 2) := fun s k => ((s.val + N * k : ℕ) : ZMod (N ^ 2)) with hg
  set coset : ZMod N → Finset (ZMod (N ^ 2)) := fun s => (Finset.range N).image (g s) with hcoset
  -- `φ` maps the `s`-coset onto `s`
  have hφcoset : ∀ s : ZMod N, ∀ y ∈ coset s, φ y = s := by
    intro s y hy
    rw [hcoset, Finset.mem_image] at hy
    obtain ⟨k, _, rfl⟩ := hy
    have hmap : φ (g s k) = ((s.val + N * k : ℕ) : ZMod N) := by rw [hg]; exact map_natCast φ _
    rw [hmap]; push_cast
    rw [ZMod.natCast_self, ZMod.natCast_zmod_val]; ring
  -- `φ n = 0 ⟹ n² = 0` (a multiple of `N` squares to a multiple of `N²`, no primality needed)
  have hnzero : ∀ n : ZMod (N ^ 2), φ n = 0 → n ^ 2 = 0 := by
    intro n hn0
    have hφn : φ n = ((n.val : ℕ) : ZMod N) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val n]
      exact map_natCast φ _
    rw [hφn] at hn0
    have hpv : N ∣ n.val := (ZMod.natCast_eq_zero_iff _ _).mp hn0
    obtain ⟨s, hs⟩ := hpv
    have hp2 : N ^ 2 ∣ n.val * n.val := ⟨s * s, by rw [hs]; ring⟩
    have hval : (n ^ 2).val = (n.val * n.val) % N ^ 2 := by rw [pow_two n, ZMod.val_mul]
    have hz : (n ^ 2).val = 0 := by
      rw [hval]; obtain ⟨t, ht⟩ := hp2; rw [ht, Nat.mul_mod_right]
    exact (ZMod.val_eq_zero _).mp hz
  -- each coset has exactly `N` elements
  have hcard_coset : ∀ s : ZMod N, (coset s).card = N := by
    intro s
    have hinj : Set.InjOn (g s) (Finset.range N) := by
      intro a ha b hb hab
      rw [Finset.coe_range, Set.mem_Iio] at ha hb
      have hlta : s.val + N * a < N ^ 2 := by
        have := ZMod.val_lt s; rw [sq]
        calc s.val + N * a < N + N * a := by omega
          _ = N * (a + 1) := by ring
          _ ≤ N * N := by gcongr; omega
      have hltb : s.val + N * b < N ^ 2 := by
        have := ZMod.val_lt s; rw [sq]
        calc s.val + N * b < N + N * b := by omega
          _ = N * (b + 1) := by ring
          _ ≤ N * N := by gcongr; omega
      have hva : (g s a).val = s.val + N * a := by rw [hg, ZMod.val_natCast, Nat.mod_eq_of_lt hlta]
      have hvb : (g s b).val = s.val + N * b := by rw [hg, ZMod.val_natCast, Nat.mod_eq_of_lt hltb]
      have heq : s.val + N * a = s.val + N * b := by rw [← hva, ← hvb, hab]
      have : N * a = N * b := by omega
      exact Nat.eq_of_mul_eq_mul_left hNpos this
    rw [hcoset, Finset.card_image_of_injOn hinj, Finset.card_range]
  -- distinct cosets are `φ`-separated, hence disjoint
  have hdisj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint (coset s) (coset t) := by
    intro s _ t _ hst
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    exact hst ((hφcoset s y hy1).symm.trans (hφcoset t y hy2))
  refine ⟨S.biUnion coset, ?_, ?_⟩
  · -- square-difference-free
    intro x hx n hn hmem
    rw [Finset.mem_biUnion] at hx hmem
    obtain ⟨s, hsS, hxs⟩ := hx
    obtain ⟨t, htS, hts⟩ := hmem
    have hφx : φ x = s := hφcoset s x hxs
    have hφt : φ (x + n ^ 2) = t := hφcoset t (x + n ^ 2) hts
    -- reducedness of `ZMod N` (squarefree) turns `n² ≠ 0` into `(φ n)² ≠ 0`
    have hsqne : (φ n) ^ 2 ≠ 0 := fun hsq0 =>
      hn (hnzero n (ZMod.sq_eq_zero_iff_eq_zero_of_squarefree hsf (φ n) hsq0))
    have hsplit : φ (x + n ^ 2) = s + (φ n) ^ 2 := by rw [map_add, map_pow, hφx]
    rw [hφt] at hsplit
    exact hS s hsS (φ n) hsqne (hsplit ▸ htS)
  · -- cardinality `|S|·N`
    rw [Finset.card_biUnion hdisj]
    simp only [hcard_coset]
    rw [Finset.sum_const, smul_eq_mul]

/-- **Super-multiplicativity of the extremal count at every squarefree modulus.**  Weakening
the primality hypothesis of `maxSqDiffFreeCard_prime_sq_ge` to squarefreeness: for squarefree
`N ≥ 1` the coset lift carries an extremal square-difference-free set in `ℤ/Nℤ` to one `N`
times larger in `ℤ/N²ℤ`, so `maxSqDiffFreeCard (N²) ≥ N · maxSqDiffFreeCard N`. -/
theorem maxSqDiffFreeCard_sq_ge_of_squarefree {N : ℕ} [NeZero N] (hsf : Squarefree N) :
    N * maxSqDiffFreeCard N ≤ maxSqDiffFreeCard (N ^ 2) := by
  haveI : NeZero (N ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne N)⟩
  obtain ⟨S, hS, hScard⟩ := exists_isSqDiffFree_card_eq_max N
  obtain ⟨A, hAfree, hAcard⟩ := sqDiffFree_lift_sq_of_squarefree hsf S hS
  calc N * maxSqDiffFreeCard N = S.card * N := by rw [hScard]; ring
    _ = A.card := hAcard.symm
    _ ≤ maxSqDiffFreeCard (N ^ 2) := le_maxSqDiffFreeCard_of_isSqDiffFree hAfree

/-- **The prime super-multiplicativity is a special case.**  Re-derives
`maxSqDiffFreeCard_prime_sq_ge` from the squarefree `maxSqDiffFreeCard_sq_ge_of_squarefree`
(primes are squarefree), confirming primality was inessential — squarefreeness suffices. -/
theorem maxSqDiffFreeCard_prime_sq_ge' {p : ℕ} (hp : p.Prime) [NeZero p] :
    p * maxSqDiffFreeCard p ≤ maxSqDiffFreeCard (p ^ 2) :=
  maxSqDiffFreeCard_sq_ge_of_squarefree hp.squarefree

/-- **A composite-modulus instance of the squarefree super-multiplicativity.**  Primality is
not needed, only squarefreeness: the three-element base `{0,2,10} ⊆ ℤ/21ℤ` is
square-difference-free (each nonzero pairwise difference avoids the nonzero squares mod `21`),
and `21 = 3·7` is squarefree, so it lifts to a square-difference-free set of
`3·21 = 63 = 3√N` elements in `ℤ/441ℤ`, giving `maxSqDiffFreeCard 441 ≥ 63`.  The modulus
`441 = 21²` is composite, so the prime-square constructions of Parts XXVIII–XXXII do not
apply. -/
theorem le_maxSqDiffFreeCard_mod_441 : 63 ≤ maxSqDiffFreeCard (21 ^ 2) := by
  haveI : NeZero (21 : ℕ) := ⟨by norm_num⟩
  have hsf : Squarefree (21 : ℕ) := by
    rw [show (21 : ℕ) = 3 * 7 from rfl, Nat.squarefree_mul (by norm_num)]
    exact ⟨Nat.prime_three.prime.squarefree, (by norm_num : Nat.Prime 7).prime.squarefree⟩
  have hS : ∀ s ∈ ({0, 2, 10} : Finset (ZMod 21)), ∀ n : ZMod 21,
      n ^ 2 ≠ 0 → s + n ^ 2 ∉ ({0, 2, 10} : Finset (ZMod 21)) := by decide
  obtain ⟨A, hAfree, hAcard⟩ :=
    sqDiffFree_lift_sq_of_squarefree hsf ({0, 2, 10} : Finset (ZMod 21)) hS
  have hc : ({0, 2, 10} : Finset (ZMod 21)).card = 3 := by decide
  have h := le_maxSqDiffFreeCard_of_isSqDiffFree (A := A) hAfree
  rw [hAcard, hc] at h
  omega

/-! ### Part XXXIV — CRT multiplicativity of the extremal count

The prime-square lift (Parts XXX–XXXIII) is a *super-multiplicative* step `N ↦ N²`.
Orthogonal to it is the behaviour across **coprime** moduli.  The Chinese Remainder
isomorphism `e : ℤ/(MN)ℤ ≃+* ℤ/Mℤ × ℤ/Nℤ` carries squares to *pairs of squares*
componentwise — because a ring isomorphism preserves squaring, and in the product ring
`(u,v)` is a square iff each of `u,v` is (any `(x_M,x_N)` is realised by a single `x`).
Consequently the (transported) product `S × T` of a square-difference-free set
`S ⊆ ℤ/Mℤ` and `T ⊆ ℤ/Nℤ` is again square-difference-free: a nonzero square difference
in `ℤ/(MN)ℤ` would force a nonzero square difference in at least one factor.  This yields
the genuine **multiplicativity**
  `maxSqDiffFreeCard (M·N) ≥ maxSqDiffFreeCard M · maxSqDiffFreeCard N`  for `gcd(M,N)=1`,
the second half of the multiplicative structure of the extremal square-difference-free
function — together with the `N ↦ N²` lift it drives the classical density lower bound. -/

/-- **The CRT product of two square-difference-free sets is square-difference-free.**
For coprime `M, N` the Chinese Remainder isomorphism `e : ℤ/(MN)ℤ ≃+* ℤ/Mℤ × ℤ/Nℤ`
transports the product `S ×ˢ T` of a square-difference-free set `S ⊆ ℤ/Mℤ` and
`T ⊆ ℤ/Nℤ` to a square-difference-free set of `|S|·|T|` elements in `ℤ/(MN)ℤ`. -/
theorem sqDiffFree_crt_prod {M N : ℕ} [NeZero M] [NeZero N] (h : Nat.Coprime M N)
    (S : Finset (ZMod M)) (T : Finset (ZMod N))
    (hS : IsSqDiffFree S) (hT : IsSqDiffFree T) :
    ∃ A : Finset (ZMod (M * N)), IsSqDiffFree A ∧ A.card = S.card * T.card := by
  classical
  set e := ZMod.chineseRemainder h with he
  -- `x` lies in the transported product iff its CRT image lands in `S ×ˢ T`.
  have hmem : ∀ y : ZMod (M * N),
      y ∈ (S ×ˢ T).image (fun p => e.symm p) ↔ e y ∈ S ×ˢ T := by
    intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩; rwa [e.apply_symm_apply]
    · intro hy; exact ⟨e y, hy, e.symm_apply_apply y⟩
  refine ⟨(S ×ˢ T).image (fun p => e.symm p), ?_, ?_⟩
  · -- square-difference-free
    intro x hx n hn hcon
    rw [hmem] at hx hcon
    rw [Finset.mem_product] at hx
    rw [map_add, map_pow, Finset.mem_product] at hcon
    obtain ⟨hxM, hxN⟩ := hx
    obtain ⟨hcM, hcN⟩ := hcon
    -- `n² ≠ 0` transports to a nonzero square in the product ring.
    have hne : (e n) ^ 2 ≠ 0 := fun h0 =>
      hn (e.injective (show e (n ^ 2) = e 0 by rw [map_pow, map_zero]; exact h0))
    -- at least one component of the square `(e n)²` is nonzero
    have hcomp : ((e n).1) ^ 2 ≠ 0 ∨ ((e n).2) ^ 2 ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hne
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
      exact ⟨by simpa using hc.1, by simpa using hc.2⟩
    -- the offending component contradicts freeness of the corresponding factor
    rcases hcomp with h1 | h2
    · exact hS (e x).1 hxM (e n).1 h1 hcM
    · exact hT (e x).2 hxN (e n).2 h2 hcN
  · rw [Finset.card_image_of_injective _ e.symm.injective, Finset.card_product]

/-- **Multiplicativity of the extremal square-difference-free count across coprime moduli.**
For `gcd(M,N)=1`, extremal square-difference-free sets in `ℤ/Mℤ` and `ℤ/Nℤ` combine via the
Chinese Remainder isomorphism to a square-difference-free set in `ℤ/(MN)ℤ` of the product
size, so
  `maxSqDiffFreeCard (M·N) ≥ maxSqDiffFreeCard M · maxSqDiffFreeCard N`.
This is the coprime-multiplicative companion of the prime-square super-multiplicativity
`maxSqDiffFreeCard_sq_ge_of_squarefree`. -/
theorem maxSqDiffFreeCard_mul_ge_of_coprime {M N : ℕ} [NeZero M] [NeZero N]
    (h : Nat.Coprime M N) :
    maxSqDiffFreeCard M * maxSqDiffFreeCard N ≤ maxSqDiffFreeCard (M * N) := by
  haveI : NeZero (M * N) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
  obtain ⟨S, hS, hScard⟩ := exists_isSqDiffFree_card_eq_max M
  obtain ⟨T, hT, hTcard⟩ := exists_isSqDiffFree_card_eq_max N
  obtain ⟨A, hAfree, hAcard⟩ := sqDiffFree_crt_prod h S T hS hT
  calc maxSqDiffFreeCard M * maxSqDiffFreeCard N = S.card * T.card := by rw [hScard, hTcard]
    _ = A.card := hAcard.symm
    _ ≤ maxSqDiffFreeCard (M * N) := le_maxSqDiffFreeCard_of_isSqDiffFree hAfree

/-- **A coprime-composite witness from CRT multiplicativity.**  The three-element base
`{0,2,7} ⊆ ℤ/13ℤ` and the two-element base `{0,2} ⊆ ℤ/5ℤ` are square-difference-free, and
`13, 5` are coprime, so their CRT product is a square-difference-free set of `3·2 = 6`
elements in `ℤ/65ℤ`: `maxSqDiffFreeCard 65 ≥ 6`.  Neither `65 = 5·13` nor its factors are
prime squares, so the Part XXX–XXXIII lifts do not reach this modulus. -/
theorem le_maxSqDiffFreeCard_mod_65 : 6 ≤ maxSqDiffFreeCard (13 * 5) := by
  have hcop : Nat.Coprime 13 5 := by decide
  have hS : IsSqDiffFree ({0, 2, 7} : Finset (ZMod 13)) := by decide
  have hT : IsSqDiffFree ({0, 2} : Finset (ZMod 5)) := by decide
  obtain ⟨A, hAfree, hAcard⟩ :=
    sqDiffFree_crt_prod hcop ({0, 2, 7} : Finset (ZMod 13)) ({0, 2} : Finset (ZMod 5)) hS hT
  have hcS : ({0, 2, 7} : Finset (ZMod 13)).card = 3 := by decide
  have hcT : ({0, 2} : Finset (ZMod 5)).card = 2 := by decide
  have hle := le_maxSqDiffFreeCard_of_isSqDiffFree (A := A) hAfree
  rw [hAcard, hcS, hcT] at hle
  omega

/-! ### Part XXXV — the multiplicative law across an arbitrary family of coprime moduli

Part XXXIV combined **two** coprime moduli.  Chaining that step along a finite family of
*pairwise* coprime moduli gives the full finite-product law
  `∏ᵢ maxSqDiffFreeCard (nᵢ) ≤ maxSqDiffFreeCard (∏ᵢ nᵢ)`,
the Lean form of "the extremal square-difference-free count is super-multiplicative over
coprime factorisations".  Combined with the prime-square lift `maxSqDiffFreeCard_prime_sq_ge`
(`maxSqDiffFreeCard (p²) ≥ p · maxSqDiffFreeCard p`) this is the mechanism behind the
Ruzsa-type density-exponent lower bound: a product of distinct prime squares carries a
square-difference-free set whose size is the product of the per-prime coset bounds.

**Honesty note on the direction of iteration.**  The iteration here is over *distinct*
coprime factors, **not** repeated squaring of a single modulus.  The naive
`maxSqDiffFreeCard (N^(2^k)) ≥ N^(2^k − 1) · maxSqDiffFreeCard N` for `k ≥ 2` is *not*
obtainable from the square lift: the lift `sqDiffFree_lift_sq_of_squarefree` requires the
base ring `ℤ/Nℤ` to be **reduced** (`N` squarefree) — that is where
`ZMod.sq_eq_zero_iff_eq_zero_of_squarefree` turns `n² ≠ 0` upstairs into `(φ n)² ≠ 0`
downstairs — and `ℤ/N²ℤ` is *never* reduced (`(N : ℤ/N²ℤ)² = 0` with `N ≠ 0`).  So the
reducedness step fails at the second iterate and the single lift is genuinely a one-shot.
Distinct coprime factors sidestep this obstruction entirely. -/

/-- Every modulus admits the one-element square-difference-free set `{0}` (the predicate is
vacuous there: `n² ≠ 0` already forces `0 + n² = n² ∉ {0}`), so `maxSqDiffFreeCard N ≥ 1`. -/
theorem one_le_maxSqDiffFreeCard (N : ℕ) [NeZero N] : 1 ≤ maxSqDiffFreeCard N := by
  have hfree : IsSqDiffFree ({0} : Finset (ZMod N)) := by
    intro x hx n hn hmem
    rw [Finset.mem_singleton] at hx hmem
    subst hx
    rw [zero_add] at hmem
    exact hn hmem
  have hc : ({0} : Finset (ZMod N)).card = 1 := Finset.card_singleton 0
  have := le_maxSqDiffFreeCard_of_isSqDiffFree hfree
  omega

/-- A finite product of nonzero naturals is nonzero, as a `NeZero` instance.  This makes
`maxSqDiffFreeCard (∏ i ∈ s, n i)` well-typed whenever every factor is `NeZero`. -/
instance instNeZeroFinsetProd {ι : Type*} (n : ι → ℕ) [∀ i, NeZero (n i)]
    (s : Finset ι) : NeZero (∏ i ∈ s, n i) :=
  ⟨Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (n i)⟩

/-- **Super-multiplicativity of the extremal square-difference-free count over an arbitrary
family of pairwise coprime moduli.**  For `n : ι → ℕ` with each `n i ≠ 0` and the `n i`
pairwise coprime on a finset `s`,
  `∏ i ∈ s, maxSqDiffFreeCard (n i) ≤ maxSqDiffFreeCard (∏ i ∈ s, n i)`.
Proved by induction on `s`, peeling one factor at a time through the two-factor law
`maxSqDiffFreeCard_mul_ge_of_coprime`.  This is the finite-product generalisation of
Part XXXIV. -/
theorem maxSqDiffFreeCard_prod_ge_of_pairwise_coprime {ι : Type*} [DecidableEq ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] (s : Finset ι)
    (hco : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (n i) (n j)) :
    ∏ i ∈ s, maxSqDiffFreeCard (n i) ≤ maxSqDiffFreeCard (∏ i ∈ s, n i) := by
  induction s using Finset.induction with
  | empty => simpa using one_le_maxSqDiffFreeCard 1
  | @insert a t ha ih =>
    simp only [Finset.prod_insert ha]
    -- `n a` is coprime to the product of the remaining factors
    have hcop : Nat.Coprime (n a) (∏ i ∈ t, n i) :=
      Nat.Coprime.prod_right fun i hi =>
        hco a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi))
    -- the coprimality hypothesis restricts to `t`
    have hco_t : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Nat.Coprime (n i) (n j) :=
      fun i hi j hj => hco i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    calc maxSqDiffFreeCard (n a) * ∏ i ∈ t, maxSqDiffFreeCard (n i)
        ≤ maxSqDiffFreeCard (n a) * maxSqDiffFreeCard (∏ i ∈ t, n i) :=
          Nat.mul_le_mul (le_refl _) (ih hco_t)
      _ ≤ maxSqDiffFreeCard (n a * ∏ i ∈ t, n i) :=
          maxSqDiffFreeCard_mul_ge_of_coprime hcop

/-- **A three-distinct-prime density witness.**  The square-difference-free bases
`{0,2} ⊆ ℤ/5ℤ`, `{0,2,7} ⊆ ℤ/13ℤ`, `{0,3} ⊆ ℤ/17ℤ` give `maxSqDiffFreeCard 5 ≥ 2`,
`maxSqDiffFreeCard 13 ≥ 3`, `maxSqDiffFreeCard 17 ≥ 2`, and `5, 13, 17` are pairwise coprime,
so the multiplicative law chains to `maxSqDiffFreeCard (5·13·17) ≥ 2·3·2 = 12` at
`N = 1105`.  The modulus is squarefree but not a prime power, so none of the coset lifts
reach it — only the coprime-multiplicative law does. -/
theorem le_maxSqDiffFreeCard_mod_1105 : 12 ≤ maxSqDiffFreeCard (5 * 13 * 17) := by
  have h5 : 2 ≤ maxSqDiffFreeCard 5 := by
    have hfree : IsSqDiffFree ({0, 2} : Finset (ZMod 5)) := by decide
    have hc : ({0, 2} : Finset (ZMod 5)).card = 2 := by decide
    have := le_maxSqDiffFreeCard_of_isSqDiffFree hfree; omega
  have h13 : 3 ≤ maxSqDiffFreeCard 13 := by
    have hfree : IsSqDiffFree ({0, 2, 7} : Finset (ZMod 13)) := by decide
    have hc : ({0, 2, 7} : Finset (ZMod 13)).card = 3 := by decide
    have := le_maxSqDiffFreeCard_of_isSqDiffFree hfree; omega
  have h17 : 2 ≤ maxSqDiffFreeCard 17 := by
    have hfree : IsSqDiffFree ({0, 3} : Finset (ZMod 17)) := by decide
    have hc : ({0, 3} : Finset (ZMod 17)).card = 2 := by decide
    have := le_maxSqDiffFreeCard_of_isSqDiffFree hfree; omega
  have c1 : Nat.Coprime (5 * 13) 17 := by decide
  have c2 : Nat.Coprime 5 13 := by decide
  have step1 := maxSqDiffFreeCard_mul_ge_of_coprime (M := 5 * 13) (N := 17) c1
  have step2 := maxSqDiffFreeCard_mul_ge_of_coprime (M := 5) (N := 13) c2
  have h65 : 6 ≤ maxSqDiffFreeCard (5 * 13) := by
    have := le_trans (Nat.mul_le_mul h5 h13) step2; omega
  have := le_trans (Nat.mul_le_mul h65 h17) step1
  omega

/-! ### Part XXXVI — the sharp UPPER bound at primes `p ≡ 3 (mod 4)`

Every result so far (Parts XXX–XXXV) is a *lower* bound: the coset lifts and the
coprime-multiplicative law all *build* large square-difference-free sets, and every concrete
witness used a prime `p ≡ 1 (mod 4)` (`5, 13, 17, …`).  That was not an accident.  Here we
prove the complementary *upper* bound, which is as sharp as possible: at a prime
`p ≡ 3 (mod 4)` the extremal count **collapses to `1`**,
  `maxSqDiffFreeCard p = 1`,
so the only square-difference-free sets are the singletons and the empty set.

The mechanism is the quadratic character.  When `p ≡ 3 (mod 4)`, `-1` is a *non-residue*
(`ZMod.exists_sq_eq_neg_one_iff`), so for every nonzero `d` exactly one of `d`, `-d` is a
nonzero square (the quadratic character is multiplicative and `χ(-1) = -1`, hence
`χ(-d) = -χ(d)`).  Consequently **any** two distinct residues `a ≠ b` differ by a nonzero
square in one of the two directions `b - a`, `a - b`, and a square-difference-free set can
therefore contain at most one element.  This is the modular Sárközy phenomenon in its
extreme form: at half of all primes the square-difference graph is so dense (it is a
*tournament*-like orientation of the complete graph — every pair adjacent) that its
independence number is `1`, and the whole lower-bound construction is vacuous there. -/

/-- **At a prime `p ≡ 3 (mod 4)`, one of `d`, `-d` is a square for every nonzero `d`.**
Because `-1` is a non-residue (`ZMod.exists_sq_eq_neg_one_iff`), the quadratic character
satisfies `χ(-d) = χ(-1)·χ(d) = -χ(d)`, so `d` and `-d` have opposite characters and one of
them is `+1` (a nonzero square). -/
private lemma isSquare_or_isSquare_neg_of_mod_four_eq_three {p : ℕ} [Fact p.Prime] [NeZero p]
    (h3 : p % 4 = 3) {d : ZMod p} (hd : d ≠ 0) : IsSquare d ∨ IsSquare (-d) := by
  by_cases hsq : IsSquare d
  · exact Or.inl hsq
  · refine Or.inr ?_
    have hchar : (quadraticChar (ZMod p)) d = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr hsq
    have hne1 : ¬ IsSquare (-1 : ZMod p) := by
      rw [ZMod.exists_sq_eq_neg_one_iff]; omega
    have hcharm1 : (quadraticChar (ZMod p)) (-1 : ZMod p) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr hne1
    have hnd : (-d) ≠ 0 := neg_ne_zero.mpr hd
    have hchar_neg : (quadraticChar (ZMod p)) (-d) = 1 := by
      have hrw : (-d) = (-1 : ZMod p) * d := by ring
      rw [hrw, map_mul, hchar, hcharm1]; norm_num
    exact (quadraticChar_one_iff_isSquare hnd).mp hchar_neg

/-- **The extremal square-difference-free count is exactly `1` at every prime `p ≡ 3 (mod 4)`.**
Any square-difference-free set with two distinct elements `a ≠ b` would have `b - a` or
`a - b` equal to a nonzero square (`isSquare_or_isSquare_neg_of_mod_four_eq_three`),
contradicting square-difference-freeness in one of the two directions.  Hence every
square-difference-free set is a singleton or empty, and `maxSqDiffFreeCard p = 1` (the lower
bound `≥ 1` is `one_le_maxSqDiffFreeCard`).  This is the sharp upper bound complementing the
Part XXX–XXXV lower-bound constructions, and it pins the Paley independence number at these
primes to `1`. -/
theorem maxSqDiffFreeCard_eq_one_of_mod_four_eq_three {p : ℕ} (hp : p.Prime) [NeZero p]
    (h3 : p % 4 = 3) : maxSqDiffFreeCard p = 1 := by
  haveI := Fact.mk hp
  refine le_antisymm ?_ (one_le_maxSqDiffFreeCard p)
  obtain ⟨A, hAfree, hAcard⟩ := exists_isSqDiffFree_card_eq_max p
  rw [← hAcard, Finset.card_le_one]
  intro a ha b hb
  by_contra hne
  have hd : b - a ≠ 0 := sub_ne_zero.mpr (fun h => hne h.symm)
  rcases isSquare_or_isSquare_neg_of_mod_four_eq_three h3 hd with hsq | hsq
  · obtain ⟨r, hr⟩ := hsq
    have hn2 : r ^ 2 ≠ 0 := by rw [pow_two, ← hr]; exact hd
    have hbeq : a + r ^ 2 = b := by rw [pow_two, ← hr]; ring
    exact hAfree a ha r hn2 (by rw [hbeq]; exact hb)
  · obtain ⟨r, hr⟩ := hsq
    have hn2 : r ^ 2 ≠ 0 := by rw [pow_two, ← hr]; exact neg_ne_zero.mpr hd
    have haeq : b + r ^ 2 = a := by rw [pow_two, ← hr]; ring
    exact hAfree b hb r hn2 (by rw [haeq]; exact ha)

/-- **Concrete collapse at `p = 7`.**  Since `7 ≡ 3 (mod 4)`, the square-difference graph on
`ℤ/7ℤ` has independence number `1`: no two distinct residues are square-difference-free.
Contrast with `maxSqDiffFreeCard 5 ≥ 2` (Part XXXV), where `5 ≡ 1 (mod 4)`. -/
theorem maxSqDiffFreeCard_seven : maxSqDiffFreeCard 7 = 1 :=
  maxSqDiffFreeCard_eq_one_of_mod_four_eq_three (by norm_num) (by norm_num)

/-- **Concrete collapse at `p = 11`.**  `11 ≡ 3 (mod 4)`, so `maxSqDiffFreeCard 11 = 1`. -/
theorem maxSqDiffFreeCard_eleven : maxSqDiffFreeCard 11 = 1 :=
  maxSqDiffFreeCard_eq_one_of_mod_four_eq_three (by norm_num) (by norm_num)

/-! ### Part XXXVII — the sharp LOWER bound at primes `p ≡ 1 (mod 4)`, and the full dichotomy

Part XXXVI showed the extremal count *collapses to `1`* at every prime `p ≡ 3 (mod 4)`.  Here
we prove the exactly complementary statement at the **other** residue class: at every prime
`p ≡ 1 (mod 4)`,
  `maxSqDiffFreeCard p ≥ 2`,
so a two-element square-difference-free set always exists.  Until now the `≥ 2` bound was only
recorded for the *concrete* primes `5, 13, 17` via `decide`; this is the first *general*
lower bound at the whole residue class.

The construction mirrors Part XXXVI.  When `p ≡ 1 (mod 4)`, `-1` **is** a square
(`ZMod.exists_sq_eq_neg_one_iff`), so for a quadratic non-residue `d` the negative `-d` is
*also* a non-residue (`IsSquare` is multiplicative: `IsSquare (-1) ∧ IsSquare (-d)` would give
`IsSquare d`).  A non-residue exists (`FiniteField.exists_nonsquare`), and then `{0, d}` is
square-difference-free: neither `d` (a non-square) nor `-d` (a non-square) is a nonzero square,
so no nonzero square connects `0` to `d` in either direction.

Combining the two halves gives the **sharp dichotomy** for odd primes:
  `maxSqDiffFreeCard p = 1  ↔  p ≡ 3 (mod 4)`,   equivalently   `2 ≤ maxSqDiffFreeCard p ↔ p ≡ 1 (mod 4)`.
The parity of `(p-1)/2` — whether `-1` is a square — *exactly* decides whether the modular
Sárközy graph has independence number `1` (a tournament orientation of `K_p`) or admits a
non-trivial square-difference-free set. -/

/-- **At a prime `p ≡ 1 (mod 4)`, the negative of a non-square is a non-square.**  Because `-1`
is a square (`ZMod.exists_sq_eq_neg_one_iff`), if `-d` were a square then so would
`(-1)·(-d) = d`, contradicting `¬ IsSquare d`. -/
private lemma not_isSquare_neg_of_mod_four_eq_one {p : ℕ} [Fact p.Prime] [NeZero p]
    (h1 : p % 4 = 1) {d : ZMod p} (hd : ¬ IsSquare d) : ¬ IsSquare (-d) := by
  have hneg1 : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  intro h
  exact hd (by simpa using hneg1.mul h)

/-- **The extremal square-difference-free count is at least `2` at every prime `p ≡ 1 (mod 4)`.**
A quadratic non-residue `d ≠ 0` exists (`FiniteField.exists_nonsquare`), and `{0, d}` is
square-difference-free: `0 + n² = d` would make `d` a square, and `d + n² = 0` would make `-d`
a square (`not_isSquare_neg_of_mod_four_eq_one`), both impossible.  This is the first *general*
lower bound at the residue class `p ≡ 1 (mod 4)`, complementing Part XXXVI's collapse at
`p ≡ 3 (mod 4)`. -/
theorem two_le_maxSqDiffFreeCard_of_mod_four_eq_one {p : ℕ} (hp : p.Prime) [NeZero p]
    (h1 : p % 4 = 1) : 2 ≤ maxSqDiffFreeCard p := by
  haveI := Fact.mk hp
  obtain ⟨d, hd⟩ : ∃ a : ZMod p, ¬ IsSquare a := by
    apply FiniteField.exists_nonsquare
    rw [ZMod.ringChar_zmod_n]; omega
  have hd0 : d ≠ 0 := by rintro rfl; exact hd ⟨0, by ring⟩
  have hnegd : ¬ IsSquare (-d) := not_isSquare_neg_of_mod_four_eq_one h1 hd
  have hfree : IsSqDiffFree ({0, d} : Finset (ZMod p)) := by
    intro x hx n hn hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [zero_add] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hn h
      · exact hd ⟨n, by rw [← h]; ring⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hnegd ⟨n, by linear_combination -h⟩
      · exact hn (by linear_combination h)
  have h0 : (0 : ZMod p) ∉ ({d} : Finset (ZMod p)) := by
    simp only [Finset.mem_singleton]; exact fun h => hd0 h.symm
  have hc : ({0, d} : Finset (ZMod p)).card = 2 := by
    rw [Finset.card_insert_of_notMem h0, Finset.card_singleton]
  have := le_maxSqDiffFreeCard_of_isSqDiffFree hfree
  omega

/-- **Sharp dichotomy for odd primes.**  For an odd prime `p`,
  `maxSqDiffFreeCard p = 1  ↔  p ≡ 3 (mod 4)`.
The `←` direction is Part XXXVI (`maxSqDiffFreeCard_eq_one_of_mod_four_eq_three`); the `→`
direction is the contrapositive of Part XXXVII: an odd prime with `p % 4 ≠ 3` has `p % 4 = 1`,
whence `maxSqDiffFreeCard p ≥ 2 > 1`.  This pins the Paley/square-difference independence
number of `ℤ/pℤ` to exactly `{1}` for `p ≡ 3` and `≥ 2` for `p ≡ 1`, decided purely by whether
`-1` is a square. -/
theorem maxSqDiffFreeCard_eq_one_iff_mod_four_eq_three {p : ℕ} (hp : p.Prime) [NeZero p]
    (hodd : p % 2 = 1) : maxSqDiffFreeCard p = 1 ↔ p % 4 = 3 := by
  constructor
  · intro heq
    by_contra hne
    have h14 : p % 4 = 1 := by omega
    have := two_le_maxSqDiffFreeCard_of_mod_four_eq_one hp h14
    omega
  · exact fun h3 => maxSqDiffFreeCard_eq_one_of_mod_four_eq_three hp h3

/-- **Companion form of the dichotomy.**  For an odd prime `p`, a two-element
square-difference-free set exists iff `p ≡ 1 (mod 4)`:
  `2 ≤ maxSqDiffFreeCard p  ↔  p ≡ 1 (mod 4)`. -/
theorem two_le_maxSqDiffFreeCard_iff_mod_four_eq_one {p : ℕ} (hp : p.Prime) [NeZero p]
    (hodd : p % 2 = 1) : 2 ≤ maxSqDiffFreeCard p ↔ p % 4 = 1 := by
  constructor
  · intro h2
    by_contra hne
    have h34 : p % 4 = 3 := by omega
    have := maxSqDiffFreeCard_eq_one_of_mod_four_eq_three hp h34
    omega
  · exact two_le_maxSqDiffFreeCard_of_mod_four_eq_one hp

/-- **Concrete general lower bound at `p = 13`.**  `13 ≡ 1 (mod 4)`, so
`maxSqDiffFreeCard 13 ≥ 2` follows from the *general* theorem (not `decide`). -/
theorem two_le_maxSqDiffFreeCard_thirteen : 2 ≤ maxSqDiffFreeCard 13 :=
  two_le_maxSqDiffFreeCard_of_mod_four_eq_one (by norm_num) (by norm_num)

/-! ### Part XXXVIII — Exponential-in-`ω(N)` lower bound from the coprime-multiplicative law

Parts XXXIV–XXXV give super-multiplicativity of `maxSqDiffFreeCard` over coprime factors, and
Part XXXVII gives the per-prime floor `maxSqDiffFreeCard p ≥ 2` at every prime `p ≡ 1 (mod 4)`.
Chaining the two turns the pointwise floor into an **exponential** lower bound: a product of `k`
*distinct* primes all `≡ 1 (mod 4)` carries a square-difference-free set of size at least `2 ^ k`.

Because a squarefree `N` is the product of its `ω(N)` distinct prime factors
(`Nat.prod_primeFactors_of_squarefree`), this reads as
  `maxSqDiffFreeCard N ≥ 2 ^ ω(N)`
whenever every prime factor of `N` is `≡ 1 (mod 4)`.  Since `ω(N)` reaches
`(1 + o(1)) · log N / log log N`, the extremal square-difference-free count is *super-polynomial*
along this family — a Behrend/Ruzsa-flavoured lower bound obtained with **no analysis**, purely from
CRT (`maxSqDiffFreeCard_mul_ge_of_coprime`) and the single-prime `{0, d}` non-residue witness of
Part XXXVII.  It is the qualitative generalisation of the concrete `maxSqDiffFreeCard 1105 ≥ 12`
(`le_maxSqDiffFreeCard_mod_1105`), where the three factors `5, 13, 17 ≡ 1 (mod 4)` each contribute
a factor `≥ 2` (the `13`-factor happened to give `3`). -/

/-- **Exponential lower bound over a family of distinct primes `≡ 1 (mod 4)`.**  For an indexing
finset `s` and `n : ι → ℕ` such that every `n i` (`i ∈ s`) is prime and `≡ 1 (mod 4)`, and the
`n i` are pairwise distinct on `s`, the product `∏ i ∈ s, n i` carries a square-difference-free
set of size at least `2 ^ s.card`.  Distinct primes are coprime (`Nat.coprime_primes`), so the
finite-product super-multiplicativity `maxSqDiffFreeCard_prod_ge_of_pairwise_coprime` applies, and
each factor `maxSqDiffFreeCard (n i) ≥ 2` (Part XXXVII) turns `∏ 2 = 2 ^ s.card` into the bound. -/
theorem two_pow_card_le_maxSqDiffFreeCard_prod {ι : Type*} [DecidableEq ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] (s : Finset ι)
    (hp : ∀ i ∈ s, (n i).Prime ∧ n i % 4 = 1)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → n i ≠ n j) :
    2 ^ s.card ≤ maxSqDiffFreeCard (∏ i ∈ s, n i) := by
  -- distinct primes are coprime, so the finite-product multiplicative law applies
  have hco : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (n i) (n j) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (hp i hi).1 (hp j hj).1).mpr (hinj i hi j hj hij)
  have hprod := maxSqDiffFreeCard_prod_ge_of_pairwise_coprime n s hco
  -- each factor is `≥ 2`, so `2 ^ card = ∏ 2 ≤ ∏ maxSqDiffFreeCard (n i)`
  have hlb : 2 ^ s.card ≤ ∏ i ∈ s, maxSqDiffFreeCard (n i) := by
    calc 2 ^ s.card = ∏ _i ∈ s, 2 := (Finset.prod_const 2).symm
      _ ≤ ∏ i ∈ s, maxSqDiffFreeCard (n i) :=
          Finset.prod_le_prod' fun i hi =>
            two_le_maxSqDiffFreeCard_of_mod_four_eq_one (hp i hi).1 (hp i hi).2
  exact le_trans hlb hprod

/-- **Exponential lower bound in the number of prime factors (squarefree modulus).**  If `N` is
squarefree and every prime factor of `N` is `≡ 1 (mod 4)`, then
  `2 ^ ω(N) ≤ maxSqDiffFreeCard N`,
where `ω(N) = N.primeFactors.card`.  This is the interpretable specialisation of
`two_pow_card_le_maxSqDiffFreeCard_prod` to the identity family on `N.primeFactors`, using
`Nat.prod_primeFactors_of_squarefree` to recover `∏ p ∈ N.primeFactors, p = N`. -/
theorem two_pow_omega_le_maxSqDiffFreeCard_of_squarefree {N : ℕ} [NeZero N]
    (hsf : Squarefree N) (h4 : ∀ p ∈ N.primeFactors, p % 4 = 1) :
    2 ^ N.primeFactors.card ≤ maxSqDiffFreeCard N := by
  classical
  -- a `NeZero`-safe stand-in for the identity: `0` (never a prime factor) is sent to `1`
  let n : ℕ → ℕ := fun i => if i = 0 then 1 else i
  haveI hz : ∀ i : ℕ, NeZero (n i) := fun i => by
    show NeZero (if i = 0 then 1 else i)
    split_ifs with h
    · exact ⟨one_ne_zero⟩
    · exact ⟨h⟩
  have hval : ∀ p ∈ N.primeFactors, n p = p := fun p hp => by
    show (if p = 0 then 1 else p) = p
    rw [if_neg (Nat.prime_of_mem_primeFactors hp).pos.ne']
  have hprodN : ∏ p ∈ N.primeFactors, n p = N := by
    rw [Finset.prod_congr rfl hval, Nat.prod_primeFactors_of_squarefree hsf]
  have hp : ∀ i ∈ N.primeFactors, (n i).Prime ∧ n i % 4 = 1 := fun i hi => by
    rw [hval i hi]; exact ⟨Nat.prime_of_mem_primeFactors hi, h4 i hi⟩
  have hinj : ∀ i ∈ N.primeFactors, ∀ j ∈ N.primeFactors, i ≠ j → n i ≠ n j := by
    intro i hi j hj hij; rw [hval i hi, hval j hj]; exact hij
  have key := two_pow_card_le_maxSqDiffFreeCard_prod n N.primeFactors hp hinj
  have heq : maxSqDiffFreeCard (∏ p ∈ N.primeFactors, n p) = maxSqDiffFreeCard N := by
    congr 1
  exact heq ▸ key

/-! ### Part XXXIX — the GENERAL value-`1` characterization at every modulus

Parts XXXVI–XXXVII pinned `maxSqDiffFreeCard p` at *primes* via the residue of `p` mod `4`
(`= 1 ↔ p ≡ 3`, `≥ 2 ↔ p ≡ 1`).  Both directions there are instances of a single elementary
equivalence that holds at **every** modulus `N`, prime or not:

  `2 ≤ maxSqDiffFreeCard N  ↔  ∃ d ≠ 0, ¬ IsSquare d ∧ ¬ IsSquare (-d)`,

equivalently

  `maxSqDiffFreeCard N = 1  ↔  ∀ d ≠ 0, IsSquare d ∨ IsSquare (-d)`.

The point is purely combinatorial: square-difference-freeness is translation invariant, so a
set of size `≥ 2` exists **iff** some translate `{0, d}` is square-difference-free, and `{0, d}`
is square-difference-free **iff** neither `d` nor `-d` is a nonzero square (the two directions of
the single forbidden step `0 ⇝ d` and `d ⇝ 0`).  No field structure, primality, or character
theory is used — those enter only when one *evaluates* the right-hand condition (Parts XXXVI–XXXVII
did exactly that at primes via whether `-1` is a square).

This generalisation has genuine teeth beyond the prime case: it explains the *composite collapse*
`maxSqDiffFreeCard 6 = 1` (where every nonzero `d ∈ ℤ/6ℤ` has `d` or `-d` a square, even though
`6 = 2·3` is not prime), a value **not** reachable from the prime dichotomy, and it makes the
value-`1` set decidable at any concrete `N` by checking the `±`-square covering condition. -/

/-- **The two-element existence criterion, at every modulus.**  A square-difference-free set of
size `≥ 2` exists in `ℤ/Nℤ` **iff** there is a nonzero `d` such that neither `d` nor `-d` is a
(nonzero) square.  Forward: two distinct elements `a ≠ b` of an extremal free set force `d = b - a`
and `-d = a - b` to both avoid the nonzero squares (else the single step `a ⇝ b` or `b ⇝ a` would
break freeness).  Backward: `{0, d}` is then square-difference-free of cardinality `2`. -/
theorem two_le_maxSqDiffFreeCard_iff {N : ℕ} [NeZero N] :
    2 ≤ maxSqDiffFreeCard N ↔ ∃ d : ZMod N, d ≠ 0 ∧ ¬ IsSquare d ∧ ¬ IsSquare (-d) := by
  constructor
  · intro h2
    obtain ⟨A, hAfree, hAcard⟩ := exists_isSqDiffFree_card_eq_max N
    rw [← hAcard] at h2
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    have hd0 : b - a ≠ 0 := sub_ne_zero.mpr (fun h => hab h.symm)
    refine ⟨b - a, hd0, ?_, ?_⟩
    · rintro ⟨r, hr⟩
      have hn2 : r ^ 2 ≠ 0 := by rw [pow_two, ← hr]; exact hd0
      have hbeq : a + r ^ 2 = b := by rw [pow_two, ← hr]; ring
      exact hAfree a ha r hn2 (hbeq ▸ hb)
    · rintro ⟨r, hr⟩
      have hn2 : r ^ 2 ≠ 0 := by
        rw [pow_two, ← hr]; exact neg_ne_zero.mpr hd0
      have haeq : b + r ^ 2 = a := by rw [pow_two, ← hr]; ring
      exact hAfree b hb r hn2 (haeq ▸ ha)
  · rintro ⟨d, hd0, hnsq, hnsqneg⟩
    have hfree : IsSqDiffFree ({0, d} : Finset (ZMod N)) := by
      intro x hx n hn hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [zero_add] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exact hn h
        · exact hnsq ⟨n, by rw [← h]; ring⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exact hnsqneg ⟨n, by linear_combination -h⟩
        · exact hn (by linear_combination h)
    have h0 : (0 : ZMod N) ∉ ({d} : Finset (ZMod N)) := by
      simp only [Finset.mem_singleton]; exact fun h => hd0 h.symm
    have hc : ({0, d} : Finset (ZMod N)).card = 2 := by
      rw [Finset.card_insert_of_notMem h0, Finset.card_singleton]
    have := le_maxSqDiffFreeCard_of_isSqDiffFree hfree
    omega

/-- **The value-`1` characterization, at every modulus.**  `maxSqDiffFreeCard N = 1` exactly when
the nonzero squares and their negatives cover every nonzero residue: `∀ d ≠ 0, IsSquare d ∨
IsSquare (-d)`.  This is the negation of `two_le_maxSqDiffFreeCard_iff` (the count is always `≥ 1`
via `one_le_maxSqDiffFreeCard`, so `= 1` is equivalent to `< 2`).  It subsumes the prime collapse
`maxSqDiffFreeCard_eq_one_of_mod_four_eq_three` (whose hypothesis `p ≡ 3 (mod 4)` supplies the
right-hand covering via `-1` being a non-residue) and, unlike it, applies to composite moduli. -/
theorem maxSqDiffFreeCard_eq_one_iff {N : ℕ} [NeZero N] :
    maxSqDiffFreeCard N = 1 ↔ ∀ d : ZMod N, d ≠ 0 → IsSquare d ∨ IsSquare (-d) := by
  have h1 := one_le_maxSqDiffFreeCard N
  constructor
  · intro heq d hd
    by_contra hcon
    push_neg at hcon
    have : 2 ≤ maxSqDiffFreeCard N :=
      two_le_maxSqDiffFreeCard_iff.mpr ⟨d, hd, hcon.1, hcon.2⟩
    omega
  · intro hall
    by_contra hne
    obtain ⟨d, hd0, hnsq, hnsqneg⟩ :=
      (two_le_maxSqDiffFreeCard_iff (N := N)).mp (by omega)
    rcases hall d hd0 with h | h
    · exact hnsq h
    · exact hnsqneg h

/-- **Composite collapse `maxSqDiffFreeCard 6 = 1`.**  A value not reachable from the prime
dichotomy (`6 = 2·3` is not prime), obtained by checking the `±`-square covering condition of
`maxSqDiffFreeCard_eq_one_iff` over the six residues of `ℤ/6ℤ`.  Concretely every nonzero
`d ∈ ℤ/6ℤ` has `d` or `-d` among the nonzero squares `{1, 3, 4}`, so no two-element
square-difference-free set exists. -/
theorem maxSqDiffFreeCard_six : maxSqDiffFreeCard 6 = 1 := by
  rw [maxSqDiffFreeCard_eq_one_iff]
  decide

/-- **Re-derivation of the prime `p ≡ 3 (mod 4)` collapse from the general criterion.**  The
covering hypothesis of `maxSqDiffFreeCard_eq_one_iff` is exactly what
`isSquare_or_isSquare_neg_of_mod_four_eq_three` supplies, so the Part XXXVI collapse is the
`N = p` instance of the modulus-agnostic characterization. -/
theorem maxSqDiffFreeCard_eq_one_of_mod_four_eq_three' {p : ℕ} (hp : p.Prime) [NeZero p]
    (h3 : p % 4 = 3) : maxSqDiffFreeCard p = 1 := by
  haveI := Fact.mk hp
  rw [maxSqDiffFreeCard_eq_one_iff]
  exact fun d hd => isSquare_or_isSquare_neg_of_mod_four_eq_three h3 hd

/-! ### Part XL — the doubling law `maxSqDiffFreeCard (2N) = maxSqDiffFreeCard N` for odd `N`

Parts XXXIV–XXXV established *super*-multiplicativity of the extremal count across coprime
factors, `maxSqDiffFreeCard M · maxSqDiffFreeCard N ≤ maxSqDiffFreeCard (M·N)`, and recorded
that the reverse inequality can *fail* (`maxSqDiffFreeCard (3·7) ≥ 3 > 1 = 1·1`).  The factor
`2` is a genuine exception: because **every residue mod `2` is a square** (`0 = 0²`, `1 = 1²`),
the `ℤ/2ℤ`-component of the Chinese Remainder isomorphism `ℤ/2Nℤ ≃+* ℤ/2ℤ × ℤ/Nℤ` imposes no
constraint, so the reduction `ℤ/2Nℤ → ℤ/Nℤ` reflects nonzero squares.  This makes the reverse
inequality `maxSqDiffFreeCard (2N) ≤ maxSqDiffFreeCard N` hold, and combined with
super-multiplicativity gives the exact **doubling law**

  `maxSqDiffFreeCard (2N) = maxSqDiffFreeCard N`   for every odd `N`.

Consequently the value-`1` collapse is *stable under doubling*: `maxSqDiffFreeCard (2p) = 1`
for every prime `p ≡ 3 (mod 4)`, an infinite composite family (`6, 14, 22, 38, 46, 62, …`)
promoting the isolated `decide`-only witness `maxSqDiffFreeCard 6 = 1` to a theorem.  In fact
the numerics show the full value-`1` locus is exactly `{1, 2} ∪ {p, 2p : p prime ≡ 3 mod 4}`,
and the doubling law supplies its composite half. -/

/-- **The reduction `ℤ/2Nℤ → ℤ/Nℤ` reflects squares** (for `N` odd).  Under the Chinese
Remainder isomorphism `e : ℤ/2Nℤ ≃+* ℤ/2ℤ × ℤ/Nℤ`, an element `y` is a square as soon as its
`ℤ/Nℤ`-component `(e y).2` is: the `ℤ/2ℤ`-component `(e y).1` is *automatically* a square
(every residue mod `2` equals `0²` or `1²`), so both components of `e y` are squares, whence
`e y` — and therefore `y = e.symm (e y)` — is a square. -/
theorem isSquare_of_chineseRemainder_snd {N : ℕ} [NeZero N] (hcop : Nat.Coprime 2 N)
    {y : ZMod (2 * N)} (h : IsSquare ((ZMod.chineseRemainder hcop y).2)) : IsSquare y := by
  have h1 : IsSquare ((ZMod.chineseRemainder hcop y).1) :=
    (by decide : ∀ z : ZMod 2, IsSquare z) _
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h
  refine ⟨(ZMod.chineseRemainder hcop).symm (s, t), ?_⟩
  have hey : ZMod.chineseRemainder hcop y = (s, t) * (s, t) := by
    rw [Prod.mk_mul_mk]
    exact Prod.ext_iff.mpr ⟨hs, ht⟩
  calc y = (ZMod.chineseRemainder hcop).symm (ZMod.chineseRemainder hcop y) :=
          ((ZMod.chineseRemainder hcop).symm_apply_apply y).symm
    _ = (ZMod.chineseRemainder hcop).symm ((s, t) * (s, t)) := by rw [hey]
    _ = (ZMod.chineseRemainder hcop).symm (s, t) * (ZMod.chineseRemainder hcop).symm (s, t) :=
          map_mul _ _ _

/-- In a square-difference-free set, **two distinct elements never differ by a square**: if
`a, b ∈ A` and `b - a` is a square then, being nonzero (as `a ≠ b`), it is a *nonzero* square
`m²`, so `a + m² = b ∈ A` contradicts freeness at `a`. -/
theorem not_isSquare_sub_of_sqDiffFree {N : ℕ} [NeZero N] {A : Finset (ZMod N)}
    (hA : IsSqDiffFree A) {a b : ZMod N} (ha : a ∈ A) (hb : b ∈ A) (hne : a ≠ b) :
    ¬ IsSquare (b - a) := by
  rintro ⟨m, hm⟩
  have hsq : b - a = m ^ 2 := by rw [hm, pow_two]
  have hne0 : m ^ 2 ≠ 0 := by
    rw [← hsq]; intro h; exact hne (sub_eq_zero.mp h).symm
  have hnot : a + m ^ 2 ∉ A := hA a ha m hne0
  apply hnot
  have : a + m ^ 2 = b := by rw [← hsq]; ring
  rw [this]; exact hb

/-- **The `≤` half of the doubling law.**  For odd `N`, projecting a maximal
square-difference-free set `A ⊆ ℤ/2Nℤ` onto the `ℤ/Nℤ`-component of the Chinese Remainder
isomorphism is injective on `A` (a collision would be a difference `N`, a nonzero square in
`ℤ/2Nℤ`) and the image is again square-difference-free (a square difference downstairs lifts
to one upstairs by `isSquare_of_chineseRemainder_snd`), so
`maxSqDiffFreeCard (2N) ≤ maxSqDiffFreeCard N`. -/
theorem maxSqDiffFreeCard_two_mul_le {N : ℕ} [NeZero N] (hodd : Odd N) :
    maxSqDiffFreeCard (2 * N) ≤ maxSqDiffFreeCard N := by
  haveI : NeZero (2 * N) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne N)⟩
  have hcop : Nat.Coprime 2 N := Nat.coprime_two_left.mpr hodd
  obtain ⟨A, hAfree, hAcard⟩ := exists_isSqDiffFree_card_eq_max (2 * N)
  -- distinct `A`-elements never have a square projection-difference
  have key : ∀ a ∈ A, ∀ b ∈ A,
      IsSquare ((ZMod.chineseRemainder hcop b).2 - (ZMod.chineseRemainder hcop a).2) → a = b := by
    intro a ha b hb hsq
    by_contra hne
    have hsub : (ZMod.chineseRemainder hcop (b - a)).2
        = (ZMod.chineseRemainder hcop b).2 - (ZMod.chineseRemainder hcop a).2 := by
      rw [map_sub]; rfl
    have hsqd : IsSquare (b - a) :=
      isSquare_of_chineseRemainder_snd hcop (by rw [hsub]; exact hsq)
    exact not_isSquare_sub_of_sqDiffFree hAfree ha hb hne hsqd
  -- the projection is injective on `A`
  have hinj : Set.InjOn (fun y => (ZMod.chineseRemainder hcop y).2) (A : Set (ZMod (2 * N))) := by
    intro a ha b hb hfab
    have hfab' : (ZMod.chineseRemainder hcop a).2 = (ZMod.chineseRemainder hcop b).2 := hfab
    exact key a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb)
      (by rw [hfab', sub_self]; exact IsSquare.zero)
  -- the projected image is square-difference-free
  have hBfree : IsSqDiffFree (A.image (fun y => (ZMod.chineseRemainder hcop y).2)) := by
    intro x hx n hn hcon
    rw [Finset.mem_image] at hx hcon
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, hb2⟩ := hcon
    have hb2' : (ZMod.chineseRemainder hcop b).2
        = (ZMod.chineseRemainder hcop a).2 + n ^ 2 := hb2
    have hd : (ZMod.chineseRemainder hcop b).2 - (ZMod.chineseRemainder hcop a).2 = n ^ 2 := by
      rw [hb2']; ring
    have hsqd : IsSquare ((ZMod.chineseRemainder hcop b).2
        - (ZMod.chineseRemainder hcop a).2) := by rw [hd]; exact ⟨n, pow_two n⟩
    have hab : a = b := key a ha b hb hsqd
    apply hn
    rw [← hd, hab, sub_self]
  have hle : (A.image (fun y => (ZMod.chineseRemainder hcop y).2)).card ≤ maxSqDiffFreeCard N :=
    le_maxSqDiffFreeCard_of_isSqDiffFree hBfree
  rwa [Finset.card_image_of_injOn hinj, hAcard] at hle

/-- **The doubling law.**  For every odd `N`, `maxSqDiffFreeCard (2N) = maxSqDiffFreeCard N`:
the `≤` direction is `maxSqDiffFreeCard_two_mul_le`, the `≥` direction is coprime
super-multiplicativity `maxSqDiffFreeCard_mul_ge_of_coprime` with the trivial factor
`maxSqDiffFreeCard 2 = 1`.  The factor `2` is thus "free" — it neither shrinks nor grows the
extremal square-difference-free count. -/
theorem maxSqDiffFreeCard_two_mul {N : ℕ} [NeZero N] (hodd : Odd N) :
    maxSqDiffFreeCard (2 * N) = maxSqDiffFreeCard N := by
  haveI : NeZero (2 * N) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne N)⟩
  refine le_antisymm (maxSqDiffFreeCard_two_mul_le hodd) ?_
  have hcop : Nat.Coprime 2 N := Nat.coprime_two_left.mpr hodd
  have h2 : maxSqDiffFreeCard 2 = 1 := maxSqDiffFreeCard_eq_one_iff.mpr (by decide)
  have hge := maxSqDiffFreeCard_mul_ge_of_coprime hcop
  rwa [h2, one_mul] at hge

/-- **Composite value-`1` collapse `maxSqDiffFreeCard (2p) = 1` for every prime `p ≡ 3 (mod 4)`.**
The doubling law reduces `2p` to `p`, where the Part XXXVI collapse
`maxSqDiffFreeCard_eq_one_of_mod_four_eq_three` applies.  This upgrades the isolated
`decide`-only fact `maxSqDiffFreeCard 6 = 1` (the `p = 3` case) to an infinite family
`6, 14, 22, 38, 46, 62, …`, the composite half of the value-`1` locus
`{1, 2} ∪ {p, 2p : p prime ≡ 3 mod 4}`. -/
theorem maxSqDiffFreeCard_two_mul_prime_eq_one {p : ℕ} (hp : p.Prime) [NeZero p]
    (h3 : p % 4 = 3) : maxSqDiffFreeCard (2 * p) = 1 := by
  have hodd : Odd p := Nat.odd_iff.mpr (by omega)
  rw [maxSqDiffFreeCard_two_mul hodd]
  exact maxSqDiffFreeCard_eq_one_of_mod_four_eq_three hp h3

/-! ### Part XLI — the necessity half: a prime factor `p ≡ 1 (mod 4)` forces `2 ≤ maxSqDiffFreeCard N`

The value-`1` characterization `maxSqDiffFreeCard_eq_one_iff` shows the collapse `= 1` is
equivalent to the `±`-square covering `∀ d ≠ 0, IsSquare d ∨ IsSquare (-d)`.  Parts XXXVI and XL
proved the *sufficiency* half of the value-`1` locus `{1, 2} ∪ {p, 2p : p prime ≡ 3 mod 4}`.
Here we begin the *necessity* half by ruling out any modulus divisible by a prime `p ≡ 1 (mod 4)`.

A quadratic non-residue `e ∈ ℤ/pℤ` exists (`FiniteField.exists_nonsquare`).  The reduction
`f : ℤ/Nℤ → ℤ/pℤ` (the ring hom `ZMod.castHom (p ∣ N)`) is *surjective* and *preserves squares*
(`IsSquare.map`), so any natural lift `d = (k : ℤ/Nℤ)` of `e` is again a non-residue: `IsSquare d`
would push forward to `IsSquare e`.  Likewise `-d` is a non-residue because its reduction `-e` is
one — `-1` is a square mod `p` (as `p ≡ 1 mod 4`), so `-e = (-1)·e` is a non-residue whenever `e`
is (`not_isSquare_neg_of_mod_four_eq_one`).  Thus `{0, d}` is a two-element square-difference-free
subset of `ℤ/Nℤ`, giving `2 ≤ maxSqDiffFreeCard N` via `two_le_maxSqDiffFreeCard_iff`.

Combined with the sufficiency half, this pins the odd part of the value-`1` locus: an odd `N` with
any prime factor `≡ 1 (mod 4)` is excluded from `{N : maxSqDiffFreeCard N = 1}`. -/
theorem two_le_maxSqDiffFreeCard_of_prime_dvd_of_mod_four_eq_one
    {N p : ℕ} [NeZero N] (hp : p.Prime) (h1 : p % 4 = 1) (hdvd : p ∣ N) :
    2 ≤ maxSqDiffFreeCard N := by
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  -- a quadratic non-residue `e` mod `p`
  obtain ⟨e, he⟩ : ∃ a : ZMod p, ¬ IsSquare a := by
    apply FiniteField.exists_nonsquare
    rw [ZMod.ringChar_zmod_n]; omega
  have he0 : e ≠ 0 := by rintro rfl; exact he ⟨0, by ring⟩
  -- the square-preserving surjection `f : ℤ/Nℤ → ℤ/pℤ`, and a natural lift `↑k` of `e`
  set f : ZMod N →+* ZMod p := ZMod.castHom hdvd (ZMod p) with hf
  obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective e
  have hfk : f (k : ZMod N) = e := by rw [map_natCast]; exact hk
  refine two_le_maxSqDiffFreeCard_iff.mpr ⟨(k : ZMod N), ?_, ?_, ?_⟩
  · -- `↑k ≠ 0` : otherwise `e = f ↑k = 0`
    intro h
    apply he0
    rw [← hfk, h, map_zero]
  · -- `↑k` is a non-residue : else `IsSquare (f ↑k) = IsSquare e`
    intro hsq
    apply he
    rw [← hfk]; exact hsq.map f
  · -- `-↑k` is a non-residue : else `IsSquare (f (-↑k)) = IsSquare (-e)`
    intro hsq
    apply not_isSquare_neg_of_mod_four_eq_one h1 he
    have hfneg : f (-(k : ZMod N)) = -e := by rw [map_neg, hfk]
    rw [← hfneg]; exact hsq.map f

/-- **Necessity half of the value-`1` locus, odd part.**  If an odd modulus `N` has
`maxSqDiffFreeCard N = 1`, then every odd prime factor of `N` is `≡ 3 (mod 4)`: a factor
`p ≡ 1 (mod 4)` would force `2 ≤ maxSqDiffFreeCard N` by
`two_le_maxSqDiffFreeCard_of_prime_dvd_of_mod_four_eq_one`.  (An odd prime is `≡ 1` or `≡ 3`
mod `4`; the `≡ 1` case is excluded.)  This is the converse-flavoured complement to the
sufficiency results of Parts XXXVI and XL. -/
theorem prime_factors_mod_four_eq_three_of_maxSqDiffFreeCard_eq_one
    {N : ℕ} [NeZero N] (hN : maxSqDiffFreeCard N = 1) {p : ℕ} (hp : p.Prime)
    (hodd : p % 2 = 1) (hdvd : p ∣ N) : p % 4 = 3 := by
  by_contra hne
  -- an odd prime is `1` or `3` mod `4`; rule out `≡ 1`
  have h1 : p % 4 = 1 := by
    have := hp.two_le
    omega
  have h2 : 2 ≤ maxSqDiffFreeCard N :=
    two_le_maxSqDiffFreeCard_of_prime_dvd_of_mod_four_eq_one hp h1 hdvd
  omega

/-! ### Part XLII — Necessity half, prime-power obstruction: `p² ∣ N ⟹ 2 ≤ maxSqDiffFreeCard N`

The odd-part necessity of Part XLI rules out prime factors `p ≡ 1 (mod 4)`, but a modulus can
still fall outside the value-`1` locus `{1,2} ∪ {p, 2p : p ≡ 3 (mod 4)}` by being *non-squarefree*
(e.g. `4`, `9`, `25`, `p²`).  Here we close that gap with a single uniform statement covering
**every** prime (including `p = 2`, i.e. `4 ∣ N`).

The engine is the arithmetic fact that a natural number `a` divisible by `p` exactly once is a
non-square modulo `p²`: if `y² ≡ a (mod p²)` then `p ∣ y²`, so `p ∣ y` by primality, whence
`p² ∣ y² ≡ a` — contradicting `p² ∤ a`.  Pushing the witness `d = (p : ℤ/Nℤ)` forward along the
reduction `ℤ/Nℤ → ℤ/p²ℤ` (squares map to squares, so *non*-squares lift back), both `d = p` and
`-d = p·(p-1)` are non-squares mod `p²`, giving a two-element square-difference-free set `{0, d}`. -/

/-- **A natural with exactly one factor of `p` is a non-square mod `p².`**  If `p ∣ a` but
`p² ∤ a`, then `(a : ℤ/p²ℤ)` is not a square.  A hypothetical square root `y` gives
`y² ≡ a (mod p²)`; reducing mod `p` forces `p ∣ y` (primality), so `p² ∣ y² ≡ a`, contradicting
`p² ∤ a`. -/
private lemma not_isSquare_natCast_zmod_sq {p a : ℕ} (hp : p.Prime)
    (hdvd : p ∣ a) (hndvd : ¬ p ^ 2 ∣ a) : ¬ IsSquare ((a : ZMod (p ^ 2))) := by
  haveI := Fact.mk hp
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  rintro ⟨y, hy⟩
  set b := y.val with hb
  have hyv : ((b : ℕ) : ZMod (p ^ 2)) = y := ZMod.natCast_rightInverse y
  have hcast : ((a : ZMod (p ^ 2))) = ((b * b : ℕ) : ZMod (p ^ 2)) := by
    rw [Nat.cast_mul, hyv, ← hy]
  have hmod : a ≡ b * b [MOD p ^ 2] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  -- reduce mod `p`: `a ≡ 0` and `a ≡ b·b`, so `p ∣ b·b`, hence `p ∣ b`
  have hmodp : a ≡ b * b [MOD p] := hmod.of_dvd (dvd_pow_self p two_ne_zero)
  have hpa : a ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hdvd
  have hpbb : p ∣ b * b := (Nat.modEq_zero_iff_dvd).mp (hmodp.symm.trans hpa)
  have hpb : p ∣ b := (hp.dvd_mul.mp hpbb).elim id id
  obtain ⟨t, ht⟩ := hpb
  -- now `b·b = p²·t²`, so `a ≡ 0 (mod p²)`, i.e. `p² ∣ a`
  have hfin : a ≡ 0 [MOD p ^ 2] := by
    refine hmod.trans ?_
    rw [Nat.modEq_zero_iff_dvd]
    exact ⟨t * t, by rw [ht]; ring⟩
  exact hndvd ((Nat.modEq_zero_iff_dvd).mp hfin)

/-- **Necessity half, prime-power obstruction.**  If `p² ∣ N` for *any* prime `p`, then
`2 ≤ maxSqDiffFreeCard N`.  The witness is `d = (p : ℤ/Nℤ)`: reducing to `ℤ/p²ℤ` sends `d ↦ p` and
`-d ↦ -p = p·(p-1)`, both of which have exactly one factor of `p` and so are non-squares
(`not_isSquare_natCast_zmod_sq`); non-squareness lifts back along the ring hom via `IsSquare.map`.
Together with `{0, d}` this yields a size-`2` square-difference-free set.

This covers `p = 2` (`4 ∣ N`) and every odd prime power `p^k`, `k ≥ 2`, uniformly, closing the
non-squarefree gap in the value-`1` locus. -/
theorem two_le_maxSqDiffFreeCard_of_prime_sq_dvd
    {N p : ℕ} [NeZero N] (hp : p.Prime) (hdvd : p ^ 2 ∣ N) :
    2 ≤ maxSqDiffFreeCard N := by
  haveI := Fact.mk hp
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  -- `p² ∤ p`
  have hnp2p : ¬ p ^ 2 ∣ p := by
    intro h
    have hpp2 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
    have heq : p ^ 2 = p := Nat.dvd_antisymm h hpp2
    rw [pow_two] at heq
    exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact heq))
  -- `p² ∤ p·(p-1)`
  have hnp2 : ¬ p ^ 2 ∣ p * (p - 1) := by
    intro h
    rw [pow_two] at h
    have hpd : p ∣ (p - 1) := (Nat.mul_dvd_mul_iff_left hp.pos).mp h
    have hpos : 0 < p - 1 := by have := hp.two_le; omega
    have := Nat.le_of_dvd hpos hpd
    omega
  -- reduction homomorphism `f : ℤ/Nℤ → ℤ/p²ℤ`
  set f : ZMod N →+* ZMod (p ^ 2) := ZMod.castHom hdvd (ZMod (p ^ 2)) with hf
  have hfp : f (p : ZMod N) = (p : ZMod (p ^ 2)) := by rw [hf, map_natCast]
  -- cast identity `↑(p·(p-1)) = -↑p` in `ℤ/p²ℤ`
  have hcastneg : ((p * (p - 1) : ℕ) : ZMod (p ^ 2)) = -(p : ZMod (p ^ 2)) := by
    have hpp : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    have h1 : ((p - 1 : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) - 1 := by
      rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [Nat.cast_mul, h1]
    linear_combination hpp
  refine two_le_maxSqDiffFreeCard_iff.mpr ⟨(p : ZMod N), ?_, ?_, ?_⟩
  · -- `↑p ≠ 0` : otherwise `N ∣ p`, forcing `p² ∣ p`
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hnp2p (dvd_trans hdvd h)
  · -- `↑p` is a non-residue : else `IsSquare (f ↑p) = IsSquare (p : ℤ/p²ℤ)`
    intro hsq
    exact not_isSquare_natCast_zmod_sq hp (dvd_refl p) hnp2p (hfp ▸ hsq.map f)
  · -- `-↑p` is a non-residue : `f (-↑p) = -↑p = ↑(p·(p-1))`, a non-residue mod `p²`
    intro hsq
    have hfneg : f (-(p : ZMod N)) = -(p : ZMod (p ^ 2)) := by rw [map_neg, hfp]
    have hsq2 : IsSquare (-(p : ZMod (p ^ 2))) := hfneg ▸ hsq.map f
    exact (hcastneg ▸ not_isSquare_natCast_zmod_sq hp (dvd_mul_right p (p - 1)) hnp2) hsq2

/-- **The value-`1` locus is squarefree.**  If `maxSqDiffFreeCard N = 1`, then `N` is squarefree:
any prime square `p² ∣ N` would force `2 ≤ maxSqDiffFreeCard N` by
`two_le_maxSqDiffFreeCard_of_prime_sq_dvd`.  Combined with the odd-part result
`prime_factors_mod_four_eq_three_of_maxSqDiffFreeCard_eq_one`, the value-`1` locus is now pinned to
squarefree moduli whose odd prime factors are all `≡ 3 (mod 4)` — matching `{1,2} ∪ {p, 2p : p ≡ 3
(mod 4)}` except for the yet-to-exclude case of two distinct odd prime factors. -/
theorem squarefree_of_maxSqDiffFreeCard_eq_one {N : ℕ} [NeZero N]
    (hN : maxSqDiffFreeCard N = 1) : Squarefree N := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hdvd
  have hdvd2 : p ^ 2 ∣ N := by rw [pow_two]; exact hdvd
  have h2 : 2 ≤ maxSqDiffFreeCard N :=
    two_le_maxSqDiffFreeCard_of_prime_sq_dvd hp hdvd2
  omega

/-! ### Part XLIII — Necessity half, final obstruction: two distinct odd prime factors force
`2 ≤ maxSqDiffFreeCard N`, completing the value-`1` locus

Parts XLI–XLII pinned the value-`1` locus inside the *squarefree* moduli whose odd prime factors
are all `≡ 3 (mod 4)`.  The only remaining escapees are moduli with **two** distinct odd prime
factors (e.g. `21 = 3·7`, both `≡ 3 mod 4`): here coprime super-multiplicativity is *useless*
(each factor contributes only `1`, so the product bound is `1`), yet the count genuinely jumps
(`maxSqDiffFreeCard 21 ≥ 2`).  The mechanism is the Chinese-Remainder splitting
`ℤ/pqℤ ≃ ℤ/pℤ × ℤ/qℤ`: choose the witness `d ↔ (u, -s)` with `u` a non-residue mod `p`
(this kills `IsSquare d` through the first projection) and `s` a non-residue mod `q` (so `-d ↔
(-u, s)` has `IsSquare (-d)` killed through the second projection).  A general
*divisibility-monotonicity* lemma then transports the witness up from `ℤ/pqℤ` to any multiple `N`. -/

/-- **Divisibility monotonicity of the extremal count.**  If `m ∣ N` then
`maxSqDiffFreeCard m ≤ maxSqDiffFreeCard N`.  Lift an extremal square-difference-free set
`B ⊆ ℤ/mℤ` along the natural section `ι : b ↦ (b.val : ℤ/Nℤ)` of the reduction ring hom
`f : ℤ/Nℤ → ℤ/mℤ` (`f ∘ ι = id`).  The section is injective on `B` (apply `f`), and its image is
again square-difference-free: a square step `ι b + n² = ι b'` pushes down under `f` to
`b' = b + (f n)²`, which either contradicts freeness of `B` (when `(f n)² ≠ 0`) or forces `b' = b`
and hence `n² = 0` (when `(f n)² = 0`).  Thus the image has the same cardinality as `B`, so
`maxSqDiffFreeCard m = B.card ≤ maxSqDiffFreeCard N`. -/
theorem maxSqDiffFreeCard_le_of_dvd {m N : ℕ} [NeZero m] [NeZero N] (hmN : m ∣ N) :
    maxSqDiffFreeCard m ≤ maxSqDiffFreeCard N := by
  set f : ZMod N →+* ZMod m := ZMod.castHom hmN (ZMod m) with hf
  -- `f` retracts the section `ι b = (b.val : ℤ/Nℤ)`
  have hfι : ∀ b : ZMod m, f ((b.val : ℕ) : ZMod N) = b := fun b => by
    rw [hf, map_natCast, ZMod.natCast_rightInverse b]
  obtain ⟨B, hBfree, hBcard⟩ := exists_isSqDiffFree_card_eq_max m
  have hinj : Set.InjOn (fun b : ZMod m => ((b.val : ℕ) : ZMod N)) (B : Set (ZMod m)) := by
    intro a _ b _ hab
    have h := congrArg f hab
    simp only [hfι] at h
    exact h
  refine le_trans (le_of_eq ?_)
    (le_maxSqDiffFreeCard_of_isSqDiffFree
      (A := B.image (fun b : ZMod m => ((b.val : ℕ) : ZMod N))) ?_)
  · rw [Finset.card_image_of_injOn hinj, hBcard]
  · -- freeness of the lifted image
    intro x hx n hn hmem
    rw [Finset.mem_image] at hx
    obtain ⟨b, hbB, rfl⟩ := hx
    rw [Finset.mem_image] at hmem
    obtain ⟨b', hb'B, hb'eq⟩ := hmem
    -- push the alleged square step down along `f`
    have hdown : b' = b + (f n) ^ 2 := by
      have h := congrArg f hb'eq
      simpa only [map_add, map_pow, hfι] using h
    by_cases hfn : (f n) ^ 2 = 0
    · rw [hfn, add_zero] at hdown
      rw [hdown] at hb'eq
      exact hn (by linear_combination hb'eq.symm)
    · exact hBfree b hbB (f n) hfn (hdown ▸ hb'B)

/-- **Two distinct odd primes in a common modulus force a size-`2` free set.**  If `p ≠ q` are odd
primes both dividing `N`, then `2 ≤ maxSqDiffFreeCard N`.  Working in the CRT factor
`ℤ/pqℤ ≃ ℤ/pℤ × ℤ/qℤ`, take `d ↔ (u, -s)` where `u, s` are quadratic non-residues mod `p, q`
(`FiniteField.exists_nonsquare`): the first projection makes `d` a non-square (its image `u` is),
the second makes `-d ↔ (-u, s)` a non-square (its image `s` is), and `d ≠ 0` because `u ≠ 0`.  The
witness transports up to any multiple `N` by `maxSqDiffFreeCard_le_of_dvd`.  This closes the last
gap in the value-`1` locus: a modulus with two distinct odd prime factors is excluded. -/
theorem two_le_maxSqDiffFreeCard_of_two_odd_primes
    {N p q : ℕ} [NeZero N] (hp : p.Prime) (hq : q.Prime)
    (hpodd : p % 2 = 1) (hqodd : q % 2 = 1) (hpq : p ≠ q)
    (hpdvd : p ∣ N) (hqdvd : q ∣ N) : 2 ≤ maxSqDiffFreeCard N := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.pos.ne' hq.pos.ne'⟩
  have hpqN : p * q ∣ N := hcop.mul_dvd_of_dvd_of_dvd hpdvd hqdvd
  refine le_trans ?_ (maxSqDiffFreeCard_le_of_dvd hpqN)
  -- non-residues mod `p` and mod `q`
  obtain ⟨u, hu⟩ : ∃ a : ZMod p, ¬ IsSquare a := by
    apply FiniteField.exists_nonsquare; rw [ZMod.ringChar_zmod_n]; omega
  obtain ⟨s, hs⟩ : ∃ a : ZMod q, ¬ IsSquare a := by
    apply FiniteField.exists_nonsquare; rw [ZMod.ringChar_zmod_n]; omega
  have hu0 : u ≠ 0 := by rintro rfl; exact hu ⟨0, by ring⟩
  -- the CRT isomorphism and the witness `d ↔ (u, -s)`
  set e := ZMod.chineseRemainder hcop with he
  set d : ZMod (p * q) := e.symm (u, -s) with hd
  have hed : e d = (u, -s) := by rw [hd, e.apply_symm_apply]
  refine two_le_maxSqDiffFreeCard_iff.mpr ⟨d, ?_, ?_, ?_⟩
  · -- `d ≠ 0` : else the first CRT component `u` would be `0`
    intro h
    apply hu0
    have h2 : ((u, -s) : ZMod p × ZMod q) = 0 := by rw [← hed, h, map_zero]
    exact (Prod.ext_iff.mp h2).1
  · -- `¬ IsSquare d` : its first CRT component `u` is a non-residue
    intro hsq
    apply hu
    have hsq2 : IsSquare (e d) := hsq.map e
    rw [hed] at hsq2
    simpa using hsq2.map (RingHom.fst (ZMod p) (ZMod q))
  · -- `¬ IsSquare (-d)` : its second CRT component is `-(-s) = s`, a non-residue
    intro hsq
    apply hs
    have hsq2 : IsSquare (e (-d)) := hsq.map e
    rw [map_neg, hed] at hsq2
    simpa using hsq2.map (RingHom.snd (ZMod p) (ZMod q))

/-- **Necessity half: the value-`1` locus has at most one odd prime factor.**  If
`maxSqDiffFreeCard N = 1` then any two odd prime factors of `N` coincide — two distinct ones would
force `2 ≤ maxSqDiffFreeCard N` by `two_le_maxSqDiffFreeCard_of_two_odd_primes`.  Combined with
`squarefree_of_maxSqDiffFreeCard_eq_one` (squarefree) and
`prime_factors_mod_four_eq_three_of_maxSqDiffFreeCard_eq_one` (odd factors `≡ 3 mod 4`), this pins
the value-`1` locus to exactly `{1, 2} ∪ {p, 2p : p prime ≡ 3 (mod 4)}`. -/
theorem odd_prime_factor_unique_of_maxSqDiffFreeCard_eq_one
    {N : ℕ} [NeZero N] (hN : maxSqDiffFreeCard N = 1) {p q : ℕ}
    (hp : p.Prime) (hpodd : p % 2 = 1) (hpdvd : p ∣ N)
    (hq : q.Prime) (hqodd : q % 2 = 1) (hqdvd : q ∣ N) : p = q := by
  by_contra hpq
  have h2 : 2 ≤ maxSqDiffFreeCard N :=
    two_le_maxSqDiffFreeCard_of_two_odd_primes hp hq hpodd hqodd hpq hpdvd hqdvd
  omega

/-! ### Part XLIV — CAPSTONE: the complete value-`1` locus classification

Assembling the two halves of Parts XXXVI–XLIII gives the *exact* classification of the moduli whose
square-difference graph has independence number `1`:

* **Sufficiency** (Parts XXXVI, XL): each of `1`, `2`, a prime `p ≡ 3 (mod 4)`, and `2p` for such a
  prime collapses to `1` (`maxSqDiffFreeCard_eq_one_of_mod_four_eq_three`,
  `maxSqDiffFreeCard_two_mul_prime_eq_one`, `decide` for the two small cases).
* **Necessity** (Parts XLI–XLIII): `maxSqDiffFreeCard N = 1` forces `N` squarefree
  (`squarefree_of_maxSqDiffFreeCard_eq_one`), its odd prime factors `≡ 3 (mod 4)`
  (`prime_factors_mod_four_eq_three_of_maxSqDiffFreeCard_eq_one`) and *unique*
  (`odd_prime_factor_unique_of_maxSqDiffFreeCard_eq_one`).

The number-theoretic bridge is the squarefree factorization `N = ∏_{q ∈ primeFactors N} q`: the
prime factors lie in `{2, p}` (`p` the unique odd factor if any), so `N ∣ 2p`; writing `N = p·m`
with `p ∣ N` forces `m ∣ 2`, hence `N ∈ {p, 2p}`.  With no odd factor `N ∣ 2`, hence `N ∈ {1, 2}`.

`maxSqDiffFreeCard N = 1  ↔  N ∈ {1, 2} ∪ {p, 2p : p prime, p ≡ 3 (mod 4)}`. -/
theorem maxSqDiffFreeCard_eq_one_iff_locus {N : ℕ} [NeZero N] :
    maxSqDiffFreeCard N = 1 ↔
      N = 1 ∨ N = 2 ∨ ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (N = p ∨ N = 2 * p) := by
  constructor
  · -- NECESSITY: assemble squarefree + unique odd factor ≡3 mod4 into the explicit locus
    intro hN
    have hsf : Squarefree N := squarefree_of_maxSqDiffFreeCard_eq_one hN
    by_cases hodd : ∃ p, p.Prime ∧ p % 2 = 1 ∧ p ∣ N
    · -- there is an odd prime factor `p`; it is unique and `≡ 3 (mod 4)`
      obtain ⟨p, hp, hpodd, hpdvd⟩ := hodd
      have hp3 : p % 4 = 3 :=
        prime_factors_mod_four_eq_three_of_maxSqDiffFreeCard_eq_one hN hp hpodd hpdvd
      -- every prime factor of `N` is `2` or the unique odd factor `p`
      have hsub : N.primeFactors ⊆ ({2, p} : Finset ℕ) := by
        intro q hq
        rw [Nat.mem_primeFactors] at hq
        obtain ⟨hqp, hqdvd, _⟩ := hq
        rcases hqp.eq_two_or_odd' with h2 | hqoddq
        · subst h2; simp
        · have hqp_eq : q = p :=
            odd_prime_factor_unique_of_maxSqDiffFreeCard_eq_one hN hqp
              (Nat.odd_iff.mp hqoddq) hqdvd hp hpodd hpdvd
          subst hqp_eq; simp
      -- squarefree factorization ⟹ `N ∣ 2p`
      have h2p : (2 : ℕ) ≠ p := by omega
      have hNdvd : N ∣ 2 * p :=
        calc N = ∏ q ∈ N.primeFactors, q := (Nat.prod_primeFactors_of_squarefree hsf).symm
          _ ∣ ∏ q ∈ ({2, p} : Finset ℕ), q := Finset.prod_dvd_prod_of_subset _ _ _ hsub
          _ = 2 * p := by rw [Finset.prod_pair h2p]
      -- `p ∣ N` gives `N = p·m` with `m ∣ 2`, so `N ∈ {p, 2p}`
      obtain ⟨m, hm⟩ := hpdvd
      have key : p * m ∣ p * 2 := by rw [← hm, mul_comm p 2]; exact hNdvd
      have hm2 : m ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hp.pos key
      rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with rfl | rfl
      · exact Or.inr (Or.inr ⟨p, hp, hp3, Or.inl (by rw [hm, mul_one])⟩)
      · exact Or.inr (Or.inr ⟨p, hp, hp3, Or.inr (by rw [hm]; ring)⟩)
    · -- no odd prime factor: every prime factor is `2`, so `N ∣ 2` and `N ∈ {1, 2}`
      push_neg at hodd
      have hsub : N.primeFactors ⊆ ({2} : Finset ℕ) := by
        intro q hq
        rw [Nat.mem_primeFactors] at hq
        obtain ⟨hqp, hqdvd, _⟩ := hq
        rcases hqp.eq_two_or_odd' with h2 | hqoddq
        · subst h2; simp
        · exact absurd hqdvd (hodd q hqp (Nat.odd_iff.mp hqoddq))
      have hNdvd : N ∣ 2 :=
        calc N = ∏ q ∈ N.primeFactors, q := (Nat.prod_primeFactors_of_squarefree hsf).symm
          _ ∣ ∏ q ∈ ({2} : Finset ℕ), q := Finset.prod_dvd_prod_of_subset _ _ _ hsub
          _ = 2 := by rw [Finset.prod_singleton]
      rcases (Nat.dvd_prime Nat.prime_two).mp hNdvd with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  · -- SUFFICIENCY: each locus member collapses to `1`
    rintro (rfl | rfl | ⟨p, hp, h3, rfl | rfl⟩)
    · rw [maxSqDiffFreeCard_eq_one_iff]; decide
    · rw [maxSqDiffFreeCard_eq_one_iff]; decide
    · -- `N = p`: `rfl` eliminated `p`, so the modulus is `N` (with `NeZero N` in scope)
      exact maxSqDiffFreeCard_eq_one_of_mod_four_eq_three hp h3
    · -- `N = 2 * p`: `rfl` eliminated `N`, so `p` survives; supply `NeZero p`
      haveI : NeZero p := ⟨hp.pos.ne'⟩
      exact maxSqDiffFreeCard_two_mul_prime_eq_one hp h3

/-! ### Part XLV — Structural corollaries of the classification: divisor-closedness and a single
divisibility test

The value-`1` locus `{1, 2} ∪ {p, 2p : p prime, p ≡ 3 (mod 4)}` of Part XLIV has two clean
structural features that the divisibility-monotonicity lemma (Part XLIII) exposes directly.

* **Divisor-closedness.**  `maxSqDiffFreeCard m` is squeezed between the trivial lower bound `1`
  (`one_le_maxSqDiffFreeCard`) and `maxSqDiffFreeCard N = 1`, so *every* divisor of a value-`1`
  modulus is again value-`1`.  This is a purely order-theoretic consequence of monotonicity and uses
  none of the number theory of Parts XLI–XLIII.

* **A single divisibility test.**  The whole locus is exactly the set of divisors of `2p` as `p`
  ranges over `1` and the primes `≡ 3 (mod 4)`: the divisors of `2·1 = 2` are `{1, 2}`, and the
  divisors of `2p` (for `p` an odd prime) are `{1, 2, p, 2p}`.  This repackages the four-way
  disjunction of Part XLIV as a *single* divisibility test, whose `←` direction is a one-liner from
  divisor-closedness applied to the known value-`1` moduli `2` and `2p`. -/

/-- **The value-`1` locus is closed under divisors.**  If `m ∣ N` and `maxSqDiffFreeCard N = 1`
then `maxSqDiffFreeCard m = 1`.  Immediate from `1 ≤ maxSqDiffFreeCard m ≤ maxSqDiffFreeCard N`
(`one_le_maxSqDiffFreeCard` and the divisibility monotonicity `maxSqDiffFreeCard_le_of_dvd`). -/
theorem maxSqDiffFreeCard_eq_one_of_dvd {m N : ℕ} [NeZero m] [NeZero N]
    (hmN : m ∣ N) (hN : maxSqDiffFreeCard N = 1) : maxSqDiffFreeCard m = 1 := by
  have h1 := one_le_maxSqDiffFreeCard m
  have h2 := maxSqDiffFreeCard_le_of_dvd (m := m) (N := N) hmN
  omega

/-- **The classification as a single divisibility test.**
`maxSqDiffFreeCard N = 1  ↔  ∃ p, (p = 1 ∨ (p prime ∧ p ≡ 3 mod 4)) ∧ N ∣ 2p`.  The value-`1`
locus of Part XLIV is precisely the set of divisors of `2p` for `p ∈ {1} ∪ {primes ≡ 3 (mod 4)}`.
The forward direction reads a witness off the classification; the reverse pushes value `1` down from
`2` (case `p = 1`) or `2p` (`maxSqDiffFreeCard_two_mul_prime_eq_one`) to the divisor `N` via
`maxSqDiffFreeCard_eq_one_of_dvd`. -/
theorem maxSqDiffFreeCard_eq_one_iff_dvd_two_mul {N : ℕ} [NeZero N] :
    maxSqDiffFreeCard N = 1 ↔
      ∃ p : ℕ, (p = 1 ∨ (p.Prime ∧ p % 4 = 3)) ∧ N ∣ 2 * p := by
  constructor
  · -- read a divisibility witness off the explicit locus
    intro hN
    rw [maxSqDiffFreeCard_eq_one_iff_locus] at hN
    rcases hN with rfl | rfl | ⟨p, hp, h3, rfl | rfl⟩
    · exact ⟨1, Or.inl rfl, one_dvd _⟩                          -- `N = 1 ∣ 2`
    · exact ⟨1, Or.inl rfl, dvd_refl 2⟩                         -- `N = 2 ∣ 2`
    · exact ⟨N, Or.inr ⟨hp, h3⟩, ⟨2, by ring⟩⟩                  -- `N = p ∣ 2p` (`rfl` renamed `p` to `N`)
    · exact ⟨p, Or.inr ⟨hp, h3⟩, dvd_refl (2 * p)⟩              -- `N = 2p ∣ 2p`
  · -- divisor-closedness pushes value `1` down from `2` or `2p` to `N`
    rintro ⟨p, hp1 | ⟨hp, h3⟩, hdvd⟩
    · -- `p = 1`: `N ∣ 2` and `maxSqDiffFreeCard 2 = 1`
      subst hp1
      have h2 : maxSqDiffFreeCard 2 = 1 := by rw [maxSqDiffFreeCard_eq_one_iff]; decide
      exact maxSqDiffFreeCard_eq_one_of_dvd (by simpa using hdvd) h2
    · -- `p` prime `≡ 3 (mod 4)`: `N ∣ 2p` and `maxSqDiffFreeCard (2p) = 1`
      haveI : NeZero p := ⟨hp.pos.ne'⟩
      haveI : NeZero (2 * p) := ⟨Nat.mul_ne_zero (by norm_num) hp.pos.ne'⟩
      exact maxSqDiffFreeCard_eq_one_of_dvd hdvd (maxSqDiffFreeCard_two_mul_prime_eq_one hp h3)

/-! ### Part XLVI — Quantitative UPPER bound on the extremal count: the analytic Sárközy
decay applied to `maxSqDiffFreeCard` itself

Every upper bound recorded so far on the extremal function `maxSqDiffFreeCard N` is the
value-`1` **collapse** of Parts XXXVI–XLV (`maxSqDiffFreeCard N = 1` on the classified locus),
while every *analytic* cardinality bound of Parts VII–XXVII (`sqDiffFree_card_le_add_of_odd`,
`|A| ≤ #{n² = 0} + N/√(minFac N)`) is a statement about an **arbitrary** square-difference-free
`A`.  The two halves were never joined.  Feeding the *attained* extremal set
(`exists_isSqDiffFree_card_eq_max`) into the analytic bound bridges them: it turns the pointwise
Weyl sup-norm estimate into a bound on the canonical extremal quantity.

For a squarefree modulus the nilpotent term vanishes — `n² = 0 ⟹ n = 0`
(`ZMod.sq_eq_zero_iff_eq_zero_of_squarefree`), so `#{n : n² = 0} = 1` — leaving the clean

    `maxSqDiffFreeCard N ≤ 1 + N/√(minFac N)`   (odd squarefree `N > 1`),

equivalently the density decay

    `maxSqDiffFreeCard N / N ≤ 1/N + 1/√(minFac N)`.

This is the sharpest *unconditional* upper bound the entire circle-method line produces on the
extremal count, and it is the honest quantitative counterpart of the `2^{ω(N)}` **lower** bound
`two_pow_omega_le_maxSqDiffFreeCard_of_squarefree`.  It exhibits Sárközy's `o(N)` density decay
outright on the modulus class `minFac N → ∞` (e.g. `N` prime, where it reads `≤ 1 + √N`), and —
by the documented no-go of Part XXVII — is `Θ(N)` when `minFac N` is bounded (odd squarefree `N`
with a fixed smallest prime factor), the genuine pointwise/minor-arc barrier. -/

/-- **The nilpotent-square locus is a single point at a squarefree modulus.**  For squarefree
`N`, `n² = 0 ⟹ n = 0` (`ZMod.sq_eq_zero_iff_eq_zero_of_squarefree`), so the filter counting
square roots of `0` is exactly `{0}` and has cardinality `1`. -/
theorem sq_eq_zero_filter_card_eq_one_of_squarefree {N : ℕ} [NeZero N] (hsf : Squarefree N) :
    (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card = 1 := by
  have hset : (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)) = {0} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨ZMod.sq_eq_zero_iff_eq_zero_of_squarefree hsf n, fun h => by rw [h]; ring⟩
  rw [hset, Finset.card_singleton]

/-- **Quantitative upper bound on the extremal count (odd squarefree modulus).**  Applying the
sharp odd-modulus analytic card bound `sqDiffFree_card_le_add_of_odd` to the *attained* extremal
square-difference-free set (`exists_isSqDiffFree_card_eq_max`), with the squarefree nilpotent
count `#{n : n² = 0} = 1`:

    `maxSqDiffFreeCard N ≤ 1 + N/√(minFac N)`.

The first upper bound on `maxSqDiffFreeCard` supplied by the Weyl/circle-method machinery (all
prior ones are the value-`1` collapse of the classification).  For `N` prime this is the
Paley/independence-number bound `α ≤ 1 + √N`. -/
theorem maxSqDiffFreeCard_le_of_squarefree_odd {N : ℕ} [NeZero N] (hodd : Odd N)
    (hsf : Squarefree N) (hN : 1 < N) :
    (maxSqDiffFreeCard N : ℝ) ≤ 1 + (N : ℝ) / Real.sqrt (N.minFac) := by
  obtain ⟨A, hAfree, hAcard⟩ := exists_isSqDiffFree_card_eq_max N
  have hbound := sqDiffFree_card_le_add_of_odd hodd hN A hAfree
  rw [sq_eq_zero_filter_card_eq_one_of_squarefree hsf] at hbound
  rw [← hAcard]
  simpa using hbound

/-- **Sárközy density decay on the extremal count (odd squarefree modulus).**  Dividing the
quantitative bound `maxSqDiffFreeCard_le_of_squarefree_odd` by `N`:

    `maxSqDiffFreeCard N / N ≤ 1/N + 1/√(minFac N)`.

For odd squarefree `N` with `minFac N → ∞` (e.g. `N` prime) the right side `→ 0`: this is
Sárközy's `o(N)` density decay, unconditional on that modulus class.  It is `Θ(1)` — no decay —
exactly when `minFac N` stays bounded, the genuine pointwise barrier of Part XXVII. -/
theorem maxSqDiffFreeCard_density_le_of_squarefree_odd {N : ℕ} [NeZero N] (hodd : Odd N)
    (hsf : Squarefree N) (hN : 1 < N) :
    (maxSqDiffFreeCard N : ℝ) / N ≤ 1 / N + 1 / Real.sqrt (N.minFac) := by
  have hb := maxSqDiffFreeCard_le_of_squarefree_odd hodd hsf hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hmf : (0 : ℝ) < (N.minFac : ℝ) := by exact_mod_cast N.minFac_pos
  have hs0 : Real.sqrt (N.minFac) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hmf)
  calc (maxSqDiffFreeCard N : ℝ) / N
      ≤ (1 + (N : ℝ) / Real.sqrt (N.minFac)) / N := by gcongr
    _ = 1 / N + 1 / Real.sqrt (N.minFac) := by field_simp

/-! ### Part XLVII — The master spectral-sum (pushforward) identity: every `Lᵖ` moment at once

Parts XVII–XXVI evaluate the moments of the Weyl coefficient magnitude one exponent at a time —
the second moment `Σ‖G(r)‖²` (Part XX) and its divisor-sum form `Σ_{d∣N,d<N} N·d·φ(N/d)`
(`sqGaussSum_normSq_sum_eq_divisor_sum_of_odd`, Part XXVI).  Every one of them is a special case of a
single **pushforward identity**.  The exact spectral distribution of Part XXV
(`sqGaussSum_normSq_level_set_card_of_odd`: exactly `φ(N/d)` nonzero frequencies attain
`‖G(r)‖² = N·d`, over the proper divisors `d ∣ N`) together with its exhaustiveness
(`sqGaussSum_spectral_partition_of_odd`) says that the image of the counting measure on the `N−1`
nonzero frequencies under `r ↦ ‖G(r)‖²` is *exactly* the divisor measure `d ↦ φ(N/d)` supported on
`{N·d : d ∣ N, d < N}`.  Integrating an **arbitrary** test function `f` against both sides gives, for
odd `N`,

    Σ_{r≠0} f(‖G(r)‖²) = Σ_{d∣N, d<N} φ(N/d)·f(N·d).

This is the master identity of the entire moment tower.  Recovered as instances:
* `f = id` → the second moment (Part XXVI);
* `f = (√·)ᵐ` → the `m`-th absolute moment `Σ‖G(r)‖ᵐ` (`..._norm_pow_sum_...` below);
* `f = √·` (`m = 1`) → the `L¹` first moment `Σ‖G(r)‖ = √N·Σ_{d∣N,d<N} φ(N/d)√d`
  (`..._norm_sum_...` below) — the exact quantity computed independently for the circle-method
  `L¹` bound;
* `f = 𝟙[· ≥ t]` → the tail (major-arc) frequency counts.

No new analysis is used beyond the exhaustive spectral partition
(`sqGaussSum_gcd_mem_proper_divisors_of_odd`) and the per-level count of Part XXV; the proof is the
`p = 2` argument of `sqGaussSum_normSq_sum_eq_divisor_sum_of_odd` with the constant summand `N·d`
replaced by `f(N·d)`.

Honest caveat (motivation, not a machine-checked claim): the `L¹` moment is `Θ(N^{3/2}) = o(N²)`
(bounded by `N·d(N)` via `√d ≤ √N` and Part XXVI's partition), yet — like the exactly-`Θ(N²)`
second moment of Part XVII — it still does **not** discharge the density bound to `o(N)`: pairing
`Σ|Â(r)|²‖G(r)‖ ≤ (max_r|Â(r)|²)·Σ‖G(r)‖` against the only available `L^∞` spectral bound
`|Â(r)|² ≤ |A|²` loses a factor `√N`.  So this master identity delimits, rather than breaks, the
single-scale barrier — no fixed `Lᵖ` moment of the Weyl coefficient reaches the Sárközy `o(N)`
density; that requires the multi-scale density-increment iteration (out of Mathlib reach, Part XXVII). -/

/-- **Master spectral-sum / pushforward identity (odd modulus).**  For odd `N` and any real test
function `f`, the frequency sum of `f(‖G(r)‖²)` over the nonzero frequencies equals the divisor sum
weighting each attained magnitude `N·d` (`d ∣ N`, `d < N`) by its exact spectral multiplicity
`φ(N/d)`:

    Σ_{r≠0} f(‖G(r)‖²) = Σ_{d∣N, d<N} φ(N/d)·f(N·d).

The single identity from which every `Lᵖ` moment of the quadratic Gauss sum follows; the second
moment (`sqGaussSum_normSq_sum_eq_divisor_sum_of_odd`) is the `f = id` instance. -/
theorem sqGaussSum_spectral_sum_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (f : ℝ → ℝ) :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => f (‖sqGaussSum r‖ ^ 2))
      = ((N.divisors).filter (· < N)).sum
          (fun d => (Nat.totient (N / d) : ℝ) * f ((N : ℝ) * d)) := by
  have hfiber : ∀ r ∈ (Finset.univ \ ({0} : Finset (ZMod N))),
      Nat.gcd (2 * r).val N ∈ (N.divisors).filter (· < N) := fun r hr =>
    sqGaussSum_gcd_mem_proper_divisors_of_odd hodd
      (by rw [Finset.mem_sdiff, Finset.mem_singleton] at hr; exact hr.2)
  rw [← Finset.sum_fiberwise_of_maps_to hfiber (fun r => f (‖sqGaussSum r‖ ^ 2))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  rw [Finset.sum_congr rfl (g := fun _ => f ((N : ℝ) * d))
        (fun r hr => by
          rw [Finset.mem_filter] at hr
          rw [sqGaussSum_normSq_eq_gcd_of_odd hodd r, hr.2])]
  rw [Finset.sum_const, sqGaussSum_gcd_level_set_card_of_odd hodd hd.1.1 hd.2, nsmul_eq_mul]

/-- **All natural-power absolute moments at once (odd modulus).**  The `f = (√·)ᵐ` instance of the
master identity `sqGaussSum_spectral_sum_of_odd`: since `‖G(r)‖ = √(‖G(r)‖²)`,

    Σ_{r≠0} ‖G(r)‖ᵐ = Σ_{d∣N, d<N} φ(N/d)·(√(N·d))ᵐ.

`m = 2` recovers the second moment `Σ N·d·φ(N/d)`; `m = 1` is the `L¹` first moment below. -/
theorem sqGaussSum_norm_pow_sum_eq_divisor_sum_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (m : ℕ) :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ m)
      = ((N.divisors).filter (· < N)).sum
          (fun d => (Nat.totient (N / d) : ℝ) * (Real.sqrt ((N : ℝ) * d)) ^ m) := by
  rw [show (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖ ^ m)
        = (Finset.univ \ {(0 : ZMod N)}).sum (fun r => (Real.sqrt (‖sqGaussSum r‖ ^ 2)) ^ m) from
      Finset.sum_congr rfl (fun r _ => by rw [Real.sqrt_sq (norm_nonneg _)])]
  exact sqGaussSum_spectral_sum_of_odd hodd (fun x => (Real.sqrt x) ^ m)

/-- **Exact `L¹` first moment of the Weyl coefficient (odd modulus).**  The `m = 1` instance of
`sqGaussSum_norm_pow_sum_eq_divisor_sum_of_odd`, with `√(N·d) = √N·√d` factored out:

    Σ_{r≠0} ‖G(r)‖ = √N · Σ_{d∣N, d<N} φ(N/d)·√d.

The exact mean absolute magnitude of the quadratic Gauss sum — the `L¹` companion of the exact
second moment (Part XX) — evaluated purely from the spectral partition, with no Gauss-sum
reciprocity.  It is `Θ(N^{3/2}) = o(N²)` yet (see Part XLVII) does not by itself furnish the
Sárközy `o(N)` density. -/
theorem sqGaussSum_norm_sum_eq_divisor_sum_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖)
      = Real.sqrt N * ((N.divisors).filter (· < N)).sum
          (fun d => (Nat.totient (N / d) : ℝ) * Real.sqrt d) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 := sqGaussSum_norm_pow_sum_eq_divisor_sum_of_odd hodd 1
  simp only [pow_one] at h1
  rw [h1, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Real.sqrt_mul hN0]
  ring

/-! ### Part XLVIII — The `L¹` mass carried by the UNIT frequencies: `Σ_{r unit} ‖G(r)‖ = φ(N)·√N`

Part XLVII's master identity sums `f(‖G(r)‖²)` over *all* `N−1` nonzero frequencies.  On the
**unit** frequencies the magnitude is flat: the general pointwise evaluation
`sqGaussSum_norm_eq_sqrt_of_odd` (every unit `r` has `‖G(r)‖ = √N`, the classical `|g(r)| = √N` for a
primitive quadratic Gauss sum) makes the `L¹` mass over the units a bare constant times a count.
Summing over the group of units `(ZMod N)ˣ`, whose cardinality is Euler's totient
(`ZMod.card_units_eq_totient`), gives the exact partial first moment

    Σ_{u ∈ (ZMod N)ˣ} ‖G(u)‖ = φ(N)·√N        (odd `N`).

This is the primitive-frequency slice of the full `L¹` first moment of Part XLVII: it isolates
exactly the `d = 1` level (the units are precisely the `r` with `gcd((2r).val, N) = 1`, magnitude
`√N`, and there are `φ(N)` of them).  At a **prime** every nonzero frequency is a unit, so the slice
becomes the *entire* nonzero sum, recovering the textbook `L¹` first moment `Σ_{r≠0} ‖G(r)‖ =
(p−1)·√p` (`sqGaussSum_norm_sum_of_prime`). -/

/-- **`L¹` mass of the unit frequencies (odd modulus).**  Every unit frequency contributes the flat
magnitude `√N` (`sqGaussSum_norm_eq_sqrt_of_odd`), and there are `φ(N)` of them
(`ZMod.card_units_eq_totient`), so the total absolute mass over the unit group is

    Σ_{u ∈ (ZMod N)ˣ} ‖G(u)‖ = φ(N)·√N.

The primitive (`d = 1`, `gcd((2r).val, N) = 1`) slice of the full `L¹` first moment
`sqGaussSum_norm_sum_eq_divisor_sum_of_odd` of Part XLVII. -/
theorem sqGaussSum_norm_sum_units_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    (Finset.univ.sum (fun u : (ZMod N)ˣ => ‖sqGaussSum (u : ZMod N)‖))
      = (Nat.totient N : ℝ) * Real.sqrt N := by
  rw [Finset.sum_congr rfl (fun u _ => sqGaussSum_norm_eq_sqrt_of_odd hodd u.isUnit),
      Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]

/-- **Exact `L¹` first moment at a prime modulus.**  At a prime every nonzero frequency is a unit,
so the flat magnitude `√p` (`sqGaussSum_norm_eq_sqrt_of_prime`) holds across all `p − 1` of them and
the total absolute mass of the Weyl coefficient is

    Σ_{r≠0} ‖G(r)‖ = (p−1)·√p.

The prime instance of both the unit slice `sqGaussSum_norm_sum_units_of_odd` (with `φ(p) = p−1`) and
the divisor-sum first moment `sqGaussSum_norm_sum_eq_divisor_sum_of_odd` (Part XLVII: at a prime the
only proper divisor is `d = 1`). -/
theorem sqGaussSum_norm_sum_of_prime {p : ℕ} [NeZero p] (hp : p.Prime) (hN2 : p ≠ 2) :
    (Finset.univ \ {(0 : ZMod p)}).sum (fun r => ‖sqGaussSum r‖) = ((p : ℝ) - 1) * Real.sqrt p := by
  rw [Finset.sum_congr rfl (fun r hr => sqGaussSum_norm_eq_sqrt_of_prime hp hN2
        (by rw [Finset.mem_sdiff, Finset.mem_singleton] at hr; exact hr.2)),
      Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ \ {(0 : ZMod p)}).card = p - 1 := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ ({0} : Finset (ZMod p)))
    rw [Finset.card_univ, ZMod.card, Finset.card_singleton] at h
    omega
  rw [hcard, Nat.cast_sub hp.one_lt.le, Nat.cast_one]

/-! ### Part XLIX — The TOTAL `L¹` mass over ALL frequencies: the boundary correction disappears

Part XLVII computes the `L¹` first moment over the `N−1` *nonzero* frequencies as a *proper* divisor
sum `√N·Σ_{d∣N, d<N} φ(N/d)√d`, with the top divisor `d = N` conspicuously excluded.  Restoring the
zero frequency `r = 0` — whose contribution is the flat maximum `‖G(0)‖ = N` (`sqGaussSum_zero`) —
supplies exactly the missing summand: `N = √N·√N` is precisely `√N` times the `d = N` term
`φ(N/N)·√N = φ(1)·√N = √N`.  So the total mass has the **exceptional-term-free** closed form

    Σ_{r ∈ ZMod N} ‖G(r)‖ = √N · Σ_{d∣N} φ(N/d)·√d,

a clean full Dirichlet-type divisor sum with no boundary correction — the zero frequency is not an
outlier to the spectral distribution but the completion of it.  The proper-divisor sum of Part XLVII
was an artefact of excluding `r = 0`; over the whole group the divisor sum closes.

The coefficient `Σ_{d∣N} φ(N/d)√d` is the Dirichlet convolution `(φ ⋆ (·^{1/2}))(N)` of two
multiplicative functions, hence multiplicative in `N`; at a prime `p` it is `φ(p)·√1 + φ(1)·√p =
(p−1) + √p`, recovering the total prime mass `Σ_{r} ‖G(r)‖ = √p·((p−1)+√p) = p + (p−1)√p`
(`sqGaussSum_norm_sum_total_of_prime` below): the trivial term `p` plus the `(p−1)√p` of Part XLVIII. -/

/-- **Exact total `L¹` mass over ALL frequencies (odd modulus).**  Adjoining the zero-frequency term
`‖G(0)‖ = N` (`sqGaussSum_zero`) to the nonzero first moment of Part XLVII
(`sqGaussSum_norm_sum_eq_divisor_sum_of_odd`) completes the proper divisor sum: `N = √N·√N` is exactly
the missing `d = N` summand `φ(1)·√N`.  Hence the entire `L¹` mass carries the boundary-correction-free
closed form

    Σ_{r ∈ ZMod N} ‖G(r)‖ = √N · Σ_{d∣N} φ(N/d)·√d,

the full Dirichlet divisor sum `√N·(φ ⋆ √)(N)`. -/
theorem sqGaussSum_norm_sum_total_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    (Finset.univ.sum (fun r : ZMod N => ‖sqGaussSum r‖))
      = Real.sqrt N * ((N.divisors).sum (fun d => (Nat.totient (N / d) : ℝ) * Real.sqrt d)) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- split the univ sum into the zero frequency and the nonzero frequencies
  have hsplit : (Finset.univ.sum (fun r : ZMod N => ‖sqGaussSum r‖))
      = ‖sqGaussSum (0 : ZMod N)‖
        + (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖sqGaussSum r‖) := by
    rw [← Finset.erase_eq]
    exact (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ 0)).symm
  -- the zero frequency contributes the flat maximum N
  have hzero : ‖sqGaussSum (0 : ZMod N)‖ = (N : ℝ) := by
    rw [sqGaussSum_zero, Complex.norm_natCast]
  -- split the top divisor d = N off the full divisor sum
  have hNmem : N ∈ N.divisors := Nat.mem_divisors_self N (NeZero.ne N)
  have hdiv : (N.divisors).sum (fun d => (Nat.totient (N / d) : ℝ) * Real.sqrt d)
      = (Nat.totient (N / N) : ℝ) * Real.sqrt N
        + ((N.divisors).erase N).sum (fun d => (Nat.totient (N / d) : ℝ) * Real.sqrt d) :=
    (Finset.add_sum_erase _ _ hNmem).symm
  -- erasing the top divisor is the same as keeping the proper divisors
  have herase : (N.divisors).erase N = (N.divisors).filter (· < N) := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hdN, hd⟩
      exact ⟨hd, lt_of_le_of_ne (Nat.le_of_dvd hNpos (Nat.mem_divisors.mp hd).1) hdN⟩
    · rintro ⟨hd, hlt⟩
      exact ⟨Nat.ne_of_lt hlt, hd⟩
  rw [hsplit, hzero, hdiv, herase, Nat.div_self hNpos, Nat.totient_one, Nat.cast_one, one_mul,
    sqGaussSum_norm_sum_eq_divisor_sum_of_odd hodd, mul_add, Real.mul_self_sqrt hN0]

/-- **Exact total `L¹` mass at a prime modulus.**  The `N = p` instance of
`sqGaussSum_norm_sum_total_of_odd`: adding the zero-frequency term `p` (`sqGaussSum_zero`) to the
nonzero prime first moment `(p−1)√p` (`sqGaussSum_norm_sum_of_prime`) gives the total mass

    Σ_{r ∈ ZMod p} ‖G(r)‖ = p + (p−1)·√p.  -/
theorem sqGaussSum_norm_sum_total_of_prime {p : ℕ} [NeZero p] (hp : p.Prime) (hN2 : p ≠ 2) :
    (Finset.univ.sum (fun r : ZMod p => ‖sqGaussSum r‖)) = (p : ℝ) + ((p : ℝ) - 1) * Real.sqrt p := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hsplit : (Finset.univ.sum (fun r : ZMod p => ‖sqGaussSum r‖))
      = ‖sqGaussSum (0 : ZMod p)‖
        + (Finset.univ \ {(0 : ZMod p)}).sum (fun r => ‖sqGaussSum r‖) := by
    rw [← Finset.erase_eq]
    exact (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ 0)).symm
  rw [hsplit, sqGaussSum_zero, Complex.norm_natCast, sqGaussSum_norm_sum_of_prime hp hN2]

/-! ### Part L — the total-mass coefficient `C(N) = Σ_{d∣N} φ(N/d)√d` is multiplicative

Part XLIX pins the total `L¹` Gauss-sum mass at an odd modulus as `√N · C(N)` with the
Dirichlet-divisor coefficient

    `C(N) = Σ_{d∣N} φ(N/d)·√d`.

This part identifies `C` as the **Dirichlet convolution** `φ ⋆ √` of two multiplicative
arithmetic functions — Euler's totient `φ` (multiplicative, `Nat.totient_mul`) and the
completely multiplicative square root `√` (`Real.sqrt_mul`, needing no coprimality) — and
transports Mathlib's `ArithmeticFunction.IsMultiplicative.mul` to conclude that `C` itself is
multiplicative:

    `gcd m n = 1  ⟹  C(m·n) = C(m)·C(n)`.

Because `√` is completely multiplicative, `√(mn) = √m · √n`, so the **entire total mass**
`√N · C(N)` inherits the multiplicative law across coprime *odd* moduli:

    `Σ_{r ∈ ZMod (m·n)} ‖G(r)‖  =  (Σ_{r ∈ ZMod m} ‖G(r)‖)·(Σ_{r ∈ ZMod n} ‖G(r)‖)`,

reducing the spectral `L¹` mass at any odd `N` to its prime-power values (e.g. the exact prime
instance `C(p) = (p−1) + √p`, recovering Part XLVIII).  All 0-axiom. -/

/-- The totient as a real-valued arithmetic function `n ↦ φ(n)`. -/
noncomputable def totientRealAF : ArithmeticFunction ℝ :=
  ⟨fun n => (Nat.totient n : ℝ), by simp⟩

/-- The square root as a real-valued arithmetic function `n ↦ √n` (with `√0 = 0`). -/
noncomputable def sqrtAF : ArithmeticFunction ℝ :=
  ⟨fun n => Real.sqrt n, by simp⟩

@[simp] theorem totientRealAF_apply (n : ℕ) : totientRealAF n = (Nat.totient n : ℝ) := rfl

@[simp] theorem sqrtAF_apply (n : ℕ) : sqrtAF n = Real.sqrt n := rfl

/-- Euler's totient is a multiplicative arithmetic function (`φ(1) = 1`, `Nat.totient_mul`). -/
theorem isMultiplicative_totientRealAF : totientRealAF.IsMultiplicative := by
  refine ⟨by simp, fun {m n} h => ?_⟩
  simp only [totientRealAF_apply, Nat.totient_mul h, Nat.cast_mul]

/-- The square root is a (completely) multiplicative arithmetic function: `√(mn) = √m·√n` for
    all naturals, so a fortiori for coprime ones. -/
theorem isMultiplicative_sqrtAF : sqrtAF.IsMultiplicative := by
  refine ⟨by simp, fun {m n} _ => ?_⟩
  simp only [sqrtAF_apply, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)]

/-- **The total-mass coefficient `C(N) = Σ_{d∣N} φ(N/d)·√d`.**  Part XLIX gives the total odd-`N`
    Gauss-sum `L¹` mass as `√N · C(N)`. -/
noncomputable def weylMassCoeff (N : ℕ) : ℝ :=
  (N.divisors).sum (fun d => (Nat.totient (N / d) : ℝ) * Real.sqrt d)

/-- `C(N)` is the Dirichlet convolution `(φ ⋆ √)(N)`: the antidiagonal sum
    `Σ_{a·b = N} φ(a)·√b` reindexes (`Nat.map_div_left_divisors`) to the divisor sum
    `Σ_{d∣N} φ(N/d)·√d`. -/
theorem weylMassCoeff_eq_convolution (N : ℕ) :
    (totientRealAF * sqrtAF) N = weylMassCoeff N := by
  rw [ArithmeticFunction.mul_apply, ← Nat.map_div_left_divisors, Finset.sum_map]
  rfl

/-- **`C` is multiplicative.**  Both factors of the convolution `φ ⋆ √` are multiplicative
    (`isMultiplicative_totientRealAF`, `isMultiplicative_sqrtAF`), so `ArithmeticFunction`'s
    convolution-multiplicativity `IsMultiplicative.mul` gives, for coprime `m, n`,

    `C(m·n) = C(m)·C(n)`. -/
theorem weylMassCoeff_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    weylMassCoeff (m * n) = weylMassCoeff m * weylMassCoeff n := by
  rw [← weylMassCoeff_eq_convolution, ← weylMassCoeff_eq_convolution,
    ← weylMassCoeff_eq_convolution,
    (isMultiplicative_totientRealAF.mul isMultiplicative_sqrtAF).map_mul_of_coprime h]

/-- `C(1) = 1` (the empty-shifted normalisation of the multiplicative `C`). -/
@[simp] theorem weylMassCoeff_one : weylMassCoeff 1 = 1 := by
  simp [weylMassCoeff]

/-- **Prime value `C(p) = (p−1) + √p`.**  The two divisors `1, p` contribute `φ(p)·√1 = p−1`
    and `φ(1)·√p = √p`; this is the coefficient behind the Part XLVIII prime first moment. -/
theorem weylMassCoeff_prime {p : ℕ} (hp : p.Prime) :
    weylMassCoeff p = ((p : ℝ) - 1) + Real.sqrt p := by
  have h1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  rw [weylMassCoeff, hp.divisors, Finset.sum_pair h1p, Nat.div_one, Nat.div_self hp.pos,
    Nat.totient_one, Nat.totient_prime hp, Nat.cast_one, Real.sqrt_one, mul_one, one_mul,
    Nat.cast_sub hp.one_le, Nat.cast_one]

/-- **Total odd-`N` `L¹` mass in coefficient form** (Part XLIX, restated with `C`):

    `Σ_{r ∈ ZMod N} ‖G(r)‖ = √N · C(N)`. -/
theorem sqGaussSum_norm_sum_total_eq_coeff_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    (Finset.univ.sum (fun r : ZMod N => ‖sqGaussSum r‖)) = Real.sqrt N * weylMassCoeff N :=
  sqGaussSum_norm_sum_total_of_odd hodd

/-- **The total `L¹` Gauss-sum mass is multiplicative across coprime odd moduli.**  Writing the
    mass as `√N · C(N)` (Part XLIX) and using the complete multiplicativity of `√`
    (`√(mn) = √m·√n`) together with the multiplicativity of `C`
    (`weylMassCoeff_mul_of_coprime`):

    `Σ_{r ∈ ZMod (m·n)} ‖G(r)‖ = (Σ_{r ∈ ZMod m} ‖G(r)‖) · (Σ_{r ∈ ZMod n} ‖G(r)‖)`

    for coprime odd `m, n`.  This reduces the entire spectral `L¹` mass at an odd modulus to its
    prime-power values. -/
theorem sqGaussSum_norm_sum_total_mul_of_coprime_odd {m n : ℕ} [NeZero m] [NeZero n]
    (hm : Odd m) (hn : Odd n) (h : Nat.Coprime m n) :
    (Finset.univ.sum (fun r : ZMod (m * n) => ‖sqGaussSum r‖))
      = (Finset.univ.sum (fun r : ZMod m => ‖sqGaussSum r‖))
        * (Finset.univ.sum (fun r : ZMod n => ‖sqGaussSum r‖)) := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  have hodd : Odd (m * n) := hm.mul hn
  rw [sqGaussSum_norm_sum_total_eq_coeff_of_odd hodd,
    sqGaussSum_norm_sum_total_eq_coeff_of_odd hm,
    sqGaussSum_norm_sum_total_eq_coeff_of_odd hn, weylMassCoeff_mul_of_coprime h,
    Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)]
  ring

/-! ### Part LI — the prime-power closed form `C(pᵏ) = pᵏ + pᵏ⁻¹√p − √(pᵏ⁻¹)`

Part L reduced the total `L¹` Gauss-sum mass at an odd modulus to the prime-power values of the
multiplicative coefficient `C`.  This part *evaluates* those prime-power values in closed form,
completing the reduction to an explicit product formula.

The engine is a one-step **recursion**.  Peeling the divisor `d = 1` (the `φ(pᵏ⁺¹)·√1` summand)
from `C(pᵏ⁺¹) = Σ_{d∣pᵏ⁺¹} φ(pᵏ⁺¹/d)·√d` and reindexing the remaining divisors `d = pʲ⁺¹` factors
a single `√p` out of every `√(pʲ⁺¹) = √p·√(pʲ)`, leaving exactly `C(pᵏ)`:

    `C(pᵏ⁺¹) = φ(pᵏ⁺¹) + √p · C(pᵏ)`.

Solving this linear recursion (base `C(p) = (p−1)+√p`, Part XLVIII) telescopes to

    `C(pᵏ⁺¹) = pᵏ⁺¹ + pᵏ·√p − √(pᵏ)`

(and, at `k = 0`, recovers `C(p) = p + √p − 1`).  Feeding this through Part XLIX gives the total
`L¹` mass at a prime-power modulus in fully explicit form,

    `Σ_{r ∈ ZMod pᵏ⁺¹} ‖G(r)‖ = √(pᵏ⁺¹)·(pᵏ⁺¹ + pᵏ√p − √(pᵏ))  ~  p^{3(k+1)/2}`,

which is `Θ(N^{3/2}) = o(N²)`.  Note this is a *mass* (`L¹`) statement: as recorded in Part XLVII
it does not by itself furnish the Sárközy density `o(N)`, which needs cross-frequency cancellation
rather than a sharper mass bound.  All 0-axiom. -/

/-- **The prime-power recursion for `C`.**  `C(pᵏ⁺¹) = φ(pᵏ⁺¹) + √p·C(pᵏ)`.

    Proof: `Nat.sum_divisors_prime_pow` turns each divisor sum into a `range` sum over the
    exponents; `Finset.sum_range_succ'` peels the exponent-`0` term (`φ(pᵏ⁺¹)·√1`), and the shift
    `pʲ ↦ pʲ⁺¹` in the tail pulls one `√p` (via `√(pʲ⁺¹) = √(pʲ)·√p`) out of the sum that remains,
    which is exactly `C(pᵏ)`. -/
theorem weylMassCoeff_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    weylMassCoeff (p ^ (k + 1))
      = (Nat.totient (p ^ (k + 1)) : ℝ) + Real.sqrt p * weylMassCoeff (p ^ k) := by
  simp only [weylMassCoeff]
  rw [Nat.sum_divisors_prime_pow hp, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ',
    Finset.mul_sum]
  simp only [pow_zero, Nat.div_one, Nat.cast_one, Real.sqrt_one, mul_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_range] at hx
  have e1 : p ^ (k + 1) / p ^ (x + 1) = p ^ (k - x) := by
    rw [Nat.pow_div (by omega) hp.pos]; congr 1; omega
  have e2 : p ^ k / p ^ x = p ^ (k - x) := Nat.pow_div (by omega) hp.pos
  have e3 : Real.sqrt ((p ^ (x + 1) : ℕ) : ℝ)
      = Real.sqrt ((p ^ x : ℕ) : ℝ) * Real.sqrt p := by
    rw [pow_succ, Nat.cast_mul, Real.sqrt_mul (by positivity)]
  rw [e1, e2, e3]
  ring

/-- **Closed form for `C` at a prime power.**  For every prime `p` and every `k`,

    `C(pᵏ⁺¹) = pᵏ⁺¹ + pᵏ·√p − √(pᵏ)`.

    (At `k = 0` this reads `C(p) = p + √p − 1`, matching `weylMassCoeff_prime`.)  Proved by
    induction on `k` from the recursion `weylMassCoeff_prime_pow_succ`, with the step discharged by
    `linear_combination` using `√p·√p = p` and `√p·√(pᵏ) = √(pᵏ⁺¹)`. -/
theorem weylMassCoeff_prime_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    weylMassCoeff (p ^ (m + 1))
      = (p : ℝ) ^ (m + 1) + (p : ℝ) ^ m * Real.sqrt p - Real.sqrt ((p : ℝ) ^ m) := by
  induction m with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Real.sqrt_one, weylMassCoeff_prime hp]
    ring
  | succ k ih =>
    rw [weylMassCoeff_prime_pow_succ hp, ih, Nat.totient_prime_pow_succ hp (k + 1)]
    push_cast [Nat.cast_sub hp.one_le]
    have hSS : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hST : Real.sqrt (p : ℝ) * Real.sqrt ((p : ℝ) ^ k)
        = Real.sqrt ((p : ℝ) ^ (k + 1)) := by
      rw [pow_succ', Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (p : ℝ))]
    linear_combination (p : ℝ) ^ k * hSS - hST

/-- **Total `L¹` Gauss-sum mass at a prime-power modulus, in closed form.**  For an odd prime `p`,

    `Σ_{r ∈ ZMod pᵏ⁺¹} ‖G(r)‖ = √(pᵏ⁺¹)·(pᵏ⁺¹ + pᵏ·√p − √(pᵏ))`.

    Combines the Part XLIX coefficient form `√N·C(N)` with the closed form
    `weylMassCoeff_prime_pow`.  The right side is `Θ(p^{3(k+1)/2}) = Θ(N^{3/2}) = o(N²)`. -/
theorem sqGaussSum_norm_sum_total_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ)
    [NeZero (p ^ (m + 1))] :
    (Finset.univ.sum (fun r : ZMod (p ^ (m + 1)) => ‖sqGaussSum r‖))
      = Real.sqrt ((p : ℝ) ^ (m + 1))
        * ((p : ℝ) ^ (m + 1) + (p : ℝ) ^ m * Real.sqrt p - Real.sqrt ((p : ℝ) ^ m)) := by
  have hodd : Odd (p ^ (m + 1)) := (hp.odd_of_ne_two hp2).pow
  rw [sqGaussSum_norm_sum_total_eq_coeff_of_odd hodd, weylMassCoeff_prime_pow hp, Nat.cast_pow]

/-! ### Part LII — the fully explicit product formula: `C(N) = ∏_{pᵏ‖N} C(pᵏ)` for every `N`

Part L proved that the total-mass coefficient `C` is multiplicative and Part LI evaluated its
prime-power values in closed form.  This part assembles the two into the **explicit product
formula over the entire prime factorization**, completing the reduction promised in Part LI: for
every `N ≠ 0`,

    C(N) = ∏_{p ∈ primeFactors N} C(p^{vₚ(N)})
         = ∏_{p ∈ primeFactors N} (p^{vₚ} + p^{vₚ−1}·√p − √(p^{vₚ−1}))   (vₚ := N.factorization p ≥ 1).

The engine is `ArithmeticFunction.IsMultiplicative.multiplicative_factorization` applied to the
convolution `φ ⋆ √` (whose value is `C` by `weylMassCoeff_eq_convolution`), followed by the
per-prime substitution of the Part LI closed form.  Feeding this through Part XLIX gives the total
odd-`N` `L¹` Gauss-sum mass in fully closed form, over *all* odd `N` (not just prime powers).

As always (Part XLVII), this is an `L¹` *mass* statement: it does not by itself furnish the
Sárközy `o(N)` density, which needs cross-frequency cancellation rather than a sharper mass value.
All 0-axiom. -/

/-- **`C` as a product over its prime factorization.**  For every `N ≠ 0`,

    `C(N) = ∏_{pᵏ‖N} C(pᵏ)`,

directly from the multiplicativity of the convolution `φ ⋆ √`
(`multiplicative_factorization`), rewriting each factor `(φ ⋆ √)(pᵏ)` back to `C(pᵏ)` via
`weylMassCoeff_eq_convolution`. -/
theorem weylMassCoeff_eq_prod_factorization {N : ℕ} (hN : N ≠ 0) :
    weylMassCoeff N = N.factorization.prod (fun p k => weylMassCoeff (p ^ k)) := by
  rw [← weylMassCoeff_eq_convolution,
    (isMultiplicative_totientRealAF.mul isMultiplicative_sqrtAF).multiplicative_factorization _ hN]
  exact Finsupp.prod_congr (fun p _ => weylMassCoeff_eq_convolution _)

/-- **Fully explicit product formula for `C` (all `N`).**  Substituting the Part LI prime-power
closed form `C(pᵏ) = pᵏ + pᵏ⁻¹·√p − √(pᵏ⁻¹)` (valid for every exponent `k ≥ 1`, i.e. on the
support of the factorization) into `weylMassCoeff_eq_prod_factorization`: for `N ≠ 0`,

    `C(N) = ∏_{p ∈ primeFactors N} (p^{vₚ} + p^{vₚ−1}·√p − √(p^{vₚ−1}))`,

with `vₚ := N.factorization p ≥ 1`. -/
theorem weylMassCoeff_eq_prod_prime_pow_closed {N : ℕ} (hN : N ≠ 0) :
    weylMassCoeff N
      = N.factorization.prod (fun p k =>
          (p : ℝ) ^ k + (p : ℝ) ^ (k - 1) * Real.sqrt p - Real.sqrt ((p : ℝ) ^ (k - 1))) := by
  rw [weylMassCoeff_eq_prod_factorization hN]
  apply Finsupp.prod_congr
  intro p hp
  have hp' : p ∈ N.primeFactors := by rwa [Nat.support_factorization] at hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp'
  have hk0 : N.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  obtain ⟨m, hm⟩ : ∃ m, N.factorization p = m + 1 := ⟨N.factorization p - 1, by omega⟩
  rw [hm, weylMassCoeff_prime_pow hpp m, Nat.add_sub_cancel]

/-- **Total odd-`N` `L¹` Gauss-sum mass in fully explicit product form (all odd `N`).**  Combining
the Part XLIX coefficient form `√N·C(N)` with the explicit factorization product for `C`:

    `Σ_{r ∈ ZMod N} ‖G(r)‖ = √N · ∏_{p ∈ primeFactors N} (p^{vₚ} + p^{vₚ−1}·√p − √(p^{vₚ−1}))`.

The complete closed form of the first spectral moment at *every* odd modulus, reducing it to the
prime factorisation.  It is `Θ(N^{3/2}) = o(N²)`; per Part XLVII it does not discharge the Sárközy
density `o(N)`. -/
theorem sqGaussSum_norm_sum_total_eq_prod_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    (Finset.univ.sum (fun r : ZMod N => ‖sqGaussSum r‖))
      = Real.sqrt N * N.factorization.prod (fun p k =>
          (p : ℝ) ^ k + (p : ℝ) ^ (k - 1) * Real.sqrt p - Real.sqrt ((p : ℝ) ^ (k - 1))) := by
  rw [sqGaussSum_norm_sum_total_eq_coeff_of_odd hodd,
    weylMassCoeff_eq_prod_prime_pow_closed (NeZero.ne N)]


/-! ### Part LIII — The unit/non-unit frequency split: the good part is Sárközy-harmless

Every prior single-scale route (Parts XV–XXII, XLVII) bounds the circle-method error
`N⁻¹·Σ_{r≠0} ‖Â(r)‖²·‖G(r)‖` by pulling a *uniform* magnitude `M = max_r ‖G(r)‖` out of the sum
(`sqDiff_error_le`).  For composite `N` that maximum is `Θ(N)` — attained at the *non-unit*
frequencies, where `‖G(r)‖ = √(N·gcd(r,N))` — so the reduction caps the density at `1/√minFac`,
never `o(N)`.

The decisive structural observation, made precise here: the nonzero frequencies split into
**units** and **non-units**, and on the unit block *every* coefficient has the identical exact
magnitude `‖G(r)‖ = √N` (`sqGaussSum_norm_eq_sqrt_of_odd`).  So on that block one may pull out the
constant `√N` and apply **Parseval** — not the lossy `max·L¹` pairing that loses a factor `√N`
(Part XLVII) — giving

    N⁻¹ · Σ_{r unit} ‖Â(r)‖²·‖G(r)‖ = N⁻¹·√N·Σ_{r unit}‖Â(r)‖² ≤ √N·|A|,

a term that forces `|A| ≲ √N` on its own.  Consequently the *entire* obstruction to the Sárközy
`o(N)` density is the **non-unit Fourier mass**

    badFreqMass(A) := Σ_{r≠0, ¬IsUnit r} ‖Â(r)‖²·‖G(r)‖,

and the density inequality sharpens (for square-difference-free `A`) to

    |A|² ≤ |A|·#{n : n² = 0} + √N·|A| + N⁻¹·badFreqMass(A),

i.e. at a squarefree modulus `|A|² ≤ |A| + √N·|A| + N⁻¹·badFreqMass(A)`.

This is the exact formal entry point to the multi-scale density increment: a non-unit frequency
`r` with `gcd(r.val, N) = d > 1` factors through the proper sub-modulus `ℤ/(N/d)`, so
`badFreqMass` is a genuinely *lower-scale* quantity.  The one remaining gap — provably out of
single-scale reach (Part XLVII) — is precisely: **`badFreqMass(A) = o(N²)` uniformly over
square-difference-free `A`**, which combined with the display above yields `|A| = o(N)`.
Everything below is 0-axiom; nothing here claims to close that gap — it isolates it. -/

/-- **The non-unit (bad) Fourier mass.**  The portion of the circle-method error sum
`Σ_{r≠0} ‖Â(r)‖²·‖G(r)‖` supported on the *non-unit* frequencies.  The unit frequencies carry the
Sárközy-harmless `√N`-magnitude block (`sqGaussSum_norm_eq_sqrt_of_odd`); this quantity is the
entire residual obstruction to the `o(N)` density (see `sqDiffFree_badFreqMass_bound`). -/
noncomputable def badFreqMass {N : ℕ} [NeZero N] (A : Finset (ZMod N)) : ℝ :=
  ((Finset.univ \ {(0 : ZMod N)}).filter (fun r => ¬ IsUnit r)).sum
    (fun r => ‖fourierCoeff A r‖ ^ 2 * ‖sqGaussSum r‖)

/-- `badFreqMass` is nonnegative (a sum of nonnegative terms). -/
theorem badFreqMass_nonneg {N : ℕ} [NeZero N] (A : Finset (ZMod N)) : 0 ≤ badFreqMass A := by
  rw [badFreqMass]; exact Finset.sum_nonneg (fun i _ => by positivity)

/-- **Unit/non-unit split of the circle-method error (odd modulus).**  On the unit block every
Gauss magnitude equals `√N` exactly, so Parseval bounds that block by `√N·(|A|·N − |A|²)`; the
remainder is exactly `badFreqMass A`.  Hence

    ‖SD(A) − |A|²‖ ≤ N⁻¹ · (√N·(|A|·N − |A|²) + badFreqMass(A)).

Unlike the uniform `sqDiff_error_le` (which pulls a single `M = Θ(N)` out of *all* nonzero
frequencies), this keeps the exact `√N` on the units and confines every `Θ(N)`-magnitude term to
`badFreqMass`. -/
theorem sqDiff_error_le_unit_split {N : ℕ} [NeZero N] (hodd : Odd N) (A : Finset (ZMod N)) :
    ‖(sqDiffCount A : ℂ) - (↑A.card) ^ 2‖
      ≤ (↑N)⁻¹ * (Real.sqrt N * (↑A.card * ↑N - (↑A.card) ^ 2) + badFreqMass A) := by
  have hsub : (sqDiffCount A : ℂ) - (↑A.card) ^ 2
      = (↑N)⁻¹ * (Finset.univ \ {(0 : ZMod N)}).sum
          (fun r => (↑(‖fourierCoeff A r‖ ^ 2) : ℂ) * sqGaussSum r) := by
    rw [sqDiffCount_fourier_main A]; ring
  rw [hsub, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- Reduce the complex norm to the real `‖Â‖²·‖G‖` sum.
  have hnorm : ‖(Finset.univ \ {(0 : ZMod N)}).sum
        (fun r => (↑(‖fourierCoeff A r‖ ^ 2) : ℂ) * sqGaussSum r)‖
      ≤ (Finset.univ \ {(0 : ZMod N)}).sum
          (fun r => ‖fourierCoeff A r‖ ^ 2 * ‖sqGaussSum r‖) := by
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  -- Split the nonzero frequencies into units and non-units.
  have hsplit : (Finset.univ \ {(0 : ZMod N)}).sum
        (fun r => ‖fourierCoeff A r‖ ^ 2 * ‖sqGaussSum r‖)
      = ((Finset.univ \ {(0 : ZMod N)}).filter (fun r => IsUnit r)).sum
          (fun r => ‖fourierCoeff A r‖ ^ 2 * ‖sqGaussSum r‖)
        + badFreqMass A := by
    rw [badFreqMass]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.univ \ {(0 : ZMod N)})
      (fun r => IsUnit r)
      (fun r => ‖fourierCoeff A r‖ ^ 2 * ‖sqGaussSum r‖)).symm
  -- Bound the unit block via the exact magnitude `√N` and Parseval.
  have hgood : ((Finset.univ \ {(0 : ZMod N)}).filter (fun r => IsUnit r)).sum
        (fun r => ‖fourierCoeff A r‖ ^ 2 * ‖sqGaussSum r‖)
      ≤ Real.sqrt N * (↑A.card * ↑N - (↑A.card) ^ 2) := by
    have hval : ((Finset.univ \ {(0 : ZMod N)}).filter (fun r => IsUnit r)).sum
          (fun r => ‖fourierCoeff A r‖ ^ 2 * ‖sqGaussSum r‖)
        = ((Finset.univ \ {(0 : ZMod N)}).filter (fun r => IsUnit r)).sum
            (fun r => ‖fourierCoeff A r‖ ^ 2) * Real.sqrt N := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      rw [Finset.mem_filter] at hr
      rw [sqGaussSum_norm_eq_sqrt_of_odd hodd hr.2]
    have hp : ((Finset.univ \ {(0 : ZMod N)}).filter (fun r => IsUnit r)).sum
          (fun r => ‖fourierCoeff A r‖ ^ 2)
        ≤ ↑A.card * ↑N - (↑A.card) ^ 2 := by
      calc ((Finset.univ \ {(0 : ZMod N)}).filter (fun r => IsUnit r)).sum
              (fun r => ‖fourierCoeff A r‖ ^ 2)
          ≤ (Finset.univ \ {(0 : ZMod N)}).sum (fun r => ‖fourierCoeff A r‖ ^ 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun i _ _ => by positivity)
        _ = ↑A.card * ↑N - (↑A.card) ^ 2 := parseval_nonzero A
    rw [hval, mul_comm]
    exact mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)
  refine le_trans hnorm ?_
  rw [hsplit]
  gcongr

/-- **Sárközy density inequality with the good block collapsed (odd modulus).**  For any
square-difference-free `A ⊆ ℤ/Nℤ` with `N` odd, the unit-frequency block contributes at most
`√N·|A|` and the entire remaining obstruction is `badFreqMass(A)`:

    |A|² ≤ |A|·#{n : n² = 0} + √N·|A| + N⁻¹·badFreqMass(A).

The `√N·|A|` term is Sárközy-harmless (it alone forces `|A| ≲ √N`); the theorem localises every
`Θ(N)`-scale contribution into the single quantity `N⁻¹·badFreqMass(A)`, whose uniform smallness
`badFreqMass = o(N²)` is exactly what remains for the `o(N)` density (Part XLVII / multi-scale). -/
theorem sqDiffFree_badFreqMass_bound {N : ℕ} [NeZero N] (hodd : Odd N) (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) ^ 2
      ≤ (A.card : ℝ) * (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card
        + Real.sqrt N * A.card + (↑N)⁻¹ * badFreqMass A := by
  have herr := sqDiff_error_le_unit_split hodd A
  -- Circle-method lower bound on the count.
  have hlow : (A.card : ℝ) ^ 2
      - (↑N)⁻¹ * (Real.sqrt N * (↑A.card * ↑N - (↑A.card) ^ 2) + badFreqMass A)
      ≤ (sqDiffCount A : ℝ) := by
    have key : |(sqDiffCount A : ℝ) - (A.card : ℝ) ^ 2|
        ≤ (↑N)⁻¹ * (Real.sqrt N * (↑A.card * ↑N - (↑A.card) ^ 2) + badFreqMass A) := by
      have e : ‖(sqDiffCount A : ℂ) - (↑A.card) ^ 2‖
          = |(sqDiffCount A : ℝ) - (A.card : ℝ) ^ 2| := by
        rw [show (sqDiffCount A : ℂ) - (↑A.card) ^ 2
              = (((sqDiffCount A : ℝ) - (A.card : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
      rwa [e] at herr
    linarith [(abs_le.mp key).1]
  have hupp : (sqDiffCount A : ℝ)
      ≤ (A.card : ℝ) * (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card := by
    exact_mod_cast sqDiffCount_le_of_free A hfree
  -- The good block `N⁻¹·√N·(|A|·N − |A|²) ≤ √N·|A|`.
  have hgoodsimp : (↑N)⁻¹ * (Real.sqrt N * (↑A.card * ↑N - (↑A.card) ^ 2))
      ≤ Real.sqrt N * (A.card : ℝ) := by
    have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    have hfrac : (↑N)⁻¹ * ((A.card : ℝ) * ↑N - (A.card : ℝ) ^ 2) ≤ (A.card : ℝ) := by
      have hrw : (↑N)⁻¹ * ((A.card : ℝ) * ↑N - (A.card : ℝ) ^ 2)
          = (A.card : ℝ) - (↑N)⁻¹ * (A.card : ℝ) ^ 2 := by
        field_simp
      rw [hrw]
      linarith [mul_nonneg (inv_nonneg.mpr hN.le) (sq_nonneg (A.card : ℝ))]
    calc (↑N)⁻¹ * (Real.sqrt N * (↑A.card * ↑N - (↑A.card) ^ 2))
        = Real.sqrt N * ((↑N)⁻¹ * ((A.card : ℝ) * ↑N - (A.card : ℝ) ^ 2)) := by ring
      _ ≤ Real.sqrt N * (A.card : ℝ) := mul_le_mul_of_nonneg_left hfrac (Real.sqrt_nonneg _)
  have hexpand : (↑N)⁻¹ * (Real.sqrt N * (↑A.card * ↑N - (↑A.card) ^ 2) + badFreqMass A)
      = (↑N)⁻¹ * (Real.sqrt N * (↑A.card * ↑N - (↑A.card) ^ 2)) + (↑N)⁻¹ * badFreqMass A := by
    ring
  linarith [hlow, hupp, hgoodsimp, hexpand]

/-- **Squarefree specialisation.**  At an odd *squarefree* modulus `#{n : n² = 0} = 1`
(`sq_eq_zero_filter_card_eq_one_of_squarefree`), so the density inequality reads

    |A|² ≤ |A| + √N·|A| + N⁻¹·badFreqMass(A).

The first two terms are `O(√N·|A|)`; the whole Sárközy question at squarefree moduli is the
uniform bound `badFreqMass(A) = o(N²)`. -/
theorem sqDiffFree_badFreqMass_bound_squarefree {N : ℕ} [NeZero N] (hodd : Odd N)
    (hsf : Squarefree N) (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) ^ 2 ≤ (A.card : ℝ) + Real.sqrt N * A.card + (↑N)⁻¹ * badFreqMass A := by
  have h := sqDiffFree_badFreqMass_bound hodd A hfree
  rw [sq_eq_zero_filter_card_eq_one_of_squarefree hsf] at h
  simpa using h

/-! ### Part LIV — Subgroup Parseval: the frequency-subgroup Fourier energy is a coset energy

Part LIII isolated the entire `o(N)` obstruction into `badFreqMass`, whose non-unit frequencies
`r` (with `gcd(r.val, N) = d > 1`) live in proper *subgroups* of the frequency group.  The
multi-scale density increment needs to read the Fourier mass carried by such a subgroup as
structural information about `A` on the *dual* cosets.  This part supplies exactly that dictionary.

For `g ∣ N`, write `M = N / g`.  The frequencies `{r : M ∣ r.val}` form the order-`g` subgroup of
`ZMod N` (the annihilator of the index-`g` subgroup `g·ZMod N`).  The **subgroup character
orthogonality**

    Σ_{r : M ∣ r.val} ψ(r·c) = g·[g ∣ c.val]

(the geometric-series collapse of a character summed over a subgroup) upgrades, via the
`Â(r)·conj Â(r)` expansion, to the **subgroup Parseval / coset-energy identity**

    Σ_{r : M ∣ r.val} ‖Â(r)‖² = g · Σ_{j < g} (#{x ∈ A : x.val ≡ j mod g})²,

i.e. the Fourier energy on the frequency subgroup equals `g` times the `ℓ²` energy of the coset
occupation counts of `A` modulo `g`.  At `g = N` (`M = 1`) this is the full Parseval identity
`Σ_r ‖Â(r)‖² = N·|A|`; at `g = 1` (`M = N`) it is the `r = 0` term `‖Â(0)‖² = |A|²`.  This is the
exact density-increment input: a large subgroup Fourier energy is equivalent to `A` concentrating
on a coset of `g·ZMod N`, the entry point for descending the Sárközy problem to the modulus `g`.
Everything here is 0-axiom. -/

/-- **Subgroup character orthogonality.**  For `g ∣ N` and `M = N/g`, summing the additive
character `ψ(·c)` over the order-`g` frequency subgroup `{r : M ∣ r.val}` gives `g` when `g ∣ c.val`
and `0` otherwise — the geometric-series collapse `Σ_{k<g} ω^k` with `ω = ψ(M·c)` a `g`-th root of
unity (`ω^g = ψ(N·c) = 1`), which is `1` exactly when `g ∣ c.val`. -/
private lemma subgroup_char_orthogonality {N : ℕ} [NeZero N] {g : ℕ} (hg : 0 < g)
    (hgN : g ∣ N) (c : ZMod N) :
    (Finset.univ.filter (fun r : ZMod N => (N / g) ∣ ZMod.val r)).sum (fun r => ψ (r * c))
      = if g ∣ ZMod.val c then (g : ℂ) else 0 := by
  set M := N / g with hM_def
  have hMg : M * g = N := Nat.div_mul_cancel hgN
  have hM_pos : 0 < M := Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hgN) hg
  -- The frequency subgroup is the injective image of `k ↦ (k·M : ZMod N)`, `k < g`.
  have himg : (Finset.univ.filter (fun r : ZMod N => M ∣ ZMod.val r))
      = (Finset.range g).image (fun k => ((k * M : ℕ) : ZMod N)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨t, ht⟩
      have htlt : t < g := by
        have hrN : ZMod.val r < N := ZMod.val_lt r
        rw [ht, ← hMg] at hrN
        exact lt_of_mul_lt_mul_left hrN (Nat.zero_le M)
      exact ⟨t, htlt, by rw [mul_comm t M, ← ht, ZMod.natCast_val, ZMod.cast_id]⟩
    · rintro ⟨k, hk, rfl⟩
      have hlt : k * M < N := by
        rw [← hMg, mul_comm M g]; exact (Nat.mul_lt_mul_right hM_pos).mpr hk
      rw [ZMod.val_natCast_of_lt hlt]
      exact dvd_mul_left M k
  rw [himg, Finset.sum_image]
  · -- Reindex the subgroup sum to a geometric series in `ω = ψ(M·c)`.
    set ω := ψ (((M : ℕ) : ZMod N) * c) with hω_def
    have hterm : ∀ k : ℕ, ψ (((k * M : ℕ) : ZMod N) * c) = ω ^ k := by
      intro k
      induction k with
      | zero => simp [psi_zero]
      | succ n ih =>
        have hsplit : (((n + 1) * M : ℕ) : ZMod N) * c
            = ((n * M : ℕ) : ZMod N) * c + ((M : ℕ) : ZMod N) * c := by push_cast; ring
        rw [hsplit, psi_add, ih, ← hω_def, pow_succ]
    simp_rw [hterm]
    -- `ω^g = 1` since `(g·M : ZMod N) = (N : ZMod N) = 0`.
    have hωg : ω ^ g = 1 := by
      rw [← hterm g,
        show ((g * M : ℕ) : ZMod N) = 0 by
          rw [mul_comm, hMg, ZMod.natCast_self], zero_mul, psi_zero]
    -- `M·c = (M·c.val : ZMod N)`, so `ω = 1 ↔ N ∣ M·c.val ↔ g ∣ c.val`.
    have hpsi_iff : ∀ x : ZMod N, ψ x = 1 ↔ x = 0 := by
      intro x
      constructor
      · intro h; by_contra hx; exact psi_ne_one x hx h
      · intro h; rw [h, psi_zero]
    have hMc : ((M : ℕ) : ZMod N) * c = ((M * ZMod.val c : ℕ) : ZMod N) := by
      conv_lhs => rw [show c = ((ZMod.val c : ℕ) : ZMod N) from by
        rw [ZMod.natCast_val, ZMod.cast_id]]
      push_cast; ring
    have hMc_zero : ((M : ℕ) : ZMod N) * c = 0 ↔ g ∣ ZMod.val c := by
      rw [hMc, ZMod.natCast_eq_zero_iff]
      set v := ZMod.val c with hv
      rw [← hMg, Nat.mul_dvd_mul_iff_left hM_pos]
    have hω1_iff : ω = 1 ↔ g ∣ ZMod.val c := by
      rw [hω_def, hpsi_iff, hMc_zero]
    by_cases hdvd : g ∣ ZMod.val c
    · rw [if_pos hdvd, hω1_iff.mpr hdvd]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    · rw [if_neg hdvd]
      exact root_unity_sum_zero ω g hωg (fun h => hdvd (hω1_iff.mp h))
  · -- Injectivity of `k ↦ (k·M : ZMod N)` on `range g`.
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    have haN : a * M < N := by
      rw [← hMg, mul_comm M g]; exact (Nat.mul_lt_mul_right hM_pos).mpr ha
    have hbN : b * M < N := by
      rw [← hMg, mul_comm M g]; exact (Nat.mul_lt_mul_right hM_pos).mpr hb
    have : a * M = b * M := by
      have := congrArg ZMod.val hab
      rwa [ZMod.val_natCast_of_lt haN, ZMod.val_natCast_of_lt hbN] at this
    exact Nat.eq_of_mul_eq_mul_right hM_pos this

/-- **Subgroup Parseval / coset additive-energy identity.**  The Fourier energy carried by the
order-`g` frequency subgroup `{r : (N/g) ∣ r.val}` equals `g` times the *subgroup additive energy*
of `A` — the number of pairs `(x, x') ∈ A × A` congruent modulo `g` (i.e. `g ∣ (x − x').val`):

    Σ_{r : (N/g) ∣ r.val} ‖Â(r)‖² = g · #{(x, x') ∈ A × A : g ∣ (x − x').val}.

Proof: expand `‖Â(r)‖² = Σ_{x,x'} ψ(r·(x−x'))`, swap the order of summation, and apply the
subgroup character orthogonality `subgroup_char_orthogonality` to the inner `r`-sum, collapsing it to
`g` on the congruent pairs and `0` otherwise.  This is the exact density-increment dictionary:
a large left-hand side forces the right-hand side (many congruent pairs), i.e. `A` concentrating on
cosets of `g·ZMod N` — the structural input that lets the Sárközy problem descend to modulus `g`.

Sanity checks: at `g = N` (whole group) it is the Parseval identity `Σ_r ‖Â(r)‖² = N·|A|` (every
pair is congruent mod `N`, giving `N·|A×A ∩ diagonal| = N·|A|`); at `g = 1` it is the zero-frequency
term `‖Â(0)‖² = |A|²` (all pairs congruent mod `1`). -/
theorem subgroup_parseval_energy {N : ℕ} [NeZero N] {g : ℕ} (hg : 0 < g) (hgN : g ∣ N)
    (A : Finset (ZMod N)) :
    (Finset.univ.filter (fun r : ZMod N => (N / g) ∣ ZMod.val r)).sum
        (fun r => ‖fourierCoeff A r‖ ^ 2)
      = (g : ℝ) * (((A ×ˢ A).filter
          (fun p : ZMod N × ZMod N => g ∣ ZMod.val (p.1 - p.2))).card) := by
  -- Per-frequency expansion `‖Â(r)‖² = Σ_{(x,x')} ψ(r·(x−x'))` (in ℂ).
  have key : ∀ r : ZMod N, (↑(‖fourierCoeff A r‖ ^ 2) : ℂ)
      = (A ×ˢ A).sum (fun p => ψ (r * (p.1 - p.2))) := by
    intro r
    rw [show (↑(‖fourierCoeff A r‖ ^ 2) : ℂ)
        = fourierCoeff A r * starRingEnd ℂ (fourierCoeff A r) from by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]]
    rw [fourierCoeff_eq_sum_psi, map_sum (starRingEnd ℂ)]
    simp_rw [conj_psi]
    rw [Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => ?_))
    rw [← psi_add, show r * x + -(r * x') = r * (x - x') from by ring]
  -- Descend from ℂ: build the complex identity, then cast back.
  have hcomplex : (↑((Finset.univ.filter (fun r : ZMod N => (N / g) ∣ ZMod.val r)).sum
        (fun r => ‖fourierCoeff A r‖ ^ 2)) : ℂ)
      = (g : ℂ) * (((A ×ˢ A).filter
          (fun p : ZMod N × ZMod N => g ∣ ZMod.val (p.1 - p.2))).card) := by
    rw [Complex.ofReal_sum]
    simp_rw [key]
    rw [Finset.sum_comm]
    simp_rw [subgroup_char_orthogonality hg hgN]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact_mod_cast hcomplex

/-! ### Part LV — the equidistribution floor: excess subgroup energy = deviation from balance

Part LIV proved the exact identity `Σ_{r : (N/g) ∣ r.val} ‖Â(r)‖² = g · #{congruent pairs mod g}`.
The zero frequency `r = 0` always lies in the subgroup (`(N/g) ∣ 0`) and contributes exactly
`‖Â(0)‖² = |A|²`.  Peeling it off turns the subgroup-Parseval identity into a **variance /
excess decomposition**

    g · #{congruent pairs mod g} = |A|² + Σ_{r : (N/g)∣r.val, r≠0} ‖Â(r)‖²,

whose right-hand tail is a sum of nonnegative Fourier masses.  Reading the two sides:

* **Floor (Cauchy–Schwarz for free).**  Dropping the nonnegative tail gives the equidistribution
  floor `|A|² ≤ g · #{congruent pairs}` — the additive-energy lower bound that a separate
  Cauchy–Schwarz would produce, here obtained purely from Fourier positivity.  Equality holds iff
  every nonzero subgroup frequency vanishes, i.e. iff `A` is perfectly equidistributed across the
  `g` cosets modulo `g`.

* **Strict increment.**  Conversely, a *single* nonzero subgroup frequency with `Â(r) ≠ 0` forces
  `|A|² < g · #{congruent pairs}`: `A` carries strictly more congruent pairs than an equidistributed
  set, i.e. it concentrates on some coset of `g·ZMod N`.  This is the exact density-increment
  trigger — a large `badFreqMass` (Part LIII) lives on such nonzero subgroup frequencies, so it
  forces coset concentration and lets the Sárközy problem descend to modulus `g`.

Everything here is 0-axiom, built directly on `subgroup_parseval_energy`. -/

/-- **Subgroup-Parseval excess decomposition.**  Splitting off the zero frequency (which always lies
in the order-`g` subgroup and contributes `‖Â(0)‖² = |A|²`) rewrites the coset additive energy as its
equidistributed value `|A|²/g` plus the nonzero subgroup Fourier mass:

    g · #{(x,x') ∈ A×A : g ∣ (x−x').val} = |A|² + Σ_{r : (N/g)∣r.val, r≠0} ‖Â(r)‖². -/
theorem subgroup_parseval_energy_split {N : ℕ} [NeZero N] {g : ℕ} (hg : 0 < g) (hgN : g ∣ N)
    (A : Finset (ZMod N)) :
    (g : ℝ) * (((A ×ˢ A).filter
        (fun p : ZMod N × ZMod N => g ∣ ZMod.val (p.1 - p.2))).card)
      = (A.card : ℝ) ^ 2 +
        ((Finset.univ.filter (fun r : ZMod N => (N / g) ∣ ZMod.val r)).erase 0).sum
          (fun r => ‖fourierCoeff A r‖ ^ 2) := by
  rw [← subgroup_parseval_energy hg hgN A]
  set S := Finset.univ.filter (fun r : ZMod N => (N / g) ∣ ZMod.val r) with hS
  have h0mem : (0 : ZMod N) ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, ZMod.val_zero, Nat.dvd_zero]
  rw [← Finset.add_sum_erase S _ h0mem]
  congr 1
  rw [fourierCoeff_zero']
  simp

/-- **Equidistribution floor (additive-energy Cauchy–Schwarz from Fourier positivity).**  The coset
additive energy of `A` modulo `g` is at least its equidistributed value:

    |A|² ≤ g · #{(x,x') ∈ A×A : g ∣ (x−x').val},

equivalently `#{congruent pairs} ≥ |A|²/g`.  Obtained by dropping the nonnegative nonzero-frequency
tail of the excess decomposition; equality holds iff every nonzero subgroup frequency vanishes. -/
theorem subgroup_additive_energy_floor {N : ℕ} [NeZero N] {g : ℕ} (hg : 0 < g) (hgN : g ∣ N)
    (A : Finset (ZMod N)) :
    (A.card : ℝ) ^ 2 ≤ (g : ℝ) * (((A ×ˢ A).filter
        (fun p : ZMod N × ZMod N => g ∣ ZMod.val (p.1 - p.2))).card) := by
  rw [subgroup_parseval_energy_split hg hgN A]
  have htail : (0 : ℝ) ≤
      ((Finset.univ.filter (fun r : ZMod N => (N / g) ∣ ZMod.val r)).erase 0).sum
        (fun r => ‖fourierCoeff A r‖ ^ 2) :=
    Finset.sum_nonneg (fun r _ => by positivity)
  linarith

/-- **Strict density increment.**  A single nonzero frequency `r` in the order-`g` subgroup with
`Â(r) ≠ 0` forces strictly more congruent pairs than an equidistributed set:

    |A|² < g · #{(x,x') ∈ A×A : g ∣ (x−x').val}.

Hence `A` concentrates on a coset of `g·ZMod N` — the exact trigger that turns a nonzero non-unit
Fourier mass (`badFreqMass`, Part LIII) into a coset density increment for Sárközy descent. -/
theorem subgroup_additive_energy_strict {N : ℕ} [NeZero N] {g : ℕ} (hg : 0 < g) (hgN : g ∣ N)
    (A : Finset (ZMod N)) {r : ZMod N} (hr : (N / g) ∣ ZMod.val r) (hr0 : r ≠ 0)
    (hrne : fourierCoeff A r ≠ 0) :
    (A.card : ℝ) ^ 2 < (g : ℝ) * (((A ×ˢ A).filter
        (fun p : ZMod N × ZMod N => g ∣ ZMod.val (p.1 - p.2))).card) := by
  rw [subgroup_parseval_energy_split hg hgN A]
  have hrmem : r ∈ (Finset.univ.filter (fun r : ZMod N => (N / g) ∣ ZMod.val r)).erase 0 := by
    rw [Finset.mem_erase]
    exact ⟨hr0, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩⟩
  have htail : (0 : ℝ) <
      ((Finset.univ.filter (fun r : ZMod N => (N / g) ∣ ZMod.val r)).erase 0).sum
        (fun r => ‖fourierCoeff A r‖ ^ 2) :=
    Finset.sum_pos' (fun s _ => by positivity)
      ⟨r, hrmem, pow_pos (norm_pos_iff.mpr hrne) 2⟩
  linarith

/-! ### Part LVI — the coset-partition identity: additive energy = Σ (coset counts)²

Parts LIV/LV expressed everything through the abstract count `#{(x,x') ∈ A×A : g ∣ (x−x').val}`
of pairs congruent modulo `g`.  This part makes that count *concrete* as a sum of squares of
**coset occupation numbers**.

Reduction modulo `g` is the ring hom `φ = ZMod.castHom (g ∣ N) : ZMod N →+* ZMod g`, whose fibers
are exactly the cosets of `g·ZMod N`.  Writing `n_j = #{x ∈ A : φ x = j}` for the number of
elements of `A` in coset `j`, two elements are congruent mod `g` iff they share a coset, so

    #{(x,x') ∈ A×A : g ∣ (x−x').val} = Σ_{j : ZMod g} n_j².

This is the standard "sum over fibers of card²" and identifies the coset additive energy of Part LIV
with `Σ n_j²`.  Combined with the equidistribution results of Part LV it yields:

* **Cauchy–Schwarz on cosets** `|A|² ≤ g · Σ_j n_j²` (the floor, now fully explicit) — the classical
  `(Σ n_j)² ≤ g · Σ n_j²` obtained here from Fourier positivity.

* **Dense coset extraction** — a single nonzero subgroup frequency `Â(r) ≠ 0` forces some coset
  strictly above the average occupation `|A|/g`:  `∃ j, |A|/g < n_j`.  Since coset `j` has exactly
  `N/g` elements, its relative density `n_j/(N/g)` then strictly exceeds the ambient density
  `|A|/N` — the concrete coset density increment that the nonzero non-unit Fourier mass
  (`badFreqMass`, Part LIII) delivers, letting the Sárközy problem descend to modulus `g`.

Everything here is 0-axiom, built on `subgroup_additive_energy_floor/strict` (Part LV). -/

/-- **Coset-partition identity.**  The number of pairs of `A` congruent modulo `g` equals the sum of
squares of the coset occupation numbers `n_j = #{x ∈ A : φ x = j}`, where `φ = castHom (g ∣ N)` is
reduction `ZMod N → ZMod g`:

    #{(x,x') ∈ A×A : g ∣ (x−x').val} = Σ_{j : ZMod g} n_j².

Proof: `g ∣ (x−x').val ↔ φ x = φ x'` (kernel of `φ`), so the congruent-pair set is the disjoint union
over `j` of `(fiber j) ×ˢ (fiber j)`; `card_biUnion` + `card_product` give `Σ_j n_j²`. -/
theorem congruent_pairs_eq_coset_sq {N : ℕ} [NeZero N] {g : ℕ} [NeZero g] (hgN : g ∣ N)
    (A : Finset (ZMod N)) :
    ((A ×ˢ A).filter (fun p : ZMod N × ZMod N => g ∣ ZMod.val (p.1 - p.2))).card
      = ∑ j : ZMod g, (A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card ^ 2 := by
  have hg : 0 < g := Nat.pos_of_ne_zero (NeZero.ne g)
  -- Kernel of `φ`: `φ y = 0 ↔ g ∣ y.val`.
  have hker : ∀ y : ZMod N, (ZMod.castHom hgN (ZMod g)) y = 0 ↔ g ∣ ZMod.val y := by
    intro y
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff]
  -- Bridge: congruence mod `g` ⟺ same coset.
  have hbridge : ∀ x x' : ZMod N, g ∣ ZMod.val (x - x') ↔
      (ZMod.castHom hgN (ZMod g)) x = (ZMod.castHom hgN (ZMod g)) x' := by
    intro x x'
    constructor
    · intro h
      have := (hker (x - x')).mpr h
      rwa [map_sub, sub_eq_zero] at this
    · intro h
      apply (hker (x - x')).mp
      rw [map_sub, sub_eq_zero]; exact h
  -- The congruent-pair set is the disjoint union of `fiber j ×ˢ fiber j` over cosets `j`.
  have hset : (A ×ˢ A).filter (fun p : ZMod N × ZMod N => g ∣ ZMod.val (p.1 - p.2))
      = Finset.univ.biUnion (fun j : ZMod g =>
          (A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)) ×ˢ
          (A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j))) := by
    ext ⟨x, x'⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_univ,
      true_and]
    rw [hbridge x x']
    constructor
    · rintro ⟨⟨hx, hx'⟩, heq⟩
      exact ⟨(ZMod.castHom hgN (ZMod g)) x, ⟨hx, rfl⟩, hx', heq.symm⟩
    · rintro ⟨j, ⟨hx, hxj⟩, hx', hx'j⟩
      exact ⟨⟨hx, hx'⟩, hxj.trans hx'j.symm⟩
  -- Fibers are pairwise disjoint (an element has a unique coset).
  have hdisj : (↑(Finset.univ : Finset (ZMod g)) : Set (ZMod g)).PairwiseDisjoint
      (fun j : ZMod g => (A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)) ×ˢ
        (A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j))) := by
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro ⟨x, x'⟩ hmem1 hmem2
    simp only [Finset.mem_product, Finset.mem_filter] at hmem1 hmem2
    exact hij (hmem1.1.2.symm.trans hmem2.1.2)
  rw [hset, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl (fun j _ => by rw [Finset.card_product, pow_two])

/-- **Coset partition of `A`.**  The coset occupation numbers sum to `|A|`:
`Σ_{j : ZMod g} #{x ∈ A : φ x = j} = |A|`.  A direct fiberwise count of `A` under `φ`. -/
theorem coset_card_sum_eq_card {N : ℕ} [NeZero N] {g : ℕ} [NeZero g] (hgN : g ∣ N)
    (A : Finset (ZMod N)) :
    ∑ j : ZMod g, (A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card = A.card := by
  exact (Finset.card_eq_sum_card_fiberwise
    (fun x _ => Finset.mem_univ ((ZMod.castHom hgN (ZMod g)) x))).symm

/-- **Cauchy–Schwarz on cosets (from Fourier positivity).**  The equidistribution floor of Part LV,
made explicit via the coset-partition identity:

    |A|² ≤ g · Σ_{j : ZMod g} n_j²,

i.e. the classical `(Σ n_j)² ≤ g · Σ n_j²` — here a consequence of Fourier positivity rather than
a separate Cauchy–Schwarz. -/
theorem coset_card_sq_sum_ge {N : ℕ} [NeZero N] {g : ℕ} [NeZero g] (hgN : g ∣ N)
    (A : Finset (ZMod N)) :
    (A.card : ℝ) ^ 2 ≤ (g : ℝ) *
      ∑ j : ZMod g, ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ) ^ 2 := by
  have hg : 0 < g := Nat.pos_of_ne_zero (NeZero.ne g)
  have hfloor := subgroup_additive_energy_floor hg hgN A
  have hcast : (((A ×ˢ A).filter (fun p : ZMod N × ZMod N => g ∣ ZMod.val (p.1 - p.2))).card : ℝ)
      = ∑ j : ZMod g, ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ) ^ 2 := by
    rw [congruent_pairs_eq_coset_sq hgN A]; push_cast; rfl
  rwa [hcast] at hfloor

/-- **Dense coset extraction.**  A single nonzero frequency `r ≠ 0` in the order-`g` subgroup with
`Â(r) ≠ 0` forces some coset strictly above the average occupation `|A|/g`:

    ∃ j : ZMod g, |A|/g < #{x ∈ A : φ x = j}.

Since coset `j` contains exactly `N/g` elements of `ZMod N`, its relative density
`n_j/(N/g)` then strictly exceeds the ambient density `|A|/N`.  This is the concrete coset density
increment triggered by a nonzero non-unit Fourier mass (`badFreqMass`, Part LIII): it lets the
Sárközy square-difference-free problem descend to modulus `g`.

Proof: the strict energy excess `|A|² < g · Σ_j n_j²` (Part LV) is incompatible with every coset
being at or below average, since `n_j ≤ |A|/g` for all `j` would give
`Σ n_j² ≤ (|A|/g)·Σ n_j = |A|²/g`, i.e. `g·Σ n_j² ≤ |A|²`. -/
theorem exists_dense_coset_of_subgroup_freq {N : ℕ} [NeZero N] {g : ℕ} [NeZero g] (hgN : g ∣ N)
    (A : Finset (ZMod N)) {r : ZMod N} (hr : (N / g) ∣ ZMod.val r) (hr0 : r ≠ 0)
    (hrne : fourierCoeff A r ≠ 0) :
    ∃ j : ZMod g, (A.card : ℝ) / g <
      (A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card := by
  have hg : 0 < g := Nat.pos_of_ne_zero (NeZero.ne g)
  have hg_ne : (g : ℝ) ≠ 0 := by positivity
  by_contra hcon
  push_neg at hcon
  -- Strict energy excess, made explicit via the coset-partition identity.
  have hstrict := subgroup_additive_energy_strict hg hgN A hr hr0 hrne
  have hcast : (((A ×ˢ A).filter (fun p : ZMod N × ZMod N => g ∣ ZMod.val (p.1 - p.2))).card : ℝ)
      = ∑ j : ZMod g, ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ) ^ 2 := by
    rw [congruent_pairs_eq_coset_sq hgN A]; push_cast; rfl
  rw [hcast] at hstrict
  -- Σ n_j = |A|.
  have hsum : ∑ j : ZMod g, ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ)
      = A.card := by exact_mod_cast coset_card_sum_eq_card hgN A
  -- Every coset at/below average ⟹ Σ n_j² ≤ (|A|/g)·|A|.
  have hub : ∑ j : ZMod g, ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ) ^ 2
      ≤ (A.card / g) * A.card := by
    calc ∑ j : ZMod g, ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ) ^ 2
        = ∑ j : ZMod g, ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ) *
            ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ) := by
          simp_rw [pow_two]
      _ ≤ ∑ j : ZMod g, ((A.card : ℝ) / g) *
            ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcon j) (by positivity))
      _ = ((A.card : ℝ) / g) *
            ∑ j : ZMod g, ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ) := by
          rw [Finset.mul_sum]
      _ = ((A.card : ℝ) / g) * A.card := by rw [hsum]
  -- g · Σ n_j² ≤ |A|², contradicting the strict excess.
  have hkey : (g : ℝ) *
      ∑ j : ZMod g, ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ) ^ 2
      ≤ (A.card : ℝ) ^ 2 := by
    calc (g : ℝ) *
        ∑ j : ZMod g, ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ) ^ 2
        ≤ (g : ℝ) * (((A.card : ℝ) / g) * A.card) :=
          mul_le_mul_of_nonneg_left hub (by positivity)
      _ = (A.card : ℝ) ^ 2 := by field_simp
  linarith

/-! ### Part LVII — the relative-density increment: the dense coset carries genuinely higher density

Part LVI (`exists_dense_coset_of_subgroup_freq`) showed that a single nonzero non-unit Fourier
coefficient forces some coset occupation `n_j = #{x ∈ A : φ x = j}` strictly above the average
`|A|/g`.  To read this as a genuine *density increment* — the engine of a Sárközy-style descent —
one must compare `n_j` against the actual size of the coset it lives in, not merely against the
average.  The coset `{x : φ x = j}` is a fiber of the reduction `φ = castHom (g ∣ N) : ZMod N → ZMod g`;
since `φ` is a surjective ring homomorphism, every fiber has *exactly* `N/g` elements
(`castHom_fiber_card`).  Hence the relative density of `A` on the dense coset,

    n_j / (N/g),

strictly exceeds the ambient density `|A|/N` (`exists_dense_coset_relative_density`): the coset
carries `A` at strictly higher density than the whole group.

**Honest remaining obstruction (the crux of Sárközy over general `N`).**  A true density-increment
*iteration* would restrict `A` to this dense coset, re-identify the coset (an arithmetic progression
with common difference `g` and `N/g` terms) with `ZMod (N/g)`, and recurse.  The obstruction is that
square-difference-freeness does **not** descend along these cosets: for `x = j + g·a`, `y = j + g·b`
in the coset, `x − y = g·(a − b)`, and `g·(a − b)` being a nonzero square in `ZMod N` is *not*
equivalent to `a − b` being a square in `ZMod (N/g)`.  The classical Sárközy increment is taken along
progressions of common difference a *perfect square* `d²` precisely to preserve the avoided set; the
subgroup `g·ZMod N` used here (dictated by the Fourier support of `badFreqMass`) is not of that form.
Closing the descent therefore requires relating the Fourier support of `badFreqMass` to square
common differences — the exact gap flagged in Parts XLVII / LIII.  Everything below is 0-axiom. -/

/-- **Coset (fiber) cardinality.**  Every fiber of the reduction `φ = castHom (g ∣ N) : ZMod N → ZMod g`
has exactly `N/g` elements:

    #{x : ZMod N | φ x = j} = N / g.

Proof: `φ` is a surjective additive hom, so translation by a preimage `x₀` of `j` gives a bijection
`fiber 0 ≃ fiber j`; all `g` fibers thus have equal cardinality, and they partition `ZMod N`
(card `N`), forcing each to be `N/g`. -/
theorem castHom_fiber_card {N : ℕ} [NeZero N] {g : ℕ} [NeZero g] (hgN : g ∣ N) (j : ZMod g) :
    (Finset.univ.filter (fun x : ZMod N => (ZMod.castHom hgN (ZMod g)) x = j)).card = N / g := by
  have hg : 0 < g := Nat.pos_of_ne_zero (NeZero.ne g)
  set f := (ZMod.castHom hgN (ZMod g)) with hf_def
  -- All fibers have equal cardinality (translate by a preimage).
  have hequal : ∀ k : ZMod g,
      (Finset.univ.filter (fun x : ZMod N => f x = k)).card
        = (Finset.univ.filter (fun x : ZMod N => f x = 0)).card := by
    intro k
    obtain ⟨x₀, hx₀⟩ := ZMod.castHom_surjective hgN k
    have hset : (Finset.univ.filter (fun x : ZMod N => f x = k))
        = (Finset.univ.filter (fun x : ZMod N => f x = 0)).map (Equiv.addRight x₀).toEmbedding := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Equiv.coe_toEmbedding, Equiv.coe_addRight]
      constructor
      · intro hy
        exact ⟨y - x₀, by rw [map_sub, hy, hx₀, sub_self], by abel⟩
      · rintro ⟨z, hz, rfl⟩
        rw [map_add, hz, hx₀, zero_add]
    rw [hset, Finset.card_map]
  -- The fibers partition `ZMod N`, whose cardinality is `N`.
  have hpart : N = ∑ k : ZMod g, (Finset.univ.filter (fun x : ZMod N => f x = k)).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (ZMod N))) (t := (Finset.univ : Finset (ZMod g)))
      (f := f) (fun x _ => Finset.mem_univ (f x))
    rwa [Finset.card_univ, ZMod.card] at h
  -- Hence `g · (fiber 0).card = N`.
  have hg_mul : g * (Finset.univ.filter (fun x : ZMod N => f x = 0)).card = N := by
    have h2 : (∑ k : ZMod g, (Finset.univ.filter (fun x : ZMod N => f x = k)).card)
        = g * (Finset.univ.filter (fun x : ZMod N => f x = 0)).card := by
      rw [Finset.sum_congr rfl (fun k _ => hequal k), Finset.sum_const, Finset.card_univ,
        ZMod.card, smul_eq_mul]
    rw [← h2]; exact hpart.symm
  rw [hequal j]
  exact (Nat.div_eq_of_eq_mul_left hg (by rw [mul_comm]; exact hg_mul.symm)).symm

/-- **Relative-density increment.**  A single nonzero frequency `r ≠ 0` in the order-`g` subgroup
with `Â(r) ≠ 0` forces a coset `j` on which the *relative* density of `A` strictly exceeds the
ambient density:

    |A| / N  <  n_j / (N/g),      where n_j = #{x ∈ A : φ x = j}.

Since the coset has exactly `N/g` elements (`castHom_fiber_card`), `n_j / (N/g)` is the honest
density of `A` on that coset.  This is the concrete density increment produced by a nonzero non-unit
Fourier mass (`badFreqMass`, Part LIII).  See the section header for the remaining obstruction to
turning this into a full descent. -/
theorem exists_dense_coset_relative_density {N : ℕ} [NeZero N] {g : ℕ} [NeZero g] (hgN : g ∣ N)
    (A : Finset (ZMod N)) {r : ZMod N} (hr : (N / g) ∣ ZMod.val r) (hr0 : r ≠ 0)
    (hrne : fourierCoeff A r ≠ 0) :
    ∃ j : ZMod g, (A.card : ℝ) / N <
      (A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card / ((N / g : ℕ) : ℝ) := by
  have hg : 0 < g := Nat.pos_of_ne_zero (NeZero.ne g)
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hMpos_nat : 0 < N / g := Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hgN) hg
  have hMpos : (0 : ℝ) < ((N / g : ℕ) : ℝ) := by exact_mod_cast hMpos_nat
  have hNeq : (N : ℝ) = ((N / g : ℕ) : ℝ) * g := by
    have hdm : (N / g) * g = N := Nat.div_mul_cancel hgN
    exact_mod_cast hdm.symm
  obtain ⟨j, hj⟩ := exists_dense_coset_of_subgroup_freq hgN A hr hr0 hrne
  refine ⟨j, ?_⟩
  set n : ℝ := ((A.filter (fun x => (ZMod.castHom hgN (ZMod g)) x = j)).card : ℝ) with hn
  -- `hj : |A|/g < n`;  clear the denominator to `|A| < n·g`.
  rw [div_lt_iff₀ hgr] at hj
  -- Cross-multiply the goal `|A|/N < n/(N/g)` and finish with `N = (N/g)·g`.
  rw [div_lt_div_iff₀ hNpos hMpos, hNeq]
  nlinarith [hj, hMpos]

end Szemeredi.Roth
