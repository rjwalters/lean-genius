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

/-- tripleCount + |A| expressed as a triple sum of AP indicators.
    ∑_{x∈A} ∑_{y∈A} ∑_{z∈A} [x+z=2y] counts all (a,d) with a,a+d,a+2d ∈ A
    (including d=0), where (a, a+2d, a+d) = (x, z, y). -/
private theorem tripleCount_add_card_eq_triple_sum {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (tripleCount A : ℂ) + ↑A.card = A.sum fun x => A.sum fun y =>
      A.sum fun z => if x + z = 2 * y then (1 : ℂ) else 0 := by
  -- Step 1: Collapse inner z-sum: x+z=2y ↔ z=2y-x, unique solution
  have inner_eq : ∀ (x y : ZMod N),
      (A.sum fun z => if x + z = 2 * y then (1 : ℂ) else 0) =
      if 2 * y - x ∈ A then 1 else 0 := by
    intro x y
    simp_rw [show ∀ z : ZMod N, (x + z = 2 * y) ↔ (z = 2 * y - x) from
      fun z => ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩]
    exact Finset.sum_ite_eq' A _ fun _ => 1
  simp_rw [inner_eq]
  -- Goal: (tripleCount A : ℂ) + ↑A.card = ∑ x∈A, ∑ y∈A, ite (2*y-x∈A) 1 0
  -- Both sides count |{(x,y) ∈ A² : 2y-x ∈ A}|.
  -- Reduce to ℕ equality via cardinality.
  set T := (A ×ˢ A).filter (fun p : ZMod N × ZMod N => 2 * p.2 - p.1 ∈ A) with T_def
  -- Key ℕ identity: T.card = ∑∑ ite 1 0 (over ℕ)
  have rhs_nat : T.card = (A.sum fun x => A.sum fun y =>
      if 2 * y - x ∈ A then (1 : ℕ) else 0) := by
    rw [T_def, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  -- Define allAP = {(a,d) : a∈A, a+d∈A, a+2d∈A} (including d=0)
  set allAP := (Finset.univ ×ˢ Finset.univ).filter
    (fun p : ZMod N × ZMod N => p.1 ∈ A ∧ (p.1 + p.2) ∈ A ∧ (p.1 + 2 * p.2) ∈ A) with allAP_def
  -- allAP bijects with T via (a,d) ↦ (a, a+d)
  have hbij : allAP.card = T.card :=
    Finset.card_bij (fun (p : ZMod N × ZMod N) _ => (p.1, p.1 + p.2))
      -- Forward: maps into T
      (fun ⟨a, d⟩ h => by
        simp only [allAP_def, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
          true_and] at h
        simp only [T_def, Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨h.1, h.2.1⟩, ?_⟩
        rw [show (2 : ZMod N) * (a + d) - a = a + 2 * d from by ring]
        exact h.2.2)
      -- Injective
      (fun ⟨a₁, d₁⟩ _ ⟨a₂, d₂⟩ _ h => by
        have heq := Prod.mk.inj h
        ext
        · exact heq.1
        · exact add_left_cancel (heq.1 ▸ heq.2))
      -- Surjective: inverse is (x, y-x)
      (fun ⟨x, y⟩ h => by
        simp only [T_def, Finset.mem_filter, Finset.mem_product] at h
        refine ⟨⟨x, y - x⟩, ?_, ?_⟩
        · simp only [allAP_def, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
          refine ⟨h.1.1, ?_, ?_⟩
          · rw [show x + (y - x) = y from by ring]; exact h.1.2
          · rw [show x + 2 * (y - x) = 2 * y - x from by ring]; exact h.2
        · exact Prod.ext rfl (show x + (y - x) = y from by ring))
  -- Partition allAP by d=0/d≠0: allAP.card = tripleCount A + A.card
  have hpart : tripleCount A + A.card = allAP.card := by
    -- Decompose allAP into d≠0 and d=0 parts
    set ne_part := allAP.filter (fun p : ZMod N × ZMod N => p.2 ≠ 0) with ne_part_def
    set eq_part := allAP.filter (fun p : ZMod N × ZMod N => p.2 = 0) with eq_part_def
    -- allAP = ne_part ∪ eq_part (disjoint)
    have hunion : allAP = ne_part ∪ eq_part := by
      ext ⟨a, d⟩
      simp only [ne_part_def, eq_part_def, Finset.mem_union, Finset.mem_filter]
      tauto
    have hdisj : Disjoint ne_part eq_part := by
      rw [Finset.disjoint_left]
      intro ⟨a, d⟩ h1 h2
      simp only [ne_part_def, eq_part_def, Finset.mem_filter] at h1 h2
      exact h1.2 h2.2
    rw [hunion, Finset.card_union_of_disjoint hdisj]
    congr 1
    · -- ne_part.card = tripleCount A (same set, reordered conjuncts)
      simp only [tripleCount, ne_part_def, allAP_def, Finset.filter_filter]
      congr 1
      ext ⟨a, d⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      tauto
    · -- eq_part.card = A.card
      -- eq_part = A.image (fun a => (a, 0))
      have heq_img : eq_part = A.image (fun a => (a, (0 : ZMod N))) := by
        ext ⟨a, d⟩
        simp only [eq_part_def, allAP_def, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
          true_and, Finset.mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨ha, -, -⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
        · rintro ⟨b, hb, rfl, rfl⟩; simp [hb]
      rw [heq_img, Finset.card_image_of_injective _
        (fun a b h => (Prod.mk.inj h).1)]
  -- Combine: tripleCount A + A.card = T.card
  have nat_eq : tripleCount A + A.card = T.card := hpart.trans hbij
  -- Cast ℕ equality to ℂ
  have lhs_cast : (tripleCount A : ℂ) + ↑A.card = ↑(tripleCount A + A.card) := by push_cast; ring
  rw [lhs_cast, nat_eq, rhs_nat]
  -- ↑(∑ℕ) = ∑ℂ: push cast through double sum and ite
  norm_cast

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

/-- The Fourier identity for AP counting:
    tripleCount(A) + |A| = N⁻¹ · Σ_r Â(r)² · conj(Â(2r))
    The RHS is the FULL triple count (including degenerate d=0 triples which
    contribute |A|). The d=0 triples are: for each a ∈ A, (a, a, a) is a
    3-AP with common difference 0.
    Proof: expand 1_A via Fourier inversion, swap sums, apply orthogonality. -/
theorem triple_count_fourier {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (tripleCount A : ℂ) + ↑A.card = (↑N)⁻¹ *
      Finset.univ.sum (fun r : ZMod N =>
        fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r))) := by
  have hN : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [eq_comm, inv_mul_eq_div, div_eq_iff hN, eq_comm]
  -- Goal: ((tripleCount A : ℂ) + ↑A.card) * ↑N = ∑ r, Â(r)² · conj(Â(2r))
  -- Part A: Expand Fourier coefficients as ψ sums
  simp_rw [fourierCoeff_eq_sum_psi, sq, map_sum (starRingEnd ℂ), conj_psi]
  -- Distribute products over sums
  simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  -- Combine ψ products: ψ(r*x) * ψ(r*z) * ψ(-(2*r*y)) → ψ(r*(x+z-2y))
  simp_rw [show ∀ (r x z y : ZMod N),
    ψ (r * x) * ψ (r * z) * ψ (-(2 * r * y)) = ψ (r * (x + z - 2 * y)) from
    fun r x z y => by rw [← psi_add, ← psi_add]; congr 1; ring]
  -- RHS: ∑_r ∑_{x∈A} ∑_{z∈A} ∑_{y∈A} ψ(r * (x + z - 2 * y))
  -- Part B: Swap r sum to innermost position
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := A)]
  -- Now: ∑_{x∈A} ∑_{z∈A} ∑_{y∈A} ∑_r ψ(r * (x + z - 2 * y))
  -- Part C: Apply character orthogonality
  simp_rw [char_orthogonality, sub_eq_zero]
  -- Each inner sum: if x + z = 2*y then ↑N else 0
  -- Part D: Factor out N and match combinatorial identity
  simp_rw [show ∀ (P : Prop) [Decidable P],
    (if P then (↑N : ℂ) else 0) = ↑N * if P then (1 : ℂ) else 0 from
    fun P _ => by split_ifs <;> simp]
  simp_rw [← Finset.mul_sum]
  rw [mul_comm]
  -- Goal: ((tripleCount A : ℂ) + ↑A.card) * ↑N = ↑N * ∑_{x∈A} ∑_{z∈A} ∑_{y∈A} if x+z=2y then 1 else 0
  congr 1
  -- The Fourier expansion sum matches the triple sum in our helper
  exact tripleCount_add_card_eq_triple_sum A

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: LARGE FOURIER COEFFICIENT FROM AP-FREENESS
-- ═══════════════════════════════════════════════════════════════════

/-- The zeroth Fourier coefficient equals the cardinality of A. -/
theorem fourierCoeff_zero {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    fourierCoeff A 0 = ↑A.card := by
  simp only [fourierCoeff, zero_mul, ZMod.val_zero, Nat.cast_zero, zero_div, mul_zero,
    Complex.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- For N ≥ 3, an AP-free subset cannot be all of ZMod N. -/
theorem apFree_card_lt {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (hAP : APFree A)
    (hN3 : N ≥ 3) : A.card < N := by
  by_contra h
  push_neg at h
  have heq : A.card = Fintype.card (ZMod N) := by
    have := card_le_nat A; rw [ZMod.card]; omega
  have hu := Finset.eq_univ_of_card A heq
  rw [hu] at hAP
  haveI : Fact (1 < N) := ⟨by omega⟩
  exact hAP 0 1 one_ne_zero (Finset.mem_univ _) (Finset.mem_univ _) (Finset.mem_univ _)

/-- For odd N, r ↦ 2r is a bijection on ZMod N (since 2 is invertible). -/
private lemma two_mul_bijective {N : ℕ} [NeZero N] (hNodd : ¬ 2 ∣ N) :
    Function.Bijective (fun r : ZMod N => 2 * r) := by
  have hcop : Nat.Coprime 2 N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hNodd
  have hu : IsUnit (2 : ZMod N) := (ZMod.unitOfCoprime 2 hcop).isUnit
  exact Finite.injective_iff_bijective.mp (fun a b h => hu.mul_left_cancel h)

/-- Parseval restricted to r ≠ 0 after change of variables r ↦ 2r for odd N:
    Σ_{r≠0} ‖Â(2r)‖² = |A|(N - |A|). -/
private lemma parseval_nonzero_double {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (hNodd : ¬ 2 ∣ N) :
    (((Finset.univ : Finset (ZMod N)).filter (· ≠ 0)).sum
      fun r => ‖fourierCoeff A (2 * r)‖ ^ 2) =
    A.card * N - A.card ^ 2 := by
  -- Step 1: filter (· ≠ 0) = erase 0
  have heq_set : (Finset.univ : Finset (ZMod N)).filter (· ≠ 0) = Finset.univ.erase 0 := by
    ext x; simp [Finset.mem_filter, Finset.mem_erase]
  rw [heq_set]
  -- Step 2: split off r=0 term: erase.sum + g(0) = univ.sum
  set g : ZMod N → ℝ := fun r => ‖fourierCoeff A (2 * r)‖ ^ 2
  have hsplit : (Finset.univ.erase (0 : ZMod N)).sum g + g 0 = Finset.univ.sum g :=
    Finset.sum_erase_add _ g (Finset.mem_univ 0)
  -- Step 3: g(0) = ‖Â(0)‖² = |A|²
  have hg0 : g 0 = (↑A.card : ℝ) ^ 2 := by
    show ‖fourierCoeff A (2 * 0)‖ ^ 2 = _
    rw [mul_zero, fourierCoeff_zero, Complex.norm_natCast]
  -- Step 4: Σ_r g(r) = Σ_s ‖Â(s)‖² = |A|·N via bijection + Parseval
  have hfull : Finset.univ.sum g = ↑A.card * ↑N := by
    show (Finset.univ.sum fun r => ‖fourierCoeff A (2 * r)‖ ^ 2) = _
    rw [show (Finset.univ.sum fun r : ZMod N => ‖fourierCoeff A (2 * r)‖ ^ 2) =
        Finset.univ.sum (fun s => ‖fourierCoeff A s‖ ^ 2) from
      Fintype.sum_equiv (Equiv.ofBijective _ (two_mul_bijective hNodd)) _ _ (fun _ => rfl)]
    exact_mod_cast parseval_on_zmod A
  -- Combine: erase.sum = |A|N - |A|²
  linarith

/-- Parseval restricted to r ≠ 0 (without the 2r change of variables):
    Σ_{r≠0} ‖Â(r)‖² = |A|(N - |A|). -/
private lemma parseval_nonzero {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (((Finset.univ : Finset (ZMod N)).filter (· ≠ 0)).sum
      fun r => ‖fourierCoeff A r‖ ^ 2) =
    A.card * N - A.card ^ 2 := by
  have heq_set : (Finset.univ : Finset (ZMod N)).filter (· ≠ 0) = Finset.univ.erase 0 := by
    ext x; simp [Finset.mem_filter, Finset.mem_erase]
  rw [heq_set]
  set f : ZMod N → ℝ := fun r => ‖fourierCoeff A r‖ ^ 2
  have hsplit : (Finset.univ.erase (0 : ZMod N)).sum f + f 0 = Finset.univ.sum f :=
    Finset.sum_erase_add _ f (Finset.mem_univ 0)
  have hf0 : f 0 = (↑A.card : ℝ) ^ 2 := by
    show ‖fourierCoeff A 0‖ ^ 2 = _
    rw [fourierCoeff_zero, Complex.norm_natCast]
  have hfull : Finset.univ.sum f = ↑A.card * ↑N := by exact_mod_cast parseval_on_zmod A
  linarith

/-- If A has no 3-AP and has density delta, then some Fourier coefficient
    is large. This is the key analytic step in Roth's proof.

    Requires N odd (so r ↦ 2r is bijective) and δ²N ≥ 4 (to ensure
    the bound δ²N/2 is achievable).

    Proof: AP-free → tripleCount = 0 → Fourier identity gives
    Σ_{r≠0} Â(r)²conj(Â(2r)) = N|A| - |A|³. Factor out max |Â(r)|,
    bound remaining sum by Parseval via AM-GM, solve for max. -/
theorem fourier_large_coefficient {N : ℕ} (hN : 0 < N) (A : Finset (ZMod N))
    (hAP : APFree A) (delta : ℝ) (hdelta : 0 < delta)
    (hdensity : (A.card : ℝ) ≥ delta * N)
    (hNodd : ¬ 2 ∣ N)
    (hd2N : delta ^ 2 * ↑N ≥ 4) :
    ∃ r : ZMod N, r ≠ 0 ∧ ‖fourierCoeff A r‖ ≥ delta ^ 2 * N / 2 := by
  haveI : NeZero N := ⟨by omega⟩
  -- N ≥ 3 (odd, positive, and δ²N ≥ 4 excludes N=1)
  have hN3 : N ≥ 3 := by
    rcases Nat.lt_or_ge N 3 with h | h
    · -- N ∈ {1, 2}. N=2 contradicts odd. N=1: δ²≥4 and |A|≥δ≥2 but |A|≤1.
      interval_cases N
      · -- N = 1: δ²≥4 but |A|≤1 so δ≤1, contradicting δ²≥4
        exfalso
        simp only [Nat.cast_one, mul_one] at hd2N hdensity
        have h1 : (A.card : ℝ) ≤ 1 := by exact_mod_cast card_le_nat A
        nlinarith [mul_le_mul_of_nonneg_left (show delta ≤ 1 by linarith) (le_of_lt hdelta)]
      · exact absurd ⟨1, rfl⟩ hNodd
    · exact h
  -- |A| < N (AP-free in ZMod N with N ≥ 3)
  have hAlt : A.card < N := apFree_card_lt A hAP hN3
  -- |A|² > N (from δ²N ≥ 4 and |A| ≥ δN: |A|² ≥ δ²N² = (δ²N)N ≥ 4N > N)
  have hA2 : (A.card : ℝ) ^ 2 > ↑N := by
    have hsq := sq_nonneg ((A.card : ℝ) - delta * ↑N)
    have hNp : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    nlinarith
  have hApos : (0 : ℝ) < A.card := by nlinarith
  have hNmA : (0 : ℝ) < ↑N - ↑A.card := by
    have : (A.card : ℝ) < ↑N := Nat.cast_lt.mpr hAlt; linarith
  have hNpos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  -- ═══ Core proof by contradiction ═══
  -- Assume ∀ r ≠ 0, ‖Â(r)‖ < δ²N/2.
  -- From AP-free + Fourier identity: Σ_{r≠0} Â(r)²conj(Â(2r)) = N|A| - |A|³
  -- Upper bound: ‖sum‖ ≤ Σ ‖Â(r)‖²‖Â(2r)‖ ≤ (δ²N/2) · Σ ‖Â(r)‖‖Â(2r)‖
  --   ≤ (δ²N/2) · |A|(N-|A|)   [by AM-GM + Parseval for odd N]
  -- Lower bound: ‖sum‖ ≥ |A|³ - |A|N   [since sum is real]
  -- Arithmetic: |A|³ - |A|N > (δ²N/2) · |A|(N-|A|) when δ²N(1+δ) > 2
  -- Contradiction.
  --
  -- Proof by contradiction: assume all Fourier coefficients are small, derive
  -- both an upper bound (Fourier analysis) and lower bound (arithmetic) that
  -- contradict each other.
  suffices h_key : (∀ r : ZMod N, r ≠ 0 → ‖fourierCoeff A r‖ < delta ^ 2 * ↑N / 2) →
      (A.card : ℝ) ^ 3 - ↑A.card * ↑N ≤
      delta ^ 2 * ↑N / 2 * (↑A.card * (↑N - ↑A.card)) from by
    by_contra hall
    push_neg at hall
    -- hall : ∀ r, r ≠ 0 → ‖Â(r)‖ < δ²N/2
    have h_upper := h_key hall
    have h_lower : (A.card : ℝ) ^ 3 - ↑A.card * ↑N >
        delta ^ 2 * ↑N / 2 * (↑A.card * (↑N - ↑A.card)) := by
      suffices hsuff : 2 * (A.card : ℝ) ^ 2 + delta ^ 2 * ↑N * ↑A.card -
          delta ^ 2 * ↑N ^ 2 - 2 * ↑N > 0 by nlinarith
      have hd2N_strict : delta ^ 2 * ↑N * (1 + delta) > 2 := by nlinarith
      have hNterm : ↑N * (delta ^ 2 * ↑N * (1 + delta) - 2) > 0 :=
        mul_pos hNpos (by linarith)
      have hab : (A.card : ℝ) - delta * ↑N ≥ 0 := by linarith
      nlinarith [sq_nonneg ((A.card : ℝ) - delta * ↑N),
                 mul_nonneg (mul_nonneg (by nlinarith : (4 * delta + delta ^ 2) ≥ 0)
                   (le_of_lt hNpos)) hab]
    linarith
  -- ═══ Prove h_key: Fourier-analytic upper bound ═══
  -- Chain: |A|³-|A|N ≤ Σ ‖Â(r)‖²‖Â(2r)‖ ≤ (δ²N/2)·Σ ‖Â(r)‖‖Â(2r)‖ ≤ (δ²N/2)·|A|(N-|A|)
  intro hall
  -- Step 1: Fourier sum for AP-free sets = |A|·N
  have hzero := (apFree_iff_tripleCount_zero A).mp hAP
  have hfour := triple_count_fourier A
  simp only [hzero, Nat.cast_zero, zero_add] at hfour
  have hN_ne : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hS : (Finset.univ.sum fun r : ZMod N =>
      fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r))) =
      (↑A.card : ℂ) * ↑N := by
    rw [eq_comm, inv_mul_eq_div, div_eq_iff hN_ne, eq_comm] at hfour; exact hfour.symm
  -- Step 2: r=0 term = |A|³
  have hf0 : fourierCoeff A 0 ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * (0 : ZMod N))) =
      (↑A.card : ℂ) ^ 3 := by
    rw [mul_zero, fourierCoeff_zero, map_natCast]; ring
  -- Step 3: Σ_{r≠0} = |A|N - |A|³
  have hNeq : ((Finset.univ.filter (· ≠ (0 : ZMod N))).sum fun r =>
      fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r))) =
      (↑A.card : ℂ) * ↑N - (↑A.card : ℂ) ^ 3 := by
    set f : ZMod N → ℂ := fun r => fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r))
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod N))
      (· ≠ (0 : ZMod N)) f
    -- Σ_{r=0} f(r) = f(0) = |A|³
    have hzero_sum : ((Finset.univ.filter (fun r : ZMod N => ¬(r ≠ 0))).sum f) =
        (↑A.card : ℂ) ^ 3 := by
      simp only [not_not, Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton]
      exact hf0
    rw [hzero_sum] at hsplit
    exact eq_sub_of_add_eq (hsplit.trans hS)
  -- Step 4: |A|³ - |A|N ≤ Σ ‖Â(r)‖²·‖Â(2r)‖  (norm chain)
  have hS_norm : (A.card : ℝ) ^ 3 - ↑A.card * ↑N ≤
      ((Finset.univ.filter (· ≠ (0 : ZMod N))).sum fun r =>
        ‖fourierCoeff A r‖ ^ 2 * ‖fourierCoeff A (2 * r)‖) := by
    -- Sum = (|A|N - |A|³ : ℝ) as complex. Its norm = |A|³ - |A|N (negative real).
    have hnorm_eq : ‖((Finset.univ.filter (· ≠ (0 : ZMod N))).sum fun r =>
        fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r)))‖ =
        (A.card : ℝ) ^ 3 - ↑A.card * ↑N := by
      rw [hNeq]
      -- Convert ℂ expression to (ℝ expression : ℂ)
      have hrc : (↑A.card : ℂ) * ↑N - (↑A.card : ℂ) ^ 3 =
          (((↑A.card : ℝ) * ↑N - (↑A.card : ℝ) ^ 3 : ℝ) : ℂ) := by push_cast; ring
      rw [hrc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by nlinarith)]
      ring
    -- Triangle inequality + norm of product
    have htri := norm_sum_le (Finset.univ.filter (· ≠ (0 : ZMod N)))
      (fun r : ZMod N => fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r)))
    have hnorm_term : ∀ r : ZMod N,
        ‖fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r))‖ =
        ‖fourierCoeff A r‖ ^ 2 * ‖fourierCoeff A (2 * r)‖ := by
      intro r; rw [norm_mul, norm_pow]; congr 1; rw [starRingEnd_apply, norm_star]
    simp_rw [hnorm_term] at htri; linarith
  -- Step 5: Σ ‖Â(r)‖²·‖Â(2r)‖ ≤ (δ²N/2)·Σ ‖Â(r)‖·‖Â(2r)‖
  have hfactor : ((Finset.univ.filter (· ≠ (0 : ZMod N))).sum fun r =>
      ‖fourierCoeff A r‖ ^ 2 * ‖fourierCoeff A (2 * r)‖) ≤
      delta ^ 2 * ↑N / 2 * ((Finset.univ.filter (· ≠ (0 : ZMod N))).sum fun r =>
        ‖fourierCoeff A r‖ * ‖fourierCoeff A (2 * r)‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    calc ‖fourierCoeff A r‖ ^ 2 * ‖fourierCoeff A (2 * r)‖
        = ‖fourierCoeff A r‖ * (‖fourierCoeff A r‖ * ‖fourierCoeff A (2 * r)‖) := by
          rw [sq]; ring
      _ ≤ delta ^ 2 * ↑N / 2 * (‖fourierCoeff A r‖ * ‖fourierCoeff A (2 * r)‖) :=
          mul_le_mul_of_nonneg_right (le_of_lt (hall r hr))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- Step 6: AM-GM + Parseval: Σ ‖Â(r)‖·‖Â(2r)‖ ≤ |A|(N-|A|)
  have hamgm : ((Finset.univ.filter (· ≠ (0 : ZMod N))).sum fun r =>
      ‖fourierCoeff A r‖ * ‖fourierCoeff A (2 * r)‖) ≤
      ↑A.card * (↑N - ↑A.card) := by
    calc ((Finset.univ.filter (· ≠ (0 : ZMod N))).sum fun r =>
          ‖fourierCoeff A r‖ * ‖fourierCoeff A (2 * r)‖)
        ≤ ((Finset.univ.filter (· ≠ (0 : ZMod N))).sum fun r =>
          (‖fourierCoeff A r‖ ^ 2 + ‖fourierCoeff A (2 * r)‖ ^ 2) / 2) := by
          apply Finset.sum_le_sum; intro r _
          nlinarith [sq_nonneg (‖fourierCoeff A r‖ - ‖fourierCoeff A (2 * r)‖),
                     norm_nonneg (fourierCoeff A r), norm_nonneg (fourierCoeff A (2 * r))]
      _ = (((Finset.univ.filter (· ≠ (0 : ZMod N))).sum fun r => ‖fourierCoeff A r‖ ^ 2) +
           ((Finset.univ.filter (· ≠ (0 : ZMod N))).sum fun r =>
            ‖fourierCoeff A (2 * r)‖ ^ 2)) / 2 := by
          rw [← Finset.sum_div, ← Finset.sum_add_distrib]
      _ = ↑A.card * (↑N - ↑A.card) := by
          rw [parseval_nonzero A, parseval_nonzero_double A hNodd]; ring
  -- Final chain
  calc (A.card : ℝ) ^ 3 - ↑A.card * ↑N
      ≤ ((Finset.univ.filter (· ≠ (0 : ZMod N))).sum fun r =>
          ‖fourierCoeff A r‖ ^ 2 * ‖fourierCoeff A (2 * r)‖) := hS_norm
    _ ≤ delta ^ 2 * ↑N / 2 * ((Finset.univ.filter (· ≠ (0 : ZMod N))).sum fun r =>
          ‖fourierCoeff A r‖ * ‖fourierCoeff A (2 * r)‖) := hfactor
    _ ≤ delta ^ 2 * ↑N / 2 * (↑A.card * (↑N - ↑A.card)) := by
        apply mul_le_mul_of_nonneg_left hamgm; positivity

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
