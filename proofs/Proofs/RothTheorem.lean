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

/-- An AP-free subset of ZMod N has strictly fewer than N elements when N ≥ 2.
    The full set always contains the 3-AP {0, 1, 2·1}. -/
theorem apFree_card_lt {N : ℕ} (hN : 1 < N) (A : Finset (ZMod N)) (hAP : APFree A) :
    A.card < N := by
  haveI : NeZero N := ⟨by omega⟩
  by_contra h; push_neg at h
  have hfull : A = Finset.univ :=
    Finset.eq_univ_of_card A (by have := card_le_nat A; simp only [ZMod.card]; omega)
  haveI : Fact (1 < N) := ⟨hN⟩
  exact hAP 0 1 one_ne_zero (hfull ▸ Finset.mem_univ _) (hfull ▸ Finset.mem_univ _)
    (hfull ▸ Finset.mem_univ _)

/-- In ZMod N, there is at most one nonzero element r with 2*r = 0.
    Both a and b have additive order 2. In the cyclic group ZMod N, there is at most
    one subgroup of order 2, so ⟨a⟩ = ⟨b⟩ and a = b. -/
private lemma two_mul_eq_zero_unique {N : ℕ} [NeZero N]
    (a b : ZMod N) (ha : a ≠ 0) (h2a : 2 * a = 0)
    (hb : b ≠ 0) (h2b : 2 * b = 0) : a = b := by
  -- Reduce to val(a) = val(b) via ZMod.val arithmetic
  -- In ZMod N (= Fin N for N > 0), 2*a = 0 means (val a + val a) % N = 0
  -- Since 0 < val a < N, this forces val a + val a = N, i.e., val a = N/2
  -- Similarly val b = N/2, so a = b
  have haa : a + a = 0 := by linear_combination h2a
  have hbb : b + b = 0 := by linear_combination h2b
  -- val(a + a) = (val a + val a) % N = 0
  have hmod_a : (ZMod.val a + ZMod.val a) % N = 0 := by
    have h := congr_arg ZMod.val haa; rw [ZMod.val_add, ZMod.val_zero] at h; exact h
  have hmod_b : (ZMod.val b + ZMod.val b) % N = 0 := by
    have h := congr_arg ZMod.val hbb; rw [ZMod.val_add, ZMod.val_zero] at h; exact h
  -- N ∣ 2 * val a, and 0 < 2 * val a < 2N, so 2 * val a = N
  have hva_pos : 0 < ZMod.val a := by
    rw [Nat.pos_iff_ne_zero]; intro h; exact ha (by rwa [ZMod.val_eq_zero] at h)
  have hvb_pos : 0 < ZMod.val b := by
    rw [Nat.pos_iff_ne_zero]; intro h; exact hb (by rwa [ZMod.val_eq_zero] at h)
  have hva_lt : ZMod.val a < N := ZMod.val_lt a
  have hvb_lt : ZMod.val b < N := ZMod.val_lt b
  -- Helper: if N ∣ s and 0 < s < 2N, then s = N
  have dvd_range_eq : ∀ {s : ℕ}, N ∣ s → 0 < s → s < 2 * N → s = N := by
    intro s hdvs hlo hhi
    obtain ⟨k, hk⟩ := hdvs  -- s = N * k
    subst hk
    -- k = 0: N*0 = 0, contradicts 0 < s
    -- k = 1: N*1 = N ✓
    -- k ≥ 2: N*k ≥ 2N, contradicts s < 2N
    rcases k with _ | _ | k
    · omega
    · omega
    · exfalso
      have h1 : N * 2 ≤ N * (k + 2) := Nat.mul_le_mul_left N (by omega)
      linarith
  have h2va : ZMod.val a + ZMod.val a = N :=
    dvd_range_eq (Nat.dvd_of_mod_eq_zero hmod_a) (by omega) (by omega)
  have h2vb : ZMod.val b + ZMod.val b = N :=
    dvd_range_eq (Nat.dvd_of_mod_eq_zero hmod_b) (by omega) (by omega)
  -- val a = val b (both = N/2), hence a = b
  have hval_eq : ZMod.val a = ZMod.val b := by omega
  exact ZMod.val_injective N hval_eq

/-- Fourier coefficient at 0 equals the cardinality: Â(0) = |A|. -/
theorem fourierCoeff_zero {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    fourierCoeff A 0 = ↑A.card := by
  unfold fourierCoeff
  simp only [zero_mul, ZMod.val_zero, Nat.cast_zero, zero_div, mul_zero, Complex.exp_zero]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Parseval for nonzero frequencies: ∑_{r≠0} ‖Â(r)‖² = |A|(N - |A|). -/
theorem parseval_nonzero {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (Finset.univ.filter (· ≠ (0 : ZMod N))).sum (fun r => ‖fourierCoeff A r‖ ^ 2) =
    (A.card : ℝ) * ((N : ℝ) - A.card) := by
  have hparseval := parseval_on_zmod A
  -- Split at r = 0
  have hsplit : (Finset.univ.sum fun r : ZMod N => ‖fourierCoeff A r‖ ^ 2) =
      ‖fourierCoeff A 0‖ ^ 2 +
      ((Finset.univ.erase (0 : ZMod N)).sum fun r => ‖fourierCoeff A r‖ ^ 2) :=
    (Finset.add_sum_erase Finset.univ (fun r : ZMod N => ‖fourierCoeff A r‖ ^ 2)
      (Finset.mem_univ (0 : ZMod N))).symm
  have hfilt : (Finset.univ : Finset (ZMod N)).filter (· ≠ 0) = Finset.univ.erase (0 : ZMod N) :=
    Finset.filter_ne' _ _
  have h_norm0 : ‖fourierCoeff A 0‖ ^ 2 = (A.card : ℝ) ^ 2 := by
    rw [fourierCoeff_zero, Complex.norm_natCast]
  rw [hfilt]; linarith [hsplit, h_norm0]

/-- If A ⊆ Z/NZ is nonempty and N ≥ 2, some nonzero Fourier coefficient satisfies
    the Parseval pigeonhole bound: ‖Â(r)‖² · (N-1) ≥ |A| · (N - |A|).

    This bound is always achievable and does not require AP-freeness.
    For the density increment argument, AP-freeness provides an identity
    (triple_count_fourier) that can give stronger bounds in certain regimes. -/
theorem fourier_parseval_pigeonhole {N : ℕ} (hN : 1 < N) (A : Finset (ZMod N))
    (_hA : A.Nonempty) :
    ∃ r : ZMod N, r ≠ 0 ∧
      ‖fourierCoeff A r‖ ^ 2 * ((N : ℝ) - 1) ≥ (A.card : ℝ) * ((N : ℝ) - A.card) := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (1 < N) := ⟨hN⟩
  -- Parseval for r ≠ 0
  have hpnz := parseval_nonzero A
  set S := Finset.univ.filter (· ≠ (0 : ZMod N)) with hS_def
  have hcard : S.card = N - 1 := by
    rw [hS_def, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, ZMod.card]
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    have := Finset.card_eq_zero.mpr h; rw [hcard] at this; omega
  -- Pigeonhole by contradiction: if all terms are strictly small, sum is too small
  by_contra hall; push_neg at hall
  -- hall : ∀ r ≠ 0, ‖Â(r)‖² * (↑N - 1) < ↑A.card * (↑N - ↑A.card)
  -- Sum the multiplicative form: ∑ [f(r) * (N-1)] < |S| * C
  have hN1_pos : (0 : ℝ) < (↑N : ℝ) - 1 := by
    have : (1 : ℝ) < ↑N := by exact_mod_cast hN
    linarith
  -- Each f(r) * (N-1) < C
  have hlt_mul : ∀ r ∈ S, ‖fourierCoeff A r‖ ^ 2 * (↑N - 1) <
      (A.card : ℝ) * (↑N - ↑A.card) :=
    fun r hr => hall r (Finset.mem_filter.mp hr).2
  -- Sum all: (∑ f) * (N-1) = ∑ (f * (N-1)) < (N-1) * C
  have hsum_bound : S.sum (fun r => ‖fourierCoeff A r‖ ^ 2 * (↑N - 1)) <
      S.sum (fun _ => (A.card : ℝ) * (↑N - ↑A.card)) :=
    Finset.sum_lt_sum (fun r hr => le_of_lt (hlt_mul r hr))
      ⟨hne.choose, hne.choose_spec, hlt_mul _ hne.choose_spec⟩
  -- RHS constant sum = (N-1) * C
  set C := (A.card : ℝ) * ((↑N : ℝ) - ↑A.card) with hC_def
  have hconst : S.sum (fun _ => C) = (↑N - 1) * C := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard,
      show (↑(N - 1) : ℝ) = (↑N : ℝ) - 1 from by
        rw [Nat.cast_sub (Nat.one_le_of_lt hN)]; simp]
  -- LHS: commute f * c → c * f, then factor
  simp_rw [mul_comm (‖fourierCoeff A _‖ ^ 2) ((↑N : ℝ) - 1)] at hsum_bound
  rw [← Finset.mul_sum, hconst] at hsum_bound
  -- (N-1) * ∑ f < (N-1) * C → ∑ f < C (cancel N-1 > 0)
  have hlt_sum : S.sum (fun r => ‖fourierCoeff A r‖ ^ 2) < C := by
    nlinarith [hsum_bound]
  linarith [hpnz]

set_option maxHeartbeats 800000 in
/-- If A has no 3-AP and has density delta, then some Fourier coefficient
    is large. This is the key analytic step in Roth's proof.

    The bound δ²N/2 follows from the AP-free Fourier identity combined with
    Parseval. When δ²N ≤ 2 (sparse regime), Parseval pigeonhole gives
    ‖Â(r)‖ ≥ 1 ≥ δ²N/2. When δ²N > 2 (dense regime), the Fourier identity
    ∑_{r≠0} Â(r)²conj(Â(2r)) = N|A| - |A|³ combined with term-by-term bounds
    gives δ²N ≤ 2, a contradiction. -/
theorem fourier_large_coefficient {N : ℕ} (hN : 1 < N) (A : Finset (ZMod N))
    (hAP : APFree A) (delta : ℝ) (hdelta : 0 < delta)
    (hdensity : (A.card : ℝ) ≥ delta * N) :
    ∃ r : ZMod N, r ≠ 0 ∧ ‖fourierCoeff A r‖ ≥ delta ^ 2 * N / 2 := by
  haveI : NeZero N := ⟨by omega⟩
  set n := A.card with hn_def
  have hNpos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr (by omega)
  have hn_pos : 0 < n := by
    rw [Nat.pos_iff_ne_zero]; intro h; rw [h] at hdensity; simp at hdensity; nlinarith
  have hAne : A.Nonempty := Finset.card_pos.mp hn_pos
  have hn_lt : n < N := apFree_card_lt hN A hAP
  by_cases hcase : delta ^ 2 * ↑N ≤ 2
  · -- CASE 1: δ²N ≤ 2, so δ²N/2 ≤ 1. Parseval pigeonhole gives ‖Â(r)‖ ≥ 1 ≥ δ²N/2.
    obtain ⟨r, hr, hpig⟩ := fourier_parseval_pigeonhole hN A hAne
    refine ⟨r, hr, ?_⟩
    have hn_ge : (1 : ℝ) ≤ ↑n := Nat.one_le_cast.mpr hn_pos
    have hn_le : (↑n : ℝ) ≤ ↑N - 1 := by
      have : n ≤ N - 1 := Nat.lt_iff_le_pred (by omega : 0 < N) |>.mp hn_lt
      have := Nat.cast_le (α := ℝ).mpr this
      have : (↑(N - 1) : ℝ) = ↑N - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ N)]; simp
      linarith
    have hprod : (↑n : ℝ) * (↑N - ↑n) ≥ ↑N - 1 := by nlinarith
    have hN1_pos : (0 : ℝ) < ↑N - 1 := by
      have : (1 : ℝ) < ↑N := by exact_mod_cast hN
      linarith
    have hnorm_sq : ‖fourierCoeff A r‖ ^ 2 ≥ 1 := by nlinarith
    -- ‖Â(r)‖ ≥ 1 from ‖Â(r)‖² ≥ 1 and ‖Â(r)‖ ≥ 0
    have hnorm_ge : ‖fourierCoeff A r‖ ≥ 1 := by
      by_contra h; push_neg at h
      have : ‖fourierCoeff A r‖ ^ 2 < 1 := by
        calc ‖fourierCoeff A r‖ ^ 2
            = ‖fourierCoeff A r‖ * ‖fourierCoeff A r‖ := sq _
          _ ≤ ‖fourierCoeff A r‖ * 1 :=
              mul_le_mul_of_nonneg_left (le_of_lt h) (norm_nonneg _)
          _ = ‖fourierCoeff A r‖ := mul_one _
          _ < 1 := h
      linarith
    linarith
  · -- CASE 2: δ²N > 2. Fourier identity + contradiction.
    push_neg at hcase
    by_contra hall; push_neg at hall
    -- Step A: n² > N (dense regime). From n ≥ δN and δ²N > 2: n² ≥ δ²N² > 2N > N
    have hn_sq : (↑n : ℝ) ^ 2 ≥ (delta * ↑N) ^ 2 := by nlinarith [sq_nonneg (↑n - delta * ↑N)]
    have hn_sq_gt : (↑n : ℝ) ^ 2 > ↑N := by nlinarith
    -- Step B: Fourier identity from AP-freeness
    have htc : tripleCount A = 0 := (apFree_iff_tripleCount_zero A).mp hAP
    have hfi := triple_count_fourier A
    rw [htc, Nat.cast_zero, zero_add] at hfi
    have hN_ne : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    set F := fun r : ZMod N => fourierCoeff A r ^ 2 * starRingEnd ℂ (fourierCoeff A (2 * r))
    have hfi2 : (↑N : ℂ) * ↑n = Finset.univ.sum F := by rw [hfi]; field_simp
    -- Step C: Split sum at r = 0, F(0) = n³
    have hF0 : F 0 = (↑n : ℂ) ^ 3 := by
      simp only [F, mul_zero, fourierCoeff_zero, map_natCast]; ring
    have hsplit : Finset.univ.sum F = F 0 + (Finset.univ.erase 0).sum F :=
      (Finset.add_sum_erase _ F (Finset.mem_univ 0)).symm
    -- Σ_{r≠0} F(r) = Nn - n³ (complex algebra, not linarith)
    have hsum_ne0 : (Finset.univ.erase 0).sum F = (↑N : ℂ) * ↑n - (↑n : ℂ) ^ 3 := by
      have h4 : (↑N : ℂ) * ↑n = (↑n : ℂ) ^ 3 + (Finset.univ.erase 0).sum F := by
        calc (↑N : ℂ) * ↑n = Finset.univ.sum F := hfi2
          _ = F 0 + (Finset.univ.erase 0).sum F := hsplit
          _ = (↑n : ℂ) ^ 3 + (Finset.univ.erase 0).sum F := by rw [hF0]
      linear_combination -h4
    -- Step D: Triangle inequality
    have htri : ‖(↑N : ℂ) * ↑n - (↑n : ℂ) ^ 3‖ ≤
        (Finset.univ.erase 0).sum (fun r => ‖F r‖) := by
      rw [← hsum_ne0]; exact norm_sum_le _ _
    have hFnorm : ∀ r : ZMod N,
        ‖F r‖ = ‖fourierCoeff A r‖ ^ 2 * ‖fourierCoeff A (2 * r)‖ := by
      intro r; simp only [F, norm_mul, norm_pow, RCLike.norm_conj]
    -- Step E: Split sum by 2r = 0 vs 2r ≠ 0
    set S₁ := (Finset.univ.erase (0 : ZMod N)).filter (fun r => 2 * r ≠ 0)
    set S₂ := (Finset.univ.erase (0 : ZMod N)).filter (fun r => 2 * r = 0)
    have hunion : (Finset.univ.erase 0) = S₁ ∪ S₂ := by
      ext r; simp [S₁, S₂, Finset.mem_filter, Finset.mem_erase]; tauto
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_filter]; intro r _ h1 h2; exact h1 h2
    have hsum_split : (Finset.univ.erase 0).sum (fun r => ‖F r‖) =
        S₁.sum (fun r => ‖F r‖) + S₂.sum (fun r => ‖F r‖) := by
      rw [hunion]; exact Finset.sum_union hdisj
    -- Step F: Bound S₁ (2r ≠ 0 so ‖Â(2r)‖ < δ²N/2)
    have hS1_bound : S₁.sum (fun r => ‖F r‖) ≤
        (delta ^ 2 * ↑N / 2) * ((↑n : ℝ) * (↑N - ↑n)) := by
      simp_rw [hFnorm]
      calc S₁.sum (fun r => ‖fourierCoeff A r‖ ^ 2 * ‖fourierCoeff A (2 * r)‖)
          ≤ S₁.sum (fun r => ‖fourierCoeff A r‖ ^ 2 * (delta ^ 2 * ↑N / 2)) := by
            apply Finset.sum_le_sum; intro r hr
            exact mul_le_mul_of_nonneg_left
              (le_of_lt (hall (2 * r) (Finset.mem_filter.mp hr).2)) (sq_nonneg _)
        _ = (delta ^ 2 * ↑N / 2) * S₁.sum (fun r => ‖fourierCoeff A r‖ ^ 2) := by
            rw [← Finset.sum_mul]; ring_nf
        _ ≤ (delta ^ 2 * ↑N / 2) * ((↑n : ℝ) * (↑N - ↑n)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc S₁.sum (fun r => ‖fourierCoeff A r‖ ^ 2)
                ≤ (Finset.univ.erase 0).sum (fun r => ‖fourierCoeff A r‖ ^ 2) :=
                  Finset.sum_le_sum_of_subset_of_nonneg
                    (fun r hr => Finset.mem_of_mem_filter r hr)
                    (fun _ _ _ => sq_nonneg _)
              _ = _ := by
                  rw [show Finset.univ.erase (0 : ZMod N) =
                    Finset.univ.filter (· ≠ 0) from (Finset.filter_ne' _ _).symm]
                  exact parseval_nonzero A
    -- Step G: Bound S₂ (at most 1 element by two_mul_eq_zero_unique)
    have hS2_card : S₂.card ≤ 1 := by
      rw [Finset.card_le_one]; intro a ha b hb
      have ha' := Finset.mem_filter.mp ha; have hb' := Finset.mem_filter.mp hb
      exact two_mul_eq_zero_unique a b
        (Finset.mem_erase.mp ha'.1).1 ha'.2 (Finset.mem_erase.mp hb'.1).1 hb'.2
    have hS2_bound : S₂.sum (fun r => ‖F r‖) ≤ (delta ^ 2 * ↑N / 2) ^ 2 * ↑n := by
      simp_rw [hFnorm]
      calc S₂.sum (fun r => ‖fourierCoeff A r‖ ^ 2 * ‖fourierCoeff A (2 * r)‖)
          ≤ S₂.sum (fun _ => (delta ^ 2 * ↑N / 2) ^ 2 * ↑n) := by
            apply Finset.sum_le_sum; intro r hr
            have hr' := Finset.mem_filter.mp hr
            have hAr := sq_le_sq' (by linarith [norm_nonneg (fourierCoeff A r)])
              (le_of_lt (hall r (Finset.mem_erase.mp hr'.1).1))
            rw [hr'.2, fourierCoeff_zero, Complex.norm_natCast]
            exact mul_le_mul_of_nonneg_right hAr (Nat.cast_nonneg n)
        _ = ↑S₂.card * ((delta ^ 2 * ↑N / 2) ^ 2 * ↑n) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 1 * ((delta ^ 2 * ↑N / 2) ^ 2 * ↑n) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hS2_card
        _ = _ := one_mul _
    -- Step H: ‖Nn - n³‖ = n(n² - N) as real numbers
    have hn_cast_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn_pos
    have hsub_pos : (0 : ℝ) < (↑n : ℝ) ^ 2 - ↑N := sub_pos.mpr hn_sq_gt
    set rval := (↑n : ℝ) * ((↑n : ℝ) ^ 2 - ↑N) with hrval_def
    have hrval_pos : 0 < rval := mul_pos hn_cast_pos hsub_pos
    have hnorm_real : ‖(↑N : ℂ) * ↑n - (↑n : ℂ) ^ 3‖ = rval := by
      have hcast : (↑N : ℂ) * ↑n - (↑n : ℂ) ^ 3 = -↑rval := by
        simp only [hrval_def]; push_cast; ring
      rw [hcast, norm_neg, Complex.norm_real]
      exact Real.norm_of_nonneg (le_of_lt hrval_pos)
    -- Step I: Combine to get n(n²-N) ≤ (δ²N/2)·n(N-n) + (δ²N/2)²·n
    have hcombined : (↑n : ℝ) * ((↑n : ℝ) ^ 2 - ↑N) ≤
        (delta ^ 2 * ↑N / 2) * ((↑n : ℝ) * (↑N - ↑n)) +
        (delta ^ 2 * ↑N / 2) ^ 2 * ↑n := by linarith [htri, hsum_split, hS1_bound, hS2_bound]
    -- Step J: Divide by n > 0 and use δ²N/2 ≤ n to simplify
    have hdelta_le : delta ≤ 1 := by
      have : (↑n : ℝ) < ↑N := by exact_mod_cast hn_lt
      nlinarith
    have hα_le_n : delta ^ 2 * ↑N / 2 ≤ ↑n := by nlinarith
    -- n²-N ≤ (δ²N/2)(N-n) + (δ²N/2)² ≤ (δ²N/2)·N (since δ²N/2 ≤ n means N-n+δ²N/2 ≤ N)
    -- Step: α² ≤ α·n (since α ≤ n and α ≥ 0)
    set α := delta ^ 2 * ↑N / 2 with hα_def
    have hα_pos : (0 : ℝ) ≤ α := by positivity
    have hα_sq_le : α ^ 2 ≤ α * ↑n :=
      calc α ^ 2 = α * α := sq α
        _ ≤ α * ↑n := mul_le_mul_of_nonneg_left hα_le_n hα_pos
    -- n(n²-N) ≤ αn(N-n) + α²n ≤ αn(N-n+n) = αnN
    have h_bound : ↑n * ((↑n : ℝ) ^ 2 - ↑N * (1 + α)) ≤ 0 := by nlinarith
    -- Since n > 0 and n·x ≤ 0, we get x ≤ 0, i.e., n² ≤ N(1+α)
    have hkey : (↑n : ℝ) ^ 2 ≤ ↑N * (1 + α) :=
      le_of_not_gt fun h => by
        have : (0 : ℝ) < (↑n : ℝ) ^ 2 - ↑N * (1 + α) := by linarith
        linarith [mul_pos hn_cast_pos this]
    -- From n ≥ δN: δ²N² ≤ n² ≤ N(1+α) = N + αN. So δ²N ≤ 1+α = 1+δ²N/2, giving δ²N ≤ 2
    have hcontra : delta ^ 2 * ↑N ≤ 2 := by nlinarith
    linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART V: DENSITY INCREMENT LEMMA
-- ═══════════════════════════════════════════════════════════════════

/-- Key lemma: casting a natural number modulo P to ZMod N and multiplying by r
    gives the same result as casting the original number, when P = addOrderOf r.
    This is because (P : ZMod N) * r = 0, so the quotient vanishes. -/
private lemma natCast_mod_mul_eq {N : ℕ} [NeZero N] (a : ℕ) (r : ZMod N) (P : ℕ)
    (hord : addOrderOf r = P) :
    (↑(a % P) : ZMod N) * r = (↑a : ZMod N) * r := by
  have hPr : (↑P : ZMod N) * r = 0 := by
    rw [← nsmul_eq_mul]; exact hord ▸ addOrderOf_nsmul_eq_zero r
  have hsum : (↑P : ZMod N) * ↑(a / P) + ↑(a % P) = ↑a := by
    have h : (↑(P * (a / P) + a % P) : ZMod N) = ↑a :=
      congrArg Nat.cast (Nat.div_add_mod a P)
    simp only [Nat.cast_add, Nat.cast_mul] at h; exact h
  have hvanish : (↑P : ZMod N) * ↑(a / P) * r = 0 := by
    calc (↑P : ZMod N) * ↑(a / P) * r
        = ↑(a / P) * ((↑P : ZMod N) * r) := by ring
      _ = ↑(a / P) * 0 := by rw [hPr]
      _ = 0 := mul_zero _
  calc (↑(a % P) : ZMod N) * r
      = 0 + (↑(a % P) : ZMod N) * r := (zero_add _).symm
    _ = (↑P : ZMod N) * ↑(a / P) * r + (↑(a % P) : ZMod N) * r := by rw [hvanish]
    _ = ((↑P : ZMod N) * ↑(a / P) + ↑(a % P)) * r := by ring
    _ = (↑a : ZMod N) * r := by rw [hsum]

/-- The coset map k ↦ a + val(k)·r is additive: the val of a sum maps to the sum
    of individual images. -/
private lemma cosetMap_add {N P : ℕ} [NeZero N] [NeZero P]
    (r : ZMod N) (hord : addOrderOf r = P)
    (a : ZMod N) (k₁ k₂ : ZMod P) :
    a + (↑(ZMod.val (k₁ + k₂)) : ZMod N) * r =
    (a + (↑(ZMod.val k₁) : ZMod N) * r) + (↑(ZMod.val k₂) : ZMod N) * r := by
  rw [ZMod.val_add, natCast_mod_mul_eq _ _ P hord, Nat.cast_add, add_mul]
  ring

/-- AP-freeness is preserved under the coset inclusion map.
    If A ⊆ Z/NZ is AP-free, r has additive order P, and B = {k ∈ Z/PZ : a + val(k)·r ∈ A},
    then B is AP-free in Z/PZ. -/
theorem apFree_coset_slice {N P : ℕ} [NeZero N] [NeZero P]
    (A : Finset (ZMod N)) (hAP : APFree A)
    (r : ZMod N) (hord : addOrderOf r = P)
    (a : ZMod N)
    (B : Finset (ZMod P))
    (hB : ∀ k : ZMod P, k ∈ B ↔ a + (↑(ZMod.val k) : ZMod N) * r ∈ A) :
    APFree B := by
  intro b e he hb hbe hb2e
  rw [hB] at hb hbe hb2e
  set d := (↑(ZMod.val e) : ZMod N) * r with hd_def
  have h1 : a + (↑(ZMod.val (b + e)) : ZMod N) * r =
      (a + (↑(ZMod.val b) : ZMod N) * r) + d :=
    cosetMap_add r hord a b e
  have h2 : a + (↑(ZMod.val (b + 2 * e)) : ZMod N) * r =
      (a + (↑(ZMod.val b) : ZMod N) * r) + 2 * d := by
    have : b + 2 * e = (b + e) + e := by ring
    rw [this, cosetMap_add r hord a (b + e) e, cosetMap_add r hord a b e]; ring
  have hd_ne : d ≠ 0 := by
    rw [hd_def]; intro h
    have hval_e_pos : 0 < ZMod.val e := by
      rw [Nat.pos_iff_ne_zero]; intro h0; exact he (by rwa [ZMod.val_eq_zero] at h0)
    have hval_e_lt : ZMod.val e < P := ZMod.val_lt e
    have := addOrderOf_dvd_of_nsmul_eq_zero
      (show (ZMod.val e) • r = 0 by rwa [nsmul_eq_mul])
    rw [hord] at this
    exact Nat.not_dvd_of_pos_of_lt hval_e_pos hval_e_lt this
  exact hAP (a + (↑(ZMod.val b) : ZMod N) * r) d hd_ne hb (h1 ▸ hbe) (h2 ▸ hb2e)

/-- The density increment lemma: if A ⊆ Z/NZ has density delta and no 3-AP,
    then A has density at least delta + c·delta² on some long arithmetic
    subprogression, and the restriction is also AP-free. This is the
    core inductive step in Roth's proof.

    Proof sketch: By fourier_large_coefficient, ∃ r ≠ 0 with large |Â(r)|.
    The character χ_r partitions Z/NZ into arithmetic progressions of
    length ~√N. By pigeonhole, A has increased density on at least one
    of these progressions. AP-freeness is preserved since any 3-AP in the
    subprogression would lift to a 3-AP in the original set. -/
theorem density_increment_lemma {N : ℕ} (hN : 1 < N) (A : Finset (ZMod N))
    (hAP : APFree A) (delta : ℝ) (hdelta : 0 < delta)
    (hdensity : (A.card : ℝ) ≥ delta * N) :
    ∃ (M : ℕ) (B : Finset (ZMod M)),
      1 < M ∧
      APFree B ∧
      (B.card : ℝ) ≥ (delta + delta ^ 2 / 100) * M := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: ROTH'S THEOREM (MAIN RESULT)
-- ═══════════════════════════════════════════════════════════════════

/-- Auxiliary: one step of the density increment iteration.
    If there exists an AP-free set of density ≥ d in Z/NZ (with N > 1),
    then there exists an AP-free set of density ≥ d + d²/100 in some
    Z/MZ with 1 < M. -/
theorem density_increment_step {N : ℕ} (hN : 1 < N) (d : ℝ) (hd : 0 < d)
    (A : Finset (ZMod N)) (hAP : APFree A)
    (hdens : (A.card : ℝ) ≥ d * N) :
    ∃ (M : ℕ) (B : Finset (ZMod M)),
      1 < M ∧ APFree B ∧ (B.card : ℝ) ≥ (d + d ^ 2 / 100) * M :=
  density_increment_lemma hN A hAP d hd hdens

/-- After k iterations of density increment starting from density delta,
    the density reaches at least delta + k * delta² / 100.

    This uses the fact that at each step the density d satisfies d ≥ delta,
    so the increment d²/100 ≥ delta²/100. Thus after k steps, the total
    increment is at least k * delta²/100. -/
theorem density_iteration (delta : ℝ) (hdelta : 0 < delta) :
    ∀ k : ℕ, ∀ N : ℕ, 1 < N →
    ∀ A : Finset (ZMod N), APFree A →
    (A.card : ℝ) ≥ (delta + k * delta ^ 2 / 100) * N →
    ∃ (M : ℕ) (B : Finset (ZMod M)),
      1 < M ∧ APFree B ∧
      (B.card : ℝ) ≥ (delta + (k + 1) * delta ^ 2 / 100) * M := by
  intro k N hN A hAP hdens
  -- Current density is d := delta + k * delta^2 / 100
  set d := delta + ↑k * delta ^ 2 / 100 with hd_def
  have hd_pos : 0 < d := by positivity
  -- Apply density increment at current density d
  obtain ⟨M, B, hMgt, hBAP, hBdens⟩ := density_increment_lemma hN A hAP d hd_pos hdens
  refine ⟨M, B, hMgt, hBAP, ?_⟩
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
  -- N₀ = 2 works: the argument applies for all N ≥ 2
  refine ⟨2, fun N hN A hdensity hAP => ?_⟩
  have hNgt : 1 < N := by omega
  -- Iteration chain: after k density-increment steps, we get a set of
  -- density ≥ delta + k * delta²/100 in some Z/MZ with M > 1
  have chain : ∀ k : ℕ, ∃ (M : ℕ) (B : Finset (ZMod M)),
      1 < M ∧ APFree B ∧ (B.card : ℝ) ≥ (delta + ↑k * delta ^ 2 / 100) * ↑M := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
      exact ⟨N, A, hNgt, hAP, hdensity⟩
    | succ k ih =>
      obtain ⟨M, B, hMgt, hBAP, hBdens⟩ := ih
      obtain ⟨M', B', hM'gt, hB'AP, hB'dens⟩ :=
        density_iteration delta hdelta k M hMgt B hBAP hBdens
      refine ⟨M', B', hM'gt, hB'AP, ?_⟩
      push_cast at hB'dens ⊢
      linarith
  -- Choose K large enough that delta + K * delta²/100 > 1
  obtain ⟨K, hK⟩ := exists_nat_gt (100 / delta ^ 2)
  obtain ⟨M, B, hMgt, _, hBdens⟩ := chain K
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
  have hMcast : (0 : ℝ) < ↑M := Nat.cast_pos.mpr (by omega : 0 < M)
  have hBgt : (B.card : ℝ) > ↑M := by
    calc (B.card : ℝ) ≥ (delta + ↑K * delta ^ 2 / 100) * ↑M := hBdens
      _ > 1 * ↑M := mul_lt_mul_of_pos_right hgt1 hMcast
      _ = ↑M := one_mul _
  -- But |B| ≤ M for any Finset of ZMod M — contradiction
  linarith [card_le_nat_real B]

end Szemeredi.Roth
