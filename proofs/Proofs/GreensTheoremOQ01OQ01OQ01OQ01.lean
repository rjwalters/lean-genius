/-
  Axiom Elimination: iteratedIntervalIntegral_order_independent
  (greens-theorem-oq-01-oq-01-oq-01-oq-01)

  ## Problem

  The parent proof `greens-theorem-oq-01-oq-01-oq-01` axiomatizes:

    iteratedIntervalIntegral_order_independent {n} {a b : Fin n → ℝ}
        (hab : ∀ i, a i ≤ b i) {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
        (σ : Equiv.Perm (Fin n)) :
        iteratedIntervalIntegral a b f =
        iteratedIntervalIntegral (a ∘ σ) (b ∘ σ) (fun x => f (fun i => x (σ.symm i)))

  ## Proof Structure

  Building blocks:
  - B0 (continuous_param): parameterized integral is continuous in its parameter
  - B1 (swap_outer_two): swap positions 0,1 via Fubini
  - B2 (perm_tail): permuting tail positions uses IH inside outer integral
  - B3 (iter_integral_swap_any): swap(x,y) by combining B1+B2
  - Main: induction on n, using swap_induction_on

  ## Sorries: 2
  1. continuous_param (succ step): compact bound for continuousAt_of_dominated_interval
  2. iter_integral_swap_zero (k ≥ 2): decomposition of swap(0,k) into products of swaps
-/

import Mathlib
import Proofs.GreensTheoremOQ01OQ01OQ01

namespace GreensTheoremOQ01OQ01OQ01OQ01

open MeasureTheory intervalIntegral Set Filter Topology
open GreensTheoremOQ01OQ01OQ01 (iteratedIntervalIntegral
  iteratedIntervalIntegral_zero iteratedIntervalIntegral_succ
  iteratedIntervalIntegral_one iteratedIntervalIntegral_two)

-- ═══════════════════════════════════════════════════
-- Section 0: Continuity of Parameterized Iterated Integral
-- ═══════════════════════════════════════════════════

/-- For any first-countable locally compact T2 space α and continuous
    F : α × (Fin n → ℝ) → ℝ, the parameterized iterated integral
    `fun x => iteratedIntervalIntegral a b (fun t => F (x, t))` is continuous.

    Proof by induction on n:
    - n=0: direct (integral is F(x, Fin.elim0))
    - n+1: apply continuousAt_of_dominated_interval with:
        • H(x, t₀) := iteratedIntervalIntegral (tail a) (tail b) (fun t => F(x, cons t₀ t))
        • H continuous by IH with α' = α × ℝ
        • Bound M: H is bounded on compact K × [a₀,b₀] by compactness -/
private lemma continuous_param :
    ∀ (n : ℕ) {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
      [FirstCountableTopology α]
      (a b : Fin n → ℝ) {F : α × (Fin n → ℝ) → ℝ} (_ : Continuous F),
    Continuous (fun x : α => iteratedIntervalIntegral a b (fun t => F (x, t))) := by
  intro n
  induction n with
  | zero =>
    intro α _ _ _ _ a b F hF
    simp only [iteratedIntervalIntegral_zero]
    exact hF.comp (continuous_id.prod_mk continuous_const)
  | succ n ih =>
    intro α _ _ _ _ a b F hF
    simp only [iteratedIntervalIntegral_succ]
    -- H(x, t₀) = iteratedIntervalIntegral (tail a) (tail b) (fun t => F(x, cons t₀ t))
    -- By IH with α' = α × ℝ and F'((x,t₀),t) = F(x, cons t₀ t):
    have H_cont : Continuous (fun q : α × ℝ =>
        iteratedIntervalIntegral (Fin.tail a) (Fin.tail b)
          (fun rest => F (q.1, Fin.cons q.2 rest))) := by
      apply @ih (α × ℝ) _ _ _ _ (Fin.tail a) (Fin.tail b)
          (fun q : (α × ℝ) × (Fin n → ℝ) => F (q.1.1, Fin.cons q.1.2 q.2))
      exact hF.comp ((continuous_fst.comp continuous_fst).prod_mk
        ((continuous_snd.comp continuous_fst).finCons continuous_snd))
    -- Now: Continuous (fun x => ∫ t₀ in a₀..b₀, H(x, t₀) dt₀)
    -- Use continuousAt_of_dominated_interval at each x₀
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨K, hK_compact, hK_nhd⟩ := exists_compact_mem_nhds x₀
    -- H is bounded on K × uIcc a₀ b₀ (compact set, image under continuous ‖H‖)
    obtain ⟨M, hM⟩ := ((hK_compact.prod isCompact_uIcc).image
      H_cont.norm.continuousOn).bddAbove
    apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M)
    · -- AEStronglyMeasurable (H(x, ·)) (vol.restrict Ι) eventually near x₀
      apply Filter.eventually_of_forall; intro x
      exact (H_cont.comp (continuous_const.prod_mk continuous_id)).measurable
          |>.aestronglyMeasurable
    · -- |H(x, t₀)| ≤ M for x near x₀ and t₀ ∈ Ι a₀ b₀
      -- Use compact K containing x₀ (from hK_nhd): H bounded on K × uIcc by hM
      filter_upwards [hK_nhd] with x hx
      apply Filter.eventually_of_forall; intro t₀ ht₀
      apply hM
      exact Set.mem_image_of_mem _
        (Set.mk_mem_prod hx (Set.uIoc_subset_uIcc _ _ ht₀))
    · -- Bound is interval-integrable (constant function)
      exact intervalIntegrable_const
    · -- H(·, t₀) is continuous at x₀ for all t₀
      apply Filter.eventually_of_forall; intro t₀ _
      exact (H_cont.comp (continuous_id.prod_mk continuous_const)).continuousAt

-- ═══════════════════════════════════════════════════
-- Section 1: Integrability for the Fubini Swap
-- ═══════════════════════════════════════════════════

/-- For continuous f, the function (x₀,x₁) ↦ [iterated integral over remaining variables]
    is integrable on Ioc(a₀,b₀) × Ioc(a₁,b₁). -/
private lemma integrable_swap_pair {n : ℕ} {a b : Fin (n + 2) → ℝ}
    (hab : ∀ i, a i ≤ b i)
    {f : (Fin (n + 2) → ℝ) → ℝ} (hf : Continuous f) :
    Integrable
      (fun p : ℝ × ℝ =>
        iteratedIntervalIntegral
          (Fin.tail (Fin.tail a)) (Fin.tail (Fin.tail b))
          (fun rest => f (Fin.cons p.1 (Fin.cons p.2 rest))))
      ((volume.restrict (Ioc (a 0) (b 0))).prod (volume.restrict (Ioc (a 1) (b 1)))) := by
  -- G(p) is continuous by continuous_param
  have hcont : Continuous (fun p : ℝ × ℝ =>
      iteratedIntervalIntegral
        (Fin.tail (Fin.tail a)) (Fin.tail (Fin.tail b))
        (fun rest => f (Fin.cons p.1 (Fin.cons p.2 rest)))) := by
    apply continuous_param n (Fin.tail (Fin.tail a)) (Fin.tail (Fin.tail b))
    -- F q = f (Fin.cons q.1.1 (Fin.cons q.1.2 q.2)) : continuous by finCons compositions
    exact hf.comp ((continuous_fst.comp continuous_fst).finCons
      ((continuous_snd.comp continuous_fst).finCons continuous_snd))
  have hint : IntegrableOn
      (fun p : ℝ × ℝ =>
        iteratedIntervalIntegral (Fin.tail (Fin.tail a)) (Fin.tail (Fin.tail b))
        (fun rest => f (Fin.cons p.1 (Fin.cons p.2 rest))))
      (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1))
      (volume.prod volume) :=
    hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hint_ioc : IntegrableOn
      (fun p : ℝ × ℝ =>
        iteratedIntervalIntegral (Fin.tail (Fin.tail a)) (Fin.tail (Fin.tail b))
        (fun rest => f (Fin.cons p.1 (Fin.cons p.2 rest))))
      (Ioc (a 0) (b 0) ×ˢ Ioc (a 1) (b 1))
      (volume.prod volume) :=
    hint.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [← Measure.prod_restrict]
  exact hint_ioc

-- ═══════════════════════════════════════════════════
-- Section 2: Key Swap Computation
-- ═══════════════════════════════════════════════════

/-- For σ = swap 0 1 in Fin(n+2), applying σ permutes the first two positions. -/
private lemma swap01_cons_eq {n : ℕ} {f : (Fin (n + 2) → ℝ) → ℝ}
    (x₀ x₁ : ℝ) (rest : Fin n → ℝ) :
    let σ := Equiv.swap (0 : Fin (n + 2)) 1
    (fun x => f (fun i => x (σ.symm i))) (Fin.cons x₁ (Fin.cons x₀ rest)) =
    f (Fin.cons x₀ (Fin.cons x₁ rest)) := by
  intro σ
  simp only [σ, Equiv.swap_symm]
  congr 1
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Equiv.swap_apply_left, Fin.cons_zero, Fin.cons_succ]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp [Equiv.swap_apply_right, Fin.cons_zero, Fin.cons_succ]
    · have hne0 : k.succ.succ ≠ (0 : Fin (n + 2)) := Fin.succ_ne_zero _
      have hne1 : k.succ.succ ≠ (1 : Fin (n + 2)) := by
        intro h; have hv := congr_arg Fin.val h; simp [Fin.val_succ] at hv; omega
      simp [Equiv.swap_apply_of_ne hne0 hne1, Fin.cons_zero, Fin.cons_succ]

-- ═══════════════════════════════════════════════════
-- Section 3: Swapping Positions 0 and 1
-- ═══════════════════════════════════════════════════

theorem swap_outer_two {n : ℕ} {a b : Fin (n + 2) → ℝ}
    (hab : ∀ i, a i ≤ b i)
    {f : (Fin (n + 2) → ℝ) → ℝ} (hf : Continuous f) :
    let σ := Equiv.swap (0 : Fin (n + 2)) 1
    iteratedIntervalIntegral a b f =
    iteratedIntervalIntegral (a ∘ σ) (b ∘ σ) (fun x => f (fun i => x (σ.symm i))) := by
  intro σ
  have lhs_expand : iteratedIntervalIntegral a b f =
      ∫ x₀ in (a 0)..(b 0), ∫ x₁ in (a 1)..(b 1),
        iteratedIntervalIntegral
          (Fin.tail (Fin.tail a)) (Fin.tail (Fin.tail b))
          (fun rest => f (Fin.cons x₀ (Fin.cons x₁ rest))) := by
    simp only [iteratedIntervalIntegral_succ, Fin.tail]
  have fubini_step :
      ∫ x₀ in (a 0)..(b 0), ∫ x₁ in (a 1)..(b 1),
        iteratedIntervalIntegral
          (Fin.tail (Fin.tail a)) (Fin.tail (Fin.tail b))
          (fun rest => f (Fin.cons x₀ (Fin.cons x₁ rest))) =
      ∫ x₁ in (a 1)..(b 1), ∫ x₀ in (a 0)..(b 0),
        iteratedIntervalIntegral
          (Fin.tail (Fin.tail a)) (Fin.tail (Fin.tail b))
          (fun rest => f (Fin.cons x₀ (Fin.cons x₁ rest))) := by
    simp_rw [integral_of_le (hab 0), integral_of_le (hab 1)]
    exact MeasureTheory.integral_integral_swap (integrable_swap_pair hab hf)
  have rhs_eq :
      iteratedIntervalIntegral (a ∘ σ) (b ∘ σ) (fun x => f (fun i => x (σ.symm i))) =
      ∫ x₁ in (a 1)..(b 1), ∫ x₀ in (a 0)..(b 0),
        iteratedIntervalIntegral
          (Fin.tail (Fin.tail a)) (Fin.tail (Fin.tail b))
          (fun rest => f (Fin.cons x₀ (Fin.cons x₁ rest))) := by
    simp only [iteratedIntervalIntegral_succ, σ, Function.comp, Equiv.swap_apply_left]
    congr 1; ext x₁
    simp only [iteratedIntervalIntegral_succ, Fin.tail, σ, Function.comp, Equiv.swap_apply_right]
    congr 1; ext x₀
    congr 1; ext rest
    exact swap01_cons_eq x₀ x₁ rest
  rw [lhs_expand, fubini_step, ← rhs_eq]

-- ═══════════════════════════════════════════════════
-- Section 4: Inner Permutation Reduction
-- ═══════════════════════════════════════════════════

/-- When σ fixes 0, reduce to a permutation of the tail by `Equiv.Perm.decomposeFin`. -/
private lemma iteratedIntervalIntegral_perm_tail {n : ℕ} {a b : Fin (n + 1) → ℝ}
    (hab : ∀ i, a i ≤ b i) {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Continuous f)
    (σ : Equiv.Perm (Fin (n + 1))) (hσ0 : σ 0 = 0)
    (ih : ∀ (a' b' : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ),
          Continuous g → (∀ i, a' i ≤ b' i) →
          ∀ τ : Equiv.Perm (Fin n),
          iteratedIntervalIntegral a' b' g =
          iteratedIntervalIntegral (a' ∘ τ) (b' ∘ τ) (fun x => g (fun i => x (τ.symm i)))) :
    iteratedIntervalIntegral a b f =
    iteratedIntervalIntegral (a ∘ σ) (b ∘ σ) (fun x => f (fun i => x (σ.symm i))) := by
  let σ' : Equiv.Perm (Fin n) := (Equiv.Perm.decomposeFin σ).2
  have hfst : (Equiv.Perm.decomposeFin σ).1 = 0 := by
    have h := @Equiv.Perm.decomposeFin_symm_apply_zero n
                (Equiv.Perm.decomposeFin σ).1 (Equiv.Perm.decomposeFin σ).2
    simp only [Prod.mk.eta, Equiv.Perm.decomposeFin.symm_apply_apply] at h
    exact h.symm.trans hσ0
  have hsucc : ∀ i : Fin n, σ i.succ = (σ' i).succ := by
    intro i
    have step : σ i.succ =
        Equiv.swap 0 ((Equiv.Perm.decomposeFin σ).1) ((Equiv.Perm.decomposeFin σ).2 i).succ := by
      conv_lhs => rw [show σ = Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin σ) from
                         (Equiv.Perm.decomposeFin.symm_apply_apply σ).symm]
      rw [show (Equiv.Perm.decomposeFin σ) =
              ((Equiv.Perm.decomposeFin σ).1, (Equiv.Perm.decomposeFin σ).2) from rfl]
      exact Equiv.Perm.decomposeFin_symm_apply_succ _ _ _
    rw [step, hfst, Equiv.swap_self]
    simp [σ']
  have hσ_symm_0 : σ.symm 0 = 0 := by
    have h := σ.symm_apply_apply 0; rw [hσ0] at h; exact h
  have hsucc_symm : ∀ j : Fin n, σ.symm j.succ = (σ'.symm j).succ := by
    intro j
    have hval : σ (σ'.symm j).succ = j.succ := by
      rw [hsucc (σ'.symm j)]; congr 1; exact σ'.apply_symm_apply j
    exact (σ.injective (hval.trans (σ.apply_symm_apply j.succ).symm)).symm
  have h0a : (a ∘ σ) 0 = a 0 := by simp [hσ0]
  have h0b : (b ∘ σ) 0 = b 0 := by simp [hσ0]
  have htail_a : Fin.tail (a ∘ σ) = Fin.tail a ∘ σ' :=
    funext fun i => by simp [Fin.tail, Function.comp, hsucc i]
  have htail_b : Fin.tail (b ∘ σ) = Fin.tail b ∘ σ' :=
    funext fun i => by simp [Fin.tail, Function.comp, hsucc i]
  rw [iteratedIntervalIntegral_succ, iteratedIntervalIntegral_succ, h0a, h0b]
  apply intervalIntegral.integral_congr
  intro x₀ _
  have hfun : ∀ x' : Fin n → ℝ,
      (fun x => f (fun i => x (σ.symm i))) (Fin.cons x₀ x') =
      (fun y' => f (Fin.cons x₀ y')) (fun i => x' (σ'.symm i)) := by
    intro x'
    simp only []
    congr 1; ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hσ_symm_0, Fin.cons_zero]
    · simp [hsucc_symm j, Fin.cons_succ]
  rw [htail_a, htail_b, funext hfun]
  exact ih (Fin.tail a) (Fin.tail b)
    (fun y' => f (Fin.cons x₀ y'))
    (hf.comp (continuous_const.finCons continuous_id))
    (fun i => hab i.succ)
    σ'

-- ═══════════════════════════════════════════════════
-- Section 5: Integral Identity for swap(0, k)
-- ═══════════════════════════════════════════════════

/-- The integral identity holds for swap(0, k) for any k : Fin(n+1).
    Proof by induction on k.val:
    - k=0: trivial (swap 0 0 = id)
    - k=1: swap_outer_two
    - k=m+2: decompose swap(0,k) = swap(k₀,k) * swap(0,k₀) * swap(k₀,k)
              using swap_mul_swap_mul_swap, then chain three applications. -/
private lemma iter_integral_swap_zero {n : ℕ}
    (ih_perm : ∀ (a' b' : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ),
          Continuous g → (∀ i, a' i ≤ b' i) →
          ∀ τ : Equiv.Perm (Fin n),
          iteratedIntervalIntegral a' b' g =
          iteratedIntervalIntegral (a' ∘ τ) (b' ∘ τ) (fun x => g (fun i => x (τ.symm i)))) :
    ∀ (m : ℕ) (hm : m < n + 1),
    ∀ {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i ≤ b i)
      {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Continuous f),
    let k : Fin (n + 1) := ⟨m, hm⟩
    iteratedIntervalIntegral a b f =
    iteratedIntervalIntegral (a ∘ Equiv.swap 0 k) (b ∘ Equiv.swap 0 k)
      (fun v => f (fun i => v ((Equiv.swap 0 k).symm i))) := by
  intro m
  induction m with
  | zero =>
    intro hm a b hab f hf
    simp [Equiv.swap_self, Function.comp]
  | succ m ihm =>
    intro hm a b hab f hf
    -- k = ⟨m+1, hm⟩, k₀ = ⟨m, lt_of_succ_lt hm⟩... no wait
    -- actually hm : m+1 < n+1, so m < n+1 holds too (but we need m < n+1 for k₀)
    -- The two cases: m = 0 (k = 1) and m ≥ 1 (k ≥ 2)
    match m with
    | 0 =>
      -- k = 1: swap(0,1) = swap_outer_two
      -- Need n ≥ 1 (n+1 ≥ 2 since m+1 < n+1 and m=0 gives 1 < n+1)
      have hn : 1 ≤ n := by omega
      -- The types: Fin(n+1) with n ≥ 1, so we have Fin(n'+2) for n' = n-1
      -- Use swap_outer_two after matching n = n'+1
      obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
      -- Now n+1 = n'+2, and the lemma swap_outer_two applies
      simp only
      convert @swap_outer_two n' a b hab f hf using 1
      · rfl
      · simp [Equiv.swap_comm]
    | succ m' =>
      -- k = m'+2 ≥ 2
      -- Let k₀ = ⟨m'+1, ...⟩ (predecessor of k)
      -- Decomposition: swap(0, k) = swap(k₀, k) * swap(0, k₀) * swap(k₀, k)
      -- from swap_mul_swap_mul_swap with x=0, y=k₀, z=k:
      --   swap(k₀, k) * swap(0, k₀) * swap(k₀, k) = swap(k, 0) = swap(0, k)
      -- So we chain 3 applications:
      -- 1. Apply ihm (swap(0, k₀)) for a, b, f
      -- 2. Apply perm_tail for swap(k₀, k) [which fixes 0] to the result of step 1
      -- 3. Apply ihm (swap(0, k₀)) again to the result of step 2
      -- Currently sorry; the algebraic verification is non-trivial
      sorry

-- ═══════════════════════════════════════════════════
-- Section 6: Integral Identity for any swap
-- ═══════════════════════════════════════════════════

/-- The integral identity holds for swap(x, y) for any x ≠ y.
    - If x, y ≠ 0: swap(x,y) fixes 0, use perm_tail + IH
    - If x = 0: use iter_integral_swap_zero
    - If y = 0: use swap_comm + iter_integral_swap_zero -/
private lemma iter_integral_swap_any {n : ℕ}
    (ih : ∀ (a' b' : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ),
          Continuous g → (∀ i, a' i ≤ b' i) →
          ∀ τ : Equiv.Perm (Fin n),
          iteratedIntervalIntegral a' b' g =
          iteratedIntervalIntegral (a' ∘ τ) (b' ∘ τ) (fun x => g (fun i => x (τ.symm i))))
    {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i ≤ b i)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Continuous f)
    (x y : Fin (n + 1)) :
    iteratedIntervalIntegral a b f =
    iteratedIntervalIntegral (a ∘ Equiv.swap x y) (b ∘ Equiv.swap x y)
      (fun v => f (fun i => v ((Equiv.swap x y).symm i))) := by
  rcases Fin.eq_or_ne x y with rfl | hxy
  · simp [Equiv.swap_self, Function.comp]
  · -- Case: x ≠ y
    rcases Fin.eq_or_ne x 0 with rfl | hx0
    · -- x = 0: use iter_integral_swap_zero
      exact iter_integral_swap_zero ih y.val y.isLt hab hf
    · rcases Fin.eq_or_ne y 0 with rfl | hy0
      · -- y = 0: swap(x, 0) = swap(0, x) by swap_comm
        rw [Equiv.swap_comm x 0]
        exact iter_integral_swap_zero ih x.val x.isLt hab hf
      · -- x ≠ 0, y ≠ 0: swap(x,y) fixes 0, use perm_tail
        have hfixes0 : (Equiv.swap x y) 0 = 0 := by
          rw [Equiv.swap_apply_of_ne hx0.symm hy0.symm]
        exact iteratedIntervalIntegral_perm_tail hab hf (Equiv.swap x y) hfixes0 ih

-- ═══════════════════════════════════════════════════
-- Section 7: Main Theorem
-- ═══════════════════════════════════════════════════

/-- **N-Dimensional Order Independence**.
    Any permutation of integration variables preserves the iterated integral.

    Proof by induction on n, then by swap_induction_on on σ:
    - P(1): trivial
    - P(swap(x,y) * τ) from P(τ) and P(swap(x,y)):
        Apply P(τ) to get integral (a∘τ) (b∘τ) (f∘τ.symm),
        then apply iter_integral_swap_any to the new bounds/function. -/
theorem iteratedIntervalIntegral_order_independent {n : ℕ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i ≤ b i) {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    (σ : Equiv.Perm (Fin n)) :
    iteratedIntervalIntegral a b f =
    iteratedIntervalIntegral (a ∘ σ) (b ∘ σ) (fun x => f (fun i => x (σ.symm i))) := by
  induction n with
  | zero =>
    have : σ = Equiv.refl (Fin 0) := Subsingleton.elim _ _
    subst this; simp [iteratedIntervalIntegral, Function.comp]
  | succ n ih =>
    have ih' : ∀ (a' b' : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ),
        Continuous g → (∀ i, a' i ≤ b' i) →
        ∀ τ : Equiv.Perm (Fin n),
        iteratedIntervalIntegral a' b' g =
        iteratedIntervalIntegral (a' ∘ τ) (b' ∘ τ) (fun x => g (fun i => x (τ.symm i))) :=
      fun a' b' g hg hab' τ => ih a' b' hab' hg τ
    -- Prove by swap induction on σ
    -- P(σ) = ∀ a b hab f hf, integral a b f = integral (a∘σ) (b∘σ) (f∘σ.symm)
    -- We prove the SPECIFIC instance with our a, b, f by using induction on σ
    -- via swap_induction_on (reduces to P(1) and P(swap(x,y) * τ) from P(τ))
    induction σ using Equiv.Perm.swap_induction_on with
    | h1 =>
      simp [Function.comp]
    | hmul_swap τ x y hxy hPτ =>
      -- hPτ : integral a b f = integral (a∘τ) (b∘τ) (fun v => f(v∘τ.symm))
      -- Goal: integral a b f = integral (a∘(swap*τ)) (b∘(swap*τ)) (fun v => f(v∘(swap*τ).symm))
      have hab_τ : ∀ i, (a ∘ τ) i ≤ (b ∘ τ) i := fun i => hab _
      have hf_τ : Continuous (fun v : Fin (n + 1) → ℝ => f (fun i => v (τ.symm i))) :=
        hf.comp (continuous_pi_iff.mpr fun i => continuous_apply (τ.symm i))
      -- Chain: a b f = a∘τ b∘τ f∘τ.symm  [hPτ]
      --            = a∘τ∘swap b∘τ∘swap (f∘τ.symm)∘swap.symm [iter_integral_swap_any]
      --            = a∘(swap*τ) b∘(swap*τ) f∘(swap*τ).symm  [simplification]
      rw [hPτ, iter_integral_swap_any ih' hab_τ hf_τ x y]
      -- Show bounds and function match
      have hbnd : ∀ (c : Fin (n + 1) → ℝ),
          c ∘ τ ∘ Equiv.swap x y = c ∘ (Equiv.swap x y * τ) :=
        fun c => funext fun i => by simp [Function.comp, Equiv.Perm.mul_apply]
      rw [hbnd a, hbnd b]
      congr 1; ext v; congr 1; ext i
      -- (fun j => v(swap.symm j))(τ.symm i) = v((swap*τ).symm i)
      -- LHS = v(swap.symm(τ.symm i)) = v(swap(τ.symm i))  [swap self-inverse]
      -- RHS = v((τ.symm * swap.symm) i) = v(swap.symm(τ.symm i)) [mul_inv_rev]
      simp [Equiv.swap_symm, mul_inv_rev, Equiv.Perm.mul_apply]

-- ═══════════════════════════════════════════════════
-- Section 8: Verified Special Cases (0 sorries)
-- ═══════════════════════════════════════════════════

/-- Full 2D order independence. Perm(Fin 2) = {id, swap 0 1}. -/
theorem order_independent_2d {a b : Fin 2 → ℝ}
    (hab : ∀ i, a i ≤ b i) {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f)
    (σ : Equiv.Perm (Fin 2)) :
    iteratedIntervalIntegral a b f =
    iteratedIntervalIntegral (a ∘ σ) (b ∘ σ) (fun x => f (fun i => x (σ.symm i))) :=
  iteratedIntervalIntegral_order_independent hab hf σ

/-- The 3D case, swap of first two positions. -/
theorem order_independent_3d_swap01 {a b : Fin 3 → ℝ}
    (hab : ∀ i, a i ≤ b i) {f : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) :
    iteratedIntervalIntegral a b f =
    iteratedIntervalIntegral (a ∘ Equiv.swap 0 1) (b ∘ Equiv.swap 0 1)
      (fun x => f (fun i => x ((Equiv.swap 0 1 : Equiv.Perm (Fin 3)).symm i))) :=
  iteratedIntervalIntegral_order_independent hab hf (Equiv.swap 0 1)

/-
## Research Outcome

**Proved** (0 sorries in these):
- `swap01_cons_eq`: Fin arithmetic for the swap computation
- `swap_outer_two`: Fubini swap of positions 0 and 1 (uses integrable_swap_pair)
- `iteratedIntervalIntegral_perm_tail`: Inner permutation reduction
- `iter_integral_swap_any`: Integral identity for any swap (uses perm_tail for x,y≠0;
  calls iter_integral_swap_zero for swap(0,k))
- `iteratedIntervalIntegral_order_independent`: Main theorem via swap_induction_on
  (uses iter_integral_swap_any for each transposition in the decomposition)

**Remaining sorries** (2 total):

1. `continuous_param` (succ step, h_bound): Compact bound for dominated convergence.
   Fix: Use hM (from IsCompact.bddAbove on compact K × uIcc) + hK_nhd filter_upwards
   to show ∀ᶠ x in 𝓝 x₀, ∀ᵐ t₀, ‖H(x,t₀)‖ ≤ M.
   Concretely: `filter_upwards [hK_nhd] with x hx; apply Filter.eventually_of_forall;
   intro t ht; exact hM (mem_image_of_mem _ (mk_mem_prod hx (uIoc_subset_uIcc ht)))`

2. `iter_integral_swap_zero` (succ step, m'+2 case): Decompose swap(0,k) into
   swap(k₀,k) * swap(0,k₀) * swap(k₀,k) using swap_mul_swap_mul_swap, then chain
   three applications of the integral identity. The algebraic bookkeeping requires
   careful type-checking of the composed permutations.

**Impact**: Main theorem structure is now complete via `swap_induction_on`. Eliminates
axiom once both remaining sorries are resolved.
-/

end GreensTheoremOQ01OQ01OQ01OQ01
