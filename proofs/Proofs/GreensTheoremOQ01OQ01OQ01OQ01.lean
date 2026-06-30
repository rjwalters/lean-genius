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

  ## Sorries: 0 (all resolved)
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
    exact hF.comp (continuous_id.prodMk continuous_const)
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
      have hpair : Continuous (fun q : (α × ℝ) × (Fin n → ℝ) =>
          ((q.1.1, Fin.cons q.1.2 q.2) : α × (Fin (n + 1) → ℝ))) := by
        refine Continuous.prodMk (continuous_fst.comp continuous_fst) ?_
        show Continuous (fun q : (α × ℝ) × (Fin n → ℝ) =>
            (Fin.cons q.1.2 q.2 : Fin (n + 1) → ℝ))
        exact Continuous.finCons (continuous_snd.comp continuous_fst) continuous_snd
      exact hF.comp hpair
    -- Now: Continuous (fun x => ∫ t₀ in a₀..b₀, H(x, t₀) dt₀)
    -- Use continuousAt_of_dominated_interval at each x₀
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨K, hK_compact, hK_nhd⟩ := exists_compact_mem_nhds x₀
    -- H is bounded on K × uIcc a₀ b₀ (compact set, image under continuous ‖H‖)
    obtain ⟨M, hM⟩ := ((hK_compact.prod isCompact_uIcc).image
      H_cont.norm).bddAbove
    apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M)
    · -- AEStronglyMeasurable (H(x, ·)) (vol.restrict Ι) eventually near x₀
      apply Filter.Eventually.of_forall; intro x
      exact (H_cont.comp (continuous_const.prodMk continuous_id)).measurable
          |>.aestronglyMeasurable
    · -- |H(x, t₀)| ≤ M for x near x₀ and t₀ ∈ Ι a₀ b₀
      -- Use compact K containing x₀ (from hK_nhd): H bounded on K × uIcc by hM
      filter_upwards [hK_nhd] with x hx
      apply Filter.Eventually.of_forall; intro t₀ ht₀
      apply hM
      exact Set.mem_image_of_mem _
        (Set.mk_mem_prod hx (Set.uIoc_subset_uIcc ht₀))
    · -- Bound is interval-integrable (constant function)
      exact intervalIntegral.intervalIntegrable_const
    · -- H(·, t₀) is continuous at x₀ for all t₀
      apply Filter.Eventually.of_forall; intro t₀ _
      exact (H_cont.comp (continuous_id.prodMk continuous_const)).continuousAt

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
        (F := fun q : (ℝ × ℝ) × (Fin n → ℝ) =>
          f (Fin.cons q.1.1 (Fin.cons q.1.2 q.2)))
    have hcons : Continuous (fun q : (ℝ × ℝ) × (Fin n → ℝ) =>
        (Fin.cons q.1.1 (Fin.cons q.1.2 q.2) : Fin (n + 2) → ℝ)) := by
      refine Continuous.finCons (continuous_fst.comp continuous_fst) ?_
      show Continuous (fun q : (ℝ × ℝ) × (Fin n → ℝ) =>
          (Fin.cons q.1.2 q.2 : Fin (n + 1) → ℝ))
      exact Continuous.finCons (continuous_snd.comp continuous_fst) continuous_snd
    exact hf.comp hcons
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
  rw [Measure.prod_restrict]
  exact hint_ioc

-- ═══════════════════════════════════════════════════
-- Section 2: Key Swap Computation
-- ═══════════════════════════════════════════════════

/-- For σ = swap 0 1 in Fin(n+2), applying σ permutes the first two positions. -/
private lemma swap01_cons_eq {n : ℕ} {f : (Fin (n + 2) → ℝ) → ℝ}
    (x₀ x₁ : ℝ) (rest : Fin n → ℝ) :
    let σ := Equiv.swap (0 : Fin (n + 2)) 1
    (fun x : Fin (n + 2) → ℝ => f (fun i => x (σ.symm i)))
        (Fin.cons x₁ (Fin.cons x₀ rest)) =
    f (Fin.cons x₀ (Fin.cons x₁ rest)) := by
  intro σ
  simp only [σ, Equiv.symm_swap]
  congr 1
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Equiv.swap_apply_left, Fin.cons_zero]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp [Equiv.swap_apply_right, Fin.cons_zero]
    · have hne0 : k.succ.succ ≠ (0 : Fin (n + 2)) := Fin.succ_ne_zero _
      have hne1 : k.succ.succ ≠ (1 : Fin (n + 2)) := by
        intro h; have hv := congr_arg Fin.val h; simp [Fin.val_succ] at hv
      simp [Equiv.swap_apply_of_ne_of_ne hne0 hne1, Fin.cons_succ]

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
    simp only [iteratedIntervalIntegral_succ, Fin.tail, Fin.succ_zero_eq_one]
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
    simp only [Fin.tail, Function.comp]
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
  -- Beta-reduced equation: rewriting inside the iterated integral.
  have hfun : ∀ x' : Fin n → ℝ,
      f (fun i => (Fin.cons x₀ x' : Fin (n + 1) → ℝ) (σ.symm i)) =
      f (Fin.cons x₀ (fun i => x' (σ'.symm i))) := by
    intro x'
    congr 1; ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hσ_symm_0, Fin.cons_zero]
    · simp [hsucc_symm j, Fin.cons_succ]
  rw [htail_a, htail_b]
  simp_rw [hfun]
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
    simp [Equiv.swap_self]
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
      -- Now n+1 = n'+2, and the lemma swap_outer_two applies directly
      -- (⟨0+1, _⟩ : Fin (n'+2)) is definitionally 1.
      simp only
      exact swap_outer_two hab hf
    | m' + 1 =>
      -- k = ⟨m'+2, hm⟩, k₀ = ⟨m'+1, hm0⟩
      have hm0 : m' + 1 < n + 1 := Nat.lt_of_succ_lt hm
      let k₀ : Fin (n + 1) := ⟨m' + 1, hm0⟩
      let k  : Fin (n + 1) := ⟨m' + 2, hm⟩
      -- Distinctness
      have hk₀_ne_0 : k₀ ≠ (0 : Fin (n + 1)) := by simp [k₀, Fin.ext_iff]
      have hk_ne_0  : k  ≠ (0 : Fin (n + 1)) := by simp [k, Fin.ext_iff]
      have hk₀_ne_k : k₀ ≠ k := by simp [k₀, k, Fin.ext_iff]
      -- Pointwise identity: conjugating swap(k₀,k) by swap(0,k₀) yields swap(0,k).
      -- Proven via Equiv.swap_apply_apply (swap conjugation lemma).
      have h_sk0 : Equiv.swap 0 k₀ k₀ = (0 : Fin (n + 1)) :=
        Equiv.swap_apply_right 0 k₀
      have h_sk : Equiv.swap 0 k₀ k = k :=
        Equiv.swap_apply_of_ne_of_ne hk_ne_0 (Ne.symm hk₀_ne_k)
      have heq : Equiv.swap (0 : Fin (n + 1)) k =
          Equiv.swap 0 k₀ * Equiv.swap k₀ k * Equiv.swap 0 k₀ := by
        conv_lhs => rw [show (0 : Fin (n + 1)) = Equiv.swap 0 k₀ k₀ from h_sk0.symm,
                        show k = Equiv.swap 0 k₀ k from h_sk.symm,
                        Equiv.swap_apply_apply, Equiv.swap_inv]
      have hcomp : ∀ i : Fin (n + 1),
          Equiv.swap 0 k₀ (Equiv.swap k₀ k (Equiv.swap 0 k₀ i)) = Equiv.swap 0 k i := by
        intro i
        have := congr_fun (congr_arg DFunLike.coe heq.symm) i
        simpa [Equiv.Perm.mul_apply] using this
      -- Step 1: apply IH for k₀
      have step1 := ihm hm0 hab hf
      -- Step 2: apply perm_tail for swap(k₀,k) (fixes 0)
      have hfixes0 : Equiv.swap k₀ k (0 : Fin (n+1)) = 0 :=
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hk₀_ne_0) (Ne.symm hk_ne_0)
      have hab₁ : ∀ i, (a ∘ Equiv.swap 0 k₀) i ≤ (b ∘ Equiv.swap 0 k₀) i :=
        fun i => hab _
      have hf₁ : Continuous (fun v : Fin (n+1) → ℝ =>
            f (fun i => v ((Equiv.swap 0 k₀).symm i))) :=
        hf.comp (continuous_pi_iff.mpr fun i => continuous_apply _)
      have step2 :=
        iteratedIntervalIntegral_perm_tail hab₁ hf₁ (Equiv.swap k₀ k) hfixes0 ih_perm
      -- Step 3: apply IH for k₀ again on the new bounds
      have hab₂ : ∀ i, (a ∘ Equiv.swap 0 k₀ ∘ Equiv.swap k₀ k) i ≤
                       (b ∘ Equiv.swap 0 k₀ ∘ Equiv.swap k₀ k) i :=
        fun i => hab _
      have hf₂ : Continuous (fun v : Fin (n+1) → ℝ =>
            f (fun i => v ((Equiv.swap k₀ k).symm ((Equiv.swap 0 k₀).symm i)))) :=
        hf.comp (continuous_pi_iff.mpr fun i => continuous_apply _)
      have step3 := ihm hm0 hab₂ hf₂
      -- Chain the three steps into one equality
      have chain : iteratedIntervalIntegral a b f =
          iteratedIntervalIntegral
            (a ∘ Equiv.swap 0 k₀ ∘ Equiv.swap k₀ k ∘ Equiv.swap 0 k₀)
            (b ∘ Equiv.swap 0 k₀ ∘ Equiv.swap k₀ k ∘ Equiv.swap 0 k₀)
            (fun v => f (fun i => v ((Equiv.swap 0 k₀).symm
                ((Equiv.swap k₀ k).symm ((Equiv.swap 0 k₀).symm i))))) :=
        step1.trans (step2.trans step3)
      -- Rewrite using hcomp: the composition equals swap(0,k)
      have ha_eq : a ∘ Equiv.swap 0 k₀ ∘ Equiv.swap k₀ k ∘ Equiv.swap 0 k₀ =
                   a ∘ Equiv.swap 0 k :=
        funext fun i => congr_arg a (hcomp i)
      have hb_eq : b ∘ Equiv.swap 0 k₀ ∘ Equiv.swap k₀ k ∘ Equiv.swap 0 k₀ =
                   b ∘ Equiv.swap 0 k :=
        funext fun i => congr_arg b (hcomp i)
      have hf_eq : (fun v : Fin (n+1) → ℝ =>
              f (fun i => v ((Equiv.swap 0 k₀).symm
                  ((Equiv.swap k₀ k).symm ((Equiv.swap 0 k₀).symm i))))) =
            fun v => f (fun i => v ((Equiv.swap 0 k).symm i)) := by
        ext v; congr 1; ext i
        simp only [Equiv.symm_swap]
        exact congr_arg v (hcomp i)
      rw [chain, ha_eq, hb_eq, hf_eq]

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
  rcases eq_or_ne x y with rfl | hxy
  · simp [Equiv.swap_self]
  · -- Case: x ≠ y
    rcases eq_or_ne x 0 with rfl | hx0
    · -- x = 0: use iter_integral_swap_zero
      exact iter_integral_swap_zero ih y.val y.isLt hab hf
    · rcases eq_or_ne y 0 with rfl | hy0
      · -- y = 0: swap(x, 0) = swap(0, x) by swap_comm
        rw [Equiv.swap_comm x 0]
        exact iter_integral_swap_zero ih x.val x.isLt hab hf
      · -- x ≠ 0, y ≠ 0: swap(x,y) fixes 0, use perm_tail
        have hfixes0 : (Equiv.swap x y) 0 = 0 := by
          rw [Equiv.swap_apply_of_ne_of_ne hx0.symm hy0.symm]
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
    subst this; simp [iteratedIntervalIntegral]
  | succ n ih =>
    have ih' : ∀ (a' b' : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ),
        Continuous g → (∀ i, a' i ≤ b' i) →
        ∀ τ : Equiv.Perm (Fin n),
        iteratedIntervalIntegral a' b' g =
        iteratedIntervalIntegral (a' ∘ τ) (b' ∘ τ) (fun x => g (fun i => x (τ.symm i))) :=
      fun a' b' g hg hab' τ => ih hab' hg τ
    -- Prove by swap induction on σ.
    -- P(σ) = ∀ a b hab f hf, integral a b f = integral (a∘σ) (b∘σ) (f∘σ.symm)
    -- We use swap_induction_on' (right-multiplication form): reduces to P(1) and
    -- P(τ * swap(x,y)) from P(τ). This matches the convention `(σ * τ) i = σ (τ i)`
    -- so that `a ∘ (τ * swap) = (a ∘ τ) ∘ swap` pointwise.
    induction σ using Equiv.Perm.swap_induction_on' with
    | one =>
      simp
    | mul_swap τ x y hxy hPτ =>
      -- hPτ : integral a b f = integral (a∘τ) (b∘τ) (fun v => f(v∘τ.symm))
      -- Goal: integral a b f = integral (a∘(τ*swap)) (b∘(τ*swap)) (fun v => f(v∘(τ*swap).symm))
      have hab_τ : ∀ i, (a ∘ τ) i ≤ (b ∘ τ) i := fun i => hab _
      have hf_τ : Continuous (fun v : Fin (n + 1) → ℝ => f (fun i => v (τ.symm i))) :=
        hf.comp (continuous_pi_iff.mpr fun i => continuous_apply (τ.symm i))
      -- Chain: a b f = a∘τ b∘τ f∘τ.symm  [hPτ]
      --            = (a∘τ)∘swap (b∘τ)∘swap (f∘τ.symm)∘swap.symm  [iter_integral_swap_any]
      --            = a∘(τ*swap) b∘(τ*swap) f∘(τ*swap).symm  [(τ*swap)(i) = τ(swap i)]
      rw [hPτ, iter_integral_swap_any ih' hab_τ hf_τ x y]
      -- Show bounds and function match
      have hbnd : ∀ (c : Fin (n + 1) → ℝ),
          (c ∘ τ) ∘ Equiv.swap x y = c ∘ (τ * Equiv.swap x y) :=
        fun _ => rfl
      rw [hbnd a, hbnd b]
      -- After the bound rewrites, the function parts coincide via congr.
      -- LHS fn at v, i: v(swap.symm(τ.symm i)) = v(swap(τ.symm i))  [swap self-inverse]
      -- RHS fn at v, i: v((τ*swap).symm i) = v(swap(τ.symm i))      [mul_inv_rev]
      congr 1

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

**Remaining sorries**: 0. Both sorries noted in earlier drafts are now discharged:

1. `continuous_param` (succ step, h_bound): Compact bound for dominated convergence,
   closed via `IsCompact.bddAbove` on the compact `K × uIcc` together with a
   `hK_nhd` `filter_upwards` giving `∀ᶠ x in 𝓝 x₀, ∀ᵐ t₀, ‖H(x,t₀)‖ ≤ M`.

2. `iter_integral_swap_zero` (succ step, m'+2 case): closed by decomposing
   `swap(0,k)` into `swap(k₀,k) * swap(0,k₀) * swap(k₀,k)` via `swap_mul_swap_mul_swap`
   and chaining three applications of the integral identity.

**Impact**: `iteratedIntervalIntegral_order_independent` is a real, sorry-free theorem
via `swap_induction_on`. The `iteratedIntervalIntegral_order_independent` *axiom* that
earlier drafts of the parent module `Proofs.GreensTheoremOQ01OQ01OQ01` used to defer the
inductive proof has been removed there (it was unused locally once this real proof
existed downstream), so the parent's `axiomCount` is 0. This resolves the open question
`greens-theorem-oq-01-oq-01-oq-01-oq-01-oq-01` (axiom elimination).
-/

end GreensTheoremOQ01OQ01OQ01OQ01
