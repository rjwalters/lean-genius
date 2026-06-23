/-
Erdős Problem #278 — Maximum Covering Density of Congruence Systems

Given a finite set of moduli A = {n₁ < n₂ < ⋯ < nᵣ}, choose residues
a₁, ..., aᵣ. The "coverage" is the set of integers m such that
m ≡ aᵢ (mod nᵢ) for some i.

Questions:
1. What is the maximum density of the coverage over all choices of residues?
2. Is the minimum density achieved when all aᵢ are equal?

Status: Partially solved.
Simpson (1986) settled Question 2 affirmatively: minimum density is achieved
when all residues are equal, giving density
  Σ 1/nᵢ - Σ 1/lcm(nᵢ,nⱼ) + Σ 1/lcm(nᵢ,nⱼ,nₖ) - ⋯
(inclusion-exclusion). Question 1 (maximum density) remains OPEN.

Reference: https://erdosproblems.com/278
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- ## Core Definitions

/-- A congruence system: a finite collection of moduli with chosen residues. -/
structure CongruenceSystem where
  moduli : Finset ℕ
  residue : ℕ → ℕ
  moduli_pos : ∀ n ∈ moduli, 0 < n

/-- An integer m is covered by the system if m ≡ a_i (mod n_i) for some i. -/
def isCovered (sys : CongruenceSystem) (m : ℕ) : Prop :=
  ∃ n ∈ sys.moduli, m % n = sys.residue n % n

/-- The LCM period of a congruence system. -/
noncomputable def systemLCM (sys : CongruenceSystem) : ℕ :=
  sys.moduli.val.toList.foldl Nat.lcm 1

/-- The coverage density: the proportion of {0,...,L-1} covered.
    For periodic systems this stabilizes at the lcm of the moduli. -/
noncomputable def coverageDensity (sys : CongruenceSystem) : ℝ :=
  let L := systemLCM sys
  ((Finset.range L).filter (fun m => ∃ n ∈ sys.moduli, m % n = sys.residue n % n)).card / (L : ℝ)

/-- The maximum coverage density over all residue choices. -/
noncomputable def maxCoverageDensity (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) : ℝ :=
  sSup { d : ℝ | ∃ r : ℕ → ℕ, d = coverageDensity ⟨moduli, r, hpos⟩ }

/-- The minimum coverage density over all residue choices. -/
noncomputable def minCoverageDensity (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) : ℝ :=
  sInf { d : ℝ | ∃ r : ℕ → ℕ, d = coverageDensity ⟨moduli, r, hpos⟩ }

-- ## Helper Lemmas

/-- foldl Nat.lcm preserves positivity when all elements are positive. -/
private lemma foldl_lcm_pos (init : ℕ) (hinit : 0 < init)
    (l : List ℕ) (hl : ∀ x ∈ l, 0 < x) : 0 < List.foldl Nat.lcm init l := by
  induction l generalizing init with
  | nil => simpa
  | cons a t ih =>
    simp only [List.foldl_cons]
    apply ih
    · have ha : 0 < a := hl a (by simp)
      exact Nat.pos_of_ne_zero (by
        intro h
        have := Nat.lcm_eq_zero_iff.mp h
        omega)
    · intro x hx; exact hl x (by simp [hx])

/-- The init divides the foldl lcm result. -/
private lemma init_dvd_foldl_lcm (init : ℕ) (l : List ℕ) :
    init ∣ List.foldl Nat.lcm init l := by
  induction l generalizing init with
  | nil => exact dvd_refl _
  | cons x t ih =>
    simp only [List.foldl_cons]
    exact dvd_trans (Nat.dvd_lcm_left init x) (ih _)

/-- Each element of a list divides the foldl lcm. -/
private lemma mem_dvd_foldl_lcm {a : ℕ} {l : List ℕ} (ha : a ∈ l) (init : ℕ) :
    a ∣ List.foldl Nat.lcm init l := by
  induction l generalizing init with
  | nil => simp at ha
  | cons x t ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact dvd_trans (Nat.dvd_lcm_right init a) (init_dvd_foldl_lcm _ _)
    · exact ih hmem _

/-- Each modulus divides the system LCM. -/
lemma dvd_systemLCM (sys : CongruenceSystem) (n : ℕ) (hn : n ∈ sys.moduli) :
    n ∣ systemLCM sys := by
  unfold systemLCM
  exact mem_dvd_foldl_lcm (Multiset.mem_toList.mpr (Finset.mem_def.mpr hn)) 1

/-- Unfolding coverageDensity without the let binding. -/
private lemma coverageDensity_eq (sys : CongruenceSystem) :
    coverageDensity sys =
      ((Finset.range (systemLCM sys)).filter
        (fun m => ∃ n ∈ sys.moduli, m % n = sys.residue n % n)).card /
      (systemLCM sys : ℝ) := rfl

/-- The LCM period is always positive. -/
lemma systemLCM_pos (sys : CongruenceSystem) : 0 < systemLCM sys := by
  unfold systemLCM
  apply foldl_lcm_pos 1 (by omega)
  intro x hx
  rw [Multiset.mem_toList] at hx
  exact sys.moduli_pos x (Finset.mem_def.mpr hx)

/-- Coverage count is at most the LCM period. -/
private lemma coverage_card_le_lcm (sys : CongruenceSystem) :
    ((Finset.range (systemLCM sys)).filter
      (fun m => ∃ n ∈ sys.moduli, m % n = sys.residue n % n)).card ≤ systemLCM sys := by
  calc ((Finset.range (systemLCM sys)).filter _).card
      ≤ (Finset.range (systemLCM sys)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = systemLCM sys := Finset.card_range _

-- ## Proved Bounds

/-- The coverage density is non-negative. -/
theorem density_nonneg (sys : CongruenceSystem) : 0 ≤ coverageDensity sys := by
  unfold coverageDensity
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

/-- The coverage density is at most 1. -/
theorem density_le_one (sys : CongruenceSystem) : coverageDensity sys ≤ 1 := by
  unfold coverageDensity
  have hL : (0 : ℝ) < systemLCM sys := Nat.cast_pos.mpr (systemLCM_pos sys)
  rw [div_le_one hL]
  exact Nat.cast_le.mpr (coverage_card_le_lcm sys)

/-- The coverage density is between 0 and 1. -/
theorem density_bounds (sys : CongruenceSystem) :
    0 ≤ coverageDensity sys ∧ coverageDensity sys ≤ 1 :=
  ⟨density_nonneg sys, density_le_one sys⟩

-- ## Density Formulas

/-- The inclusion-exclusion density for pairwise coprime moduli:
    1 - ∏ᵢ(1 - 1/nᵢ) = Σ 1/nᵢ - Σ 1/(nᵢnⱼ) + ⋯
    For coprime moduli, this is the exact density for ALL residue choices (by CRT). -/
noncomputable def coprimeDensity (moduli : Finset ℕ) : ℝ :=
  1 - moduli.prod (fun n => 1 - 1 / (n : ℝ))

/-- The first-order approximation Σ 1/nᵢ (upper bound on density for coprime moduli). -/
noncomputable def sumReciprocalDensity (moduli : Finset ℕ) : ℝ :=
  moduli.sum (fun n => (1 : ℝ) / n)

-- ## Coprime LCM = Product

/-- For pairwise coprime elements, foldl Nat.lcm = foldl (· * ·). -/
private lemma foldl_lcm_eq_foldl_mul (l : List ℕ) (acc : ℕ)
    (hcop_acc : ∀ x ∈ l, Nat.Coprime acc x)
    (hcop_pairs : l.Pairwise Nat.Coprime) :
    l.foldl Nat.lcm acc = l.foldl (· * ·) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hpw := List.pairwise_cons.mp hcop_pairs
    have ha_cop : Nat.Coprime acc a := hcop_acc a (by simp)
    rw [Nat.Coprime.lcm_eq_mul ha_cop]
    exact ih (acc * a)
      (fun x hx => Nat.Coprime.mul_left
        (hcop_acc x (by simp [hx]))
        (hpw.1 x hx))
      hpw.2

/-- For pairwise coprime moduli, the system LCM equals the product of moduli. -/
lemma systemLCM_coprime_eq_prod (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n)
    (hcop : ∀ m ∈ moduli, ∀ n ∈ moduli, m ≠ n → Nat.Coprime m n) (r : ℕ → ℕ) :
    systemLCM ⟨moduli, r, hpos⟩ = moduli.prod id := by
  unfold systemLCM
  set l := moduli.val.toList with hl_def
  -- Convert pairwise coprime from Finset to List
  have hnd : l.Nodup := by
    simp only [hl_def, ← Multiset.coe_nodup, Multiset.coe_toList]; exact moduli.nodup
  have hpw : l.Pairwise Nat.Coprime :=
    hnd.imp_of_mem fun {a} {b} ha hb hne => by
      rw [hl_def] at ha hb
      exact hcop a (Finset.mem_def.mpr (Multiset.mem_toList.mp ha))
                   b (Finset.mem_def.mpr (Multiset.mem_toList.mp hb)) hne
  rw [foldl_lcm_eq_foldl_mul l 1 (fun x _ => Nat.coprime_one_left x) hpw]
  -- Relate List.foldl (· * ·) 1 to Finset.prod
  rw [← List.prod_eq_foldl]
  -- l.prod = moduli.val.prod = moduli.prod id
  change l.prod = moduli.prod id
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id, hl_def]
  exact Multiset.prod_toList moduli.val

-- ## CRT Complement Counting (for proving coprime_density_formula)

/-- If n ∣ L, then (j + k*L) % n = j % n. -/
private lemma mod_add_mul_dvd (j k n L : ℕ) (h : n ∣ L) : (j + k * L) % n = j % n := by
  obtain ⟨q, rfl⟩ := h
  rw [show k * (n * q) = n * (q * k) from by ring]
  exact Nat.add_mul_mod_self_left j n (q * k)

/-- For coprime L and n, residue shift is injective on {0,...,n-1}. -/
private lemma coprime_shift_injective {n L : ℕ} (hn : 0 < n) (hcop : Nat.Coprime L n)
    {j k₁ k₂ : ℕ} (hk₁ : k₁ < n) (hk₂ : k₂ < n)
    (heq : (j + k₁ * L) % n = (j + k₂ * L) % n) : k₁ = k₂ := by
  by_contra hne
  wlog hle : k₁ ≤ k₂ with H
  · exact H hn hcop hk₂ hk₁ heq.symm (Ne.symm hne) (le_of_not_le hle)
  have hlt : k₁ < k₂ := lt_of_le_of_ne hle hne
  have h1 : j + k₁ * L ≤ j + k₂ * L :=
    Nat.add_le_add_left (Nat.mul_le_mul_right L hle) j
  have h2 : j + k₂ * L - (j + k₁ * L) = (k₂ - k₁) * L := by
    have hkL : k₁ * L ≤ k₂ * L := Nat.mul_le_mul_right L hle
    rw [Nat.sub_mul]
    omega
  have hdvd := (Nat.modEq_iff_dvd' h1).mp heq
  rw [h2] at hdvd
  exact absurd (Nat.le_of_dvd (by omega) (hcop.symm.dvd_of_dvd_mul_right hdvd)) (by omega)

/-- For coprime L and n, residues {(j+kL) % n : k < n} cover all of {0,...,n-1}. -/
private lemma coprime_residues_complete {n L : ℕ} (hn : 0 < n) (hcop : Nat.Coprime L n) (j : ℕ) :
    (Finset.range n).image (fun k => (j + k * L) % n) = Finset.range n :=
  Finset.eq_of_subset_of_card_le
    (fun _ hx => Finset.mem_range.mpr (by
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx; exact Nat.mod_lt _ hn))
    (by rw [Finset.card_range]
        have hinj : Set.InjOn (fun k => (j + k * L) % n) ↑(Finset.range n) :=
          fun _ hk₁ _ hk₂ heq =>
            coprime_shift_injective hn hcop (Finset.mem_range.mp (Finset.mem_coe.mp hk₁))
              (Finset.mem_range.mp (Finset.mem_coe.mp hk₂)) heq
        rw [Finset.card_image_of_injOn hinj, Finset.card_range])

/-- Among k < n, exactly (n-1) give (j+kL) % n ≠ t (for coprime L, n). -/
private lemma coprime_avoid_count {n L : ℕ} (hn : 0 < n) (hcop : Nat.Coprime L n)
    {j t : ℕ} (ht : t < n) :
    ((Finset.range n).filter (fun k => (j + k * L) % n ≠ t)).card = n - 1 := by
  have hmem : t ∈ (Finset.range n).image (fun k => (j + k * L) % n) := by
    rw [coprime_residues_complete hn hcop j]; exact Finset.mem_range.mpr ht
  obtain ⟨k₀, hk₀, hmod₀⟩ := Finset.mem_image.mp hmem
  have hhit : (Finset.range n).filter (fun k => (j + k * L) % n = t) = {k₀} :=
    Finset.ext fun k => ⟨
      fun h => by
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton] at h ⊢
        exact coprime_shift_injective hn hcop h.1 (Finset.mem_range.mp hk₀) (by rw [h.2, hmod₀]),
      fun h => by rw [Finset.mem_singleton.mp h]; exact Finset.mem_filter.mpr ⟨hk₀, hmod₀⟩⟩
  have : (Finset.range n).filter (fun k => (j + k * L) % n ≠ t) =
      Finset.range n \ (Finset.range n).filter (fun k => (j + k * L) % n = t) :=
    Finset.ext fun k => by
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range]
      constructor
      · intro ⟨hk, hne⟩; exact ⟨hk, fun ⟨_, heq⟩ => hne heq⟩
      · intro ⟨hk, h⟩; exact ⟨hk, fun heq => h ⟨hk, heq⟩⟩
  rw [this, hhit]
  have hk₀_mem : k₀ ∈ Finset.range n := hk₀
  rw [show Finset.range n \ ({k₀} : Finset ℕ) = (Finset.range n).erase k₀ from
      (Finset.erase_eq (Finset.range n) k₀).symm,
    Finset.card_erase_of_mem hk₀_mem, Finset.card_range]

/-- The complement count for coprime moduli equals ∏(nᵢ - 1) (CRT argument by Finset induction). -/
private lemma complement_eq_prod (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n)
    (hcop : ∀ m ∈ moduli, ∀ n ∈ moduli, m ≠ n → Nat.Coprime m n)
    (r : ℕ → ℕ) :
    ((Finset.range (moduli.prod id)).filter
      (fun m => ∀ n ∈ moduli, m % n ≠ r n % n)).card =
    moduli.prod (fun n => n - 1) := by
  revert hpos hcop
  refine Finset.induction_on moduli ?_ ?_
  · intro _ _; simp [Finset.filter_true_of_mem]
  · intro a S haS ih hpos hcop
    have hpos_S : ∀ n ∈ S, 0 < n := fun n hn => hpos n (Finset.mem_insert_of_mem hn)
    have hcop_S : ∀ m ∈ S, ∀ n ∈ S, m ≠ n → Nat.Coprime m n :=
      fun m hm n hn hmn => hcop m (Finset.mem_insert_of_mem hm) n (Finset.mem_insert_of_mem hn) hmn
    have ha_pos : 0 < a := hpos a (Finset.mem_insert_self a S)
    have hcop_aS : ∀ n ∈ S, Nat.Coprime a n := fun n hn =>
      hcop a (Finset.mem_insert_self a S) n (Finset.mem_insert_of_mem hn)
        (fun h => haS (h ▸ hn))
    specialize ih hpos_S hcop_S
    set L := S.prod id with hL_def
    have hL_pos : 0 < L := Finset.prod_pos (fun n hn => hpos_S n hn)
    set t := r a % a
    -- Rewrite products for insert
    have hprod_id : (insert a S).prod id = a * L := by
      rw [Finset.prod_insert haS]; simp [hL_def]
    rw [hprod_id, Finset.prod_insert haS, ← ih]
    -- Split filter condition: ∀n∈insert a S ↔ (m%a ≠ t) ∧ (∀n∈S, ...)
    have hfilter_eq : (Finset.range (a * L)).filter
        (fun m => ∀ n ∈ insert a S, m % n ≠ r n % n) =
        (Finset.range (a * L)).filter
        (fun m => m % a ≠ t ∧ ∀ n ∈ S, m % n ≠ r n % n) := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · intro ⟨hm, h⟩; exact ⟨hm, h a (Or.inl rfl), fun n hn => h n (Or.inr hn)⟩
      · intro ⟨hm, ha_c, hS_c⟩; exact ⟨hm, fun n hn => hn.elim (· ▸ ha_c) (hS_c n)⟩
    rw [hfilter_eq]
    -- Define complement_S and fiber function
    set compS := (Finset.range L).filter (fun j => ∀ n ∈ S, j % n ≠ r n % n)
    set fib := fun (j : ℕ) =>
      ((Finset.range a).filter (fun k => (j + k * L) % a ≠ t)).image (fun k => j + k * L)
    -- Show the complement equals biUnion of fibers
    have hbi : (Finset.range (a * L)).filter
        (fun m => m % a ≠ t ∧ ∀ n ∈ S, m % n ≠ r n % n) = compS.biUnion fib := by
      ext m; constructor
      · intro hm
        have ⟨hm_r, hm_a, hm_S⟩ := Finset.mem_filter.mp hm
        refine Finset.mem_biUnion.mpr ⟨m % L, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.mod_lt m hL_pos), fun n hn => by
            have hndvd : n ∣ L := Finset.dvd_prod_of_mem id hn
            have hmodL : m % L % n = m % n := by
              have heq1 : (m % L + m / L * L) % n = m % L % n :=
                mod_add_mul_dvd (m % L) (m / L) n L hndvd
              have heq2 : m % L + m / L * L = m := by
                linarith [Nat.div_add_mod m L, mul_comm L (m / L)]
              rw [heq2] at heq1; exact heq1.symm
            rw [hmodL]; exact hm_S n hn⟩,
          Finset.mem_image.mpr ⟨m / L, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact Finset.mem_range.mp hm_r)),
             by have hmod_eq : m % L + m / L * L = m := by
                  linarith [Nat.div_add_mod m L, mul_comm L (m / L)]
                rw [hmod_eq]; exact hm_a⟩,
            by linarith [Nat.div_add_mod m L, mul_comm L (m / L)]⟩⟩
      · intro hm
        obtain ⟨j, hj, hm_fib⟩ := Finset.mem_biUnion.mp hm
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm_fib
        have hj_d := Finset.mem_filter.mp hj
        have hk_d := Finset.mem_filter.mp hk
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
          have hj_lt : j < L := Finset.mem_range.mp hj_d.1
          have hk_lt : k < a := Finset.mem_range.mp hk_d.1
          have hkL : k * L ≤ (a - 1) * L :=
            Nat.mul_le_mul_right L (by omega)
          have hcalc : L + (a - 1) * L = a * L := by
            have : a - 1 + 1 = a := Nat.succ_pred_eq_of_pos ha_pos
            nlinarith
          calc j + k * L < L + (a - 1) * L := by omega
            _ = a * L := hcalc),
          hk_d.2, fun n hn => by
            rw [mod_add_mul_dvd j k n L (Finset.dvd_prod_of_mem id hn)]; exact hj_d.2 n hn⟩
    rw [hbi]
    -- Fibers are pairwise disjoint (different j → different m%L)
    have hdisj : Set.PairwiseDisjoint (↑compS : Set ℕ) fib := by
      intro j₁ hj₁ j₂ hj₂ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro m hm₁ hm₂
      obtain ⟨k₁, _, rfl⟩ := Finset.mem_image.mp hm₁
      obtain ⟨k₂, _, heq⟩ := Finset.mem_image.mp hm₂
      apply hne
      have h1 : j₁ < L := Finset.mem_range.mp (Finset.mem_filter.mp hj₁).1
      have h2 : j₂ < L := Finset.mem_range.mp (Finset.mem_filter.mp hj₂).1
      have h3 : (j₁ + k₁ * L) % L = j₁ := by
        rw [show j₁ + k₁ * L = j₁ + L * k₁ from by ring, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt h1]
      have h4 : (j₂ + k₂ * L) % L = j₂ := by
        rw [show j₂ + k₂ * L = j₂ + L * k₂ from by ring, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt h2]
      calc j₁ = (j₁ + k₁ * L) % L := h3.symm
        _ = (j₂ + k₂ * L) % L := by rw [heq]
        _ = j₂ := h4
    rw [Finset.card_biUnion hdisj]
    -- L is coprime to a (product of coprime elements)
    have hcop_La : Nat.Coprime L a := by
      rw [hL_def]; exact Nat.coprime_prod_left_iff.mpr (fun n hn => (hcop_aS n hn).symm)
    -- Each fiber has cardinality a - 1
    have hfib_card : ∀ j ∈ compS, (fib j).card = a - 1 := fun j _ => by
      rw [Finset.card_image_of_injOn (fun k₁ _ k₂ _ (heq : j + k₁ * L = j + k₂ * L) =>
        Nat.eq_of_mul_eq_mul_right hL_pos (by linarith))]
      exact coprime_avoid_count ha_pos hcop_La (Nat.mod_lt (r a) ha_pos)
    -- Sum of constant (a-1) over compS = (a-1) * compS.card
    rw [Finset.sum_congr rfl hfib_card, Finset.sum_const, smul_eq_mul, mul_comm]

/-- Product fraction identity: ∏((n-1)/n) = ∏(n-1) / ∏n in ℝ, for positive naturals. -/
private lemma prod_sub_one_div (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) :
    (↑(moduli.prod (fun n => n - 1)) : ℝ) / ↑(moduli.prod id) =
    moduli.prod (fun n => 1 - 1 / (↑n : ℝ)) := by
  revert hpos
  refine Finset.induction_on moduli ?_ ?_
  · intro _; simp
  · intro a S haS ih hpos
    have hpos_S : ∀ n ∈ S, 0 < n := fun n hn => hpos n (Finset.mem_insert_of_mem hn)
    have ha_pos : 0 < a := hpos a (Finset.mem_insert_self a S)
    have ha_ne : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hL_ne : (↑(S.prod id) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by
      exact Nat.pos_iff_ne_zero.mp (Finset.prod_pos (fun n hn => hpos_S n hn)))
    rw [Finset.prod_insert haS, Finset.prod_insert haS, Finset.prod_insert haS]
    conv_lhs => rw [show (id a : ℕ) = a from rfl]
    rw [← ih hpos_S, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ a)]
    field_simp
    ring

-- ## Simpson's Theorem (1986)

-- Simpson's theorem (1986): the minimum coverage density is achieved when
-- all residues are equal. Deep combinatorial result.
-- Not axiomatized since it is not used by any theorem in this file.

/-- Helper: (x % n + y) % n = (x + y) % n -/
private lemma mod_add_right (x y n : ℕ) : (x % n + y) % n = (x + y) % n := by
  conv_lhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl n), ← Nat.add_mod]

/-- If a ≡ b (mod k) and b ≤ a, then k | (a - b). -/
private lemma dvd_sub_of_mod_eq {a b k : ℕ} (h : a % k = b % k) (hab : b ≤ a) :
    k ∣ (a - b) :=
  (Nat.modEq_iff_dvd' hab).mp h.symm

/-- The coverage filter for constant residue a has the same cardinality as for
    constant residue 0, via the cyclic shift bijection on {0,...,L-1}.
    Since n∣L for each modulus n, the shift preserves residue classes. -/
private lemma coverage_card_shift (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) (a : ℕ) :
    let L := systemLCM ⟨moduli, fun _ => a, hpos⟩
    ((Finset.range L).filter (fun m => ∃ n ∈ moduli, m % n = a % n)).card =
    ((Finset.range L).filter (fun m => ∃ n ∈ moduli, m % n = 0)).card := by
  intro L
  have hLpos : 0 < L := systemLCM_pos ⟨moduli, fun _ => a, hpos⟩
  have hb : a % L < L := Nat.mod_lt a hLpos
  have hdvd : ∀ n ∈ moduli, n ∣ L := fun n hn =>
    dvd_systemLCM ⟨moduli, fun _ => a, hpos⟩ n hn
  -- Bijection: "≡a" → "divisible" via m ↦ (m+L-a%L)%L, inverse: m ↦ (m+a)%L
  apply Finset.card_bij' (fun m _ => (m + L - a % L) % L) (fun m _ => (m + a) % L)
  -- Forward (hi): maps "≡a" filter → "divisible" filter
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
    refine ⟨Nat.mod_lt _ hLpos, ?_⟩
    obtain ⟨_, k, hk, hmod⟩ := hm
    have hkL := hdvd k hk
    refine ⟨k, hk, ?_⟩
    -- Show: ((m+L-a%L)%L) % k = 0
    rw [Nat.mod_mod_of_dvd _ hkL]
    -- Goal: (m + L - a%L) % k = 0
    have hLk : L % k = 0 := by obtain ⟨q, hq⟩ := hkL; rw [hq]; exact Nat.mul_mod_right k q
    have haLk : (a % L) % k = a % k := Nat.mod_mod_of_dvd a hkL
    have hk_pos := hpos k hk
    have hmL_mod : (m + L) % k = (a % L) % k := by
      rw [Nat.add_mod, hLk, Nat.add_zero, hmod, haLk,
          Nat.mod_eq_of_lt (Nat.mod_lt a hk_pos)]
    have hdvd_sub := dvd_sub_of_mod_eq hmL_mod (by omega : a % L ≤ m + L)
    rwa [Nat.dvd_iff_mod_eq_zero] at hdvd_sub
  -- Backward (hj): maps "divisible" filter → "≡a" filter
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
    refine ⟨Nat.mod_lt _ hLpos, ?_⟩
    obtain ⟨_, k, hk, hmod⟩ := hm
    exact ⟨k, hk, by
      rw [Nat.mod_mod_of_dvd _ (hdvd k hk), Nat.add_mod, hmod, Nat.zero_add,
          Nat.mod_mod_of_dvd _ (dvd_refl k)]⟩
  -- Round-trip: backward ∘ forward = id (left_inv)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    -- ((m + L - a%L) % L + a) % L = m
    rw [mod_add_right]
    -- (m + L - a%L + a) % L = m
    have hstep : m + L - a % L + a = m + (L + L * (a / L)) := by
      have := Nat.div_add_mod a L; omega
    have hfactor : L + L * (a / L) = L * (a / L + 1) := by ring
    rw [hstep, hfactor, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm.1]
  -- Round-trip: forward ∘ backward = id (right_inv)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    -- ((m + a) % L + L - a%L) % L = m
    have hassoc : (m + a) % L + L - a % L = (m + a) % L + (L - a % L) := by
      have : a % L ≤ (m + a) % L + L := by omega
      omega
    rw [hassoc, mod_add_right]
    -- (m + a + (L - a%L)) % L = m
    have hstep : m + a + (L - a % L) = m + (L + L * (a / L)) := by
      have := Nat.div_add_mod a L; omega
    have hfactor : L + L * (a / L) = L * (a / L + 1) := by ring
    rw [hstep, hfactor, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm.1]

/-- The all-equal-residue system achieves minimum density: the coverage density
    with constant residue a equals that with constant residue 0.
    Proved via cyclic shift bijection on {0,...,L-1}. -/
theorem equal_residues_minimize (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n)
    (a : ℕ) :
    coverageDensity ⟨moduli, (fun _ => a), hpos⟩ =
    coverageDensity ⟨moduli, (fun _ => 0), hpos⟩ := by
  have hcard := coverage_card_shift moduli hpos a
  simp only [coverageDensity_eq, Nat.zero_mod]
  -- systemLCM is definitionally equal for both (depends only on moduli)
  -- so after simp, both sides have same range and denominator
  -- Just need to show cast of equal ℕ cards divided by same denominator are equal
  congr 1
  exact_mod_cast hcard

-- ## Question 1: Maximum Density (OPEN)

/-- For pairwise coprime moduli, all residue choices give the same density:
    the density equals 1 - ∏ᵢ(1 - 1/nᵢ) regardless of residue selection.
    This follows from the Chinese Remainder Theorem: since the moduli are coprime,
    the residue classes partition Z/LZ uniformly.
    NOTE: Previously stated as "= Σ 1/nᵢ" which is incorrect for |moduli| ≥ 2
    (e.g., for {2,3}: actual density = 2/3, not 5/6). -/
theorem coprime_density_formula (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n)
    (hcop : ∀ m ∈ moduli, ∀ n ∈ moduli, m ≠ n → Nat.Coprime m n)
    (r : ℕ → ℕ) :
    coverageDensity ⟨moduli, r, hpos⟩ = coprimeDensity moduli := by
  -- Rewrite to explicit filter form
  rw [coverageDensity_eq]
  -- Replace systemLCM with moduli.prod id
  have hL := systemLCM_coprime_eq_prod moduli hpos hcop r
  conv_lhs => rw [hL]
  dsimp only []
  -- Setup
  have hP : 0 < moduli.prod id := Finset.prod_pos (fun n hn => hpos n hn)
  have hP_ne : (↑(moduli.prod id) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hP)
  -- Complement count = ∏(nᵢ - 1) by CRT
  have hcomp := complement_eq_prod moduli hpos hcop r
  -- Coverage + complement = moduli.prod id (partition)
  have hpart :
    ((Finset.range (moduli.prod id)).filter (fun m => ∃ n ∈ moduli, m % n = r n % n)).card +
    ((Finset.range (moduli.prod id)).filter (fun m => ∀ n ∈ moduli, m % n ≠ r n % n)).card =
    moduli.prod id := by
    have hdisj : Disjoint
        ((Finset.range (moduli.prod id)).filter (fun m => ∃ n ∈ moduli, m % n = r n % n))
        ((Finset.range (moduli.prod id)).filter (fun m => ∀ n ∈ moduli, m % n ≠ r n % n)) := by
      rw [Finset.disjoint_left]; intro m hm1 hm2
      obtain ⟨n, hn, heq⟩ := (Finset.mem_filter.mp hm1).2
      exact absurd heq ((Finset.mem_filter.mp hm2).2 n hn)
    have hunion : (Finset.range (moduli.prod id)).filter (fun m => ∃ n ∈ moduli, m % n = r n % n) ∪
        (Finset.range (moduli.prod id)).filter (fun m => ∀ n ∈ moduli, m % n ≠ r n % n) =
        Finset.range (moduli.prod id) := by
      ext m; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.elim And.left And.left,
        fun hm => if h : ∃ n ∈ moduli, m % n = r n % n then .inl ⟨hm, h⟩
                   else .inr ⟨hm, by push_neg at h; exact h⟩⟩
    linarith [Finset.card_union_of_disjoint hdisj, hunion ▸ Finset.card_range (moduli.prod id)]
  -- coverage = prod(id) - prod(n-1) in ℕ and ℝ
  have hle : moduli.prod (fun n => n - 1) ≤ moduli.prod id := by
    calc moduli.prod (fun n => n - 1)
        = ((Finset.range (moduli.prod id)).filter
            (fun m => ∀ n ∈ moduli, m % n ≠ r n % n)).card := hcomp.symm
      _ ≤ (Finset.range (moduli.prod id)).card := Finset.card_filter_le _ _
      _ = moduli.prod id := Finset.card_range _
  have hcov_eq : (((Finset.range (moduli.prod id)).filter
      (fun m => ∃ n ∈ moduli, m % n = r n % n)).card : ℝ) =
      ↑(moduli.prod id) - ↑(moduli.prod (fun n => n - 1)) := by
    have hnat : ((Finset.range (moduli.prod id)).filter
      (fun m => ∃ n ∈ moduli, m % n = r n % n)).card =
      moduli.prod id - moduli.prod (fun n => n - 1) := by rw [← hcomp]; omega
    rw [hnat, Nat.cast_sub hle]
  -- density = 1 - ∏(1-1/n) = coprimeDensity
  unfold coprimeDensity
  rw [hcov_eq, sub_div, div_self hP_ne]
  congr 1
  exact prod_sub_one_div moduli hpos

/-- coprimeDensity for a singleton is 1/n. -/
theorem coprimeDensity_singleton (n : ℕ) (_hn : 0 < n) :
    coprimeDensity {n} = 1 / (n : ℝ) := by
  unfold coprimeDensity
  rw [Finset.prod_singleton]
  ring

/-- For coprime moduli, max = min = coprimeDensity. -/
theorem coprime_max_eq_min (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n)
    (hcop : ∀ m ∈ moduli, ∀ n ∈ moduli, m ≠ n → Nat.Coprime m n) :
    maxCoverageDensity moduli hpos = minCoverageDensity moduli hpos := by
  unfold maxCoverageDensity minCoverageDensity
  -- Both sets equal {coprimeDensity moduli} since every residue choice gives the same density
  have hall : ∀ r : ℕ → ℕ,
      coverageDensity ⟨moduli, r, hpos⟩ = coprimeDensity moduli :=
    fun r => coprime_density_formula moduli hpos hcop r
  have hset : { d : ℝ | ∃ r, d = coverageDensity ⟨moduli, r, hpos⟩ } =
      {coprimeDensity moduli} := by
    ext d; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨r, rfl⟩; exact hall r
    · intro h; exact ⟨fun _ => 0, by rw [hall, h]⟩
  rw [hset]; simp [csSup_singleton, csInf_singleton]

/-- The maximum coverage density is at most 1 (follows from density_le_one). -/
theorem erdos_278_density_le_one (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) :
    maxCoverageDensity moduli hpos ≤ 1 := by
  unfold maxCoverageDensity
  apply csSup_le
  · exact ⟨_, ⟨fun _ => 0, rfl⟩⟩
  · rintro d ⟨r, rfl⟩; exact density_le_one _

-- ## Single Modulus Case

/-- The LCM of a singleton moduli set {n} is just n. -/
private lemma systemLCM_singleton (n : ℕ) (r : ℕ → ℕ)
    (hpos : ∀ m ∈ ({n} : Finset ℕ), 0 < m) :
    systemLCM ⟨{n}, r, hpos⟩ = n := by
  unfold systemLCM
  set l := ({n} : Finset ℕ).val.toList with hl_def
  have hlen : l.length = 1 := by rw [hl_def, Multiset.length_toList]; simp
  have hmem : n ∈ l := by rw [hl_def, Multiset.mem_toList]; exact Finset.mem_singleton_self n
  -- l has length 1 and contains n, so l = [n]
  have hl : l = [n] := by
    match l, hlen, hmem with
    | [a], _, ha =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rw [ha]
  rw [hl]
  simp [Nat.lcm, Nat.gcd_one_left]

/-- For singleton moduli {n}, coverage density is 1/n regardless of residue choice. -/
private lemma coverageDensity_singleton (n : ℕ) (hn : 0 < n) (r : ℕ → ℕ)
    (hpos : ∀ m ∈ ({n} : Finset ℕ), 0 < m) :
    coverageDensity ⟨{n}, r, hpos⟩ = 1 / (n : ℝ) := by
  rw [coverageDensity_eq, systemLCM_singleton n r hpos]
  -- After rewrite, struct field accesses reduce: .moduli = {n}, .residue = r
  -- Goal: card(filter) / n = 1 / n where filter selects m < n with m % n = r n % n
  suffices hfilt : ((Finset.range n).filter
      (fun m => ∃ k ∈ ({n} : Finset ℕ), m % k = r k % k)).card = 1 by
    rw [hfilt]; push_cast; ring
  -- The filter = {r n % n} since for m < n, m % n = m
  have hsub : (Finset.range n).filter
      (fun m => ∃ k ∈ ({n} : Finset ℕ), m % k = r k % k) = {r n % n} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · intro ⟨hm, k, hk, hmod⟩
      -- After simp, hk : k = n
      subst hk
      rwa [Nat.mod_eq_of_lt hm] at hmod
    · intro heq
      rw [heq]
      exact ⟨Nat.mod_lt _ hn, n, rfl, Nat.mod_eq_of_lt (Nat.mod_lt _ hn)⟩
  rw [hsub, Finset.card_singleton]

/-- For a single modulus n, both the max and min density are 1/n. -/
theorem single_modulus_density (n : ℕ) (hn : 0 < n) :
    maxCoverageDensity {n} (by intro m hm; simp at hm; rwa [hm]) = 1 / (n : ℝ) := by
  unfold maxCoverageDensity
  have hpos : ∀ m ∈ ({n} : Finset ℕ), 0 < m := by intro m hm; simp at hm; rwa [hm]
  -- All densities in the set equal 1/n
  have hall : ∀ d ∈ { d : ℝ | ∃ r : ℕ → ℕ, d = coverageDensity ⟨{n}, r, hpos⟩ },
      d = 1 / (n : ℝ) := by
    intro d hd
    obtain ⟨r, rfl⟩ := hd
    exact coverageDensity_singleton n hn r hpos
  -- sSup of a set where all elements are c, and the set is nonempty, is c
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨fun _ => 0, rfl⟩⟩
    · intro d hd; rw [hall d hd]
  · apply le_csSup
    · exact ⟨1, by rintro d ⟨r, rfl⟩; exact density_le_one _⟩
    · exact ⟨fun _ => 0, (coverageDensity_singleton n hn _ hpos).symm⟩
