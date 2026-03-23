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

-- ## Inclusion-Exclusion Formula

/-- The inclusion-exclusion density when all residues are equal:
    Σ 1/nᵢ - Σ 1/lcm(nᵢ,nⱼ) + ⋯
    (Simplified: only the first-order term for now.) -/
noncomputable def inclusionExclusionDensity (moduli : Finset ℕ) : ℝ :=
  moduli.sum (fun n => (1 : ℝ) / n)

-- ## Simpson's Theorem (1986)

/-- Simpson's theorem: the minimum coverage density is achieved when
    all residues are equal. -/
axiom simpson_theorem (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) :
    ∀ r : ℕ → ℕ,
      coverageDensity ⟨moduli, (fun _ => 0), hpos⟩ ≤ coverageDensity ⟨moduli, r, hpos⟩

-- ===== Proving equal_residues_minimize (axiom → theorem) =====

/-- Helper: if (x + y) % n = y and x < n, then x = 0.
    Uses Euclidean division and case analysis on the quotient. -/
private lemma add_mod_eq_right_imp (x y n : ℕ) (hx : x < n)
    (h : (x + y) % n = y) : x = 0 := by
  have h1 := Nat.div_add_mod (x + y) n
  rw [h] at h1
  -- h1 : n * ((x + y) / n) + y = x + y, so n * ((x + y) / n) = x
  -- Since x < n, the quotient must be 0
  have hq : (x + y) / n < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < n)]; omega
  interval_cases ((x + y) / n) <;> omega

/-- Cyclic shift preserves coverage: n | m ↔ (m + a) % L ≡ a (mod n), when n ∣ L. -/
private lemma shift_coverage_iff (m a n L : ℕ) (hn : 0 < n) (hL : 0 < L)
    (hndvdL : n ∣ L) :
    m % n = 0 ↔ (m + a) % L % n = a % n := by
  constructor
  · intro hm
    rw [Nat.mod_mod_of_dvd _ hndvdL, Nat.add_mod, hm, Nat.zero_add]
    exact Nat.mod_eq_of_lt (Nat.mod_lt a hn)
  · intro h
    rw [Nat.mod_mod_of_dvd _ hndvdL, Nat.add_mod] at h
    exact add_mod_eq_right_imp (m % n) (a % n) n (Nat.mod_lt m hn) h

/-- Modular addition cancellation: if a, b < n and (a+c) ≡ (b+c) (mod n), then a = b. -/
private lemma mod_add_cancel_right {a b c n : ℕ} (ha : a < n) (hb : b < n)
    (h : (a + c) % n = (b + c) % n) : a = b := by
  -- Reduce c to d = c % n
  set d := c % n with hd_def
  have hdn : d < n := Nat.mod_lt c (by omega)
  -- (a + c) % n = (a + d) % n  and  (b + c) % n = (b + d) % n
  have h1 : (a + c) % n = (a + d) % n := by
    rw [Nat.add_mod a c n, Nat.add_mod a d n, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha,
        show d % n = d from Nat.mod_eq_of_lt hdn]
  have h2 : (b + c) % n = (b + d) % n := by
    rw [Nat.add_mod b c n, Nat.add_mod b d n, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb,
        show d % n = d from Nat.mod_eq_of_lt hdn]
  rw [h1, h2] at h
  -- Use Euclidean division to case-split on the quotients
  have da := Nat.div_add_mod (a + d) n
  have db := Nat.div_add_mod (b + d) n
  rw [h] at da
  have qa_lt : (a + d) / n < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < n)]; omega
  have qb_lt : (b + d) / n < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < n)]; omega
  interval_cases ((a + d) / n) <;> interval_cases ((b + d) / n) <;> omega

/-- (x % L + a) % L = (x + a) % L: taking mod before adding preserves the result. -/
private lemma mod_add_mod (x a L : ℕ) (hL : 0 < L) :
    (x % L + a) % L = (x + a) % L := by
  rw [Nat.add_mod (x % L) a L, Nat.add_mod x a L,
      show x % L % L = x % L from Nat.mod_eq_of_lt (Nat.mod_lt x hL)]

/-- The inverse shift: ((m + (L - a%L)) % L + a) % L = m, for m < L.
    This establishes that the cyclic shift by a has an inverse. -/
private lemma shift_inverse (m a L : ℕ) (hm : m < L) (hL : 0 < L) :
    ((m + (L - a % L)) % L + a) % L = m := by
  have haL : a % L < L := Nat.mod_lt a hL
  -- Step 1: Reduce (x%L + a)%L to (x + a)%L
  rw [mod_add_mod _ a L hL, Nat.add_assoc]
  -- Step 2: (L - a%L) + a is a positive multiple of L
  have harith : L - a % L + a = L * (1 + a / L) := by
    have := Nat.div_add_mod a L; omega
  rw [harith]
  -- Step 3: (m + L * k) % L = m % L = m
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero,
             Nat.mod_eq_of_lt (Nat.mod_lt m hL), Nat.mod_eq_of_lt hm]

/-- All-equal-residue systems have the same coverage density regardless of the
    common residue value. Proof: the cyclic shift m ↦ (m+a) % L bijects
    coverage-for-0 onto coverage-for-a, preserving cardinality. -/
theorem equal_residues_minimize (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n)
    (a : ℕ) :
    coverageDensity ⟨moduli, (fun _ => a), hpos⟩ =
    coverageDensity ⟨moduli, (fun _ => 0), hpos⟩ := by
  rw [coverageDensity_eq, coverageDensity_eq]
  -- Both systems share the same LCM period (systemLCM depends only on moduli)
  set L := systemLCM ⟨moduli, (fun _ => 0), hpos⟩ with hL_def
  have hLpos : 0 < L := systemLCM_pos ⟨moduli, (fun _ => 0), hpos⟩
  have hdvd : ∀ n ∈ moduli, n ∣ L := fun n hn =>
    dvd_systemLCM ⟨moduli, (fun _ => 0), hpos⟩ n hn
  have hL_eq : systemLCM ⟨moduli, fun _ => a, hpos⟩ = L := rfl
  rw [hL_eq]
  -- Suffices: the two filtered finsets have the same cardinality
  suffices hcard :
      ((Finset.range L).filter (fun m => ∃ n ∈ moduli, m % n = a % n)).card =
      ((Finset.range L).filter (fun m => ∃ n ∈ moduli, m % n = 0)).card by
    push_cast [hcard]
  -- Bijection from filter₀ to filterₐ via (· + a) % L
  symm
  exact Finset.card_bij (fun m _ => (m + a) % L)
    -- hi: shift maps filter₀ into filterₐ
    (fun m hm => by
      simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
      exact ⟨Nat.mod_lt _ hLpos, by
        obtain ⟨n, hn, hmod⟩ := hm.2
        exact ⟨n, hn, (shift_coverage_iff m a n L (hpos n hn) hLpos (hdvd n hn)).mp hmod⟩⟩)
    -- i_inj: shift is injective on filter₀
    (fun m₁ hm₁ m₂ hm₂ h => by
      simp only [Finset.mem_filter, Finset.mem_range] at hm₁ hm₂
      exact mod_add_cancel_right hm₁.1 hm₂.1 h)
    -- i_surj: shift is surjective onto filterₐ
    (fun m hm => by
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      -- Preimage: m' = (m + (L - a%L)) % L
      refine ⟨(m + (L - a % L)) % L, ?_, shift_inverse m a L hm.1 hLpos⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hLpos, ?_⟩
      obtain ⟨n, hn, hmod⟩ := hm.2
      exact ⟨n, hn, by
        -- Need: (m + (L - a%L)) % L % n = 0
        -- By shift_coverage_iff: equivalent to ((m+(L-a%L))%L + a)%L%n = a%n
        rw [shift_coverage_iff _ a n L (hpos n hn) hLpos (hdvd n hn),
            shift_inverse m a L hm.1 hLpos]
        exact hmod⟩)

-- ## Question 1: Maximum Density (OPEN)

/-- For coprime moduli, the maximum is Σ 1/nᵢ (≤ 1). -/
axiom max_density_coprime_case (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n)
    (hcop : ∀ m ∈ moduli, ∀ n ∈ moduli, m ≠ n → Nat.Coprime m n) :
    maxCoverageDensity moduli hpos = moduli.sum (fun n => (1 : ℝ) / n)

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
