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

-- ## Simpson's Theorem (1986)

/-- Simpson's theorem: the minimum coverage density is achieved when
    all residues are equal. -/
axiom simpson_theorem (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n) :
    ∀ r : ℕ → ℕ,
      coverageDensity ⟨moduli, (fun _ => 0), hpos⟩ ≤ coverageDensity ⟨moduli, r, hpos⟩

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
axiom coprime_density_formula (moduli : Finset ℕ) (hpos : ∀ n ∈ moduli, 0 < n)
    (hcop : ∀ m ∈ moduli, ∀ n ∈ moduli, m ≠ n → Nat.Coprime m n)
    (r : ℕ → ℕ) :
    coverageDensity ⟨moduli, r, hpos⟩ = coprimeDensity moduli

/-- coprimeDensity for a singleton is 1/n. -/
theorem coprimeDensity_singleton (n : ℕ) (hn : 0 < n) :
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
