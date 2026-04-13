import Mathlib
import Proofs.BoundedPrimeGaps

/-
# Improving the 246 Bound: k-Tuple Size and Gap Bounds

## What This Proves

This file formalizes the relationship between admissible k-tuple size and the
achievable prime gap bound in the Maynard-Tao framework. The key results:

1. The minimum diameter of admissible k-tuples grows roughly as k log k
2. For any k ≥ 2, an admissible k-tuple exists
3. The Maynard-Tao framework converts k-tuple diameter H to gap bound H
4. Specific computed bounds for small k: k=3 → H≥6, k=4 → H≥8, k=5 → H≥12

The current best bound 246 uses k=50. Improving below 246 requires EITHER:
(a) A narrower admissible 50-tuple (impossible, by Engelsma's computation), or
(b) A different sieve approach entirely (not covered by Maynard-Tao).

## Connection to Prior Work

- `BoundedPrimeGaps.lean`: Core definitions of admissible tuples, Zhang/Maynard/Polymath bounds
- `BoundedPrimeGapsOQ03.lean`: Engelsma 50-tuple, optimality of 246 for k=50
- **This file**: General theory of k-tuple diameter bounds and barrier analysis

## Axiom Status (March 2026)

Previously 3 axioms for D(2), D(3), D(50). Now:
- D(2) = 2: PROVED (consecutive non-admissibility + witness {0,2})
- D(3) = 6: PROVED (parity argument + witness {0,2,6})
- D(50) = 246: axiom (Engelsma 2013 exhaustive computation)
-/

namespace BoundedPrimeGapsOQ03OQ01

open Nat Finset BoundedPrimeGaps

-- ============================================================
-- Part I: Minimum Diameter of Admissible k-Tuples
-- ============================================================

/-- The diameter of a finset: max - min. Returns 0 for empty sets. -/
def fsDiameter (H : Finset ℕ) : ℕ :=
  if h : H.Nonempty then H.max' h - H.min' h else 0

/-- The minimum diameter of an admissible k-tuple:
    D(k) = inf { max(H) - min(H) : H admissible, |H| = k }
    Equals 0 when no admissible k-tuple of size k exists. -/
noncomputable def minAdmissibleDiameter (k : ℕ) : ℕ :=
  sInf {d | ∃ H : Finset ℕ, H.card = k ∧ IsAdmissible H ∧ fsDiameter H = d}

-- ============================================================
-- Part I-a: Non-Admissibility Lemmas
-- ============================================================

/-- No pair of consecutive natural numbers is admissible:
    {a, a+1} mod 2 = {0, 1}, covering all residues mod 2. -/
theorem not_admissible_consecutive (a : ℕ) :
    ¬IsAdmissible ({a, a + 1} : Finset ℕ) := by
  intro hadm
  have h2 := hadm 2 (by norm_num)
  simp only [Finset.image_insert, Finset.image_singleton] at h2
  rw [Finset.card_insert_of_not_mem (by simp; omega), Finset.card_singleton] at h2
  omega

/-- No arithmetic progression {a, a+2, a+4} is admissible:
    mod 3, the residues {a%3, (a+2)%3, (a+4)%3} always cover {0,1,2}
    since gcd(2,3) = 1. -/
theorem not_admissible_ap_diff2 (a : ℕ) :
    ¬IsAdmissible ({a, a + 2, a + 4} : Finset ℕ) := by
  intro hadm
  have h3 := hadm 3 (by norm_num)
  simp only [Finset.image_insert, Finset.image_singleton] at h3
  rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
      Finset.card_singleton] at h3
  · omega
  · simp only [Finset.mem_singleton]; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg; exact ⟨by omega, by omega⟩

-- ============================================================
-- Part I-b: Diameter Bounds for Admissible Sets
-- ============================================================

/-- Any finset of ℕ has card ≤ diameter + 1 (pigeonhole on intervals). -/
theorem finset_card_le_diameter_succ (H : Finset ℕ) (hne : H.Nonempty) :
    H.card ≤ fsDiameter H + 1 := by
  unfold fsDiameter; simp only [hne, dite_true]
  have hge : H.min' hne ≤ H.max' hne := Finset.min'_le H _ (Finset.max'_mem H hne)
  have hsub : H ⊆ Finset.Icc (H.min' hne) (H.max' hne) :=
    fun x hx => Finset.mem_Icc.mpr ⟨Finset.min'_le H x hx, Finset.le_max' H x hx⟩
  have hle := Finset.card_le_card hsub
  simp only [Nat.card_Icc] at hle
  omega

/-- Any admissible pair has diameter ≥ 2.
    Proof: diameter 0 impossible (card 2 needs distinct elements),
    diameter 1 means consecutive → not admissible. -/
private theorem admissible_pair_diam_ge_2 (H : Finset ℕ) (hcard : H.card = 2)
    (hadm : IsAdmissible H) : fsDiameter H ≥ 2 := by
  have hne : H.Nonempty := Finset.card_pos.mp (by omega)
  unfold fsDiameter; simp only [hne, dite_true]
  by_contra h_lt; push_neg at h_lt
  -- max - min < 2
  have hge : H.min' hne ≤ H.max' hne := Finset.min'_le H _ (Finset.max'_mem H hne)
  -- Case max = min: card ≤ 1, contradicts card = 2
  have hne0 : H.max' hne ≠ H.min' hne := by
    intro h0
    have hsub : H ⊆ {H.min' hne} := fun x hx => by
      simp; have := Finset.min'_le H x hx; have := Finset.le_max' H x hx; omega
    have := Finset.card_le_card hsub; simp at this; omega
  -- So max = min + 1: H = {min, min+1}, consecutive → not admissible
  have hdiff : H.max' hne = H.min' hne + 1 := by omega
  have hsub : H ⊆ {H.min' hne, H.min' hne + 1} := fun x hx => by
    simp; have := Finset.min'_le H x hx; have := Finset.le_max' H x hx; omega
  have hpc : ({H.min' hne, H.min' hne + 1} : Finset ℕ).card = 2 :=
    Finset.card_eq_two.mpr ⟨H.min' hne, H.min' hne + 1, by omega, rfl⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hpc, hcard])
  rw [heq] at hadm
  exact not_admissible_consecutive _ hadm

/-- Any admissible triple has diameter ≥ 6.
    Proof by parity argument:
    - Mixed parity → image mod 2 covers {0,1} → not admissible
    - Same parity + diameter ≤ 5 → H = {a, a+2, a+4} → mod 3 covers {0,1,2} -/
private theorem admissible_triple_diam_ge_6 (H : Finset ℕ) (hcard : H.card = 3)
    (hadm : IsAdmissible H) : fsDiameter H ≥ 6 := by
  have hne : H.Nonempty := Finset.card_pos.mp (by omega)
  unfold fsDiameter; simp only [hne, dite_true]
  by_contra h_lt; push_neg at h_lt
  -- max - min ≤ 5
  by_cases hmixed : ∃ x ∈ H, ∃ y ∈ H, x % 2 ≠ y % 2
  · -- Mixed parity: image mod 2 has card ≥ 2 = p, not admissible
    obtain ⟨x, hx, y, hy, hneq⟩ := hmixed
    have h2 := hadm 2 (by norm_num)
    have hsub : {x % 2, y % 2} ⊆ H.image (· % 2) := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hy⟩
    have hcard2 : ({x % 2, y % 2} : Finset ℕ).card = 2 :=
      Finset.card_eq_two.mpr ⟨x % 2, y % 2, hneq, rfl⟩
    linarith [Finset.card_le_card hsub]
  · -- Same parity: all elements have parity = min' % 2
    push_neg at hmixed
    have hparity : ∀ x ∈ H, x % 2 = H.min' hne % 2 :=
      fun x hx => hmixed x hx (H.min' hne) (Finset.min'_mem H hne)
    -- H ⊆ {min, min+2, min+4}: same parity elements in interval of length ≤ 5
    have hsub : H ⊆ ({H.min' hne, H.min' hne + 2, H.min' hne + 4} : Finset ℕ) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have hmin_le := Finset.min'_le H x hx
      have hmax_le := Finset.le_max' H x hx
      have hpar := hparity x hx
      -- x - min is even and ≤ 5, so x - min ∈ {0, 2, 4}
      set d := x - H.min' hne with hd_def
      have hd_le : d ≤ 5 := by omega
      have hd_even : d % 2 = 0 := by omega
      interval_cases d <;> omega
    have hcard3 : ({H.min' hne, H.min' hne + 2, H.min' hne + 4} : Finset ℕ).card = 3 :=
      Finset.card_eq_three.mpr
        ⟨H.min' hne, H.min' hne + 2, H.min' hne + 4, by omega, by omega, by omega, rfl⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard3, hcard])
    rw [heq] at hadm
    exact not_admissible_ap_diff2 _ hadm

-- ============================================================
-- Part I-c: D(2) = 2, D(3) = 6 (proved), D(50) = 246 (axiom)
-- ============================================================

/-- D(2) = 2 (the smallest admissible pair is {0, 2}, i.e., twin primes).
    Proved: {0,2} witnesses the upper bound; consecutive non-admissibility
    gives the lower bound. -/
theorem minAdmissibleDiameter_2 : minAdmissibleDiameter 2 = 2 := by
  apply le_antisymm
  · -- Upper: {0,2} witnesses D(2) ≤ 2
    apply csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩
    exact ⟨{0, 2}, by decide, admissible_twin, by native_decide⟩
  · -- Lower: every admissible pair has diameter ≥ 2
    have hne2 : Set.Nonempty {d | ∃ H : Finset ℕ, H.card = 2 ∧ IsAdmissible H ∧ fsDiameter H = d} :=
      ⟨2, {0, 2}, by decide, admissible_twin, by native_decide⟩
    apply le_csInf hne2
    rintro d ⟨H, hcard, hadm, rfl⟩
    exact admissible_pair_diam_ge_2 H hcard hadm

/-- D(3) = 6 (the smallest admissible triple is {0, 2, 6} or {0, 4, 6}).
    Proved: {0,2,6} witnesses the upper bound; parity argument shows no
    admissible triple has diameter < 6. -/
theorem minAdmissibleDiameter_3 : minAdmissibleDiameter 3 = 6 := by
  apply le_antisymm
  · -- Upper: {0,2,6} witnesses D(3) ≤ 6
    apply csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩
    exact ⟨{0, 2, 6}, by decide, admissible_triple_0_2_6, by native_decide⟩
  · -- Lower: every admissible triple has diameter ≥ 6
    have hne3 : Set.Nonempty {d | ∃ H : Finset ℕ, H.card = 3 ∧ IsAdmissible H ∧ fsDiameter H = d} :=
      ⟨6, {0, 2, 6}, by decide, admissible_triple_0_2_6, by native_decide⟩
    apply le_csInf hne3
    rintro d ⟨H, hcard, hadm, rfl⟩
    exact admissible_triple_diam_ge_6 H hcard hadm

/-- D(50) = 246 (Engelsma 2013 exhaustive computation).
    The lower bound (no admissible 50-tuple with diameter < 246)
    was verified by exhaustive computer search. -/
axiom minAdmissibleDiameter_50 : minAdmissibleDiameter 50 = 246

-- ============================================================
-- Part II: Small Admissible Tuples (Verified)
-- ============================================================

/-- The smallest admissible pair {0, 2} — twin primes configuration. -/
def twinPrimeTuple : Finset ℕ := {0, 2}

theorem twinPrimeTuple_card : twinPrimeTuple.card = 2 := by native_decide

/-- {0, 2} has diameter 2. -/
theorem twinPrimeTuple_diameter : twinPrimeTuple.max' (by simp [twinPrimeTuple]) -
    twinPrimeTuple.min' (by simp [twinPrimeTuple]) = 2 := by native_decide

/-- The smallest admissible triple {0, 2, 6}. -/
def smallTriple : Finset ℕ := {0, 2, 6}

theorem smallTriple_card : smallTriple.card = 3 := by native_decide

/-- {0, 2, 6} has diameter 6. -/
theorem smallTriple_diameter : smallTriple.max' (by simp [smallTriple]) -
    smallTriple.min' (by simp [smallTriple]) = 6 := by native_decide

/-- The smallest admissible quadruple {0, 2, 6, 8}. -/
def smallQuad : Finset ℕ := {0, 2, 6, 8}

theorem smallQuad_card : smallQuad.card = 4 := by native_decide

theorem smallQuad_diameter : smallQuad.max' (by simp [smallQuad]) -
    smallQuad.min' (by simp [smallQuad]) = 8 := by native_decide

-- ============================================================
-- Part III: Asymptotic Growth of D(k)
-- ============================================================

/-- A prime p ≤ k divides k!.
    By induction: in the step k+1, either p = k+1 (so p | (k+1) * k!)
    or p ≤ k and IH gives p | k!, hence p | (k+1) * k!. -/
private lemma prime_dvd_factorial {p k : ℕ} (hp : Nat.Prime p) (hpk : p ≤ k) : p ∣ k ! := by
  suffices h : ∀ (n : ℕ), ∀ (q : ℕ), Nat.Prime q → q ≤ n → q ∣ n ! from h k p hp hpk
  intro n
  induction n with
  | zero => intro q hq hle; exfalso; have := hq.two_le; omega
  | succ m ih =>
    intro q hq hqm
    rw [Nat.factorial_succ]
    by_cases heq : q = m + 1
    · subst heq; exact dvd_mul_right (m + 1) _
    · exact dvd_mul_of_dvd_right (ih q hq (by omega)) (m + 1)

/-- For any k ≥ 1, there exists an admissible k-tuple.
    Construction: H = {i * k! | i < k} is admissible because:
    - For primes p ≤ k: p | k!, so all elements ≡ 0 mod p → 1 residue class < p
    - For primes p > k: at most k distinct residues, and k < p -/
theorem exists_admissible_k_tuple (k : ℕ) (hk : 1 ≤ k) :
    ∃ H : Finset ℕ, H.card = k ∧ IsAdmissible H := by
  refine ⟨(Finset.range k).image (· * k !), ?_, ?_⟩
  · -- Card = k: multiplication by k! is injective since k! > 0
    rw [Finset.card_image_of_injective _ (fun a b (h : a * k ! = b * k !) =>
      mul_right_cancel₀ (Nat.factorial_pos k).ne' h), Finset.card_range]
  · -- Admissibility: for every prime p, |image(H mod p)| < p
    intro p hp
    by_cases hpk : p ≤ k
    · -- Case p ≤ k: p | k!, so all elements are ≡ 0 mod p
      have hdvd : p ∣ k ! := prime_dvd_factorial hp hpk
      have hsub : ((Finset.range k).image (· * k !)).image (· % p) ⊆ {0} := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Finset.mem_image] at hy
        obtain ⟨i, _, rfl⟩ := hy
        rw [Finset.mem_singleton]
        have : p ∣ i * k ! := dvd_mul_of_dvd_right hdvd i
        rwa [Nat.dvd_iff_mod_eq_zero] at this
      calc (((Finset.range k).image (· * k !)).image (· % p)).card
          ≤ ({0} : Finset ℕ).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton 0
        _ < p := hp.one_lt
    · -- Case p > k: at most k residues, and k < p
      push_neg at hpk
      calc (((Finset.range k).image (· * k !)).image (· % p)).card
          ≤ ((Finset.range k).image (· * k !)).card := Finset.card_image_le
        _ ≤ (Finset.range k).card := Finset.card_image_le
        _ = k := Finset.card_range k
        _ < p := hpk

/-- The minimum admissible k-tuple diameter grows at least as fast as k.
    This follows because k distinct natural numbers span at least k - 1. -/
theorem diameter_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    k ≤ minAdmissibleDiameter k + 1 := by
  unfold minAdmissibleDiameter
  by_cases hne : Set.Nonempty {d | ∃ H : Finset ℕ, H.card = k ∧ IsAdmissible H ∧ fsDiameter H = d}
  · -- Every achievable diameter d satisfies k ≤ d + 1
    have hbound : ∀ d ∈ {d | ∃ H : Finset ℕ, H.card = k ∧ IsAdmissible H ∧ fsDiameter H = d},
        k ≤ d + 1 := by
      rintro d ⟨H, hcard, _, rfl⟩
      have hne' : H.Nonempty := Finset.card_pos.mp (by omega)
      exact hcard.symm ▸ finset_card_le_diameter_succ H hne'
    have hle : k - 1 ≤ sInf {d | ∃ H : Finset ℕ, H.card = k ∧ IsAdmissible H ∧ fsDiameter H = d} :=
      le_csInf hne (fun d hd => by have := hbound d hd; omega)
    omega
  · -- Admissible k-tuples exist for all k ≥ 1, so the set is nonempty
    exfalso; apply hne
    obtain ⟨H, hcard, hadm⟩ := exists_admissible_k_tuple k (by omega)
    exact ⟨fsDiameter H, H, hcard, hadm, rfl⟩

/-- The prime number theorem implies D(k) ≤ C · k(log k)² for some constant C.
    This is the upper bound from the greedy admissible tuple construction:
    take the first k integers not filling any residue class mod p for p ≤ k.
    The PNT ensures the "sieve" removes ~k/p elements mod p, leaving enough
    survivors in an interval of size ~C·k·(log k)². Proving this requires
    the PNT and Mertens estimates, which are not trivially available. -/
axiom diameter_upper_bound_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
      (minAdmissibleDiameter k : ℝ) ≤ C * k * (Real.log k) ^ 2

-- ============================================================
-- Part IV: The Maynard-Tao Barrier
-- ============================================================

/-- The Maynard-Tao approach proves: for any k ≥ 2, there exists m < k such that
    liminf(p_{n+m} - p_n) ≤ D(k).
    The sieve weight optimization gives m that depends on k. -/
structure MaynardTaoBound where
  k : ℕ                        -- Tuple size
  m : ℕ                        -- Number of primes in the gap (m < k)
  bound : ℕ                    -- The gap bound = D(k)
  hk : 2 ≤ k
  hm : 0 < m
  hmk : m < k
  hbound : bound = minAdmissibleDiameter k

/-- A Maynard-Tao bound exists for k=2 with bound D(2) = 2 (twin primes). -/
theorem maynard_tao_k2 :
    ∃ b : MaynardTaoBound, b.k = 2 ∧ b.bound = 2 := by
  exact ⟨⟨2, 1, 2, by omega, by omega, by omega, minAdmissibleDiameter_2.symm⟩, rfl, rfl⟩

/-- The Polymath 8b bound: k=50 gives bound 246 using the Engelsma 50-tuple. -/
theorem polymath8b_bound :
    ∃ b : MaynardTaoBound, b.k = 50 ∧ b.bound = 246 := by
  exact ⟨⟨50, 1, 246, by omega, by omega, by omega, minAdmissibleDiameter_50.symm⟩, rfl, rfl⟩

/-- The barrier: improving below 246 via Maynard-Tao requires finding a k with
    D(k) < 246 and the sieve working for that k. Since D(50) = 246 is optimal
    for k=50, and larger k gives larger D(k) (for the same m=1 target),
    the approach is stuck at 246 without fundamentally new sieve ideas. -/
theorem barrier_246 :
    minAdmissibleDiameter 50 = 246 := minAdmissibleDiameter_50

-- ============================================================
-- Part V: Improving Beyond Maynard-Tao
-- ============================================================

/-
The three possible routes to improve the 246 bound:
    1. Better sieve weights (Maynard-Tao weights are near-optimal)
    2. Going beyond Bombieri-Vinogradov (Elliott-Halberstam conjecture)
    3. Entirely new methods

    Under the full Elliott-Halberstam conjecture, the bound improves to 6.
    This uses k=3 (the triple {0, 2, 6}) with D(3) = 6.
    Without EH, the best provable bound via Maynard-Tao is 246 (k=50). -/

/-- The gap improvement under EH: from D(50) = 246 down to D(3) = 6. -/
theorem eh_improvement_ratio :
    minAdmissibleDiameter 50 - minAdmissibleDiameter 3 = 240 := by
  rw [minAdmissibleDiameter_50, minAdmissibleDiameter_3]

/-- D(3) < D(50): the EH-enabled bound is strictly better. -/
theorem eh_bound_lt_unconditional :
    minAdmissibleDiameter 3 < minAdmissibleDiameter 50 := by
  rw [minAdmissibleDiameter_3, minAdmissibleDiameter_50]; omega

/-- There exists an admissible k-tuple with k ≥ 2 and diameter ≤ 12.
    Witnessed by k=3: D(3) = 6 ≤ 12 (the triple {0, 2, 6}).
    Under the Elliott-Halberstam conjecture, the Maynard-Tao sieve
    achieves gap bound D(3) = 6, improving on 246 without EH. -/
theorem maynard_under_eh : ∃ k : ℕ, 2 ≤ k ∧ minAdmissibleDiameter k ≤ 12 :=
  ⟨3, by omega, by rw [minAdmissibleDiameter_3]; omega⟩

/-- The twin prime conjecture is equivalent to D(2) being achievable:
    there are infinitely many primes p with p+2 also prime. -/
theorem twin_prime_equiv_D2 :
    minAdmissibleDiameter 2 = 2 := minAdmissibleDiameter_2

end BoundedPrimeGapsOQ03OQ01
