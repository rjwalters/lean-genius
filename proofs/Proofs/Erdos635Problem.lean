/-
Erdős Problem #635: Non-Divisibility Condition on Differences

Given t ≥ 1 and A ⊆ {1,...,N}, suppose that whenever a, b ∈ A with
b - a ≥ t, we have (b - a) ∤ b. How large can |A| be?

**Conjecture**: |A| ≤ (1/2 + o_t(1)) · N.

**Status**: OPEN

**Known results**:
- For t = 1, the maximum is ⌊(N+1)/2⌋ (all odd numbers work)
- For t = 2, Erdős showed |A| ≥ N/2 + c·log(N) for some c > 0
  using odd numbers augmented with certain powers of 2
- The conjecture says density is always close to 1/2

**Origin**: Asked by Erdős in a letter to Ruzsa (~1980)
**References**: [Gu83] Gupta, [Ru99] Ruzsa

Reference: https://erdosproblems.com/635
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Nat Finset

namespace Erdos635

/- ## Part I: The Non-Divisibility Condition

The key constraint is: if two elements a < b of the set satisfy b - a ≥ t,
then (b - a) must NOT divide b. This is a non-trivial restriction on which
elements can coexist — it couples the gap between elements to their
absolute values via divisibility. -/

/-- A set A ⊆ {1,...,N} satisfies the t-non-divisibility condition
    if whenever a, b ∈ A with b - a ≥ t, then (b - a) does not divide b.

    Note: If b - a divides b, then b - a also divides a (since a = b - (b-a)).
    So the condition equivalently says: large gaps cannot divide either endpoint. -/
def IsNonDivisible (A : Finset ℕ) (t : ℕ) : Prop :=
  ∀ a b, a ∈ A → b ∈ A → a < b → b - a ≥ t → ¬(b - a ∣ b)

/-- A t-admissible set in {1,...,N}: contained in {1,...,N} and satisfying
    the t-non-divisibility condition. -/
def IsAdmissible (A : Finset ℕ) (N t : ℕ) : Prop :=
  (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) ∧ IsNonDivisible A t

/- ## Part II: The Extremal Function

f(N, t) is the maximum size of a t-admissible set in {1,...,N}.
This is the central quantity of the problem — Erdős asks for its
asymptotic behavior as N → ∞ for fixed t. -/

/-- f(N, t) = the maximum size of a t-admissible set in {1,...,N}.
    Defined as the supremum over all achievable cardinalities. -/
noncomputable def f (N t : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A.card = k ∧ IsAdmissible A N t}

/- ## Part III: The Case t = 1 — Odd Numbers

When t = 1, every pair with a < b has b - a ≥ 1, so the condition
applies to ALL pairs. The odd numbers {1, 3, 5, ...} form an optimal
solution: if a and b are both odd, then b - a is even, and an even
number cannot divide an odd number. -/

/-- The odd numbers in {1,...,N}. -/
def oddSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n % 2 = 1)

/-- The odd set is 1-admissible: if a, b are both odd with a < b,
    then b - a is even. Since b is odd, (b - a) ∤ b. -/
theorem oddSet_admissible (N : ℕ) (hN : N ≥ 1) :
    IsAdmissible (oddSet N) N 1 := by
  constructor
  · -- All elements are in {1,...,N}
    intro x hx
    simp only [oddSet, mem_filter, mem_Icc] at hx
    exact hx.1
  · -- Non-divisibility condition
    intro a b ha hb hab hd
    simp only [oddSet, mem_filter, mem_Icc] at ha hb
    -- Both a and b are odd
    have ha_odd := ha.2
    have hb_odd := hb.2
    -- b - a is even (difference of two odds)
    intro ⟨k, hk⟩
    -- If (b - a) | b then b = k * (b - a) for some k
    have hba_pos : b - a > 0 := by omega
    -- b - a is even: a % 2 = 1 and b % 2 = 1 means (b - a) % 2 = 0
    have hba_even : (b - a) % 2 = 0 := by omega
    -- But b is odd, so b % 2 = 1
    -- If b = k * (b - a) and (b - a) is even, then b is even: contradiction
    have hba_dvd_two : 2 ∣ (b - a) := Nat.dvd_of_mod_eq_zero hba_even
    obtain ⟨m, hm⟩ := hba_dvd_two
    have : b % 2 = 0 := by rw [hk, hm]; ring_nf; omega
    omega

/-- The odd set has size ⌊(N+1)/2⌋. -/
theorem oddSet_card (N : ℕ) : (oddSet N).card = (N + 1) / 2 := by
  simp only [oddSet]
  induction N with
  | zero => simp
  | succ n ih =>
    have key : (Finset.Icc 1 (n + 1)).filter (fun m => m % 2 = 1) =
        if (n + 1) % 2 = 1 then
          insert (n + 1) ((Finset.Icc 1 n).filter (fun m => m % 2 = 1))
        else
          (Finset.Icc 1 n).filter (fun m => m % 2 = 1) := by
      split <;> {
        ext x; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
        constructor <;> intro h <;> omega
      }
    rw [key]
    split <;> rename_i hn
    · rw [Finset.card_insert_of_notMem]
      · rw [ih]; omega
      · simp only [Finset.mem_filter, Finset.mem_Icc, not_and_or]; omega
    · rw [ih]; omega

/-- Key lemma: no two consecutive numbers can be in a 1-admissible set.
    Since (a+1) - a = 1 and 1 divides everything, the non-divisibility
    condition is immediately violated. -/
private lemma no_consecutive_in_admissible (A : Finset ℕ) (N : ℕ)
    (hA : IsAdmissible A N 1) (a : ℕ) (ha : a ∈ A) (ha1 : a + 1 ∈ A) : False := by
  have := hA.2 a (a + 1) ha ha1 (by omega) (by omega)
  exact this ⟨a + 1, by omega⟩

/-- Upper bound: any 1-admissible set in {1,...,N} has at most (N+1)/2 elements.
    Proof: the map a ↦ (a-1)/2 is injective on A (no consecutive elements
    means distinct elements map to distinct values) and its range has
    size (N+1)/2. -/
private theorem admissible_card_upper (A : Finset ℕ) (N : ℕ) (hA : IsAdmissible A N 1) :
    A.card ≤ (N + 1) / 2 := by
  -- Injection: a ↦ (a - 1) / 2
  let φ : ℕ → ℕ := fun a => (a - 1) / 2
  -- Show φ is injective on A
  have hinj : Set.InjOn φ ↑A := by
    intro a ha b hb heq
    simp only [φ] at heq
    have ha1 : 1 ≤ a := (hA.1 a (Finset.mem_coe.mp ha)).1
    have hb1 : 1 ≤ b := (hA.1 b (Finset.mem_coe.mp hb)).1
    -- From (a-1)/2 = (b-1)/2, derive a and b are in the same {2k+1, 2k+2}
    have ha_mod := Nat.div_add_mod (a - 1) 2
    have hb_mod := Nat.div_add_mod (b - 1) 2
    have ha_r := Nat.mod_lt (a - 1) (by omega : 0 < 2)
    have hb_r := Nat.mod_lt (b - 1) (by omega : 0 < 2)
    -- a = 2k + (a-1)%2 + 1, b = 2k + (b-1)%2 + 1 where k = (a-1)/2 = (b-1)/2
    by_contra hab
    -- a ≠ b means (a-1)%2 ≠ (b-1)%2, so they differ by exactly 1
    have : a = b + 1 ∨ b = a + 1 := by omega
    rcases this with rfl | rfl
    · exact no_consecutive_in_admissible A N hA b
        (Finset.mem_coe.mp hb) (Finset.mem_coe.mp ha)
    · exact no_consecutive_in_admissible A N hA a
        (Finset.mem_coe.mp ha) (Finset.mem_coe.mp hb)
  -- Show φ(A) ⊆ Finset.range ((N+1)/2)
  have hrange : A.image φ ⊆ Finset.range ((N + 1) / 2) := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [Finset.mem_range, φ]
    have ha_le : a ≤ N := (hA.1 a ha).2
    have ha_ge : a ≥ 1 := (hA.1 a ha).1
    -- (a-1)/2 < (N+1)/2 since a ≤ N
    have : a - 1 < N + 1 := by omega
    exact Nat.div_lt_of_lt_mul (by omega)
  -- Combine: |A| = |φ(A)| ≤ |range((N+1)/2)| = (N+1)/2
  calc A.card = (A.image φ).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range ((N + 1) / 2)).card := Finset.card_le_card hrange
    _ = (N + 1) / 2 := Finset.card_range _

/-- For t = 1, the maximum is exactly ⌊(N+1)/2⌋.

    This is tight: the odd set achieves it (lower bound, proved via oddSet),
    and no set with more than (N+1)/2 elements can satisfy the condition
    (upper bound, proved via no-consecutive injection). -/
theorem f_t1 (N : ℕ) (hN : N ≥ 1) : f N 1 = (N + 1) / 2 := by
  apply le_antisymm
  · -- Upper bound: f(N,1) ≤ (N+1)/2
    unfold f
    exact csSup_le (f_set_nonempty N 1) fun _ ⟨A, hcard, hAdm⟩ =>
      hcard ▸ admissible_card_upper A N hAdm
  · -- Lower bound: (N+1)/2 ≤ f(N,1) via oddSet
    unfold f
    rw [← oddSet_card N]
    exact le_csSup (f_set_bddAbove N 1) ⟨oddSet N, rfl, oddSet_admissible N hN⟩

/- ## Part IV: The Case t = 2 — Beating the N/2 Barrier

For t = 2, the condition only applies to pairs with b - a ≥ 2. This
allows b - a = 1 to be "free," meaning consecutive elements can coexist.
Erdős showed one can improve beyond N/2 by augmenting the odd set with
certain powers of 2. -/

/- ## Part V: The Main Conjecture (OPEN)

The central question: does the density of the extremal set always
approach 1/2 as N → ∞, regardless of t? The o_t(1) notation means
the error may depend on t but vanishes for large N. -/

/--
**Erdős Problem #635 (OPEN):**
For any fixed t, |A| ≤ (1/2 + o_t(1)) · N.

Formally: for every ε > 0 and every t ≥ 1, there exists N₀ such that
for all N ≥ N₀, f(N, t) ≤ (1/2 + ε) · N.

This is the main open conjecture. The difficulty increases with t because
larger t allows more "free" differences (those below t), potentially
enabling larger sets. -/
def ErdosConjecture635 : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ t : ℕ, t ≥ 1 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (f N t : ℝ) ≤ (1 / 2 + ε) * N

/-- The conjecture is axiomatized as it remains open. -/
axiom erdos_635 : ErdosConjecture635

/- ## Part VI: Upper and Lower Bounds -/

/-- t-admissibility weakens with larger t: fewer pairs are constrained.
    If b - a ≥ t' ≥ t, the t-condition already covers it. -/
theorem IsAdmissible_mono_t {A : Finset ℕ} {N t t' : ℕ} (h : t ≤ t')
    (hA : IsAdmissible A N t) : IsAdmissible A N t' :=
  ⟨hA.1, fun a b ha hb hab hd => hA.2 a b ha hb hab (le_trans h hd)⟩

/-- The set of achievable cardinalities is nonempty (∅ is always admissible). -/
theorem f_set_nonempty (N t : ℕ) :
    {k | ∃ A : Finset ℕ, A.card = k ∧ IsAdmissible A N t}.Nonempty :=
  ⟨0, ∅, rfl, ⟨fun _ h => absurd h (Finset.not_mem_empty _),
    fun _ _ h => absurd h (Finset.not_mem_empty _)⟩⟩

/-- The set of achievable cardinalities is bounded above by N. -/
theorem f_set_bddAbove (N t : ℕ) :
    BddAbove {k | ∃ A : Finset ℕ, A.card = k ∧ IsAdmissible A N t} :=
  ⟨N, fun _ ⟨A, hcard, hAdm⟩ => hcard ▸
    le_trans (Finset.card_le_card (fun x hx => Finset.mem_Icc.mpr (hAdm.1 x hx)))
      (by simp [Finset.card_Icc]; omega)⟩

/-- Trivial upper bound: f(N, t) ≤ N for all t.
    Proof: A ⊆ {1,...,N} implies |A| ≤ N. -/
theorem f_upper_trivial (N t : ℕ) : f N t ≤ N := by
  unfold f
  exact csSup_le (f_set_nonempty N t) fun _ ⟨A, hcard, hAdm⟩ => hcard ▸
    le_trans (Finset.card_le_card (fun x hx => Finset.mem_Icc.mpr (hAdm.1 x hx)))
      (by simp [Finset.card_Icc]; omega)

/-- Monotonicity: f(N, t) ≤ f(N, t') when t ≤ t'.
    Proof: Larger t means fewer restricted pairs, so more admissible sets. -/
theorem f_monotone_t (N t t' : ℕ) (h : t ≤ t') : f N t ≤ f N t' := by
  unfold f
  exact csSup_le_csSup (f_set_bddAbove N t') (f_set_nonempty N t)
    fun _ ⟨A, hcard, hAdm⟩ => ⟨A, hcard, IsAdmissible_mono_t h hAdm⟩

/-- Lower bound: f(N, t) ≥ (N+1)/2 for all t ≥ 1.
    Proof: The odd set is 1-admissible (hence t-admissible) with card (N+1)/2. -/
theorem f_lower_half (N t : ℕ) (hN : N ≥ 1) (ht : t ≥ 1) :
    f N t ≥ (N + 1) / 2 := by
  unfold f
  rw [← oddSet_card N]
  exact le_csSup (f_set_bddAbove N t)
    ⟨oddSet N, rfl, IsAdmissible_mono_t (by omega : 1 ≤ t) (oddSet_admissible N hN)⟩

/-- The density is at most 1/2 + o(1) for t = 1.
    Since f(N,1) = ⌊(N+1)/2⌋, the ratio f(N,1)/N → 1/2 as N → ∞.

    Proof: By f_t1, f(N,1) = (N+1)/2 (Nat division). We squeeze:
    - Lower: N ≤ ((N+1)/2)*2 (omega), so 1/2 ≤ f(N,1)/N
    - Upper: ((N+1)/2)*2 ≤ N+1 (Nat.div_mul_le_self), so f(N,1)/N ≤ (N+1)/(2N)
    Then (N+1)/(2N) = 1/2 + 1/(2N) → 1/2. -/
theorem f_t1_density :
    Filter.Tendsto (fun N => (f N 1 : ℝ) / N) Filter.atTop (nhds (1 / 2)) := by
  -- Squeeze: constant 1/2 ≤ f(N,1)/N ≤ 1/2 + 1/(2N) → 1/2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
  · -- Upper bound function: 1/2 + 1/(2N) → 1/2
    have h0 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (2 * (N : ℝ))) Filter.atTop (nhds 0) := by
      have := Filter.Tendsto.const_mul
        (show Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) from
          tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) (1 / 2 : ℝ)
      simp only [mul_zero] at this
      convert this using 1
      ext n; ring
    convert h0.const_add (1 / 2) using 1
    · ext; ring
    · ring
  · -- Lower bound: 1/2 ≤ f(N,1)/N eventually
    exact Filter.eventually_atTop.mpr ⟨2, fun N hN => by
      rw [f_t1 N (by omega : N ≥ 1)]
      rw [le_div_iff (by positivity : (0 : ℝ) < ↑N)]
      have : N ≤ ((N + 1) / 2) * 2 := by omega
      exact_mod_cast this⟩
  · -- Upper bound: f(N,1)/N ≤ 1/2 + 1/(2N) eventually
    exact Filter.eventually_atTop.mpr ⟨2, fun N hN => by
      rw [f_t1 N (by omega : N ≥ 1)]
      have hNpos : (0 : ℝ) < ↑N := by positivity
      rw [div_le_iff hNpos]
      have hdiv : ((N + 1) / 2 : ℕ) * 2 ≤ N + 1 := Nat.div_mul_le_self (N + 1) 2
      have : (((N + 1) / 2 : ℕ) : ℝ) ≤ ((N : ℝ) + 1) / 2 := by
        rw [div_le_iff (two_pos)]
        exact_mod_cast hdiv
      calc (((N + 1) / 2 : ℕ) : ℝ) ≤ ((N : ℝ) + 1) / 2 := this
        _ = (1 / 2 + 1 / (2 * ↑N)) * ↑N := by field_simp; ring
      ⟩

/- ## Part VII: Structural Observations

Additional properties connecting the non-divisibility condition to
number-theoretic structure. -/

/-- For any t-admissible set A, no element can be a double of
    another element at distance ≥ t.

    If b = 2·a, then b - a = a divides b = 2·a,
    violating the non-divisibility condition when b - a ≥ t.

    Note: The original axiom claimed this for all k ≥ 2, but that is
    incorrect. For k = 3: b - a = 2a and (2a) ∤ (3a) when a > 0.
    The condition is only violated when (k-1) | k, i.e., k = 2. -/
theorem no_far_doubles (A : Finset ℕ) (N t : ℕ)
    (hA : IsAdmissible A N t) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a < b) (hd : b - a ≥ t) :
    b ≠ 2 * a := by
  intro heq
  have hnd := hA.2 a b ha hb hab hd
  apply hnd
  -- b - a = 2*a - a = a, and a | 2*a
  rw [heq]
  show 2 * a - a ∣ 2 * a
  have : 2 * a - a = a := by omega
  rw [this]
  exact dvd_mul_left a 2

/- ## Part VIII: Summary -/

/--
**Erdős Problem #635: Summary**

PROBLEM: For A ⊆ {1,...,N} with b - a ≥ t ⟹ (b-a) ∤ b,
is |A| ≤ (1/2 + o_t(1)) · N?

STATUS: OPEN

KNOWN:
- t = 1: f(N,1) = ⌊(N+1)/2⌋ (all odd numbers, tight)
- t = 2: f(N,2) ≥ N/2 + c·log(N) (Erdős construction)
- General: f(N,t) ≥ (N+1)/2 for all t (odd numbers always work)
- Conjecture: density → 1/2 for all fixed t

The problem captures a deep connection between the additive
structure of a set (gaps between elements) and multiplicative
structure (divisibility relations).
-/
theorem erdos_635_t1_solved (N : ℕ) (hN : N ≥ 1) :
    f N 1 = (N + 1) / 2 := f_t1 N hN

/-- The t=1 case is solved; the general conjecture remains open. -/
theorem erdos_635_status :
    (∀ N : ℕ, N ≥ 1 → f N 1 = (N + 1) / 2) ∧ ErdosConjecture635 :=
  ⟨f_t1, erdos_635⟩

end Erdos635
