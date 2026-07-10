/-
  Szemerédi Regularity Lemma — OQ-04: the finiteness engine of the strong
  (Alon–Fischer–Krivelevich–Szegedy) regularity lemma.

  The strong regularity lemma (AFKS 2000) is proved by *iterating* the classical
  lemma with a decreasing tolerance: whenever the current partition fails the
  "almost-all-pairs, arbitrary-precision" requirement one refines it, and each
  such refinement increases the mean-square edge density (the partition
  `energy`) by a fixed positive amount `δ`.  Because energy is trapped in the
  interval `[0, 1]`, this can happen only finitely many times — that bounded
  loop is exactly what makes the iteration terminate and gives the qualitative
  strong regularity statement.

  This file formalizes that finiteness engine, fully machine-checked, on top of
  the gallery's own `partitionEnergy` and its bounds `partitionEnergy_nonneg`
  (Core) and `partitionEnergy_le_one` (Regularity):

  * `energy_steps_bounded`     — abstract telescoping bound: if `f n ∈ [0,1]`
    and `f` jumps by at least `δ` at each of the first `N` steps then
    `N • δ ≤ 1`.  This is the pigeonhole heart of AFKS, stated for an arbitrary
    real (`ℚ`)-valued potential.
  * `energy_iteration_count_le` — the `δ > 0` count form: `N ≤ 1 / δ`.
  * `no_infinite_energy_increments` — termination: no `[0,1]`-valued potential
    can increase by a fixed `δ > 0` at *every* step.
  * `partitionEnergy_iteration_bound` — graph instantiation: a refinement chain
    of covering, pairwise-disjoint partitions whose energy grows by `≥ δ` each
    step has length at most `1 / δ`.
  * `partitionEnergy_no_infinite_increments` — the graph termination corollary:
    the AFKS energy-increment loop must halt.

  The remaining content of OQ-04 — spelling out the two-level partition and the
  exceptional-pair accounting of the full strong lemma statement — is the open
  research goal; see `research/problems/szemeredi-regularity-oq-04`.  This file
  supplies the reusable, verified iteration bound that any such proof consumes.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularity

namespace Szemeredi.RegularityOQ04

open Szemeredi.Core Szemeredi.Regularity

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: ABSTRACT ENERGY-ITERATION TERMINATION
-- ═══════════════════════════════════════════════════════════════════

/-- **Telescoping energy bound.**  Let `f : ℕ → ℚ` be a potential confined to
    `[0, 1]` that increases by at least `δ` at each of the first `N` steps.  Then
    `N • δ ≤ 1`.  This is the finiteness engine of the AFKS iteration: only
    `⌊1/δ⌋` genuine energy-increment refinements are possible.

    No sign hypothesis on `δ` is required for this form (for `δ ≤ 0` it is
    vacuous / trivial). -/
theorem energy_steps_bounded (f : ℕ → ℚ) (N : ℕ) (δ : ℚ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1)
    (hstep : ∀ n, n < N → f n + δ ≤ f (n + 1)) :
    (N : ℚ) * δ ≤ 1 := by
  -- Telescoping: from `f 0` the potential has climbed by at least `m • δ` after
  -- `m ≤ N` steps.
  have key : ∀ m, m ≤ N → f 0 + (m : ℚ) * δ ≤ f m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ k ih =>
        intro hk1
        have hkN : k ≤ N := Nat.le_of_succ_le hk1
        have hklt : k < N := hk1
        have ihk := ih hkN
        have hs := hstep k hklt
        have hexp : ((k : ℚ) + 1) * δ = (k : ℚ) * δ + δ := by ring
        push_cast
        linarith [ihk, hs, hexp]
  have hN := key N le_rfl
  linarith [h0 0, h1 N, hN]

/-- **Sharpness of the telescoping energy bound.**  The bound `N • δ ≤ 1` of
    `energy_steps_bounded` is *tight*: for `δ = 1 / N` the potential
    `f n = min(n, N) / N` stays in `[0, 1]`, increases by *exactly* `δ` at each of
    the first `N` steps, and attains `N • δ = 1` with equality.  Hence the AFKS
    finiteness bound cannot be improved — an energy-increment iteration can genuinely
    require the full `⌊1/δ⌋` refinement steps before a regular step is forced. -/
theorem energy_steps_bounded_sharp (N : ℕ) (hN : 0 < N) :
    ∃ f : ℕ → ℚ, (∀ n, 0 ≤ f n) ∧ (∀ n, f n ≤ 1) ∧
      (∀ n, n < N → f n + (1 / (N : ℚ)) ≤ f (n + 1)) ∧
      (N : ℚ) * (1 / (N : ℚ)) = 1 := by
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  refine ⟨fun n => (min n N : ℚ) / (N : ℚ), ?_, ?_, ?_, ?_⟩
  · -- `0 ≤ f n`
    intro n; positivity
  · -- `f n ≤ 1`
    intro n
    rw [div_le_one hNQ]
    exact_mod_cast Nat.min_le_right n N
  · -- exact `δ`-increment on each of the first `N` steps
    intro n hn
    refine le_of_eq ?_
    push_cast
    rw [min_eq_left (show (n : ℚ) ≤ (N : ℚ) by exact_mod_cast hn.le),
        min_eq_left (show (n : ℚ) + 1 ≤ (N : ℚ) by exact_mod_cast hn)]
    ring
  · -- equality `N • δ = 1`
    rw [mul_one_div, div_self hNQ.ne']

/-- **Iteration-count bound.**  With a genuine positive increment `δ`, an
    `[0,1]`-valued potential can perform at most `1 / δ` increment steps. -/
theorem energy_iteration_count_le (f : ℕ → ℚ) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1)
    (hstep : ∀ n, n < N → f n + δ ≤ f (n + 1)) :
    (N : ℚ) ≤ 1 / δ := by
  have hb : (N : ℚ) * δ ≤ 1 := energy_steps_bounded f N δ h0 h1 hstep
  rw [le_div_iff₀ hδ]
  exact hb

/-- **Termination of the AFKS energy loop.**  No `[0,1]`-valued potential can
    increase by a fixed positive `δ` at *every* step: the refinement iteration
    that drives the strong regularity lemma must halt. -/
theorem no_infinite_energy_increments (f : ℕ → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) :
    ¬ (∀ n, f n + δ ≤ f (n + 1)) := by
  intro hstep
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hb : (N : ℚ) * δ ≤ 1 :=
    energy_steps_bounded f N δ h0 h1 (fun n _ => hstep n)
  rw [div_lt_iff₀ hδ] at hN
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART II: INSTANTIATION ON PARTITION ENERGY
-- ═══════════════════════════════════════════════════════════════════

/-- **Graph-theoretic iteration bound.**  Let `parts : ℕ → Finset (Finset V)` be
    a sequence of partitions of `V` — each covering and pairwise disjoint — whose
    `partitionEnergy` grows by at least `δ > 0` at each of the first `N` steps.
    Then `N ≤ 1 / δ`.

    This is the concrete finiteness bound the AFKS iteration relies on: the
    energy bounds `partitionEnergy_nonneg` and `partitionEnergy_le_one` confine
    the potential to `[0, 1]`, so only finitely many energy-increment refinements
    can occur. -/
theorem partitionEnergy_iteration_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hstep : ∀ n, n < N →
      partitionEnergy G (parts n) + δ ≤ partitionEnergy G (parts (n + 1))) :
    (N : ℚ) ≤ 1 / δ := by
  refine energy_iteration_count_le
    (fun n => partitionEnergy G (parts n)) N δ hδ ?_ ?_ hstep
  · intro n; exact partitionEnergy_nonneg G (parts n)
  · intro n; exact partitionEnergy_le_one G (parts n) (hcover n) (hdisjoint n)

/-- **Termination of the graph energy loop.**  A refinement sequence of covering,
    pairwise-disjoint partitions cannot increase `partitionEnergy` by a fixed
    `δ > 0` at every step — the AFKS refinement iteration terminates. -/
theorem partitionEnergy_no_infinite_increments
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (δ : ℚ) (hδ : 0 < δ)
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q) :
    ¬ (∀ n,
      partitionEnergy G (parts n) + δ ≤ partitionEnergy G (parts (n + 1))) := by
  apply no_infinite_energy_increments (fun n => partitionEnergy G (parts n)) δ hδ
  · intro n; exact partitionEnergy_nonneg G (parts n)
  · intro n; exact partitionEnergy_le_one G (parts n) (hcover n) (hdisjoint n)

-- ═══════════════════════════════════════════════════════════════════
-- PART III: A REGULAR (NON-INCREMENT) STEP IS REACHED WITHIN THE BOUND
-- ═══════════════════════════════════════════════════════════════════

/-- **A non-increment step is reached within any horizon `N > 1/δ`.**  The
    contrapositive *existence* form of `energy_iteration_count_le`: an
    `[0,1]`-valued potential admits at most `1/δ` genuine `δ`-increments, so any
    window of `N > 1/δ` steps must contain a step `n < N` at which the potential
    fails to climb by `δ`.  This is the abstract "a regular step is reached in
    `O(1/δ)` steps" statement that drives AFKS termination — the positive
    counterpart of `no_infinite_energy_increments`, quantified with an explicit
    finite horizon rather than the whole tail. -/
theorem energy_regular_step_exists (f : ℕ → ℚ) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) (hN : 1 / δ < (N : ℚ)) :
    ∃ n < N, ¬ (f n + δ ≤ f (n + 1)) := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ n < N, f n + δ ≤ f (n+1)` — every step increments, so `N ≤ 1/δ`.
  have hb : (N : ℚ) ≤ 1 / δ := energy_iteration_count_le f N δ hδ h0 h1 hcon
  linarith

/-- **Graph instantiation: a regular refinement step is reached within the bound.**
    Within any horizon `N > 1/δ`, a sequence of covering, pairwise-disjoint
    partitions contains a step `n < N` at which `partitionEnergy` fails to climb by
    `δ`.  Concretely: the AFKS energy-increment iteration reaches a non-increment
    ("regular") refinement in at most `⌈1/δ⌉` steps — the finite-horizon existence
    form of `partitionEnergy_no_infinite_increments`. -/
theorem partitionEnergy_regular_step_exists
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hN : 1 / δ < (N : ℚ)) :
    ∃ n < N,
      ¬ (partitionEnergy G (parts n) + δ ≤ partitionEnergy G (parts (n + 1))) := by
  refine energy_regular_step_exists
    (fun n => partitionEnergy G (parts n)) N δ hδ ?_ ?_ hN
  · intro n; exact partitionEnergy_nonneg G (parts n)
  · intro n; exact partitionEnergy_le_one G (parts n) (hcover n) (hdisjoint n)

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: EXPLICIT INTEGER TERMINATION HORIZON  ⌊1/δ⌋₊
-- ═══════════════════════════════════════════════════════════════════

/-- **A regular step occurs by time `⌊1/δ⌋₊`.**  Sharpening
    `energy_regular_step_exists` from "some horizon `N > 1/δ`" to a *concrete
    integer* bound: an `[0,1]`-valued potential fails to climb by `δ` at some step
    `n ≤ ⌊1/δ⌋₊`.  This pins the abstract `O(1/δ)` termination time of the AFKS
    iteration to an explicit natural number, obtained by instantiating the horizon
    at `N = ⌊1/δ⌋₊ + 1 > 1/δ` (`Nat.lt_floor_add_one`). -/
theorem energy_regular_step_exists_floor (f : ℕ → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) :
    ∃ n ≤ ⌊1 / δ⌋₊, ¬ (f n + δ ≤ f (n + 1)) := by
  have hN : 1 / δ < ((⌊1 / δ⌋₊ + 1 : ℕ) : ℚ) := by
    push_cast
    exact Nat.lt_floor_add_one (1 / δ)
  obtain ⟨n, hn, hstep⟩ :=
    energy_regular_step_exists f (⌊1 / δ⌋₊ + 1) δ hδ h0 h1 hN
  exact ⟨n, by omega, hstep⟩

/-- **Graph instantiation: a regular refinement step occurs by time `⌊1/δ⌋₊`.**
    The concrete-integer counterpart of `partitionEnergy_regular_step_exists`: a
    sequence of covering, pairwise-disjoint partitions reaches a non-increment
    ("regular") step `n ≤ ⌊1/δ⌋₊` — the explicit `⌈1/δ⌉`-many-steps termination
    bound for the AFKS energy-increment iteration, with no free horizon parameter. -/
theorem partitionEnergy_regular_step_exists_floor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (δ : ℚ) (hδ : 0 < δ)
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q) :
    ∃ n ≤ ⌊1 / δ⌋₊,
      ¬ (partitionEnergy G (parts n) + δ ≤ partitionEnergy G (parts (n + 1))) := by
  refine energy_regular_step_exists_floor
    (fun n => partitionEnergy G (parts n)) δ hδ ?_ ?_
  · intro n; exact partitionEnergy_nonneg G (parts n)
  · intro n; exact partitionEnergy_le_one G (parts n) (hcover n) (hdisjoint n)

-- ═══════════════════════════════════════════════════════════════════
-- PART V: THE INCREMENT (IRREGULAR) STEPS ARE GLOBALLY RARE
-- ═══════════════════════════════════════════════════════════════════

/-  Parts I–IV bound the *first* non-increment step: within any window of
    `N > 1/δ` steps at least one is regular.  But for the AFKS iteration the
    potential is *monotone* (a refinement never decreases the energy), and that
    extra structure upgrades "one regular step exists" to the far stronger
    statement that the increment steps are **globally rare**: only `⌊1/δ⌋` of
    them can ever occur, across the whole run, no matter how long.  Hence in any
    window of `N` steps at least `N − 1/δ` are regular — asymptotically *all*
    refinements are already regular, and the irregular ones are a bounded
    exceptional set.  This is the quantitative heart of why the strong lemma's
    partition is "almost everywhere regular". -/

/-- **The increment steps carry bounded total weight.**  For a *monotone*
    `[0,1]`-valued potential `f`, the set of steps `n < N` at which `f` genuinely
    climbs by `≥ δ` satisfies `card • δ ≤ 1`.  Unlike `energy_steps_bounded`
    (which assumes *every* step increments), here non-increment steps are
    allowed: monotonicity ensures they never subtract from the telescoped total
    `f N − f 0 ≤ 1`, so the δ-increment steps alone are pinned in number
    regardless of how large the window `N` is. -/
theorem energy_increment_steps_card_bound (f : ℕ → ℚ) (N : ℕ) (δ : ℚ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) (hmono : ∀ n, f n ≤ f (n + 1)) :
    (((Finset.range N).filter (fun n => f n + δ ≤ f (n + 1))).card : ℚ) * δ ≤ 1 := by
  set S := (Finset.range N).filter (fun n => f n + δ ≤ f (n + 1)) with hS
  -- Telescoping over the whole window.
  have htel : ∑ n ∈ Finset.range N, (f (n + 1) - f n) = f N - f 0 :=
    Finset.sum_range_sub f N
  -- Restricting to `S` only drops nonnegative (monotone) terms.
  have hsub : ∑ n ∈ S, (f (n + 1) - f n)
      ≤ ∑ n ∈ Finset.range N, (f (n + 1) - f n) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _; linarith [hmono i]
  -- Every increment term is `≥ δ`, so their sum dominates `card • δ`.
  have hlow : (S.card : ℚ) * δ ≤ ∑ n ∈ S, (f (n + 1) - f n) := by
    have hcmp : ∑ _n ∈ S, δ ≤ ∑ n ∈ S, (f (n + 1) - f n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hfn : f n + δ ≤ f (n + 1) := (Finset.mem_filter.mp hn).2
      linarith
    simpa [Finset.sum_const, nsmul_eq_mul] using hcmp
  have hchain : (S.card : ℚ) * δ ≤ f N - f 0 := by
    calc (S.card : ℚ) * δ ≤ ∑ n ∈ S, (f (n + 1) - f n) := hlow
      _ ≤ ∑ n ∈ Finset.range N, (f (n + 1) - f n) := hsub
      _ = f N - f 0 := htel
  linarith [h0 0, h1 N]

/-- **At most `1/δ` increment steps in total.**  The count form of
    `energy_increment_steps_card_bound`: a monotone `[0,1]`-valued potential has
    at most `⌊1/δ⌋` steps at which it climbs by `≥ δ`, in *any* window `[0, N)`
    — the number is independent of `N`. -/
theorem energy_increment_count_le (f : ℕ → ℚ) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) (hmono : ∀ n, f n ≤ f (n + 1)) :
    (((Finset.range N).filter (fun n => f n + δ ≤ f (n + 1))).card : ℚ) ≤ 1 / δ := by
  rw [le_div_iff₀ hδ]
  exact energy_increment_steps_card_bound f N δ h0 h1 hmono

/-- **The regular steps are the overwhelming majority.**  For a monotone
    `[0,1]`-valued potential, at least `N − 1/δ` of the first `N` steps are
    *regular* (non-increment).  Since the deficit `1/δ` is a fixed constant, the
    fraction of regular steps tends to `1` as `N → ∞`: the AFKS energy-increment
    iteration is regular at all but a bounded exceptional set of times. -/
theorem energy_regular_steps_card_ge (f : ℕ → ℚ) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) (hmono : ∀ n, f n ≤ f (n + 1)) :
    (N : ℚ) - 1 / δ ≤
      (((Finset.range N).filter (fun n => ¬ (f n + δ ≤ f (n + 1)))).card : ℚ) := by
  have hpart :
      ((Finset.range N).filter (fun n => f n + δ ≤ f (n + 1))).card
      + ((Finset.range N).filter (fun n => ¬ (f n + δ ≤ f (n + 1)))).card
      = (Finset.range N).card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  rw [Finset.card_range] at hpart
  have hcast :
      (((Finset.range N).filter (fun n => f n + δ ≤ f (n + 1))).card : ℚ)
      + (((Finset.range N).filter (fun n => ¬ (f n + δ ≤ f (n + 1)))).card : ℚ)
      = (N : ℚ) := by exact_mod_cast hpart
  have hinc := energy_increment_count_le f N δ hδ h0 h1 hmono
  linarith

/-- **Graph instantiation: at most `1/δ` energy-increment refinements in total.**
    A sequence of covering, pairwise-disjoint partitions whose `partitionEnergy`
    is *monotone* (each refinement never decreases it) has at most `⌊1/δ⌋` steps
    `n < N` at which the energy climbs by `≥ δ`, independent of the window `N`.
    The monotonicity hypothesis is exactly refinement-monotonicity of
    `partitionEnergy`, which holds along any AFKS refinement chain. -/
theorem partitionEnergy_increment_count_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hmono : ∀ n,
      partitionEnergy G (parts n) ≤ partitionEnergy G (parts (n + 1))) :
    (((Finset.range N).filter (fun n =>
        partitionEnergy G (parts n) + δ ≤ partitionEnergy G (parts (n + 1)))).card
      : ℚ) ≤ 1 / δ := by
  refine energy_increment_count_le
    (fun n => partitionEnergy G (parts n)) N δ hδ ?_ ?_ hmono
  · intro n; exact partitionEnergy_nonneg G (parts n)
  · intro n; exact partitionEnergy_le_one G (parts n) (hcover n) (hdisjoint n)

/-- **Graph instantiation: almost every refinement step is regular.**  Along a
    monotone AFKS refinement chain, at least `N − 1/δ` of the first `N` steps are
    *regular* (non-increment).  The exceptional (energy-increment, "irregular")
    steps form a set of bounded size `⌊1/δ⌋`, so as `N → ∞` the regular steps are
    an overwhelming majority — the quantitative form of "the strong regularity
    partition is almost everywhere regular". -/
theorem partitionEnergy_regular_steps_card_ge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hmono : ∀ n,
      partitionEnergy G (parts n) ≤ partitionEnergy G (parts (n + 1))) :
    (N : ℚ) - 1 / δ ≤
      (((Finset.range N).filter (fun n =>
        ¬ (partitionEnergy G (parts n) + δ ≤ partitionEnergy G (parts (n + 1))))).card
      : ℚ) := by
  refine energy_regular_steps_card_ge
    (fun n => partitionEnergy G (parts n)) N δ hδ ?_ ?_ hmono
  · intro n; exact partitionEnergy_nonneg G (parts n)
  · intro n; exact partitionEnergy_le_one G (parts n) (hcover n) (hdisjoint n)

/-! ## Part VI: the increment count as an explicit natural number `⌊1/δ⌋₊`

`energy_increment_count_le` bounds the increment-step count by the *rational* `1/δ`.
Since the count is a natural number, it is in fact bounded by the integer `⌊1/δ⌋₊`.
This is the increment-count analogue of the Part IV horizon sharpening
`energy_regular_step_exists_floor`, pinning the exceptional-set size to a concrete
natural number. -/

/-- **At most `⌊1/δ⌋₊` increment steps (integer bound).**  Sharpens
    `energy_increment_count_le` from the rational bound `1/δ` to the natural number
    `⌊1/δ⌋₊`: a monotone `[0,1]`-valued potential has at most `⌊1/δ⌋₊` steps at which
    it climbs by `≥ δ`, in *any* window `[0, N)`. -/
theorem energy_increment_count_le_floor (f : ℕ → ℚ) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) (hmono : ∀ n, f n ≤ f (n + 1)) :
    ((Finset.range N).filter (fun n => f n + δ ≤ f (n + 1))).card ≤ ⌊1 / δ⌋₊ := by
  apply Nat.le_floor
  exact_mod_cast energy_increment_count_le f N δ hδ h0 h1 hmono

/-- **Graph instantiation: at most `⌊1/δ⌋₊` energy-increment refinements (integer
    bound).**  Along a monotone AFKS refinement chain, the number of window-`[0,N)`
    steps at which `partitionEnergy` climbs by `≥ δ` is at most the explicit natural
    number `⌊1/δ⌋₊`, independent of `N`. -/
theorem partitionEnergy_increment_count_le_floor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hmono : ∀ n,
      partitionEnergy G (parts n) ≤ partitionEnergy G (parts (n + 1))) :
    ((Finset.range N).filter (fun n =>
        partitionEnergy G (parts n) + δ ≤ partitionEnergy G (parts (n + 1)))).card
      ≤ ⌊1 / δ⌋₊ := by
  apply Nat.le_floor
  exact_mod_cast partitionEnergy_increment_count_le G parts N δ hδ hcover hdisjoint hmono

/-- **At least `N − ⌊1/δ⌋₊` regular steps (integer bound).**  The integer/`ℕ`
    sharpening of the rational `energy_regular_steps_card_ge`: since the increment
    steps number at most `⌊1/δ⌋₊` (`energy_increment_count_le_floor`) and the increment
    and regular steps partition the window `[0, N)`, at least `N − ⌊1/δ⌋₊` of the first
    `N` steps of a monotone `[0,1]`-valued potential are *regular* (non-increment).
    Stated with truncated `ℕ` subtraction, so no `1/δ ≤ N` side condition is required —
    the complement of the Part VI increment-count floor bound. -/
theorem energy_regular_steps_card_ge_floor (f : ℕ → ℚ) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) (hmono : ∀ n, f n ≤ f (n + 1)) :
    N - ⌊1 / δ⌋₊ ≤
      ((Finset.range N).filter (fun n => ¬ (f n + δ ≤ f (n + 1)))).card := by
  have hpart :
      ((Finset.range N).filter (fun n => f n + δ ≤ f (n + 1))).card
      + ((Finset.range N).filter (fun n => ¬ (f n + δ ≤ f (n + 1)))).card = N := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.range N) (p := fun n => f n + δ ≤ f (n + 1))
    rwa [Finset.card_range] at h
  have hinc := energy_increment_count_le_floor f N δ hδ h0 h1 hmono
  omega

/-- **Graph instantiation: at least `N − ⌊1/δ⌋₊` regular refinement steps (integer
    bound).**  Along a monotone AFKS refinement chain, at least `N − ⌊1/δ⌋₊` of the
    first `N` steps are regular (do not raise `partitionEnergy` by `≥ δ`).  The `ℕ`
    sharpening of `partitionEnergy_regular_steps_card_ge`, delegating to the general
    `energy_regular_steps_card_ge_floor` with `f := partitionEnergy G (parts ·)`. -/
theorem partitionEnergy_regular_steps_card_ge_floor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hmono : ∀ n,
      partitionEnergy G (parts n) ≤ partitionEnergy G (parts (n + 1))) :
    N - ⌊1 / δ⌋₊ ≤
      ((Finset.range N).filter (fun n =>
        ¬ (partitionEnergy G (parts n) + δ ≤ partitionEnergy G (parts (n + 1))))).card := by
  refine energy_regular_steps_card_ge_floor
    (fun n => partitionEnergy G (parts n)) N δ hδ ?_ ?_ hmono
  · intro n; exact partitionEnergy_nonneg G (parts n)
  · intro n; exact partitionEnergy_le_one G (parts n) (hcover n) (hdisjoint n)

/-- **Refinement-depth bound: an all-increment chain has length `≤ ⌊1/δ⌋₊`.**  If a
    monotone `[0,1]`-valued potential climbs by `≥ δ` at *every* one of the first `N`
    steps (`hall`), then `N ≤ ⌊1/δ⌋₊`.  This is the contrapositive "termination"
    reading of `energy_regular_step_exists_floor`: since the increment set is then all
    of `[0, N)`, its cardinality `N` is bounded by `energy_increment_count_le_floor`.
    It is the explicit cap on how deep an AFKS energy-increment refinement chain can
    run — the O(1/δ) iteration depth at the heart of the strong-regularity argument,
    stated directly on the chain length rather than as an existence of one regular
    step. -/
theorem energy_all_increment_length_le (f : ℕ → ℚ) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) (hmono : ∀ n, f n ≤ f (n + 1))
    (hall : ∀ n < N, f n + δ ≤ f (n + 1)) :
    N ≤ ⌊1 / δ⌋₊ := by
  have hfilter :
      (Finset.range N).filter (fun n => f n + δ ≤ f (n + 1)) = Finset.range N :=
    Finset.filter_true_of_mem (fun n hn => hall n (Finset.mem_range.mp hn))
  have h := energy_increment_count_le_floor f N δ hδ h0 h1 hmono
  rwa [hfilter, Finset.card_range] at h

/-- **Graph instantiation: an all-increment AFKS refinement chain has depth `≤ ⌊1/δ⌋₊`.**
    If every one of the first `N` refinement steps raises `partitionEnergy` by `≥ δ`,
    then `N ≤ ⌊1/δ⌋₊`.  The explicit termination-depth cap on a strictly energy-climbing
    refinement chain: no monotone chain can climb by `δ` more than `⌊1/δ⌋₊` times before
    hitting the `[0,1]` energy ceiling, so the AFKS iteration halts within `⌊1/δ⌋₊`
    steps. -/
theorem partitionEnergy_all_increment_length_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hmono : ∀ n,
      partitionEnergy G (parts n) ≤ partitionEnergy G (parts (n + 1)))
    (hall : ∀ n < N,
      partitionEnergy G (parts n) + δ ≤ partitionEnergy G (parts (n + 1))) :
    N ≤ ⌊1 / δ⌋₊ := by
  have hfilter :
      (Finset.range N).filter (fun n =>
        partitionEnergy G (parts n) + δ ≤ partitionEnergy G (parts (n + 1)))
        = Finset.range N :=
    Finset.filter_true_of_mem (fun n hn => hall n (Finset.mem_range.mp hn))
  have h := partitionEnergy_increment_count_le_floor G parts N δ hδ hcover hdisjoint hmono
  rwa [hfilter, Finset.card_range] at h

-- ═══════════════════════════════════════════════════════════════════
-- PART III: THE VARIANCE ATOM (energy-increment lower bound)
-- ═══════════════════════════════════════════════════════════════════

/-- **Weighted-variance identity.**  For weights `w` and values `x` on a finite
    index set `s`, whenever `μ` is the weighted mean (`∑ wᵢxᵢ = (∑ wᵢ)·μ`),
    `∑ wᵢ(xᵢ − μ)² = (∑ wᵢxᵢ²) − (∑ wᵢ)·μ²`.  The König/Huygens decomposition,
    stated multiplicatively so no division by the total weight is needed. -/
theorem weighted_variance_eq {ι : Type*} (s : Finset ι) (w x : ι → ℚ) (μ : ℚ)
    (hmean : ∑ i ∈ s, w i * x i = (∑ i ∈ s, w i) * μ) :
    ∑ i ∈ s, w i * (x i - μ) ^ 2
      = (∑ i ∈ s, w i * x i ^ 2) - (∑ i ∈ s, w i) * μ ^ 2 := by
  have hcong : ∑ i ∈ s, w i * (x i - μ) ^ 2
      = ∑ i ∈ s, (w i * x i ^ 2 - 2 * μ * (w i * x i) + μ ^ 2 * w i) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [hcong, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hmean]
  ring

/-- **The variance atom: a single deviating cell forces a positive second moment.**
    Weighted values with nonnegative weights and weighted mean `μ` have their
    weighted second moment about `μ` bounded below by the single-cell contribution:
    if one index `j` deviates from the mean by at least `d` (`d² ≤ (xⱼ − μ)²`), then
    `wⱼ·d² ≤ (∑ wᵢxᵢ²) − (∑ wᵢ)·μ²`.

    This is the abstract engine behind the AFKS *energy-increment step*: when a
    refinement splits a part into sub-cells whose edge densities deviate from the
    part's mean density by a defect `d`, the mean-square density (partition energy)
    rises by at least the deviating cell's weighted square defect `wⱼ·d²` — the
    positive `δ` that `energy_steps_bounded` then caps in number.  Combined with the
    `[0,1]` energy trap it yields the finite iteration; the quantitative `d = d(ε)`
    from irregularity is the remaining analytic input. -/
theorem weighted_variance_atom_bound {ι : Type*} (s : Finset ι) (w x : ι → ℚ) (μ d : ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmean : ∑ i ∈ s, w i * x i = (∑ i ∈ s, w i) * μ)
    (j : ι) (hj : j ∈ s) (hd : d ^ 2 ≤ (x j - μ) ^ 2) :
    w j * d ^ 2 ≤ (∑ i ∈ s, w i * x i ^ 2) - (∑ i ∈ s, w i) * μ ^ 2 := by
  rw [← weighted_variance_eq s w x μ hmean]
  have hterm_nonneg : ∀ i ∈ s, 0 ≤ w i * (x i - μ) ^ 2 :=
    fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hle_sum : w j * (x j - μ) ^ 2 ≤ ∑ i ∈ s, w i * (x i - μ) ^ 2 :=
    Finset.single_le_sum hterm_nonneg hj
  have hatom : w j * d ^ 2 ≤ w j * (x j - μ) ^ 2 :=
    mul_le_mul_of_nonneg_left hd (hw j hj)
  linarith [hle_sum, hatom]

end Szemeredi.RegularityOQ04
