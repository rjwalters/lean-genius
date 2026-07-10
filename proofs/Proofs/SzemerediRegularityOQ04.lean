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

end Szemeredi.RegularityOQ04
