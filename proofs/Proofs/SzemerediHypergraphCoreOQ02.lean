/-
  The Energy-Increment Engine of the Hypergraph Regularity Lemma
  Open Question OQ-02 from SzemerediHypergraphCore

  > "Prove the hypergraph regularity lemma: every k-graph admits an
  >  ε-regular partition with a bounded number of parts."

  The full Gowers (2007) / Rödl–Skokan (2004) hypergraph regularity
  lemma is a deep, multi-stage analytic theorem that is *not* in Mathlib
  and is far out of reach of a single self-contained file: it requires
  the relative-density / simplicial-complex machinery (see
  SzemerediHypergraphCoreOQ01.lean) together with a hypergraph
  Cauchy–Schwarz density-increment step.

  This file is HONEST about that gap. It does NOT claim the full lemma.
  Instead it isolates and *fully verifies* (0 sorries, 0 axioms) the
  combinatorial engine that converts a local "density/energy increment"
  into the lemma's headline guarantee — a **bounded number of parts**:

    PART I   `partitionEnergy` : weighted mean-square of cell densities,
             proven to lie in [0,1] (the bounded, monotone potential that
             every regularity proof — graph or hypergraph — increments).

    PART II  `energy_increment_bounded_steps` : if a [0,1]-valued energy
             increases by at least δ > 0 at every "irregular" step, then
             an ε-regular state is reached within ⌈1/δ⌉ steps.  This is
             the precise pigeonhole that makes the iteration terminate —
             the reason M(ε) exists and is finite.

    PART III `parts_bounded` / `hypergraph_regularity_engine` : combining
             the step bound with a per-step part-count blow-up factor f
             gives the explicit ceiling  parts ≤ parts₀ · f^⌈1/δ⌉  on the
             number of parts of the final ε-regular partition — exactly
             the "bounded number of parts" the open question asks for,
             conditional on the (documented) density-increment input.

  In Szemerédi's original graph proof and in Mathlib's
  `SzemerediRegularity`, this is exactly the bookkeeping that turns the
  Cauchy–Schwarz energy boost into the regularity lemma; the same engine
  drives the Gowers hypergraph proof.  What remains genuinely open here
  is the *analytic* input (the hypergraph density-increment inequality),
  which is stated precisely in PART IV as the remaining direction.

  References:
  - Gowers, W.T. (2007). "Hypergraph regularity and the multidimensional
    Szemerédi theorem." Annals of Mathematics 166(3), 897–946.
  - Rödl, V., Skokan, J. (2004). RSA 25(1), 1–42.
  - Szemerédi, E. (1978). "Regular partitions of graphs."
-/
import Mathlib

namespace Szemeredi.Hypergraph.OQ02

open Finset

-- ═══════════════════════════════════════════════════════════════════
-- PART I: PARTITION ENERGY  (the bounded, monotone potential)
-- ═══════════════════════════════════════════════════════════════════

/-- The **energy** (mean-square index) of a partition, indexed by a
    finite set `ι` of cells, with a probability weight `w i ≥ 0`
    (the relative mass of cell `i`, summing to 1) and a cell density
    `d i ∈ [0,1]`:

        energy = ∑ᵢ w i · (d i)²

    This is the hypergraph analogue of Szemerédi's mean-square density
    index.  Refining the partition can only increase it (Cauchy–Schwarz),
    and — as proven below — it is bounded above by 1.  Those two facts
    are what make the energy-increment iteration terminate. -/
def partitionEnergy {ι : Type*} (s : Finset ι) (w d : ι → ℚ) : ℚ :=
  ∑ i ∈ s, w i * (d i) ^ 2

/-- Energy is non-negative when the weights are non-negative. -/
theorem partitionEnergy_nonneg {ι : Type*} (s : Finset ι) (w d : ι → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ partitionEnergy s w d := by
  unfold partitionEnergy
  apply Finset.sum_nonneg
  intro i hi
  have : (0:ℚ) ≤ (d i) ^ 2 := sq_nonneg _
  exact mul_nonneg (hw i hi) this

/-- Energy is bounded above by 1 when the weights are a probability
    distribution (`w i ≥ 0`, `∑ w i = 1`) and the densities lie in
    `[0,1]` (`|d i| ≤ 1`).  This is the upper barrier the increment
    cannot cross — the source of the finiteness of `M(ε)`. -/
theorem partitionEnergy_le_one {ι : Type*} (s : Finset ι) (w d : ι → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hd : ∀ i ∈ s, |d i| ≤ 1) :
    partitionEnergy s w d ≤ 1 := by
  unfold partitionEnergy
  calc ∑ i ∈ s, w i * (d i) ^ 2
      ≤ ∑ i ∈ s, w i * 1 := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (hw i hi)
        obtain ⟨hlo, hhi⟩ := abs_le.mp (hd i hi)
        nlinarith
    _ = ∑ i ∈ s, w i := by simp
    _ = 1 := hsum

-- ═══════════════════════════════════════════════════════════════════
-- PART II: ENERGY-INCREMENT ITERATION  (the bounded-step pigeonhole)
-- ═══════════════════════════════════════════════════════════════════

/-- **Energy lower bound after `m` increment steps.**  If the energy
    increases by at least `δ` whenever the current state is irregular,
    and every state up to index `N` is irregular, then after `m ≤ N+1`
    steps the energy is at least `E 0 + m·δ`. -/
theorem energy_ge_of_steps
    (E : ℕ → ℚ) (Irregular : ℕ → Prop) (δ : ℚ) (N : ℕ)
    (hstep : ∀ n, Irregular n → E n + δ ≤ E (n + 1))
    (hirr : ∀ n ≤ N, Irregular n) :
    ∀ m ≤ N + 1, E 0 + m * δ ≤ E m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hkN : k ≤ N := by omega
      have hkstep : E k + δ ≤ E (k + 1) := hstep k (hirr k hkN)
      have hih : E 0 + k * δ ≤ E k := ih (by omega)
      have : E 0 + (k + 1 : ℕ) * δ = (E 0 + k * δ) + δ := by push_cast; ring
      rw [this]
      linarith

/-- **The energy-increment terminates in a bounded number of steps.**

    Let `E : ℕ → ℚ` be an energy that starts non-negative and never
    exceeds `1`.  Suppose that at every *irregular* state the next step
    boosts the energy by at least `δ > 0`.  Then within `⌈1/δ⌉` steps we
    reach a *regular* state (one that is not irregular).

    This is the abstract heart of every Szemerédi-type regularity lemma:
    a bounded potential that jumps by a fixed amount cannot jump forever,
    so the irregular phase must end quickly.  The bound `⌈1/δ⌉` is
    independent of the ground set — which is exactly why the number of
    parts in the regularity lemma is bounded by a function of `ε` alone. -/
theorem energy_increment_bounded_steps
    (E : ℕ → ℚ) (Irregular : ℕ → Prop) (δ : ℚ)
    (hδ : 0 < δ)
    (hE0 : 0 ≤ E 0)
    (hbound : ∀ n, E n ≤ 1)
    (hstep : ∀ n, Irregular n → E n + δ ≤ E (n + 1)) :
    ∃ n ≤ ⌈(1 : ℚ) / δ⌉₊, ¬ Irregular n := by
  by_contra h
  push_neg at h
  -- `h : ∀ n ≤ ⌈1/δ⌉₊, Irregular n`
  set N := ⌈(1 : ℚ) / δ⌉₊ with hN
  have hge : E 0 + (N + 1 : ℕ) * δ ≤ E (N + 1) :=
    energy_ge_of_steps E Irregular δ N hstep h (N + 1) (le_refl _)
  -- `N·δ ≥ 1` since `N = ⌈1/δ⌉₊ ≥ 1/δ`.
  have hceil : (1 : ℚ) / δ ≤ (N : ℚ) := by
    rw [hN]; exact Nat.le_ceil _
  have hNδ : (1 : ℚ) ≤ (N : ℚ) * δ := by
    rw [div_le_iff₀ hδ] at hceil; linarith
  have hbig : (1 : ℚ) < ((N : ℚ) + 1) * δ := by nlinarith
  have hcast : ((N + 1 : ℕ) : ℚ) = (N : ℚ) + 1 := by push_cast; ring
  rw [hcast] at hge
  have : (1 : ℚ) < E (N + 1) := by nlinarith [hE0]
  exact absurd (hbound (N + 1)) (by linarith)

-- ═══════════════════════════════════════════════════════════════════
-- PART III: BOUNDED NUMBER OF PARTS  (the headline guarantee)
-- ═══════════════════════════════════════════════════════════════════

/-- If the number of parts is multiplied by at most a factor `f` at each
    refinement step, then after `n` steps it is at most `parts₀ · fⁿ`. -/
theorem parts_le_pow
    (parts : ℕ → ℕ) (f : ℕ)
    (hf : ∀ n, parts (n + 1) ≤ parts n * f) :
    ∀ n, parts n ≤ parts 0 * f ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      calc parts (k + 1) ≤ parts k * f := hf k
        _ ≤ (parts 0 * f ^ k) * f := by
              apply Nat.mul_le_mul_right; exact ih
        _ = parts 0 * f ^ (k + 1) := by ring

/-- **The energy-increment engine of the hypergraph regularity lemma.**

    Assemble the two ingredients.  Given:
    * a bounded energy `E ∈ [0,1]` that boosts by `δ > 0` at every
      irregular step (the Cauchy–Schwarz density-increment input), and
    * a per-step part-count blow-up by at most a factor `f`,

    there is a step `n ≤ ⌈1/δ⌉` reaching an ε-**regular** partition whose
    number of parts is bounded by the explicit, ground-set-independent
    constant  `parts₀ · f^⌈1/δ⌉`.

    This is precisely the structure "every k-graph admits an ε-regular
    partition with a bounded number of parts": the bound depends only on
    the starting partition, the increment `δ = δ(ε)`, and the refinement
    factor `f = f(ε)` — never on the size of the vertex set. -/
theorem hypergraph_regularity_engine
    (E : ℕ → ℚ) (Irregular : ℕ → Prop) (parts : ℕ → ℕ) (δ : ℚ) (f : ℕ)
    (hδ : 0 < δ)
    (hE0 : 0 ≤ E 0)
    (hbound : ∀ n, E n ≤ 1)
    (hstep : ∀ n, Irregular n → E n + δ ≤ E (n + 1))
    (hf1 : 1 ≤ f)
    (hf : ∀ n, parts (n + 1) ≤ parts n * f) :
    ∃ n, ¬ Irregular n ∧ parts n ≤ parts 0 * f ^ ⌈(1 : ℚ) / δ⌉₊ := by
  obtain ⟨n, hnle, hreg⟩ :=
    energy_increment_bounded_steps E Irregular δ hδ hE0 hbound hstep
  refine ⟨n, hreg, ?_⟩
  calc parts n ≤ parts 0 * f ^ n := parts_le_pow parts f hf n
    _ ≤ parts 0 * f ^ ⌈(1 : ℚ) / δ⌉₊ := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right hf1 hnle

/-
## PART IV: What remains genuinely open (the analytic input)

The engine above is *unconditional*: it is a fully verified theorem.
What it consumes as a hypothesis (`hstep`) is the single deep analytic
fact specific to hypergraphs, which is what the full proof must supply:

  **Hypergraph density-increment (Gowers / Rödl–Skokan).**
  If a k-partite k-graph is *not* ε-regular relative to its underlying
  (k-1)-complex (in the sense of `IsGowersRegular`,
  SzemerediHypergraphCoreOQ01.lean), then there is a refinement of the
  complex, multiplying the number of parts by at most some `f(ε)`, that
  increases `partitionEnergy` by at least some `δ(ε) > 0`.

Once this Cauchy–Schwarz/martingale increment is established for the
relative `kPartiteDensity`, `hypergraph_regularity_engine` immediately
yields a Gowers ε-regular partition with at most `parts₀ · f^⌈1/δ⌉`
parts — the regularity lemma.  The increment step is the genuinely hard,
still-unformalized core (it is not in Mathlib even for the graph case in
the `partitionEnergy` formulation used here); it requires a hypergraph
counting/Cauchy–Schwarz argument over the (k-1)-skeleton and is left as
the remaining direction.

References:
- Gowers (2007), Annals 166(3); Rödl–Skokan (2004), RSA 25(1).
- Tao, T. "Szemerédi's regularity lemma via random partitions" /
  "The dichotomy between structure and randomness" (energy-increment
  exposition).
-/

end Szemeredi.Hypergraph.OQ02
