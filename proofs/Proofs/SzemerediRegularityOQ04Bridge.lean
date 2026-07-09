/-
  Szemerédi Regularity Lemma — OQ-04: connecting the `pairEnergy` refinement
  machinery to the gallery's `partitionEnergy`.

  The companion file `SzemerediRegularityOQ04Energy` builds a normalized
  per-ordered-pair energy `pairEnergy G A B = (|A||B|/n²)·d(A,B)²` and proves its
  refinement behaviour (`pairEnergy_split_mono`, `pairEnergy_split_gain`,
  `pairEnergy_row_split_mono`).  Its docstring asserts — but never proves — that
  *summing* `pairEnergy` over all ordered pairs of parts reproduces
  `partitionEnergy`.  Without that bridge the whole `pairEnergy` layer is
  disconnected from the actual gallery energy, so none of its monotonicity
  content transfers.

  This file supplies the missing bridge and cashes it out, fully machine-checked:

  * `partitionEnergy_eq_sum_pairEnergy` — the bridge: `partitionEnergy G parts`
    is exactly `Σ_{(P,Q) ∈ parts ×ˢ parts} pairEnergy G P Q`, unconditionally
    (the `n = 0` degenerate case is handled because every `pairEnergy` term
    carries the same vanishing `1/n²` weight).
  * `pairEnergy_comm` — symmetry `pairEnergy G A B = pairEnergy G B A`, via the
    gallery's `edgeDensity_symm`.
  * `pairEnergy_split_mono_right` — the second-argument (B-side) form of
    `pairEnergy_split_mono`.
  * `partitionEnergy_single_split_mono` — **genuine refinement monotonicity of
    the gallery energy**: replacing a part `A₁ ∪ A₂` by its two disjoint pieces
    never decreases `partitionEnergy`.  This is the "splitting a part never
    decreases energy" fact stated in the `partitionEnergy` docstring but not
    previously proved for the actual refinement operation (the existing
    `partitionEnergy_mono` is only monotone under *set inclusion* of the family,
    which does not model a refinement — a refinement removes `A₁ ∪ A₂` and adds
    `A₁, A₂`).  The proof decomposes the ordered-pair sum into the diagonal, row,
    and column blocks and applies the `pairEnergy` split lemmas to each.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Energy
import Proofs.SzemerediRegularityOQ04
import Proofs.SzemerediRegularityOQ01

namespace Szemeredi.RegularityOQ04Bridge

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE BRIDGE — partitionEnergy IS THE SUM OF pairEnergy
-- ═══════════════════════════════════════════════════════════════════

/-- **Bridge lemma.**  The gallery's `partitionEnergy G parts` is exactly the sum
    of the normalized `pairEnergy` contributions over all ordered pairs of parts.
    This holds unconditionally: in the degenerate `n = |V| = 0` case both sides
    vanish, since every `pairEnergy` term carries the common `1/n²` factor. -/
theorem partitionEnergy_eq_sum_pairEnergy (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) :
    partitionEnergy G parts =
      (parts.product parts).sum (fun pq => pairEnergy G pq.1 pq.2) := by
  unfold partitionEnergy pairEnergy
  by_cases hn : (Fintype.card V : ℚ) = 0
  · simp only [if_pos hn]
    symm
    apply Finset.sum_eq_zero
    intro pq _
    simp [hn]
  · simp only [if_neg hn]

/-- The bridge in nested-double-sum form, convenient for block decompositions. -/
private theorem partitionEnergy_eq_double_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) :
    partitionEnergy G parts =
      parts.sum (fun P => parts.sum (fun Q => pairEnergy G P Q)) := by
  rw [partitionEnergy_eq_sum_pairEnergy,
    show parts.product parts = parts ×ˢ parts from rfl, Finset.sum_product]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: SYMMETRY AND THE SECOND-ARGUMENT SPLIT
-- ═══════════════════════════════════════════════════════════════════

/-- **Symmetry of pair energy.**  `pairEnergy G A B = pairEnergy G B A`, an
    immediate consequence of `edgeDensity_comm` and `|A||B| = |B||A|`. -/
theorem pairEnergy_comm (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    pairEnergy G A B = pairEnergy G B A := by
  unfold pairEnergy
  rw [Szemeredi.Regularity.OQ01.edgeDensity_comm G A B]
  ring

/-- **Second-argument refinement monotonicity.**  Splitting the `B`-side of a pair
    into disjoint `B₁, B₂` never decreases its normalized energy contribution.
    This is `pairEnergy_split_mono` transported through `pairEnergy_comm`. -/
theorem pairEnergy_split_mono_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B₁ B₂ : Finset V) (hB : Disjoint B₁ B₂) :
    pairEnergy G A (B₁ ∪ B₂) ≤ pairEnergy G A B₁ + pairEnergy G A B₂ := by
  rw [pairEnergy_comm G A (B₁ ∪ B₂), pairEnergy_comm G A B₁, pairEnergy_comm G A B₂]
  exact pairEnergy_split_mono G B₁ B₂ A hB

-- ═══════════════════════════════════════════════════════════════════
-- PART III: REFINEMENT MONOTONICITY OF partitionEnergy
-- ═══════════════════════════════════════════════════════════════════

/-- **Refinement monotonicity of the gallery energy.**  Let `R` be a family of
    parts and let `A₁, A₂` be two disjoint sets, neither in `R`, whose union is
    also not in `R`.  Then refining the partition by replacing the single part
    `A₁ ∪ A₂` with its two pieces `A₁, A₂` never decreases `partitionEnergy`:

    `partitionEnergy G (insert (A₁ ∪ A₂) R) ≤ partitionEnergy G (insert A₁ (insert A₂ R))`.

    This is the exact "splitting a part never decreases energy" statement from the
    `partitionEnergy` docstring, realized for the genuine refinement operation.
    The ordered-pair sum splits into a diagonal block `(A,A)`, a row block
    `(A, R)`, a column block `(R, A)`, and the untouched `R × R` block; the three
    affected blocks are each controlled by the `pairEnergy` split lemmas. -/
theorem partitionEnergy_single_split_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A₁ A₂ : Finset V) (hdisj : Disjoint A₁ A₂)
    (hA₁R : A₁ ∉ R) (hA₂R : A₂ ∉ R) (hne : A₁ ≠ A₂) (hAR : A₁ ∪ A₂ ∉ R) :
    partitionEnergy G (insert (A₁ ∪ A₂) R) ≤
      partitionEnergy G (insert A₁ (insert A₂ R)) := by
  -- A₁ is not in the smaller inserted family either.
  have hA₁ : A₁ ∉ insert A₂ R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hne, hA₁R⟩
  -- Diagonal block: (A₁∪A₂,A₁∪A₂) ≤ the four sub-pairs.
  have h1 : pairEnergy G (A₁ ∪ A₂) (A₁ ∪ A₂) ≤
      pairEnergy G A₁ A₁ + pairEnergy G A₁ A₂ +
        pairEnergy G A₂ A₁ + pairEnergy G A₂ A₂ := by
    have a := pairEnergy_split_mono G A₁ A₂ (A₁ ∪ A₂) hdisj
    have b := pairEnergy_split_mono_right G A₁ A₁ A₂ hdisj
    have c := pairEnergy_split_mono_right G A₂ A₁ A₂ hdisj
    linarith
  -- Row block: Σ_{Q∈R} pairEnergy (A₁∪A₂) Q ≤ Σ pairEnergy A₁ Q + Σ pairEnergy A₂ Q.
  have h2 := pairEnergy_row_split_mono G A₁ A₂ hdisj R
  rw [Finset.sum_add_distrib] at h2
  -- Column block: Σ_{P∈R} pairEnergy P (A₁∪A₂) ≤ Σ pairEnergy P A₁ + Σ pairEnergy P A₂.
  have h3 : R.sum (fun P => pairEnergy G P (A₁ ∪ A₂)) ≤
      R.sum (fun P => pairEnergy G P A₁) + R.sum (fun P => pairEnergy G P A₂) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro P _
    exact pairEnergy_split_mono_right G P A₁ A₂ hdisj
  -- Expand both energies to their block decompositions and combine.
  rw [partitionEnergy_eq_double_sum, partitionEnergy_eq_double_sum]
  simp only [Finset.sum_insert hAR, Finset.sum_insert hA₁, Finset.sum_insert hA₂R,
    Finset.sum_add_distrib]
  linarith [h1, h2, h3]

/-- **Quantitative refinement increment of the gallery energy (energy-increment
    step).**  Suppose the refined part `A₁ ∪ A₂` has an irregular partner `B₀ ∈ R`:
    the two halves see densities differing by at least `δ`, i.e.
    `|d(A₁,B₀) − d(A₂,B₀)| ≥ δ`.  Then refining the partition by replacing
    `A₁ ∪ A₂` with its pieces `A₁, A₂` raises `partitionEnergy` by a *definite*
    positive amount:

    `partitionEnergy G (insert (A₁ ∪ A₂) R) + gain ≤
        partitionEnergy G (insert A₁ (insert A₂ R))`,

    where `gain = (|A₁||A₂|/(|A₁|+|A₂|))·(|B₀|/n²)·δ²`.  Every block of the
    ordered-pair sum still moves in the right direction by `pairEnergy` monotonicity;
    the row block against `R` carries the strict Cauchy–Schwarz surplus at `B₀`
    (`pairEnergy_row_split_gain`).  This is the analytic heart of the strong
    (Alon–Fischer–Krivelevich–Szegedy) regularity lemma: paired with the abstract
    `[0,1]`-potential termination bound of `SzemerediRegularityOQ04`, the fixed
    `gain > 0` forces the refinement loop to halt after at most `⌊1/gain⌋` steps. -/
theorem partitionEnergy_single_split_gain (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A₁ A₂ B₀ : Finset V) (hdisj : Disjoint A₁ A₂)
    (hA₁R : A₁ ∉ R) (hA₂R : A₂ ∉ R) (hne : A₁ ≠ A₂) (hAR : A₁ ∪ A₂ ∉ R)
    (hB₀ : B₀ ∈ R)
    (hn₁ : 0 < (A₁.card : ℚ)) (hn₂ : 0 < (A₂.card : ℚ)) (hB : 0 < (B₀.card : ℚ))
    (δ : ℚ) (hδ : 0 ≤ δ)
    (hdev : |edgeDensity G A₁ B₀ - edgeDensity G A₂ B₀| ≥ δ) :
    partitionEnergy G (insert (A₁ ∪ A₂) R) +
        (A₁.card : ℚ) * A₂.card / ((A₁.card : ℚ) + A₂.card) *
          ((B₀.card : ℚ) / (Fintype.card V : ℚ) ^ 2) * δ ^ 2 ≤
      partitionEnergy G (insert A₁ (insert A₂ R)) := by
  -- A₁ is not in the smaller inserted family either.
  have hA₁ : A₁ ∉ insert A₂ R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hne, hA₁R⟩
  -- Diagonal block: (A₁∪A₂,A₁∪A₂) ≤ the four sub-pairs (pure monotonicity).
  have h1 : pairEnergy G (A₁ ∪ A₂) (A₁ ∪ A₂) ≤
      pairEnergy G A₁ A₁ + pairEnergy G A₁ A₂ +
        pairEnergy G A₂ A₁ + pairEnergy G A₂ A₂ := by
    have a := pairEnergy_split_mono G A₁ A₂ (A₁ ∪ A₂) hdisj
    have b := pairEnergy_split_mono_right G A₁ A₁ A₂ hdisj
    have c := pairEnergy_split_mono_right G A₂ A₁ A₂ hdisj
    linarith
  -- Row block: the strict Cauchy–Schwarz surplus at the irregular partner B₀.
  have h2 := pairEnergy_row_split_gain G A₁ A₂ hdisj R B₀ hB₀ hn₁ hn₂ hB δ hδ hdev
  rw [Finset.sum_add_distrib] at h2
  -- Column block: pure monotonicity again.
  have h3 : R.sum (fun P => pairEnergy G P (A₁ ∪ A₂)) ≤
      R.sum (fun P => pairEnergy G P A₁) + R.sum (fun P => pairEnergy G P A₂) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro P _
    exact pairEnergy_split_mono_right G P A₁ A₂ hdisj
  -- Expand both energies to their block decompositions and combine.
  rw [partitionEnergy_eq_double_sum, partitionEnergy_eq_double_sum]
  simp only [Finset.sum_insert hAR, Finset.sum_insert hA₁, Finset.sum_insert hA₂R,
    Finset.sum_add_distrib]
  linarith [h1, h2, h3]

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: UNIFORM GAIN FLOOR AND THE EXPLICIT AFKS ITERATION COUNT
-- ═══════════════════════════════════════════════════════════════════

/-- **Parallel-resistance floor.**  The quantity `x·y / (x + y)` (the harmonic
    half-sum appearing as the Cauchy–Schwarz factor in the AFKS gain) is at least
    `1/2` once both `x, y ≥ 1`.  This is what lets the *size-dependent* energy
    increment be replaced by a *size-independent* floor: no matter how a part is
    split, the two nonempty halves contribute a resistance factor `≥ 1/2`.

    Proof: `x·y/(x+y) ≥ 1/2 ⟺ 2xy ≥ x + y`, and `2xy - x - y ≥ 0` follows from
    `(x-1)(y-1) ≥ 0` together with `x + y ≥ 2`. -/
theorem parallel_resistance_ge_half {x y : ℚ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (1 : ℚ) / 2 ≤ x * y / (x + y) := by
  have hxy : 0 < x + y := by linarith
  rw [le_div_iff₀ hxy]
  nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ x - 1) (by linarith : (0 : ℚ) ≤ y - 1)]

/-- **Uniform (size-independent) energy-increment step.**  This is
    `partitionEnergy_single_split_gain` with its `A`-side sizes bounded below by
    `1`: the exact, size-dependent gain
    `(|A₁||A₂|/(|A₁|+|A₂|))·(|B₀|/n²)·δ²` is floored to the clean, part-count-free
    quantity `δ² / (2n²)`.

    The two flooring steps are: the parallel-resistance factor
    `|A₁||A₂|/(|A₁|+|A₂|) ≥ 1/2` (`parallel_resistance_ge_half`, using
    `|A₁|,|A₂| ≥ 1`) and `|B₀|/n² ≥ 1/n²` (using `|B₀| ≥ 1`).  Since `B₀` is a
    subset of `V`, `1 ≤ |B₀| ≤ n` forces `n > 0`, so the degenerate weight cannot
    vanish.

    The point of the uniform floor is that a *single* `δ = ε` now yields the same
    increment at every refinement step regardless of the current part sizes — this
    is exactly the hypothesis shape the abstract `[0,1]`-potential termination
    bound requires, and it is what produces the explicit `2n²/ε²` step count
    below. -/
theorem partitionEnergy_single_split_gain_uniform (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A₁ A₂ B₀ : Finset V) (hdisj : Disjoint A₁ A₂)
    (hA₁R : A₁ ∉ R) (hA₂R : A₂ ∉ R) (hne : A₁ ≠ A₂) (hAR : A₁ ∪ A₂ ∉ R)
    (hB₀ : B₀ ∈ R)
    (hn₁ : 1 ≤ (A₁.card : ℚ)) (hn₂ : 1 ≤ (A₂.card : ℚ)) (hB : 1 ≤ (B₀.card : ℚ))
    (ε : ℚ) (hε : 0 ≤ ε)
    (hdev : |edgeDensity G A₁ B₀ - edgeDensity G A₂ B₀| ≥ ε) :
    partitionEnergy G (insert (A₁ ∪ A₂) R) +
        ε ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤
      partitionEnergy G (insert A₁ (insert A₂ R)) := by
  -- The exact size-dependent increment.
  have hgain := partitionEnergy_single_split_gain G R A₁ A₂ B₀ hdisj hA₁R hA₂R hne
    hAR hB₀ (by linarith) (by linarith) (by linarith) ε hε hdev
  -- `1 ≤ |B₀| ≤ n` gives `n > 0`.
  have hBcard : (B₀.card : ℚ) ≤ (Fintype.card V : ℚ) := by
    exact_mod_cast Finset.card_le_univ B₀
  have hnpos : 0 < (Fintype.card V : ℚ) := by linarith
  -- Parallel-resistance and `B₀`-weight floors, applied to the exact gain.
  have hres : (1 : ℚ) / 2 ≤ (A₁.card : ℚ) * A₂.card / ((A₁.card : ℚ) + A₂.card) :=
    parallel_resistance_ge_half hn₁ hn₂
  have hfloor : ε ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤
      (A₁.card : ℚ) * A₂.card / ((A₁.card : ℚ) + A₂.card) *
        ((B₀.card : ℚ) / (Fintype.card V : ℚ) ^ 2) * ε ^ 2 := by
    rw [show ε ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2)
          = (1 : ℚ) / 2 * ((1 : ℚ) / (Fintype.card V : ℚ) ^ 2) * ε ^ 2 from by ring]
    gcongr
  linarith [hgain, hfloor]

/-- **Explicit AFKS iteration count (energy-increment finiteness).**  Let
    `parts : ℕ → Finset (Finset V)` be a sequence of covering, pairwise-disjoint
    partitions whose `partitionEnergy` climbs by at least the *uniform* floor
    `ε² / (2n²)` at each of the first `N` refinement steps.  Then

    `N ≤ 2n² / ε²`.

    Combined with `partitionEnergy_single_split_gain_uniform` — which certifies
    that one irregular-partner split *does* realize that floor — this is the
    complete tower-free finiteness statement behind the strong (AFKS) regularity
    lemma: a graph on `n` vertices admits at most `2n²/ε²` genuine energy-increment
    refinements before every relevant pair is `ε`-regular.  It is a thin corollary
    of the abstract `[0,1]`-potential bound `partitionEnergy_iteration_bound`, but
    it is the corollary that pins the count to an explicit polynomial in `n` and
    `1/ε` rather than the opaque `1/δ` of the abstract engine. -/
theorem afks_energy_iteration_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (ε : ℚ) (hε : 0 < ε)
    (hcard : 0 < (Fintype.card V : ℚ))
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hstep : ∀ n, n < N →
      partitionEnergy G (parts n) + ε ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤
        partitionEnergy G (parts (n + 1))) :
    (N : ℚ) ≤ 2 * (Fintype.card V : ℚ) ^ 2 / ε ^ 2 := by
  have hδ : 0 < ε ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) :=
    div_pos (pow_pos hε 2) (mul_pos (by norm_num) (pow_pos hcard 2))
  have hbound := Szemeredi.RegularityOQ04.partitionEnergy_iteration_bound G parts N
    (ε ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2)) hδ hcover hdisjoint hstep
  rwa [one_div_div] at hbound

-- ═══════════════════════════════════════════════════════════════════
-- PART V: FROM AN IRREGULARITY WITNESS TO THE TWO-HALVES DEVIATION
-- ═══════════════════════════════════════════════════════════════════

/-- **Sub-pair deviation dominated by the two-halves deviation.**  Split a part
    `A = A₁ ∪ A₂` (disjoint, nonempty) against a fixed nonempty partner `B`.  The
    density deviation of one half `A₁` from the *whole* part `A` is never larger
    than the deviation *between the two halves*:

    `|d(A₁,B) − d(A₁∪A₂,B)| ≤ |d(A₁,B) − d(A₂,B)|`.

    Reason: `edgeDensity_union_mul` makes `d(A₁∪A₂,B)` the `|A₁|,|A₂|`-weighted
    average of `d(A₁,B)` and `d(A₂,B)`, so
    `d(A₁,B) − d(A,B) = (|A₂|/(|A₁|+|A₂|))·(d(A₁,B) − d(A₂,B))`, and the weight
    `|A₂|/(|A₁|+|A₂|) ≤ 1`.

    This is the missing bridge that converts an **ε-irregularity witness** — a
    subset `A' ⊆ A` whose density against `B` deviates from `d(A,B)` by `≥ ε`
    (`exists_irregular_witness`, in the one-sided form where the partner `B` is
    kept whole) — into the *two-halves* deviation hypothesis `hdev` consumed by
    `partitionEnergy_single_split_gain_uniform`.  Taking `A₂ = A \ A'` realizes
    the split. -/
theorem edgeDensity_split_deviation_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hA : Disjoint A₁ A₂)
    (hAcard : 0 < ((A₁ ∪ A₂).card : ℚ)) (hBcard : 0 < (B.card : ℚ)) :
    |edgeDensity G A₁ B - edgeDensity G (A₁ ∪ A₂) B| ≤
      |edgeDensity G A₁ B - edgeDensity G A₂ B| := by
  set c1 : ℚ := (A₁.card : ℚ) with hc1
  set c2 : ℚ := (A₂.card : ℚ) with hc2
  set b : ℚ := (B.card : ℚ) with hb
  set d1 : ℚ := edgeDensity G A₁ B with hd1
  set d2 : ℚ := edgeDensity G A₂ B with hd2
  set dU : ℚ := edgeDensity G (A₁ ∪ A₂) B with hdU
  have hcu : ((A₁ ∪ A₂).card : ℚ) = c1 + c2 := by
    rw [hc1, hc2]; exact_mod_cast Finset.card_union_of_disjoint hA
  have hsum_pos : 0 < c1 + c2 := by rw [← hcu]; exact hAcard
  have hc1nn : 0 ≤ c1 := by rw [hc1]; positivity
  have hc2nn : 0 ≤ c2 := by rw [hc2]; positivity
  -- Weighted-average identity, with the common `|B|` factor cancelled.
  have hmul := edgeDensity_union_mul G A₁ A₂ B hA
  rw [hcu] at hmul
  -- `hmul : (c1+c2)*b*dU = c1*b*d1 + c2*b*d2`.
  have hb' : b ≠ 0 := ne_of_gt hBcard
  have h2 : ((c1 + c2) * dU) * b = (c1 * d1 + c2 * d2) * b := by linear_combination hmul
  have hcancel : (c1 + c2) * dU = c1 * d1 + c2 * d2 := mul_right_cancel₀ hb' h2
  have key : (c1 + c2) * (d1 - dU) = c2 * (d1 - d2) := by linear_combination -hcancel
  -- Take absolute values; the weight `c2 ≤ c1+c2` gives the bound.
  have habs : (c1 + c2) * |d1 - dU| = c2 * |d1 - d2| := by
    have h := congrArg abs key
    rwa [abs_mul, abs_mul, abs_of_nonneg (le_of_lt hsum_pos),
      abs_of_nonneg hc2nn] at h
  have hfinal : (c1 + c2) * |d1 - dU| ≤ (c1 + c2) * |d1 - d2| := by
    rw [habs]; nlinarith [abs_nonneg (d1 - d2), hc1nn]
  exact le_of_mul_le_mul_left hfinal hsum_pos

/-- **Irregularity witness ⇒ uniform energy jump.**  If refining `A₁ ∪ A₂` into
    its halves produces a half `A₁` whose density against a fixed existing part
    `B₀` deviates from the *whole part's* density by at least `ε` — exactly the
    datum an ε-irregularity witness supplies (with `A₁` the witness subset `A'`,
    `A₂ = A \ A'`, and `B₀` kept whole) — then the refinement realizes the uniform
    energy floor `ε² / (2n²)`.

    Composes `edgeDensity_split_deviation_ge` (witness-vs-whole deviation ⇒
    two-halves deviation) with `partitionEnergy_single_split_gain_uniform`.  This
    is the last link that lets an *actual* irregular pair — not a hand-supplied
    two-halves gap — drive the `hstep` hypothesis of `afks_energy_iteration_count`,
    closing the loop from irregularity to the explicit `2n²/ε²` refinement bound
    on the one-sided (partner-preserving) refinement. -/
theorem partitionEnergy_subpair_split_gain_uniform (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A₁ A₂ B₀ : Finset V) (hdisj : Disjoint A₁ A₂)
    (hA₁R : A₁ ∉ R) (hA₂R : A₂ ∉ R) (hne : A₁ ≠ A₂) (hAR : A₁ ∪ A₂ ∉ R)
    (hB₀ : B₀ ∈ R)
    (hn₁ : 1 ≤ (A₁.card : ℚ)) (hn₂ : 1 ≤ (A₂.card : ℚ)) (hB : 1 ≤ (B₀.card : ℚ))
    (ε : ℚ) (hε : 0 ≤ ε)
    (hdev : |edgeDensity G A₁ B₀ - edgeDensity G (A₁ ∪ A₂) B₀| ≥ ε) :
    partitionEnergy G (insert (A₁ ∪ A₂) R) +
        ε ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤
      partitionEnergy G (insert A₁ (insert A₂ R)) := by
  have hcu : ((A₁ ∪ A₂).card : ℚ) = (A₁.card : ℚ) + A₂.card := by
    exact_mod_cast Finset.card_union_of_disjoint hdisj
  have hAcard : 0 < ((A₁ ∪ A₂).card : ℚ) := by rw [hcu]; linarith
  have hBcard : 0 < (B₀.card : ℚ) := by linarith
  have hbridge := edgeDensity_split_deviation_ge G A₁ A₂ B₀ hdisj hAcard hBcard
  have hdev2 : |edgeDensity G A₁ B₀ - edgeDensity G A₂ B₀| ≥ ε := le_trans hdev hbridge
  exact partitionEnergy_single_split_gain_uniform G R A₁ A₂ B₀ hdisj hA₁R hA₂R hne
    hAR hB₀ hn₁ hn₂ hB ε hε hdev2

end Szemeredi.RegularityOQ04Bridge
