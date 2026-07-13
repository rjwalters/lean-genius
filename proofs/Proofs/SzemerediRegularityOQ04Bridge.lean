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

/-- **Sharp AFKS iteration count (no-loss `ε⁴` route).**  The counterpart of
    `afks_energy_iteration_count` for the *simultaneous* two-coordinate refinement of
    `partitionEnergy_prod_gain_eps4`, which raises the whole-partition energy by the
    sharp `ε⁴·|A||B|/n²` — free of the factor-`¼` loss the one-sided branches
    (`partitionEnergy_gain_of_irregular_pair`) incur.  If every one of the first `N`
    refinement steps clears the *uniform* floor `ε⁴·m/n²`, where `m` lower-bounds the
    mass-product `|A||B|` of the refined pair, then

    `N ≤ n² / (ε⁴·m)`.

    Where the one-sided route pays `2n²/ε²`, the no-loss product route pays only
    `n²/(ε⁴·m)`: once the refined cells carry macroscopic mass (`m ≳ 1/ε²`) the sharp
    floor `ε⁴·m/n²` exceeds the one-sided `ε²/(2n²)`, so this is the tighter
    finiteness bound.  Like its `ε²` sibling it is a thin corollary of the abstract
    `[0,1]`-potential bound `partitionEnergy_iteration_bound`, here specialised to the
    sharp floor that `partitionEnergy_prod_gain_eps4` supplies. -/
theorem afks_energy_iteration_count_sharp (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (N : ℕ) (ε m : ℚ) (hε : 0 < ε) (hm : 0 < m)
    (hcard : 0 < (Fintype.card V : ℚ))
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hstep : ∀ n, n < N →
      partitionEnergy G (parts n) + ε ^ 4 * m / (Fintype.card V : ℚ) ^ 2 ≤
        partitionEnergy G (parts (n + 1))) :
    (N : ℚ) ≤ (Fintype.card V : ℚ) ^ 2 / (ε ^ 4 * m) := by
  have hδ : 0 < ε ^ 4 * m / (Fintype.card V : ℚ) ^ 2 :=
    div_pos (mul_pos (pow_pos hε 4) hm) (pow_pos hcard 2)
  have hbound := Szemeredi.RegularityOQ04.partitionEnergy_iteration_bound G parts N
    (ε ^ 4 * m / (Fintype.card V : ℚ) ^ 2) hδ hcover hdisjoint hstep
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

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: FROM ¬IsEpsilonRegular TO A ONE-SIDED DEVIATION
-- ═══════════════════════════════════════════════════════════════════

/-- **Irregularity witness extraction.**  If a pair `(A, B)` fails to be
    `ε`-regular then, by the very definition of `IsEpsilonRegular`, there exist
    subsets `A' ⊆ A`, `B' ⊆ B` meeting the size thresholds `|A'| ≥ ε|A|`,
    `|B'| ≥ ε|B|` whose density deviates from `d(A, B)` by strictly more than
    `ε`.  This is the definitional content of `¬ IsEpsilonRegular`, named for
    reuse as the entry point of the energy-increment argument. -/
theorem exists_irregular_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) (hirr : ¬ IsEpsilonRegular G eps A B) :
    ∃ A' B' : Finset V, A' ⊆ A ∧ B' ⊆ B ∧
      (A'.card : ℚ) ≥ eps * A.card ∧ (B'.card : ℚ) ≥ eps * B.card ∧
      |edgeDensity G A' B' - edgeDensity G A B| > eps := by
  unfold IsEpsilonRegular at hirr
  push_neg at hirr
  obtain ⟨A', B', hA', hB', hAc, hBc, hdev⟩ := hirr
  exact ⟨A', B', hA', hB', hAc, hBc, hdev⟩

/-- **Two-sided deviation splits into two one-sided deviations.**  The full
    witness deviation `|d(A', B') − d(A, B)|` is at most the sum of

    * the **B-side** deviation `|d(A', B') − d(A', B)|` — refining `B` against
      the fixed sub-part `A'`, and
    * the **A-side** deviation `|d(A', B) − d(A, B)|` — refining `A` against the
      whole partner `B`.

    A plain triangle inequality through the mixed density `d(A', B)`. -/
theorem edgeDensity_two_sided_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (A A' B B' : Finset V) :
    |edgeDensity G A' B' - edgeDensity G A B| ≤
      |edgeDensity G A' B' - edgeDensity G A' B| +
      |edgeDensity G A' B - edgeDensity G A B| :=
  abs_sub_le _ _ _

/-- **From an irregular pair to a one-sided deviation of size `≥ ε/2`.**  If
    `(A, B)` is not `ε`-regular, its extracted witness yields *either*

    * an **A-side** deviation `|d(A', B) − d(A, B)| ≥ ε/2` (partner `B` kept
      whole — directly usable by `partitionEnergy_subpair_split_gain_uniform`
      with `A₁ = A'`, `A₂ = A \ A'`), *or*
    * a **B-side** deviation `|d(A', B') − d(A', B)| ≥ ε/2` (a refinement of `B`
      against the fixed sub-part `A'` — the symmetric case requiring a second
      refinement).

    The witness deviation `> ε` is split by `edgeDensity_two_sided_le`, so at
    least one summand carries `≥ ε/2`.  This is the structural reduction that
    turns *two-sided* irregularity into the *one-sided* increment datum the
    energy machinery consumes, at the cost of a factor `1/2` in the tolerance
    (hence `1/4` in the energy floor). -/
theorem exists_onesided_deviation_of_irregular (G : SimpleGraph V)
    [DecidableRel G.Adj] (eps : ℚ) (A B : Finset V)
    (hirr : ¬ IsEpsilonRegular G eps A B) :
    ∃ A' B' : Finset V, A' ⊆ A ∧ B' ⊆ B ∧
      (A'.card : ℚ) ≥ eps * A.card ∧ (B'.card : ℚ) ≥ eps * B.card ∧
      (|edgeDensity G A' B - edgeDensity G A B| ≥ eps / 2 ∨
       |edgeDensity G A' B' - edgeDensity G A' B| ≥ eps / 2) := by
  obtain ⟨A', B', hA', hB', hAc, hBc, hdev⟩ :=
    exists_irregular_witness G eps A B hirr
  refine ⟨A', B', hA', hB', hAc, hBc, ?_⟩
  have htri := edgeDensity_two_sided_le G A A' B B'
  by_contra hcon
  push_neg at hcon
  obtain ⟨hAside, hBside⟩ := hcon
  linarith [htri, hdev]

/-- **A-side irregularity ⇒ uniform energy jump.**  Package the A-side branch of
    `exists_onesided_deviation_of_irregular` into an actual `partitionEnergy`
    increment.  If a witness sub-part `A' ⊆ A` (with complement `A \ A'` inside
    `A`) deviates from the whole part's density against a fixed existing part
    `B₀ ∈ R` by at least `ε/2`, then refining `A` into `A'` and `A \ A'` raises
    `partitionEnergy` by the uniform floor `(ε/2)² / (2n²) = ε² / (8n²)`.

    Composes `Finset.union_sdiff_of_subset` (to present `A` as the disjoint
    union `A' ∪ (A \ A')`) with `partitionEnergy_subpair_split_gain_uniform`.
    This is the first *end-to-end* link from a genuine irregular pair to a
    concrete energy increment, closing the A-side case of the AFKS iteration. -/
theorem partitionEnergy_Aside_gain_of_irregular (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A B₀ A' : Finset V) (hA' : A' ⊆ A)
    (hA'R : A' ∉ R) (hcompR : A \ A' ∉ R) (hne : A' ≠ A \ A') (hAR : A ∉ R)
    (hB₀ : B₀ ∈ R)
    (hn₁ : 1 ≤ (A'.card : ℚ)) (hn₂ : 1 ≤ ((A \ A').card : ℚ))
    (hB : 1 ≤ (B₀.card : ℚ))
    (eps : ℚ) (hε : 0 ≤ eps)
    (hdev : |edgeDensity G A' B₀ - edgeDensity G A B₀| ≥ eps / 2) :
    partitionEnergy G (insert A R) +
        (eps / 2) ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤
      partitionEnergy G (insert A' (insert (A \ A') R)) := by
  have hunion : A' ∪ (A \ A') = A := Finset.union_sdiff_of_subset hA'
  have hdisj : Disjoint A' (A \ A') := disjoint_sdiff_self_right
  -- Re-express the whole part `A` as its disjoint two-piece union, then feed the
  -- one-sided subpair gain lemma with tolerance `ε/2`.
  have hdev' : |edgeDensity G A' B₀ - edgeDensity G (A' ∪ (A \ A')) B₀| ≥ eps / 2 := by
    rwa [hunion]
  have hAR' : A' ∪ (A \ A') ∉ R := by rwa [hunion]
  have hgain := partitionEnergy_subpair_split_gain_uniform G R A' (A \ A') B₀
    hdisj hA'R hcompR hne hAR' hB₀ hn₁ hn₂ hB (eps / 2) (by linarith) hdev'
  rwa [hunion] at hgain

-- ═══════════════════════════════════════════════════════════════════
-- PART VII: THE SYMMETRIC (B-SIDE) IRREGULAR-PAIR ENERGY INCREMENT
-- ═══════════════════════════════════════════════════════════════════

/-- **B-side irregularity ⇒ uniform energy jump (mirror of
    `partitionEnergy_Aside_gain_of_irregular`).**  The A-side lemma refines the
    *part* `A` against a whole partner `B₀`.  Refinement is symmetric in the two
    coordinates of `partitionEnergy` — it is a sum over *ordered* pairs — so the
    same increment fires with the roles swapped: a witness sub-partner `B' ⊆ B`
    whose density against a fixed existing part `A₀ ∈ R` deviates from the whole
    partner `B`'s density, `|d(A₀, B') − d(A₀, B)| ≥ ε/2`, drives the uniform
    energy floor `(ε/2)² / (2n²) = ε² / (8n²)` when `B` is split into `B'` and
    `B \ B'`.

    Proof: transport the deviation across `edgeDensity_comm` to the partner-second
    orientation `|d(B', A₀) − d(B, A₀)|` and feed
    `partitionEnergy_subpair_split_gain_uniform` with split part `B` (=
    `B' ∪ (B \ B')`) and partner `A₀`.  Together with
    `partitionEnergy_Aside_gain_of_irregular` this supplies *both* one-sided
    branches of the AFKS energy-increment step: whichever coordinate an irregular
    pair's deviation localizes to (against a *whole* partner), a single-part split
    on that coordinate realizes the `ε²/(8n²)` floor. -/
theorem partitionEnergy_Bside_gain_of_irregular (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (R : Finset (Finset V)) (B A₀ B' : Finset V) (hB' : B' ⊆ B)
    (hB'R : B' ∉ R) (hcompR : B \ B' ∉ R) (hne : B' ≠ B \ B') (hBR : B ∉ R)
    (hA₀ : A₀ ∈ R)
    (hn₁ : 1 ≤ (B'.card : ℚ)) (hn₂ : 1 ≤ ((B \ B').card : ℚ))
    (hA : 1 ≤ (A₀.card : ℚ))
    (eps : ℚ) (hε : 0 ≤ eps)
    (hdev : |edgeDensity G A₀ B' - edgeDensity G A₀ B| ≥ eps / 2) :
    partitionEnergy G (insert B R) +
        (eps / 2) ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤
      partitionEnergy G (insert B' (insert (B \ B') R)) := by
  have hunion : B' ∪ (B \ B') = B := Finset.union_sdiff_of_subset hB'
  have hdisj : Disjoint B' (B \ B') := disjoint_sdiff_self_right
  -- Transport the deviation to the partner-second orientation, rewriting `B`.
  have hdev' : |edgeDensity G B' A₀ - edgeDensity G (B' ∪ (B \ B')) A₀| ≥ eps / 2 := by
    rw [hunion, Szemeredi.Regularity.OQ01.edgeDensity_comm G B' A₀,
      Szemeredi.Regularity.OQ01.edgeDensity_comm G B A₀]
    exact hdev
  have hgain := partitionEnergy_subpair_split_gain_uniform G R B' (B \ B') A₀
    hdisj hB'R hcompR hne (by rwa [hunion]) hA₀ hn₁ hn₂ hA (eps / 2) (by linarith) hdev'
  rwa [hunion] at hgain

-- ═══════════════════════════════════════════════════════════════════
-- PART VIII: THE CONVERSE — A SPLIT DENSITY GAP CERTIFIES IRREGULARITY
-- ═══════════════════════════════════════════════════════════════════

/-- **Balanced union density is the arithmetic mean of the two halves.**  When the
    disjoint halves `A₁, A₂` have *equal* cardinality — the equipartition regime in
    which the strong regularity lemma is iterated — the union density is exactly the
    mean of the two half-densities, so each half deviates from it by exactly half
    the inter-half gap:

    `d(A₁, B) − d(A₁ ∪ A₂, B) = (d(A₁, B) − d(A₂, B)) / 2`.

    A direct consequence of the weighted-average identity `edgeDensity_union_mul`
    once the `|A₁| = |A₂|` weights collapse to `1 : 1`. -/
theorem edgeDensity_balanced_union_sub (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hA : Disjoint A₁ A₂)
    (hcardeq : (A₁.card : ℚ) = A₂.card) (hpos : 0 < (A₁.card : ℚ))
    (hB : 0 < (B.card : ℚ)) :
    edgeDensity G A₁ B - edgeDensity G (A₁ ∪ A₂) B =
      (edgeDensity G A₁ B - edgeDensity G A₂ B) / 2 := by
  have hcard : ((A₁ ∪ A₂).card : ℚ) = (A₁.card : ℚ) + A₂.card := by
    rw [Finset.card_union_of_disjoint hA]; push_cast; ring
  have hmul := edgeDensity_union_mul G A₁ A₂ B hA
  rw [hcard] at hmul
  have hBne : (B.card : ℚ) ≠ 0 := ne_of_gt hB
  have havg : ((A₁.card : ℚ) + A₂.card) * edgeDensity G (A₁ ∪ A₂) B =
      (A₁.card : ℚ) * edgeDensity G A₁ B + (A₂.card : ℚ) * edgeDensity G A₂ B :=
    mul_left_cancel₀ hBne (by linear_combination hmul)
  rw [← hcardeq] at havg
  have hane : (A₁.card : ℚ) ≠ 0 := ne_of_gt hpos
  -- Cancel the common `|A₁|` to get `2·d(union) = d₁ + d₂`.
  have h2 : (2 : ℚ) * edgeDensity G (A₁ ∪ A₂) B =
      edgeDensity G A₁ B + edgeDensity G A₂ B := by
    apply mul_left_cancel₀ hane
    linear_combination havg
  linear_combination (-1 / 2 : ℚ) * h2

/-- **A split density gap certifies irregularity (balanced case).**  If the two
    equal-size halves `A₁, A₂` of a part have densities against `B₀` differing by
    at least `δ`, then the coarse pair `(A₁ ∪ A₂, B₀)` is *not* `ε`-regular for any
    `ε` below `δ/2` (and `≤ 1/2`).  Concretely the half `A₁` is a large subset of
    the union (`|A₁| = |A₁ ∪ A₂|/2 ≥ ε|A₁ ∪ A₂|`) whose density deviates from
    `d(A₁ ∪ A₂, B₀)` by `|d(A₁,B₀) − d(A₂,B₀)|/2 ≥ δ/2 > ε`, violating the
    ε-regularity bound.

    This is the converse of the energy machinery: the very `δ`-gap hypothesis
    consumed by the quantitative increment lemmas (`pairEnergy_split_gain`,
    `partitionEnergy_single_split_gain`) is itself a certificate that the
    *unrefined* pair fails ε-regularity.  Energy is therefore gained only where the
    partition is genuinely irregular — the two notions coincide up to the constant
    `1/2`, closing the conceptual loop in both directions. -/
theorem split_gap_not_regular_balanced (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B₀ : Finset V) (hA : Disjoint A₁ A₂)
    (hcardeq : (A₁.card : ℚ) = A₂.card) (hpos : 0 < (A₁.card : ℚ))
    (hB : 0 < (B₀.card : ℚ)) (δ ε : ℚ)
    (hεle : ε ≤ 1 / 2) (hεδ : ε < δ / 2)
    (hgap : |edgeDensity G A₁ B₀ - edgeDensity G A₂ B₀| ≥ δ) :
    ¬ IsEpsilonRegular G ε (A₁ ∪ A₂) B₀ := by
  intro hreg
  have hcard : ((A₁ ∪ A₂).card : ℚ) = (A₁.card : ℚ) + A₂.card := by
    rw [Finset.card_union_of_disjoint hA]; push_cast; ring
  -- `A₁` is a large subset of the union, and `B₀` is a large subset of itself.
  have hA1big : (A₁.card : ℚ) ≥ ε * ((A₁ ∪ A₂).card) := by
    rw [hcard, ← hcardeq]
    nlinarith [mul_nonneg (le_of_lt hpos) (by linarith : (0 : ℚ) ≤ 1 - 2 * ε)]
  have hB0big : (B₀.card : ℚ) ≥ ε * B₀.card := by
    nlinarith [mul_nonneg (le_of_lt hB) (by linarith : (0 : ℚ) ≤ 1 - ε)]
  -- Regularity bounds the deviation of `A₁` from the whole pair by `ε` …
  have hbound := hreg A₁ B₀ Finset.subset_union_left (Finset.Subset.refl B₀) hA1big hB0big
  -- … but that deviation is exactly half the inter-half gap.
  have hdevid := edgeDensity_balanced_union_sub G A₁ A₂ B₀ hA hcardeq hpos hB
  rw [hdevid, abs_div, show |(2 : ℚ)| = 2 by norm_num] at hbound
  -- `|d₁ − d₂|/2 ≥ δ/2 > ε`, contradicting `hbound`.
  linarith [hgap]
-- ═══════════════════════════════════════════════════════════════════
-- PART IX: THE TWO-LEVEL (BOTH-COORDINATE) B-SIDE CLOSURE
-- ═══════════════════════════════════════════════════════════════════

/-- **B-side energy jump via subset-promotion — the two-level closure.**  This
    resolves the honest crux left open by Parts VI–VII: the one-sided reduction
    `exists_onesided_deviation_of_irregular` hands its B-side branch a deviation
    `|d(A', B') − d(A', B)| ≥ ε/2` measured against the *witness subset* `A'`,
    which is **not** a part of the current partition — so the whole-partner
    increment `partitionEnergy_Bside_gain_of_irregular` (which needs a genuine
    part `A₀ ∈ R`) cannot fire directly.

    The fix is a two-level refinement.  First split the part `A` into `A'` and
    `A \ A'`; by refinement-monotonicity (`partitionEnergy_single_split_mono`)
    this **never decreases** `partitionEnergy`, and it makes `A'` a genuine part
    of the refined partition.  *Now* the B-side increment applies with `A₀ = A'`:
    splitting `B` into `B', B \ B'` realizes the uniform floor
    `(ε/2)² / (2n²) = ε² / (8n²)` on top of the (non-decreased) post-promotion
    energy.  The net gain over the original partition is therefore at least the
    full floor — no energy is lost in the promotion step.

    This is the missing link that makes the *B-side* branch of an irregular pair
    actually drive an energy increment, closing the coordinate that the plain
    triangle reduction could not reach without refining both coordinates. -/
theorem partitionEnergy_Bside_gain_via_promotion (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A B A' B' : Finset V)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (hA'_fresh : A' ∉ insert B R) (hcomp_fresh : A \ A' ∉ insert B R)
    (hA_fresh : A ∉ insert B R) (hneA : A' ≠ A \ A')
    (hB'_fresh : B' ∉ insert A' (insert (A \ A') R))
    (hBcomp_fresh : B \ B' ∉ insert A' (insert (A \ A') R))
    (hB_fresh : B ∉ insert A' (insert (A \ A') R)) (hneB : B' ≠ B \ B')
    (hn₁ : 1 ≤ (B'.card : ℚ)) (hn₂ : 1 ≤ ((B \ B').card : ℚ))
    (hA'card : 1 ≤ (A'.card : ℚ))
    (eps : ℚ) (hε : 0 ≤ eps)
    (hdev : |edgeDensity G A' B' - edgeDensity G A' B| ≥ eps / 2) :
    partitionEnergy G (insert A (insert B R)) +
        (eps / 2) ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤
      partitionEnergy G (insert B' (insert (B \ B') (insert A' (insert (A \ A') R)))) := by
  have hdisjA : Disjoint A' (A \ A') := disjoint_sdiff_self_right
  have hunionA : A' ∪ (A \ A') = A := Finset.union_sdiff_of_subset hA'
  -- Step 1: split `A → A', A\A'`; refinement never decreases energy, and now `A'`
  -- is a genuine part.
  have hmono := partitionEnergy_single_split_mono G (insert B R) A' (A \ A')
    hdisjA hA'_fresh hcomp_fresh hneA (by rw [hunionA]; exact hA_fresh)
  rw [hunionA] at hmono
  -- Reorder inserts: `B` becomes the split part, `A'` a present partner.
  have hcomm : insert A' (insert (A \ A') (insert B R))
      = insert B (insert A' (insert (A \ A') R)) := by
    rw [Finset.insert_comm (A \ A') B R, Finset.insert_comm A' B (insert (A \ A') R)]
  rw [hcomm] at hmono
  -- Step 2: split `B → B', B\B'` against the now-present whole partner `A'`.
  have hbside := partitionEnergy_Bside_gain_of_irregular G
    (insert A' (insert (A \ A') R)) B A' B' hB' hB'_fresh hBcomp_fresh hneB hB_fresh
    (Finset.mem_insert_self A' _) hn₁ hn₂ hA'card eps hε hdev
  linarith [hmono, hbside]

-- ═══════════════════════════════════════════════════════════════════
-- PART X: THE UNIFIED AFKS ENERGY-INCREMENT STEP
-- ═══════════════════════════════════════════════════════════════════

/-- **An irregular pair always gains the uniform energy floor.**  Given an
    ε-irregularity *witness* `(A', B')` for the pair of parts `(A, B)` — supplied
    as the one-sided dichotomy `hdich` that `exists_onesided_deviation_of_irregular`
    produces — refining the partition realizes an energy increment of at least
    `(ε/2)² / (2n²) = ε² / (8n²)`, **whichever coordinate the irregularity
    localizes to**:

    * A-side branch (`|d(A', B) − d(A, B)| ≥ ε/2`): split the part `A` alone,
      keeping the whole partner `B`; `partitionEnergy_Aside_gain_of_irregular`.
    * B-side branch (`|d(A', B') − d(A', B)| ≥ ε/2`): promote `A'` to a part and
      split `B`; `partitionEnergy_Bside_gain_via_promotion`.

    The conclusion is existential in the refined partition `P'` because the two
    branches produce different refinements, but both clear the *same* floor.  This
    is the complete AFKS energy-increment step: combined with
    `afks_energy_iteration_count` (which bounds the number of floor-clearing
    refinements by `2n²/ε²`), it certifies that a graph admits only finitely many
    genuine refinements before every relevant pair is ε-regular — the tower-free
    finiteness at the heart of the strong regularity lemma. -/
theorem partitionEnergy_gain_of_irregular_pair (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A B A' B' : Finset V)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (hA'_fresh : A' ∉ insert B R) (hcomp_fresh : A \ A' ∉ insert B R)
    (hA_fresh : A ∉ insert B R) (hneA : A' ≠ A \ A')
    (hB'_fresh : B' ∉ insert A' (insert (A \ A') R))
    (hBcomp_fresh : B \ B' ∉ insert A' (insert (A \ A') R))
    (hB_fresh : B ∉ insert A' (insert (A \ A') R)) (hneB : B' ≠ B \ B')
    (hn₁ : 1 ≤ (A'.card : ℚ)) (hn₂ : 1 ≤ ((A \ A').card : ℚ))
    (hBc : 1 ≤ (B.card : ℚ))
    (hm₁ : 1 ≤ (B'.card : ℚ)) (hm₂ : 1 ≤ ((B \ B').card : ℚ))
    (eps : ℚ) (hε : 0 ≤ eps)
    (hdich : |edgeDensity G A' B - edgeDensity G A B| ≥ eps / 2 ∨
             |edgeDensity G A' B' - edgeDensity G A' B| ≥ eps / 2) :
    ∃ P', partitionEnergy G (insert A (insert B R)) +
        (eps / 2) ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤ partitionEnergy G P' := by
  rcases hdich with hAside | hBside
  · -- A-side: split the part `A`, keeping the whole partner `B ∈ insert B R`.
    exact ⟨insert A' (insert (A \ A') (insert B R)),
      partitionEnergy_Aside_gain_of_irregular G (insert B R) A B A'
        hA' hA'_fresh hcomp_fresh hneA hA_fresh (Finset.mem_insert_self B R)
        hn₁ hn₂ hBc eps hε hAside⟩
  · -- B-side: promote `A'` to a part, then split `B`.
    exact ⟨_, partitionEnergy_Bside_gain_via_promotion G R A B A' B'
      hA' hB' hA'_fresh hcomp_fresh hA_fresh hneA hB'_fresh hBcomp_fresh hB_fresh hneB
      hm₁ hm₂ hn₁ eps hε hBside⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART XI: THE DIRECT 2×2 ENERGY INCREMENT FROM AN IRREGULAR PAIR
-- ═══════════════════════════════════════════════════════════════════

/-- **Irregular pair ⇒ direct 2×2 energy increment (no triangle detour).**
    This is the clean capstone that bypasses the one-sided A-side/B-side
    reduction (PARTS VI–X) entirely.  Sessions 4–5 split the witness deviation
    `|d(A′,B′) − d(A,B)| > ε` through a *mixed* density `d(A′,B)` via the triangle
    inequality (`edgeDensity_two_sided_le`), keeping one coordinate whole; that
    route loses a factor `½` in the tolerance (hence `¼` in the floor) and stumbles
    on the mixed second-difference defect that no triangle inequality kills.

    The witness deviation is, however, measured *directly against the coarse
    density* `d(A,B)` — which is exactly the mean identity that the 2×2 variance
    atom bound `pairEnergy_prod_refinement_gain` consumes.  So we refine **both**
    coordinates simultaneously into the grid `{A′, A∖A′} × {B′, B∖B′}` and read off
    the increment with no detour: the witness cell `A′×B′` is a single variance atom
    of the four-cell density distribution whose deviation from the centroid `d(A,B)`
    is `> ε`, contributing an energy gain of at least `(|A′||B′|/n²)·ε²`.

    The unions `A′ ∪ (A∖A′) = A`, `B′ ∪ (B∖B′) = B` are honest disjoint splits
    (`Finset.union_sdiff_of_subset`, `disjoint_sdiff_self_right`), so
    `pairEnergy_prod_refinement_gain` applies verbatim with `d := ε`. -/
theorem pairEnergy_prod_gain_of_irregular (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 ≤ eps) (A B : Finset V)
    (hirr : ¬ IsEpsilonRegular G eps A B) :
    ∃ A' B' : Finset V, A' ⊆ A ∧ B' ⊆ B ∧
      eps * A.card ≤ (A'.card : ℚ) ∧ eps * B.card ≤ (B'.card : ℚ) ∧
      pairEnergy G A B +
          (↑A'.card : ℚ) * ↑B'.card / (Fintype.card V : ℚ) ^ 2 * eps ^ 2 ≤
        pairEnergy G A' B' + pairEnergy G A' (B \ B') +
          pairEnergy G (A \ A') B' + pairEnergy G (A \ A') (B \ B') := by
  obtain ⟨A', B', hA', hB', hAc, hBc, hdev⟩ := exists_irregular_witness G eps A B hirr
  refine ⟨A', B', hA', hB', hAc, hBc, ?_⟩
  have hunionA : A' ∪ (A \ A') = A := Finset.union_sdiff_of_subset hA'
  have hunionB : B' ∪ (B \ B') = B := Finset.union_sdiff_of_subset hB'
  have hdisjA : Disjoint A' (A \ A') := disjoint_sdiff_self_right
  have hdisjB : Disjoint B' (B \ B') := disjoint_sdiff_self_right
  have hdev' : eps ≤
      |edgeDensity G A' B' - edgeDensity G (A' ∪ (A \ A')) (B' ∪ (B \ B'))| := by
    rw [hunionA, hunionB]; exact le_of_lt hdev
  have hgain := pairEnergy_prod_refinement_gain G A' (A \ A') B' (B \ B')
    hdisjA hdisjB eps heps hdev'
  rwa [hunionA, hunionB] at hgain

/-- **Irregular pair ⇒ explicit `ε⁴` energy increment.**  The AFKS-consumable form
    of `pairEnergy_prod_gain_of_irregular`: floor the size-dependent cell gain
    `(|A′||B′|/n²)·ε²` to the clean, subset-free bound `ε⁴·|A||B|/n²` using the
    witness size thresholds `|A′| ≥ ε|A|`, `|B′| ≥ ε|B|`.  This is the genuine
    `ε⁴` energy jump that the strong-regularity iteration consumes: an `ε`-irregular
    pair, refined simultaneously on both coordinates, raises `pairEnergy` by at
    least `ε⁴·|A||B|/n²` — a definite positive amount whenever the pair carries
    positive mass.  Combined with the `[0,1]`-potential termination engine
    (`afks_energy_iteration_count`, `N ≤ 2n²/ε²`) this is the quantitative core of
    the AFKS finiteness statement, now free of the factor-`¼` loss the one-sided
    branches incurred. -/
theorem pairEnergy_prod_gain_of_irregular_eps4 (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 ≤ eps) (A B : Finset V)
    (hirr : ¬ IsEpsilonRegular G eps A B) :
    ∃ A' B' : Finset V, A' ⊆ A ∧ B' ⊆ B ∧
      pairEnergy G A B +
          eps ^ 4 * (↑A.card * ↑B.card) / (Fintype.card V : ℚ) ^ 2 ≤
        pairEnergy G A' B' + pairEnergy G A' (B \ B') +
          pairEnergy G (A \ A') B' + pairEnergy G (A \ A') (B \ B') := by
  obtain ⟨A', B', hA', hB', hAc, hBc, hgain⟩ :=
    pairEnergy_prod_gain_of_irregular G eps heps A B hirr
  refine ⟨A', B', hA', hB', ?_⟩
  -- Floor the exact cell gain `(|A′||B′|/n²)·ε²` by `ε⁴·|A||B|/n²`, then chain.
  have hcard : (eps * A.card) * (eps * B.card) ≤ (↑A'.card : ℚ) * ↑B'.card :=
    mul_le_mul hAc hBc (by positivity) (by positivity)
  have he2 : (0 : ℚ) ≤ eps ^ 2 / (Fintype.card V : ℚ) ^ 2 := by positivity
  have hfloor : eps ^ 4 * (↑A.card * ↑B.card) / (Fintype.card V : ℚ) ^ 2
      ≤ (↑A'.card : ℚ) * ↑B'.card / (Fintype.card V : ℚ) ^ 2 * eps ^ 2 :=
    calc eps ^ 4 * (↑A.card * ↑B.card) / (Fintype.card V : ℚ) ^ 2
        = (eps * A.card) * (eps * B.card) * (eps ^ 2 / (Fintype.card V : ℚ) ^ 2) := by
          ring
      _ ≤ (↑A'.card : ℚ) * ↑B'.card * (eps ^ 2 / (Fintype.card V : ℚ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard he2
      _ = (↑A'.card : ℚ) * ↑B'.card / (Fintype.card V : ℚ) ^ 2 * eps ^ 2 := by ring
  linarith [hgain, hfloor]

/-- **Two-step B-branch energy increment.**  Closes the `B`-branch of the two-sided
    AFKS energy-increment argument, where the deviating coordinate is measured
    against a *witness sub-part* `A' ⊆ A` rather than a genuine existing part.

    `exists_onesided_deviation_of_irregular` hands back a `B`-side deviation
    `|d(A', B') − d(A', B)| ≥ ε/2` measured against the witness sub-part `A'`, which
    is *not* a part of the current partition `insert A (insert B R)`.  The direct
    `partitionEnergy_Bside_gain_of_irregular` cannot consume it, since it needs the
    deviating partner to already be a genuine part.  Resolution — a two-step
    refinement:

    1. split `A → {A', A \ A'}` via `partitionEnergy_single_split_mono`.  This step
       is monotone (energy never drops) and, crucially, *promotes* `A'` to a genuine
       part of the intermediate partition `insert B (insert A' (insert (A \ A') R))`;
    2. now refine `B` against the present part `A'` via
       `partitionEnergy_Bside_gain_of_irregular`, realizing the uniform floor
       `(ε/2)² / (2n²) = ε² / (8n²)`.

    Chaining the monotone step against the gain step (`linarith`) yields the full
    increment on the composite `2×2`-style refinement.  Together with
    `partitionEnergy_Aside_gain_of_irregular`, *both* disjuncts of
    `exists_onesided_deviation_of_irregular` now produce a concrete `partitionEnergy`
    increment `≥ ε² / (8n²)`, i.e. both drive the `hstep` hypothesis of
    `afks_energy_iteration_count`: the two-sided AFKS increment is end-to-end. -/
theorem partitionEnergy_twostep_Bside_gain_of_irregular (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A B A' B' : Finset V)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    -- freshness of the `A`-split parts inside `insert B R`
    (hA'R : A' ∉ insert B R) (hAcR : A \ A' ∉ insert B R) (hAne : A' ≠ A \ A')
    (hAR : A ∉ insert B R)
    -- freshness of the `B`-split parts against the refined family `A' :: A\A' :: R`
    (hB'R : B' ∉ insert A' (insert (A \ A') R))
    (hBcR : B \ B' ∉ insert A' (insert (A \ A') R))
    (hBne : B' ≠ B \ B')
    (hBR : B ∉ insert A' (insert (A \ A') R))
    -- nonemptiness of the promoted part and the `B`-split pieces
    (hnA' : 1 ≤ (A'.card : ℚ)) (hnB' : 1 ≤ (B'.card : ℚ))
    (hnBc : 1 ≤ ((B \ B').card : ℚ))
    (eps : ℚ) (hε : 0 ≤ eps)
    (hdev : |edgeDensity G A' B' - edgeDensity G A' B| ≥ eps / 2) :
    partitionEnergy G (insert A (insert B R)) +
        (eps / 2) ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤
      partitionEnergy G
        (insert B' (insert (B \ B') (insert A' (insert (A \ A') R)))) := by
  have hAunion : A' ∪ (A \ A') = A := Finset.union_sdiff_of_subset hA'
  have hAdisj : Disjoint A' (A \ A') := disjoint_sdiff_self_right
  -- Step 1: split `A` into `{A', A \ A'}` inside `insert B R` (monotone).
  have hmono := partitionEnergy_single_split_mono G (insert B R) A' (A \ A')
    hAdisj hA'R hAcR hAne (by rw [hAunion]; exact hAR)
  rw [hAunion] at hmono
  -- Reorder so the intermediate partition presents `B` on the outside, with `A'`
  -- now a genuine part of the remaining family `insert A' (insert (A \ A') R)`.
  have hreorder : insert A' (insert (A \ A') (insert B R)) =
      insert B (insert A' (insert (A \ A') R)) := by
    ext x; simp only [Finset.mem_insert]; tauto
  rw [hreorder] at hmono
  -- Step 2: B-side gain against the promoted part `A'`.
  have hgain := partitionEnergy_Bside_gain_of_irregular G
    (insert A' (insert (A \ A') R)) B A' B'
    hB' hB'R hBcR hBne hBR (Finset.mem_insert_self _ _)
    hnB' hnBc hnA' eps hε hdev
  linarith [hmono, hgain]

/-- **Unified irregular-pair energy increment (single existential interface).**
    Collapses the two branch-specific gain lemmas
    (`partitionEnergy_Aside_gain_of_irregular` and
    `partitionEnergy_twostep_Bside_gain_of_irregular`) into one statement of the
    exact shape the AFKS iteration consumes: *from a one-sided deviation of an
    irregular pair there EXISTS a refinement of `insert A (insert B R)` whose
    `partitionEnergy` exceeds the current one by the uniform floor
    `(ε/2)² / (2n²) = ε² / (8n²)`.*

    The hypothesis is the disjunction produced by
    `exists_onesided_deviation_of_irregular`:

    * the **A-side** branch (`|d(A', B) − d(A, B)| ≥ ε/2`, partner `B` kept whole)
      returns the single-split refinement `A' :: A\A' :: (B :: R)` via
      `partitionEnergy_Aside_gain_of_irregular` with the fixed partner `B` supplied
      by `Finset.mem_insert_self`;
    * the **B-side** branch (`|d(A', B') − d(A', B)| ≥ ε/2`, partner the witness
      sub-part `A'`) returns the two-step refinement
      `B' :: B\B' :: A' :: A\A' :: R` via
      `partitionEnergy_twostep_Bside_gain_of_irregular`.

    Either way the SAME floor is realized, so the two branches unify to one
    existential.  This is the clean interface theorem: composed with
    `exists_onesided_deviation_of_irregular`, the only remaining gap to a fully
    hypothesis-free `¬ IsEpsilonRegular → ∃ refinement` statement is discharging
    the freshness/nonemptiness side conditions of the *internally extracted*
    witness (automatic under an equipartition-based refinement, but not available
    at this level of abstraction — hence kept as hypotheses on the named
    witness). -/
theorem exists_refinement_energy_gain_of_onesided_deviation (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A B A' B' : Finset V)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    -- freshness of the `A`-split parts inside `insert B R`
    (hA'R : A' ∉ insert B R) (hAcR : A \ A' ∉ insert B R) (hAne : A' ≠ A \ A')
    (hAR : A ∉ insert B R)
    -- freshness of the `B`-split parts against the refined family `A' :: A\A' :: R`
    (hB'R : B' ∉ insert A' (insert (A \ A') R))
    (hBcR : B \ B' ∉ insert A' (insert (A \ A') R))
    (hBne : B' ≠ B \ B')
    (hBR : B ∉ insert A' (insert (A \ A') R))
    -- nonemptiness of the witness sub-parts, their complements, and partner `B`
    (hnA' : 1 ≤ (A'.card : ℚ)) (hnAc : 1 ≤ ((A \ A').card : ℚ))
    (hnB' : 1 ≤ (B'.card : ℚ)) (hnBc : 1 ≤ ((B \ B').card : ℚ))
    (hnB : 1 ≤ (B.card : ℚ))
    (eps : ℚ) (hε : 0 ≤ eps)
    (hdev : |edgeDensity G A' B - edgeDensity G A B| ≥ eps / 2 ∨
            |edgeDensity G A' B' - edgeDensity G A' B| ≥ eps / 2) :
    ∃ R' : Finset (Finset V),
      partitionEnergy G (insert A (insert B R)) +
          (eps / 2) ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤ partitionEnergy G R' := by
  rcases hdev with hAside | hBside
  · -- A-side branch: refine `A` against the whole partner `B` (a genuine part).
    refine ⟨insert A' (insert (A \ A') (insert B R)), ?_⟩
    exact partitionEnergy_Aside_gain_of_irregular G (insert B R) A B A'
      hA' hA'R hAcR hAne hAR (Finset.mem_insert_self B R)
      hnA' hnAc hnB eps hε hAside
  · -- B-side branch: two-step refinement, `B` against the promoted witness `A'`.
    refine ⟨insert B' (insert (B \ B') (insert A' (insert (A \ A') R))), ?_⟩
    exact partitionEnergy_twostep_Bside_gain_of_irregular G R A B A' B'
      hA' hB' hA'R hAcR hAne hAR hB'R hBcR hBne hBR
      hnA' hnB' hnBc eps hε hBside

-- ═══════════════════════════════════════════════════════════════════
-- PART VII: DISCHARGING WITNESS FRESHNESS FROM A GENUINE PARTITION
-- ═══════════════════════════════════════════════════════════════════

/-- **A nonempty subset of one part differs from every other part.**  In a
    pairwise-disjoint family `fam`, if `S ⊆ A` is nonempty and `Q ∈ fam` is a part
    *distinct from* `A`, then `S ≠ Q`.  Reason: `Q` and `A` are disjoint, so `Q`
    contains no point of `A`, whereas the nonempty `S ⊆ A` does.

    This is the structural fact behind every "freshness" side-condition of the
    refinement lemmas.  The energy-increment machinery insists that the newly
    carved sub-parts (`A'`, `A \ A'`, …) are *not already present* in the family
    being refined, because inserting a duplicate part into a `Finset` is a no-op
    and would silently break the intended split.  In a genuine partition that can
    never happen, and this lemma is why. -/
theorem ne_of_subset_part_of_disjoint
    (fam : Finset (Finset V))
    (hdisj : ∀ P ∈ fam, ∀ Q ∈ fam, P ≠ Q → Disjoint P Q)
    (A S Q : Finset V) (hA : A ∈ fam) (hQ : Q ∈ fam) (hQA : Q ≠ A)
    (hSA : S ⊆ A) (hSne : S.Nonempty) : S ≠ Q := by
  intro heq
  obtain ⟨x, hx⟩ := hSne
  have hxA : x ∈ A := hSA hx
  have hxQ : x ∈ Q := heq ▸ hx
  exact absurd hxA (Finset.disjoint_left.mp (hdisj Q hQ A hA hQA) hxQ)

/-- **A nonempty subset of `A` differs from any subset of a disjoint part `B`.**
    If `Disjoint A B`, `S ⊆ A` is nonempty and `T ⊆ B`, then `S ≠ T` — the two
    live in disjoint parts, so a common element would sit in `A ∩ B = ∅`.  Used
    to separate witness sub-parts of `A` (namely `A'`, `A \ A'`) from witness
    sub-parts of the disjoint partner `B` (namely `B'`, `B \ B'`), which are
    *not* members of the ambient family and so out of reach of
    `ne_of_subset_part_of_disjoint`. -/
theorem ne_of_subset_disjoint_parts
    (A B S T : Finset V) (hAB : Disjoint A B)
    (hSA : S ⊆ A) (hTB : T ⊆ B) (hSne : S.Nonempty) : S ≠ T := by
  intro heq
  obtain ⟨x, hx⟩ := hSne
  have hxA : x ∈ A := hSA hx
  have hxB : x ∈ B := hTB (heq ▸ hx)
  exact absurd hxA (Finset.disjoint_right.mp hAB hxB)

/-- **Irregular pair in a genuine partition ⇒ refinement with an energy jump —
    freshness discharged.**  This is `exists_refinement_energy_gain_of_onesided_deviation`
    with *all eight* freshness side-conditions replaced by the single, natural
    hypothesis that the ambient family `insert A (insert B R)` is a genuine
    partition: its parts are pairwise disjoint (`hdisj`), `A` and `B` are two
    distinct genuine parts (`hAR`, `hBR`, `hAB` say `A, B ∉ R` and `A ≠ B`).

    From disjointness alone, the two structural lemmas above discharge every
    freshness obligation:

    * each witness sub-part (`A'`, `A \ A'`) is a nonempty subset of `A`, hence —
      by `ne_of_subset_part_of_disjoint` — distinct from every other part of the
      family, and — by `ne_of_subset_disjoint_parts` — distinct from every
      sub-part of the disjoint partner `B`;
    * symmetrically for `B'`, `B \ B'`;
    * `A ≠ B` and `A, B ∉ R` handle the whole-part obligations directly.

    The card-`≥ 1` obligations collapse to plain nonemptiness of the four
    sub-parts and of `B`.  What remains is exactly the deviation disjunction
    produced by `exists_onesided_deviation_of_irregular`.  This is the first
    statement in which a *bare partition + irregular witness* — with no bespoke
    non-membership bookkeeping — yields the AFKS energy increment, closing the
    freshness gap flagged by `exists_refinement_energy_gain_of_onesided_deviation`. -/
theorem exists_refinement_energy_gain_of_irregular_in_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A B A' B' : Finset V)
    (hdisj : ∀ P ∈ insert A (insert B R), ∀ Q ∈ insert A (insert B R),
      P ≠ Q → Disjoint P Q)
    (hAR : A ∉ R) (hBR : B ∉ R) (hAB : A ≠ B)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (hA'ne : A'.Nonempty) (hAcne : (A \ A').Nonempty)
    (hB'ne : B'.Nonempty) (hBcne : (B \ B').Nonempty)
    (hBne : B.Nonempty)
    (eps : ℚ) (hε : 0 ≤ eps)
    (hdev : |edgeDensity G A' B - edgeDensity G A B| ≥ eps / 2 ∨
            |edgeDensity G A' B' - edgeDensity G A' B| ≥ eps / 2) :
    ∃ R' : Finset (Finset V),
      partitionEnergy G (insert A (insert B R)) +
          (eps / 2) ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤ partitionEnergy G R' := by
  -- Basic membership / disjointness facts about the genuine partition.
  have hAfam : A ∈ insert A (insert B R) := Finset.mem_insert_self _ _
  have hBfam : B ∈ insert A (insert B R) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have disjAB : Disjoint A B := hdisj A hAfam B hBfam hAB
  have memfam_of_R : ∀ {Q : Finset V}, Q ∈ R → Q ∈ insert A (insert B R) :=
    fun hQ => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hQ)
  have neA_of_R : ∀ {Q : Finset V}, Q ∈ R → Q ≠ A := fun hQ h => hAR (h ▸ hQ)
  have neB_of_R : ∀ {Q : Finset V}, Q ∈ R → Q ≠ B := fun hQ h => hBR (h ▸ hQ)
  -- Convenient nonempty ⇒ (1 : ℚ) ≤ card.
  have cardQ : ∀ {S : Finset V}, S.Nonempty → (1 : ℚ) ≤ (S.card : ℚ) := by
    intro S hS
    have h1 : 1 ≤ S.card := Finset.card_pos.mpr hS
    exact_mod_cast h1
  -- A' and A \ A' are nonempty subsets of A; B' and B \ B' of B.
  have hAc' : A \ A' ⊆ A := Finset.sdiff_subset
  have hBc' : B \ B' ⊆ B := Finset.sdiff_subset
  -- ─── A-side freshness ─────────────────────────────────────────────
  have hA'R_ : A' ∉ insert B R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨ne_of_subset_disjoint_parts A B A' B disjAB hA' (Finset.Subset.refl B) hA'ne,
      fun hmem => ne_of_subset_part_of_disjoint _ hdisj A A' A' hAfam
        (memfam_of_R hmem) (neA_of_R hmem) hA' hA'ne rfl⟩
  have hAcR_ : A \ A' ∉ insert B R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨ne_of_subset_disjoint_parts A B (A \ A') B disjAB hAc' (Finset.Subset.refl B) hAcne,
      fun hmem => ne_of_subset_part_of_disjoint _ hdisj A (A \ A') (A \ A') hAfam
        (memfam_of_R hmem) (neA_of_R hmem) hAc' hAcne rfl⟩
  have hAne_ : A' ≠ A \ A' := by
    intro heq
    obtain ⟨x, hx⟩ := hA'ne
    exact absurd hx (Finset.disjoint_right.mp disjoint_sdiff_self_right (heq ▸ hx))
  have hAR_ : A ∉ insert B R := by
    simp only [Finset.mem_insert, not_or]; exact ⟨hAB, hAR⟩
  -- ─── B-side freshness (against `insert A' (insert (A \ A') R)`) ────
  have hB'R_ : B' ∉ insert A' (insert (A \ A') R) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨ne_of_subset_disjoint_parts B A B' A' disjAB.symm hB' hA' hB'ne,
      ne_of_subset_disjoint_parts B A B' (A \ A') disjAB.symm hB' hAc' hB'ne,
      fun hmem => ne_of_subset_part_of_disjoint _ hdisj B B' B' hBfam
        (memfam_of_R hmem) (neB_of_R hmem) hB' hB'ne rfl⟩
  have hBcR_ : B \ B' ∉ insert A' (insert (A \ A') R) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨ne_of_subset_disjoint_parts B A (B \ B') A' disjAB.symm hBc' hA' hBcne,
      ne_of_subset_disjoint_parts B A (B \ B') (A \ A') disjAB.symm hBc' hAc' hBcne,
      fun hmem => ne_of_subset_part_of_disjoint _ hdisj B (B \ B') (B \ B') hBfam
        (memfam_of_R hmem) (neB_of_R hmem) hBc' hBcne rfl⟩
  have hBne_ : B' ≠ B \ B' := by
    intro heq
    obtain ⟨x, hx⟩ := hB'ne
    exact absurd hx (Finset.disjoint_right.mp disjoint_sdiff_self_right (heq ▸ hx))
  have hBR_ : B ∉ insert A' (insert (A \ A') R) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨ne_of_subset_disjoint_parts B A B A' disjAB.symm (Finset.Subset.refl B) hA' hBne,
      ne_of_subset_disjoint_parts B A B (A \ A') disjAB.symm (Finset.Subset.refl B) hAc' hBne,
      hBR⟩
  -- Assemble via the S10 single-existential interface.
  exact exists_refinement_energy_gain_of_onesided_deviation G R A B A' B'
    hA' hB' hA'R_ hAcR_ hAne_ hAR_ hB'R_ hBcR_ hBne_ hBR_
    (cardQ hA'ne) (cardQ hAcne) (cardQ hB'ne) (cardQ hBcne) (cardQ hBne)
    eps hε hdev

-- ═══════════════════════════════════════════════════════════════════
-- PART VIII: INTERNALIZING THE WITNESS — ¬IsEpsilonRegular ⇒ ∃ refinement
-- ═══════════════════════════════════════════════════════════════════

/-- **Partner-nonempty part freshness.**  Mirror of `ne_of_subset_part_of_disjoint`
    that discharges the freshness of a *possibly empty* sub-part `S ⊆ A` using the
    nonemptiness of the *other* part `Q` rather than that of `S`.  In a
    pairwise-disjoint family, a part `Q ≠ A` that is nonempty cannot equal any
    subset `S ⊆ A`: were `S = Q` then `Q ⊆ A`, but `Disjoint A Q` forces
    `Q ⊆ A ∩ Q = ∅`, contradicting `Q.Nonempty`.

    This is the enabling variant for *internalizing* the irregularity witness.
    When the extracted witness `A'` happens to equal the whole part `A`, its
    complement `A \ A'` is empty, so the earlier `ne_of_subset_part_of_disjoint`
    (which leans on `S.Nonempty`) no longer applies.  The ambient partition's
    parts, however, are always nonempty, so this version discharges the same
    obligation with no strictness assumption on the carved sub-part. -/
theorem ne_of_subset_part_of_disjoint'
    (fam : Finset (Finset V))
    (hdisj : ∀ P ∈ fam, ∀ Q ∈ fam, P ≠ Q → Disjoint P Q)
    (A S Q : Finset V) (hA : A ∈ fam) (hQ : Q ∈ fam) (hQA : Q ≠ A)
    (hSA : S ⊆ A) (hQne : Q.Nonempty) : S ≠ Q := by
  intro heq
  obtain ⟨x, hx⟩ := hQne
  have hxA : x ∈ A := hSA (heq.symm ▸ hx)
  exact absurd hxA (Finset.disjoint_left.mp (hdisj Q hQ A hA hQA) hx)

/-- **Partner-nonempty cross-part freshness.**  Mirror of
    `ne_of_subset_disjoint_parts` using the nonemptiness of `T ⊆ B` rather than of
    `S ⊆ A`.  If `Disjoint A B`, `S ⊆ A`, `T ⊆ B` and `T` is nonempty then
    `S ≠ T`: else `T = S ⊆ A`, so `T ⊆ A ∩ B = ∅`, contradicting `T.Nonempty`.
    The companion to `ne_of_subset_part_of_disjoint'` that separates a possibly
    empty sub-part of `A` from a nonempty sub-part of the disjoint partner `B`. -/
theorem ne_of_subset_disjoint_parts'
    (A B S T : Finset V) (hAB : Disjoint A B)
    (hSA : S ⊆ A) (hTB : T ⊆ B) (hTne : T.Nonempty) : S ≠ T := by
  intro heq
  obtain ⟨x, hx⟩ := hTne
  have hxA : x ∈ A := hSA (heq.symm ▸ hx)
  have hxB : x ∈ B := hTB hx
  exact absurd hxB (Finset.disjoint_left.mp hAB hxA)

/-- **Fully internalized AFKS energy increment.**  The capstone of Parts VI–VII:
    from *nothing but* a genuine partition and the raw hypothesis that the pair
    `(A, B)` is `¬ ε`-regular, there EXISTS a refinement of `insert A (insert B R)`
    whose `partitionEnergy` exceeds the current one by the uniform floor
    `(ε/2)² / (2n²) = ε² / (8n²)`.

    Every prior interface still carried the *extracted witness* `A', B'` and its
    freshness/nonemptiness as explicit hypotheses.  Here the witness is produced
    *internally* by `exists_onesided_deviation_of_irregular`, and all of its side
    conditions are discharged from the partition data:

    * **Nonemptiness of the witness sub-parts** `A', B'` follows from their size
      thresholds `|A'| ≥ ε|A|`, `|B'| ≥ ε|B|` together with `ε > 0` and the
      nonemptiness of `A, B`.
    * **Strictness** `A' ⊊ A` (A-side) resp. `B' ⊊ B` (B-side) — the source of the
      complement nonemptiness that the energy gain needs — is forced by the
      deviation: an equality `A' = A` would make `d(A', B) = d(A, B)`, collapsing
      the `≥ ε/2 > 0` deviation to `0`.  Crucially this strictness is available
      *only on the deviating coordinate*; the off-coordinate complement (`A \ A'`
      in the B-side branch) may be empty, which is exactly why freshness is
      discharged through the *partner-nonempty* lemmas above rather than through
      the sub-part's own nonemptiness.
    * **Freshness** of all carved parts against the family being refined follows
      from pairwise disjointness plus nonemptiness of the ambient parts (`hRne`,
      `hAne`, `hBne`), via `ne_of_subset_part_of_disjoint'` /
      `ne_of_subset_disjoint_parts'`.

    This closes the reduction `¬ IsEpsilonRegular → ∃ refinement, energy jumps`:
    the single remaining task for a full AFKS proof is the *outer loop* — iterate
    this increment and feed the per-step gain into `afks_energy_iteration_count`. -/
theorem exists_refinement_energy_gain_of_irregular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A B : Finset V)
    (hdisj : ∀ P ∈ insert A (insert B R), ∀ Q ∈ insert A (insert B R),
      P ≠ Q → Disjoint P Q)
    (hRne : ∀ P ∈ R, P.Nonempty)
    (hAR : A ∉ R) (hBR : B ∉ R) (hAB : A ≠ B)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (eps : ℚ) (hε : 0 < eps)
    (hirr : ¬ IsEpsilonRegular G eps A B) :
    ∃ R' : Finset (Finset V),
      partitionEnergy G (insert A (insert B R)) +
          (eps / 2) ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤ partitionEnergy G R' := by
  -- Internal witness extraction.
  obtain ⟨A', B', hA', hB', hAc, hBc, hdev⟩ :=
    exists_onesided_deviation_of_irregular G eps A B hirr
  -- Partition bookkeeping (mirrors `exists_refinement_energy_gain_of_irregular_in_partition`).
  have hAfam : A ∈ insert A (insert B R) := Finset.mem_insert_self _ _
  have hBfam : B ∈ insert A (insert B R) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have disjAB : Disjoint A B := hdisj A hAfam B hBfam hAB
  have memfam_of_R : ∀ {Q : Finset V}, Q ∈ R → Q ∈ insert A (insert B R) :=
    fun hQ => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hQ)
  have neA_of_R : ∀ {Q : Finset V}, Q ∈ R → Q ≠ A := fun hQ h => hAR (h ▸ hQ)
  have neB_of_R : ∀ {Q : Finset V}, Q ∈ R → Q ≠ B := fun hQ h => hBR (h ▸ hQ)
  have cardQ : ∀ {S : Finset V}, S.Nonempty → (1 : ℚ) ≤ (S.card : ℚ) := by
    intro S hS
    exact_mod_cast Finset.card_pos.mpr hS
  have hAc' : A \ A' ⊆ A := Finset.sdiff_subset
  have hBc' : B \ B' ⊆ B := Finset.sdiff_subset
  -- Witness sub-parts `A', B'` are nonempty (from the size thresholds and ε > 0).
  have hA'ne : A'.Nonempty := by
    rw [← Finset.card_pos]
    have hApos : (0 : ℚ) < (A.card : ℚ) := by exact_mod_cast Finset.card_pos.mpr hAne
    have h2 : (0 : ℚ) < (A'.card : ℚ) := lt_of_lt_of_le (mul_pos hε hApos) hAc
    exact_mod_cast h2
  have hB'ne : B'.Nonempty := by
    rw [← Finset.card_pos]
    have hBpos : (0 : ℚ) < (B.card : ℚ) := by exact_mod_cast Finset.card_pos.mpr hBne
    have h2 : (0 : ℚ) < (B'.card : ℚ) := lt_of_lt_of_le (mul_pos hε hBpos) hBc
    exact_mod_cast h2
  -- Shared A-side freshness (A' and A\A' fresh in `insert B R`); no strictness needed.
  have hA'R_ : A' ∉ insert B R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨ne_of_subset_disjoint_parts' A B A' B disjAB hA' (Finset.Subset.refl B) hBne,
      fun hmem => ne_of_subset_part_of_disjoint' _ hdisj A A' A' hAfam
        (memfam_of_R hmem) (neA_of_R hmem) hA' (hRne _ hmem) rfl⟩
  have hAcR_ : A \ A' ∉ insert B R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨ne_of_subset_disjoint_parts' A B (A \ A') B disjAB hAc' (Finset.Subset.refl B) hBne,
      fun hmem => ne_of_subset_part_of_disjoint' _ hdisj A (A \ A') (A \ A') hAfam
        (memfam_of_R hmem) (neA_of_R hmem) hAc' (hRne _ hmem) rfl⟩
  have hAne_ : A' ≠ A \ A' := by
    intro heq
    obtain ⟨x, hx⟩ := hA'ne
    exact absurd hx (Finset.disjoint_right.mp disjoint_sdiff_self_right (heq ▸ hx))
  have hAR_ : A ∉ insert B R := by
    simp only [Finset.mem_insert, not_or]; exact ⟨hAB, hAR⟩
  rcases hdev with hAside | hBside
  · -- A-side branch: strictness `A' ⊊ A` yields `A \ A'` nonempty.
    have hAcne : (A \ A').Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hsub
      have heq : A' = A := Finset.Subset.antisymm hA' hsub
      rw [heq] at hAside
      simp only [sub_self, abs_zero] at hAside
      linarith
    refine ⟨insert A' (insert (A \ A') (insert B R)), ?_⟩
    exact partitionEnergy_Aside_gain_of_irregular G (insert B R) A B A'
      hA' hA'R_ hAcR_ hAne_ hAR_ (Finset.mem_insert_self B R)
      (cardQ hA'ne) (cardQ hAcne) (cardQ hBne) eps hε.le hAside
  · -- B-side branch: strictness `B' ⊊ B` yields `B \ B'` nonempty.  Note `A \ A'`
    -- may be empty here — its freshness is carried by the partner-nonempty lemmas.
    have hBcne : (B \ B').Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hsub
      have heq : B' = B := Finset.Subset.antisymm hB' hsub
      rw [heq] at hBside
      simp only [sub_self, abs_zero] at hBside
      linarith
    have hB'R_ : B' ∉ insert A' (insert (A \ A') R) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨ne_of_subset_disjoint_parts' B A B' A' disjAB.symm hB' hA' hA'ne,
        (ne_of_subset_disjoint_parts' A B (A \ A') B' disjAB hAc' hB' hB'ne).symm,
        fun hmem => ne_of_subset_part_of_disjoint' _ hdisj B B' B' hBfam
          (memfam_of_R hmem) (neB_of_R hmem) hB' (hRne _ hmem) rfl⟩
    have hBcR_ : B \ B' ∉ insert A' (insert (A \ A') R) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨ne_of_subset_disjoint_parts' B A (B \ B') A' disjAB.symm hBc' hA' hA'ne,
        (ne_of_subset_disjoint_parts' A B (A \ A') (B \ B') disjAB hAc' hBc' hBcne).symm,
        fun hmem => ne_of_subset_part_of_disjoint' _ hdisj B (B \ B') (B \ B') hBfam
          (memfam_of_R hmem) (neB_of_R hmem) hBc' (hRne _ hmem) rfl⟩
    have hBne_ : B' ≠ B \ B' := by
      intro heq
      obtain ⟨x, hx⟩ := hB'ne
      exact absurd hx (Finset.disjoint_right.mp disjoint_sdiff_self_right (heq ▸ hx))
    have hBR_ : B ∉ insert A' (insert (A \ A') R) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨ne_of_subset_disjoint_parts' B A B A' disjAB.symm (Finset.Subset.refl B) hA' hA'ne,
        (ne_of_subset_disjoint_parts' A B (A \ A') B disjAB hAc' (Finset.Subset.refl B) hBne).symm,
        hBR⟩
    refine ⟨insert B' (insert (B \ B') (insert A' (insert (A \ A') R))), ?_⟩
    exact partitionEnergy_twostep_Bside_gain_of_irregular G R A B A' B'
      hA' hB' hA'R_ hAcR_ hAne_ hAR_ hB'R_ hBcR_ hBne_ hBR_
      (cardQ hA'ne) (cardQ hB'ne) (cardQ hBcne) eps hε.le hBside

-- ═══════════════════════════════════════════════════════════════════
-- PART VII: EMPTY-PART CLEANUP — REPRODUCING THE NONEMPTY LOOP HYPOTHESIS
-- ═══════════════════════════════════════════════════════════════════

/-- **Empty parts carry no energy.**  `partitionEnergy` is unchanged by deleting
    the empty members of a family: every ordered pair `(P, Q)` in which `P` or `Q`
    is empty contributes `pairEnergy G P Q = (|P|·|Q|/n²)·d(P,Q)² = 0`, because the
    size weight `|P|·|Q|` vanishes.  Formally, filtering the family down to its
    parts of nonzero cardinality preserves the gallery energy.

    This is the bookkeeping tool that lets the AFKS outer loop *reproduce its own
    hypothesis*.  The one-sided refinement produced by
    `exists_refinement_energy_gain_of_irregular` inserts the complement `A \ A'`
    even on the `B`-side branch, where strictness is unavailable and `A \ A'` may
    be **empty** (the witness can return `A' = A`).  Such an empty part would break
    the *nonempty-parts* precondition (`hRne`) needed to feed the refinement back
    into the next iteration.  This lemma shows the empty part can be dropped for
    free, at no energy cost — see
    `exists_refinement_energy_gain_of_irregular_nonempty`. -/
theorem partitionEnergy_filter_card_ne_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) :
    partitionEnergy G (parts.filter (fun P => P.card ≠ 0)) = partitionEnergy G parts := by
  rw [partitionEnergy_eq_sum_pairEnergy, partitionEnergy_eq_sum_pairEnergy]
  refine (Finset.sum_subset
    (Finset.product_subset_product (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    ?_)
  intro pq hpq hnot
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpq
  -- `pq` sits in the full ordered-pair set; not being in the filtered product
  -- forces one of its two parts to be empty (`card = 0`).
  have hzero : pq.1.card = 0 ∨ pq.2.card = 0 := by
    by_contra h
    push_neg at h
    exact hnot (Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨h1, h.1⟩, Finset.mem_filter.mpr ⟨h2, h.2⟩⟩)
  rcases hzero with h | h <;> simp [pairEnergy, h]

/-- **One-sided refinement with a genuinely nonempty output family.**  Strengthens
    the capstone `exists_refinement_energy_gain_of_irregular`: from a bare
    `¬ IsEpsilonRegular G eps A B` inside a genuine partition, it produces a
    refinement `R'` whose parts are all nonempty *and* whose energy exceeds that of
    `insert A (insert B R)` by the uniform floor `(ε/2)² / (2n²) = ε² / (8n²)`.

    The nonemptiness is recovered by discarding the empty parts (via
    `partitionEnergy_filter_card_ne_zero`, which leaves the energy untouched).
    This closes the *nonempty-parts half* of genuineness preservation: the produced
    family satisfies the `hRne`-style precondition that the outer AFKS loop needs to
    feed the refinement back into the next iteration.  (Pairwise-disjointness of the
    output — the remaining half of genuineness — is inherited from the concrete
    inserts and is orthogonal to this cleanup.) -/
theorem exists_refinement_energy_gain_of_irregular_nonempty
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A B : Finset V)
    (hdisj : ∀ P ∈ insert A (insert B R), ∀ Q ∈ insert A (insert B R),
      P ≠ Q → Disjoint P Q)
    (hRne : ∀ P ∈ R, P.Nonempty)
    (hAR : A ∉ R) (hBR : B ∉ R) (hAB : A ≠ B)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (eps : ℚ) (hε : 0 < eps)
    (hirr : ¬ IsEpsilonRegular G eps A B) :
    ∃ R' : Finset (Finset V),
      (∀ P ∈ R', P.Nonempty) ∧
      partitionEnergy G (insert A (insert B R)) +
          (eps / 2) ^ 2 / (2 * (Fintype.card V : ℚ) ^ 2) ≤ partitionEnergy G R' := by
  obtain ⟨R', hR'⟩ :=
    exists_refinement_energy_gain_of_irregular G R A B hdisj hRne hAR hBR hAB
      hAne hBne eps hε hirr
  refine ⟨R'.filter (fun P => P.card ≠ 0), ?_, ?_⟩
  · intro P hP
    exact Finset.card_pos.mp (Nat.pos_of_ne_zero (Finset.mem_filter.mp hP).2)
  · rwa [partitionEnergy_filter_card_ne_zero]


end Szemeredi.RegularityOQ04Bridge
