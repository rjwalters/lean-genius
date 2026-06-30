/-
Quantitative 1D Edge-Isoperimetric Stability: Boundary Counts Runs

Open Question from: Isoperimetric Theorem (Wiedijk #43), OQ-02 → OQ-03 → OQ-01

The parent entry (IsoperimetricTheoremOQ02OQ03) proves the *equality rigidity*
for the discrete 1D isoperimetric inequality on `ℤ`: a finite nonempty `S ⊆ ℤ`
has *vertex* boundary `|∂S| = 2` iff `S` is an integer interval. In its closing
remark it flags — but does **not** prove — the clean *edge*-boundary statement:

  "The edge count (number of lattice edges crossing between S and its complement)
   equals 2·(number of maximal runs)."

This file proves exactly that identity and its quantitative consequences.

Setup.
  For a finite `S ⊆ ℤ` write `m = min S`, `M = max S`. A *maximal run* is a
  maximal block of consecutive integers contained in `S`. We count runs by their
  left endpoints:
        `numRuns S := |{ x ∈ S : x - 1 ∉ S }|`.
  The *edge boundary* is the set of lattice edges `(x, x+1)` with exactly one
  endpoint in `S`. Such an edge is either *rising* (`x ∉ S`, `x+1 ∈ S`) or
  *falling* (`x ∈ S`, `x+1 ∉ S`); we count
        `edgeBoundaryCount S := |(S-1) \ S| + |(S+1) \ S|`
  where `S ± 1` is the image of `S` under translation. The first summand counts
  rising edges, the second falling edges.

Main result.
        `edgeBoundaryCount S = 2 * numRuns S`,
  hence `edgeBoundaryCount S = 2 + 2k ⟺ numRuns S = k + 1`: each additional
  maximal run (each gap) contributes exactly two boundary edges. This is the
  precise "boundary = 2·runs" identity and the quantitative stability statement.

Proof idea (no telescoping needed).
  Let `numRuns = |leftEnds|` count left endpoints `{x∈S : x-1∉S}` and let
  `numEnds = |rightEnds|` count right endpoints `{x∈S : x+1∉S}`. Within `S`,
  the left endpoints are the complement of the "has-predecessor" set
  `internalL = {x∈S : x-1∈S}`, and the right endpoints are the complement of the
  "has-successor" set `internalR = {x∈S : x+1∈S}`. The translation `x ↦ x-1` is a
  bijection `internalL ≃ internalR`, so `|internalL| = |internalR|`, whence
  `|leftEnds| = |S| - |internalL| = |S| - |internalR| = |rightEnds|`. The two edge
  summands have the same cardinalities as `leftEnds` and `rightEnds`
  respectively, so `edgeBoundaryCount = |leftEnds| + |rightEnds| = 2·numRuns`.

References:
  - Bollobás (1986), Combinatorics, Cambridge University Press.
  - Harper (1966), Optimal numberings and isoperimetric problems on graphs.

Tags: combinatorics, discrete-geometry, isoperimetric-inequality, stability
-/
import Mathlib

namespace DiscreteIsoperimetric1DRuns

/-- Right endpoints of the maximal runs of `S`: elements whose successor is
    missing. -/
def rightEnds (S : Finset ℤ) : Finset ℤ := S.filter (fun x => x + 1 ∉ S)

/-- Left endpoints of the maximal runs of `S`: elements whose predecessor is
    missing. The number of maximal runs is `|leftEnds S|`. -/
def leftEnds (S : Finset ℤ) : Finset ℤ := S.filter (fun x => x - 1 ∉ S)

/-- Elements of `S` whose successor is also in `S` ("has a right neighbour"). -/
def internalR (S : Finset ℤ) : Finset ℤ := S.filter (fun x => x + 1 ∈ S)

/-- Elements of `S` whose predecessor is also in `S` ("has a left neighbour"). -/
def internalL (S : Finset ℤ) : Finset ℤ := S.filter (fun x => x - 1 ∈ S)

/-- The number of maximal runs of `S`, counted by left endpoints. -/
def numRuns (S : Finset ℤ) : ℕ := (leftEnds S).card

/-- The number of boundary edges: rising edges `(S-1)\S` plus falling edges
    `(S+1)\S`. -/
def edgeBoundaryCount (S : Finset ℤ) : ℕ :=
  ((S.image (· - 1)) \ S).card + ((S.image (· + 1)) \ S).card

/-! ### Internal "has-neighbour" sets are equinumerous -/

/-- Translation `x ↦ x - 1` carries the has-predecessor set onto the
    has-successor set; hence they have equal cardinality. -/
theorem card_internalL_eq_card_internalR (S : Finset ℤ) :
    (internalL S).card = (internalR S).card := by
  apply Finset.card_bij (fun x _ => x - 1)
  · -- maps internalL into internalR
    intro a ha
    simp only [internalL, Finset.mem_filter] at ha
    simp only [internalR, Finset.mem_filter]
    obtain ⟨haS, hpred⟩ := ha
    refine ⟨hpred, ?_⟩
    simpa using haS
  · -- injective
    intro a _ b _ hab
    omega
  · -- surjective
    intro b hb
    simp only [internalR, Finset.mem_filter] at hb
    refine ⟨b + 1, ?_, by ring⟩
    simp only [internalL, Finset.mem_filter]
    exact ⟨hb.2, by simpa using hb.1⟩

/-! ### Left/right endpoint counts agree (= number of runs) -/

/-- Within `S`, the right endpoints partition off the has-successor elements. -/
theorem card_rightEnds_add_card_internalR (S : Finset ℤ) :
    (rightEnds S).card + (internalR S).card = S.card := by
  have key : internalR S = S.filter (fun x => ¬ (x + 1 ∉ S)) := by
    simp only [internalR, not_not]
  rw [rightEnds, key]
  exact Finset.filter_card_add_filter_neg_card_eq_card (fun x => x + 1 ∉ S)

/-- Within `S`, the left endpoints partition off the has-predecessor elements. -/
theorem card_leftEnds_add_card_internalL (S : Finset ℤ) :
    (leftEnds S).card + (internalL S).card = S.card := by
  have key : internalL S = S.filter (fun x => ¬ (x - 1 ∉ S)) := by
    simp only [internalL, not_not]
  rw [leftEnds, key]
  exact Finset.filter_card_add_filter_neg_card_eq_card (fun x => x - 1 ∉ S)

/-- **Left = right.** The number of left endpoints equals the number of right
    endpoints: every maximal run starts once and ends once. -/
theorem card_leftEnds_eq_card_rightEnds (S : Finset ℤ) :
    (leftEnds S).card = (rightEnds S).card := by
  have hL := card_leftEnds_add_card_internalL S
  have hR := card_rightEnds_add_card_internalR S
  have hint := card_internalL_eq_card_internalR S
  omega

/-! ### Edge summands count endpoints -/

/-- The rising-edge set `(S-1)\S` is the `(· - 1)`-image of the left endpoints,
    hence has cardinality `numRuns`. -/
theorem card_image_sub_one_sdiff (S : Finset ℤ) :
    ((S.image (· - 1)) \ S).card = (leftEnds S).card := by
  have hset : (S.image (· - 1)) \ S = (leftEnds S).image (· - 1) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_image, leftEnds, Finset.mem_filter]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hx⟩
      exact ⟨a, ⟨ha, by simpa using hx⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hpred⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, by simpa using hpred⟩
  rw [hset, Finset.card_image_of_injective]
  intro a b hab
  simpa using hab

/-- The falling-edge set `(S+1)\S` is the `(· + 1)`-image of the right endpoints,
    hence has cardinality `|rightEnds|`. -/
theorem card_image_add_one_sdiff (S : Finset ℤ) :
    ((S.image (· + 1)) \ S).card = (rightEnds S).card := by
  have hset : (S.image (· + 1)) \ S = (rightEnds S).image (· + 1) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_image, rightEnds, Finset.mem_filter]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hx⟩
      exact ⟨a, ⟨ha, by simpa using hx⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hsucc⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, by simpa using hsucc⟩
  rw [hset, Finset.card_image_of_injective]
  intro a b hab
  simpa using hab

/-! ### Main identity: boundary = 2 · runs -/

/-- **Boundary counts runs.** For any finite `S ⊆ ℤ`, the number of boundary
    edges equals twice the number of maximal runs:
        `edgeBoundaryCount S = 2 * numRuns S`.
    Each maximal run contributes exactly two boundary edges (one rising at its
    left end, one falling at its right end). -/
theorem edgeBoundaryCount_eq_two_mul_numRuns (S : Finset ℤ) :
    edgeBoundaryCount S = 2 * numRuns S := by
  rw [edgeBoundaryCount, numRuns, card_image_sub_one_sdiff,
    card_image_add_one_sdiff, ← card_leftEnds_eq_card_rightEnds]
  ring

/-- **Quantitative stability.** The boundary has `2 + 2k` edges iff `S` has
    exactly `k + 1` maximal runs: each extra run/gap adds two boundary edges. -/
theorem edgeBoundaryCount_eq_iff_numRuns (S : Finset ℤ) (k : ℕ) :
    edgeBoundaryCount S = 2 + 2 * k ↔ numRuns S = k + 1 := by
  rw [edgeBoundaryCount_eq_two_mul_numRuns]
  omega

/-! ### Endpoints, nonemptiness and the single-run (interval) case -/

/-- For nonempty `S`, the minimum is a left endpoint, so there is at least one
    run. -/
theorem min'_mem_leftEnds {S : Finset ℤ} (h : S.Nonempty) :
    S.min' h ∈ leftEnds S := by
  simp only [leftEnds, Finset.mem_filter]
  refine ⟨S.min'_mem h, ?_⟩
  intro hcon
  have := S.min'_le _ hcon
  omega

/-- A nonempty set has at least one run. -/
theorem one_le_numRuns {S : Finset ℤ} (h : S.Nonempty) : 1 ≤ numRuns S := by
  rw [numRuns]
  exact Finset.card_pos.mpr ⟨S.min' h, min'_mem_leftEnds h⟩

/-- A nonempty set with a single run has boundary exactly `2`, recovering the
    interval case of the parent rigidity theorem. -/
theorem numRuns_eq_one_iff_edgeBoundaryCount_eq_two {S : Finset ℤ} :
    numRuns S = 1 ↔ edgeBoundaryCount S = 2 := by
  rw [edgeBoundaryCount_eq_two_mul_numRuns]
  omega

/-- An integer interval `[a, b]` (`a ≤ b`) has exactly one maximal run: only its
    left endpoint `a` lacks a predecessor in the set. -/
theorem numRuns_Icc {a b : ℤ} (h : a ≤ b) :
    numRuns (Finset.Icc a b) = 1 := by
  rw [numRuns]
  have : leftEnds (Finset.Icc a b) = {a} := by
    ext x
    simp only [leftEnds, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hax, hxb⟩, hpred⟩
      by_contra hne
      exact hpred ⟨by omega, by omega⟩
    · rintro rfl
      refine ⟨⟨le_refl _, h⟩, ?_⟩
      rintro ⟨h1, _⟩
      omega
  rw [this, Finset.card_singleton]

/-- Consequently an interval has boundary edge count exactly `2`. -/
theorem edgeBoundaryCount_Icc {a b : ℤ} (h : a ≤ b) :
    edgeBoundaryCount (Finset.Icc a b) = 2 := by
  rw [edgeBoundaryCount_eq_two_mul_numRuns, numRuns_Icc h]

/-! ### Fuglede-type lower bound: more runs ⇒ farther from an interval -/

/-- The symmetric-difference distance from `S` to its spanning interval is at
    least the number of gaps `numRuns S - 1`. Combined with the main identity,
    `edgeBoundaryCount S = 2 + 2k` forces `S` to differ from the interval
    `[min S, max S]` in at least `k` points: a discrete Fuglede-type stability
    estimate. -/
theorem numRuns_sub_one_le_card_sdiff {S : Finset ℤ} (h : S.Nonempty) :
    numRuns S - 1 ≤ (Finset.Icc (S.min' h) (S.max' h) \ S).card := by
  set m := S.min' h with hm
  set M := S.max' h with hM
  -- Build an injection from `leftEnds S \ {m}` into the missing points.
  have key : ((leftEnds S).erase m).card ≤ (Finset.Icc m M \ S).card := by
    apply Finset.card_le_card_of_injOn (fun x => x - 1)
    · -- each non-minimal left endpoint has a missing predecessor in the interval
      intro x hx
      rw [Finset.mem_coe, Finset.mem_erase] at hx
      obtain ⟨hxm, hxL⟩ := hx
      rw [leftEnds, Finset.mem_filter] at hxL
      obtain ⟨hxS, hpred⟩ := hxL
      rw [Finset.mem_coe]
      simp only [Finset.mem_sdiff, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, hpred⟩
      · -- m ≤ x - 1 : since x ∈ S, m ≤ x, and x ≠ m, x > m so x - 1 ≥ m
        have hmx : m ≤ x := by rw [hm]; exact S.min'_le _ hxS
        omega
      · -- x - 1 ≤ M : x ≤ M so x - 1 < M
        have hxM : x ≤ M := by rw [hM]; exact S.le_max' _ hxS
        omega
    · -- injective on the erase set
      intro a _ b _ hab
      have : a - 1 = b - 1 := hab
      omega
  have hcard : ((leftEnds S).erase m).card = numRuns S - 1 := by
    rw [numRuns, Finset.card_erase_of_mem (min'_mem_leftEnds h)]
  omega

end DiscreteIsoperimetric1DRuns
