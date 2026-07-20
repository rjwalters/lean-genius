/-
  Szemerédi Regularity Lemma — OQ-04: the outer-loop assembly (item 3).

  `state.md` "What remains open" lists three pieces of the strong (AFKS) regularity lemma:

    1. **Energy-increment step** — a bad `ε`-irregular pair forces a refinement whose
       `partitionEnergy` jumps by a fixed `δ = δ(ε)` (the analytic crux; supplied in the
       sibling energy files as the sharp `2×2` gain / the internalized `Bside` capstone).
    2. **Two-level statement** — the AFKS conclusion packaged as a single proposition,
       `IsAFKSTwoLevel` (discharged in `SzemerediRegularityOQ04TwoLevel`).
    3. **Assemble** — *run the outer loop* using the finiteness/termination certificate to
       produce such a two-level partition.

  This file discharges the **structural half of item 3**: it wires the termination
  certificate (`afks_regular_step_within_bound`, itself the contrapositive of the sharp
  energy iteration-count bound) to the packaged two-level conclusion
  (`IsAFKSTwoLevel`).  The one input it takes as an explicit hypothesis is the
  *regular-or-refine dichotomy* — "if the current fine partition is **not** AFKS-fine-regular
  then a witnessed sharp-`2×2` gain-refinement step exists".  That dichotomy is exactly
  item 1's analytic realizability (a fine partition failing the `E(k)`-regular budget
  contains an `E(k)`-irregular pair, and refining it along the sharp `2×2` split realizes
  the no-loss energy gain); it is *not* proved here.  What **is** proved here is that the
  dichotomy plus the termination bound genuinely *closes the loop*: a two-level partition is
  reached in a bounded number of refinements.

  Contents:

  * `IsWitnessedSharpStep G parts n eps m` — the per-step predicate "the refinement
    `parts n → parts (n+1)` is a mass-`m`, `eps`-irregular sharp `2×2` split", named so the
    dichotomy hypothesis reads cleanly.  It matches, clause-for-clause, the witness inside
    `afks_regular_step_within_bound`.
  * `exists_afksTwoLevel_of_dichotomy` — **the assembly**: from a fixed coarse `ε`-regular
    partition `Vparts`, a refinement chain `parts : ℕ → …` (each a cover by pairwise-disjoint
    parts, each refining `Vparts`), a horizon `N` beyond the sharp iteration bound at the fine
    tolerance `E(k)`, and the dichotomy, there **exists** a step `n < N` at which
    `(Vparts, parts n)` is an `IsAFKSTwoLevel` partition at coarse tolerance `ε` and dependent
    fine tolerance `E`.  This is item 3 — the outer AFKS loop run to its regular step —
    modulo the analytic dichotomy of item 1.
  * `exists_afksTwoLevel_of_dichotomy_equipartition` — the same conclusion with the horizon
    stated in the vertex-count-free `k²/E(k)⁴` form (the tower-free bound) via the
    equipartition mass floor `m = n/k`.

  0 axioms, 0 sorries.  Everything above the dichotomy hypothesis is machine-checked from the
  already-verified termination bound and the two-level packaging.
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Assembly
import Proofs.SzemerediRegularityOQ04TwoLevel

namespace Szemeredi.RegularityOQ04Outer

open Classical Szemeredi.Core Szemeredi.RegularityOQ04ToleranceBridge
  Szemeredi.RegularityOQ04TwoLevel

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE PER-STEP WITNESS PREDICATE
-- ═══════════════════════════════════════════════════════════════════

/-- **A witnessed sharp `2×2` refinement step.**  The refinement `parts n → parts (n+1)`
    splits two distinct mass-`≥ m` parts `A, B` of `parts n` into `{A₁,A₂}`, `{B₁,B₂}`
    (fresh, disjoint, covering) so that the `A₁`/`B₁` corner keeps an `eps`-fraction of the
    mass and its edge density deviates from the parent `A,B` density by `≥ eps` — i.e. the
    step is a mass-`m`, `eps`-irregular sharp `2×2` split.

    This is precisely the witness negated inside `afks_regular_step_within_bound`; isolating
    it as a named predicate lets the outer-loop dichotomy hypothesis be stated readably. -/
def IsWitnessedSharpStep (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (n : ℕ) (eps m : ℚ) : Prop :=
  ∃ R : Finset (Finset V), ∃ A B A₁ A₂ B₁ B₂ : Finset V,
    parts n = insert A (insert B R) ∧
    parts (n + 1) = insert A₁ (insert A₂ (insert B₁ (insert B₂ R))) ∧
    A₁ ∪ A₂ = A ∧ B₁ ∪ B₂ = B ∧ Disjoint A₁ A₂ ∧ Disjoint B₁ B₂ ∧
    A ∉ insert B R ∧ B ∉ R ∧
    A₁ ∉ insert A₂ (insert B₁ (insert B₂ R)) ∧ A₂ ∉ insert B₁ (insert B₂ R) ∧
    B₁ ∉ insert B₂ R ∧ B₂ ∉ R ∧
    m ≤ (A.card : ℚ) ∧ m ≤ (B.card : ℚ) ∧
    eps * A.card ≤ (A₁.card : ℚ) ∧ eps * B.card ≤ (B₁.card : ℚ) ∧
    eps ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B|

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE OUTER-LOOP ASSEMBLY (item 3, modulo the item-1 dichotomy)
-- ═══════════════════════════════════════════════════════════════════

/-- **The outer AFKS loop, run to its regular step.**  Fix a coarse `ε`-regular partition
    `Vparts` (size `k = |Vparts|`) and a refinement chain `parts : ℕ → Finset (Finset V)`,
    each term a cover by pairwise-disjoint parts and each refining `Vparts`.  Suppose the
    horizon `N` exceeds the sharp iteration bound `n² / (E(k)⁴·m²)` at the *fine* tolerance
    `E(k)`, and the **regular-or-refine dichotomy** holds: whenever a term `parts n`
    (`n < N`) fails to be AFKS-fine-regular at coarse budget `ε` and fine tolerance `E(k)`,
    the step `parts n → parts (n+1)` is a witnessed mass-`m`, `E(k)`-irregular sharp `2×2`
    split.

    Then there is a step `n < N` at which `(Vparts, parts n)` is an `IsAFKSTwoLevel`
    partition: the coarse level is `ε`-regular, `parts n` refines it, and `parts n` is
    AFKS-fine-regular at the dependent tolerance `E(k)`.

    *Why this closes item 3.*  `afks_regular_step_within_bound` (the contrapositive of the
    energy iteration-count bound) guarantees some `n < N` at which **no** witnessed sharp
    `2×2` refinement step occurs.  By the dichotomy's contrapositive, that `parts n` must
    already be AFKS-fine-regular — the loop has reached its regular partition.  Packaging it
    against the fixed coarse `ε`-regular `Vparts` yields the two-level conclusion.  The only
    unproved ingredient is the dichotomy itself (item 1's analytic energy-increment
    realizability); the termination-to-conclusion wiring is fully machine-checked. -/
theorem exists_afksTwoLevel_of_dichotomy
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℚ) (E : ℕ → ℚ) (Vparts : Finset (Finset V)) (parts : ℕ → Finset (Finset V))
    (N : ℕ) (m : ℚ)
    (hEpos : 0 < E Vparts.card) (hm : 0 < m) (hcard : 0 < (Fintype.card V : ℚ))
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hN : (Fintype.card V : ℚ) ^ 2 / (E Vparts.card ^ 4 * m ^ 2) < N)
    (hcoarse : IsRegularPartition G ε Vparts)
    (href : ∀ n, IsRefinement (parts n) Vparts)
    (hdich : ∀ n, n < N → ¬ IsAFKSFineRegular G ε (E Vparts.card) (parts n) →
      IsWitnessedSharpStep G parts n (E Vparts.card) m) :
    ∃ n < N, IsAFKSTwoLevel G ε E Vparts (parts n) := by
  obtain ⟨n, hn, hno⟩ :=
    Szemeredi.RegularityOQ04Bridge.afks_regular_step_within_bound
      G parts N (E Vparts.card) m hEpos hm hcard hcover hdisjoint hN
  refine ⟨n, hn, ?_⟩
  -- The found step has no witnessed sharp 2×2 refinement; by the dichotomy's
  -- contrapositive `parts n` is therefore AFKS-fine-regular.
  have hfine : IsAFKSFineRegular G ε (E Vparts.card) (parts n) := by
    by_contra hcon
    exact hno (hdich n hn hcon)
  exact
    { coarseRegular := hcoarse
      refines := href n
      fineRegular := hfine }

/-- **Vertex-count-free (tower-free) horizon form.**  Identical conclusion to
    `exists_afksTwoLevel_of_dichotomy`, but the horizon requirement is stated in the
    dimension-free `k² / E(k)⁴` shape: with an equipartition mass floor `m = n/k`
    (every refined part carries at least a `1/k` fraction of the vertices), the sharp
    bound `n² / (E(k)⁴·m²)` collapses to `k² / E(k)⁴`, independent of `n = |V|`.  Any
    horizon `N` exceeding `k² / E(k)⁴` therefore also exceeds the vertex-dependent bound at
    `m = n/k`, so the assembly applies. -/
theorem exists_afksTwoLevel_of_dichotomy_equipartition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℚ) (E : ℕ → ℚ) (Vparts : Finset (Finset V)) (parts : ℕ → Finset (Finset V))
    (N : ℕ)
    (hEpos : 0 < E Vparts.card) (hkpos : 0 < Vparts.card) (hcard : 0 < (Fintype.card V : ℚ))
    (hcover : ∀ n, ∀ v : V, ∃ P ∈ parts n, v ∈ P)
    (hdisjoint : ∀ n, ∀ P Q : Finset V, P ∈ parts n → Q ∈ parts n → P ≠ Q →
      Disjoint P Q)
    (hN : (Vparts.card : ℚ) ^ 2 / E Vparts.card ^ 4 < N)
    (hcoarse : IsRegularPartition G ε Vparts)
    (href : ∀ n, IsRefinement (parts n) Vparts)
    (hdich : ∀ n, n < N → ¬ IsAFKSFineRegular G ε (E Vparts.card) (parts n) →
      IsWitnessedSharpStep G parts n (E Vparts.card)
        ((Fintype.card V : ℚ) / Vparts.card)) :
    ∃ n < N, IsAFKSTwoLevel G ε E Vparts (parts n) := by
  -- Translate the `k²/E(k)⁴` horizon into the vertex-dependent `n²/(E(k)⁴·m²)` horizon
  -- at `m = n/k`, then apply the general assembly.
  set k : ℚ := (Vparts.card : ℚ) with hk
  set n : ℚ := (Fintype.card V : ℚ) with hnc
  have hkq : (0 : ℚ) < k := by rw [hk]; exact_mod_cast hkpos
  have hmpos : (0 : ℚ) < n / k := div_pos hcard hkq
  have hEne : E Vparts.card ≠ 0 := hEpos.ne'
  have hkne : k ≠ 0 := hkq.ne'
  have hnne : n ≠ 0 := hcard.ne'
  -- `n² / (E(k)⁴ · (n/k)²) = k² / E(k)⁴`.
  have heq : n ^ 2 / (E Vparts.card ^ 4 * (n / k) ^ 2) = k ^ 2 / E Vparts.card ^ 4 := by
    field_simp
  refine exists_afksTwoLevel_of_dichotomy G ε E Vparts parts N (n / k)
    hEpos hmpos hcard hcover hdisjoint ?_ hcoarse href hdich
  rw [heq]; exact hN

end Szemeredi.RegularityOQ04Outer
