import Mathlib

/-!
# Local packing consumer for the B.3 residual Gram obstruction

This file packages the exact logical interface isolated by the q=9 B.3
audit.  It does not prove the outer-design dichotomy: it proves that either
horn of that dichotomy contradicts any symmetric residual relation having
the prescribed degrees, eligible support, and Gram common-neighbor law.
-/

namespace Erdos85

variable {V : Type*} [Fintype V]

/-- A demanded local packing inside the eligible relation `H`, with no
`W`-conflicting pair. -/
def IsLocalGramPacking (H W : V → V → Prop) (d : V → ℕ)
    (u : V) (X : Finset V) : Prop :=
  X.card = d u ∧
  (∀ x ∈ X, H u x) ∧
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ¬ W x y

/-- A vertex belongs to every demanded local packing at `u`. -/
def IsForcedLocalGramNeighbor (H W : V → V → Prop) (d : V → ℕ)
    (u w : V) : Prop :=
  ∀ X : Finset V, IsLocalGramPacking H W d u X → w ∈ X

/-- A demanded local packing at `u` which omits the candidate `w`. -/
def HasLocalGramPackingAvoiding (H W : V → V → Prop) (d : V → ℕ)
    (u w : V) : Prop :=
  ∃ X : Finset V, IsLocalGramPacking H W d u X ∧ w ∉ X

/-- A demanded local packing at `u` which contains the candidate `w`. -/
def HasLocalGramPackingContaining (H W : V → V → Prop) (d : V → ℕ)
    (u w : V) : Prop :=
  ∃ X : Finset V, IsLocalGramPacking H W d u X ∧ w ∈ X

/-- The exact local alternative consumed by the Gram obstruction theorem. -/
def HasLocalGramPackingObstruction (H W : V → V → Prop)
    (d : V → ℕ) : Prop :=
  (∃ u, ∀ X : Finset V, ¬ IsLocalGramPacking H W d u X) ∨
  ∃ u v w, W u v ∧
    IsForcedLocalGramNeighbor H W d u w ∧
    IsForcedLocalGramNeighbor H W d v w

/-- A forced incidence whose reverse orientation is absent from every
demanded local packing. -/
def HasLocalGramPackingReciprocityObstruction
    (H W : V → V → Prop) (d : V → ℕ) : Prop :=
  ∃ u w, IsForcedLocalGramNeighbor H W d u w ∧
    ∀ Y : Finset V, IsLocalGramPacking H W d w Y → u ∉ Y

/-- Every demanded packing at one row makes some membership decision which
no demanded packing at the reverse row can match.  This is the first
configuration-level strengthening of the single forced-edge reciprocity
obstruction. -/
def HasLocalGramPackingOneRowCompatibilityObstruction
    (H W : V → V → Prop) (d : V → ℕ) : Prop :=
  ∃ u, ∀ X : Finset V, IsLocalGramPacking H W d u X →
    ∃ w,
      (w ∈ X ∧ ∀ Y : Finset V,
        IsLocalGramPacking H W d w Y → u ∉ Y) ∨
      (w ∉ X ∧ IsForcedLocalGramNeighbor H W d w u)

/-- A demanded packing lying between the two reverse-incidence bounds at
`u`: it contains every candidate forced by the reverse local family and
omits every candidate impossible in the reverse local family. -/
def IsReverseIntervalLocalGramPacking
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ)
    (u : V) (X : Finset V) : Prop :=
  IsLocalGramPacking H W d u X ∧
  (∀ w, IsForcedLocalGramNeighbor H W d w u → w ∈ X) ∧
  ∀ w, (∀ Y : Finset V,
    IsLocalGramPacking H W d w Y → u ∉ Y) → w ∉ X

/-- A partial local packing: every member is eligible and distinct members
are conflict-free, but no target cardinality is imposed. -/
def IsLocalGramPrepacking (H W : V → V → Prop)
    (u : V) (F : Finset V) : Prop :=
  (∀ w ∈ F, H u w) ∧
  ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ¬ W x y

/-- The lower interval bound at `u`: rows whose every demanded packing
contains `u`. -/
noncomputable def reverseForcedLocalGramNeighborFinset
    (H W : V → V → Prop) (d : V → ℕ) (u : V) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun w =>
      IsForcedLocalGramNeighbor H W d w u

/-- The upper interval exclusion at `u`: rows having no demanded packing
which contains `u`. -/
noncomputable def reverseImpossibleLocalGramNeighborFinset
    (H W : V → V → Prop) (d : V → ℕ) (u : V) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun w =>
      ∀ Y : Finset V, IsLocalGramPacking H W d w Y → u ∉ Y

/-- A residual witness after contracting the reverse-forced lower bound and
deleting the reverse-impossible upper bound.  The remaining mathematical
task is precisely to produce such a `Y`. -/
def IsReverseIntervalContractedExtension
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ)
    (u : V) (Y : Finset V) : Prop :=
  let F := reverseForcedLocalGramNeighborFinset H W d u
  let I := reverseImpossibleLocalGramNeighborFinset H W d u
  IsLocalGramPrepacking H W u (F ∪ Y) ∧
  (F ∪ Y).card = d u ∧
  Disjoint (F ∪ Y) I

/-- A Hall/rank-style certificate at one row: every eligible conflict-free
superset of the forced lower bound which avoids the impossible upper set is
strictly smaller than the demanded cardinality. -/
def HasReverseIntervalRankDeficitAt
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) (u : V) : Prop :=
  let F := reverseForcedLocalGramNeighborFinset H W d u
  let I := reverseImpossibleLocalGramNeighborFinset H W d u
  ∀ X : Finset V, IsLocalGramPrepacking H W u X →
    F ⊆ X → Disjoint X I → X.card < d u

/-- The canonical fractional relaxation of a reverse-interval packing.
The mass has full demanded size, is supported on eligible rows, obeys every
point capacity, equals one on the reverse-forced lower fiber, and vanishes on
the reverse-impossible upper fiber. -/
def IsCanonicalFractionalIntervalExtension
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H W : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (u : V) (mass : V → ℚ) : Prop :=
  (∀ w, 0 ≤ mass w ∧ mass w ≤ 1) ∧
  (∑ w : V, mass w) = d u ∧
  (∀ w, 0 < mass w → H u w) ∧
  (∀ p, (∑ w ∈ Finset.univ.filter fun z => p ∈ B z, mass w) ≤ 1) ∧
  (∀ w, IsForcedLocalGramNeighbor H W d w u → mass w = 1) ∧
  ∀ w, (∀ Y : Finset V, IsLocalGramPacking H W d w Y → u ∉ Y) →
    mass w = 0

/-- A collision inside the canonical reverse-forced lower fiber already
makes a full fractional interval extension impossible: the two forced unit
masses violate the capacity of their shared point. -/
theorem no_canonicalFractionalIntervalExtension_of_forced_sharedPoint
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H W : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (u x y : V) (p : P) (hxy : x ≠ y)
    (hpx : p ∈ B x) (hpy : p ∈ B y)
    (hx : IsForcedLocalGramNeighbor H W d x u)
    (hy : IsForcedLocalGramNeighbor H W d y u) :
    ¬ ∃ mass, IsCanonicalFractionalIntervalExtension H W d B u mass := by
  rintro ⟨mass, hmass⟩
  rcases hmass with ⟨hnonneg, _, _, hcapacity, hforced, _⟩
  have hxmass : mass x = 1 := hforced x hx
  have hymass : mass y = 1 := hforced y hy
  let S := Finset.univ.filter fun z => p ∈ B z
  have hxS : x ∈ S := by simp [S, hpx]
  have hyS : y ∈ S := by simp [S, hpy]
  have hpairSubset : ({x, y} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxS
    · exact hyS
  have hpairLe : mass x + mass y ≤ ∑ z ∈ S, mass z := by
    calc
      mass x + mass y = ∑ z ∈ ({x, y} : Finset V), mass z := by
        simp [hxy]
      _ ≤ ∑ z ∈ S, mass z := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hpairSubset
          (fun z _ _ => hnonneg z |>.1)
  have hcap : (∑ z ∈ S, mass z) ≤ 1 := by
    simpa [S] using hcapacity p
  rw [hxmass, hymass] at hpairLe
  norm_num at hpairLe hcap
  exact (not_le_of_gt (show (1 : ℚ) < 2 by norm_num)) (hpairLe.trans hcap)

/-- Fractional hypergraph weak duality in the exact point-capacity form used
by the canonical interval relaxation. -/
theorem totalMass_le_totalPointWeight
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (B : V → Finset P) (mass : V → ℚ) (weight : P → ℚ)
    (hmass : ∀ w, 0 ≤ mass w)
    (hweight : ∀ p, 0 ≤ weight p)
    (hcapacity : ∀ p,
      (∑ w ∈ Finset.univ.filter fun z => p ∈ B z, mass w) ≤ 1)
    (hcover : ∀ w, 0 < mass w → 1 ≤ ∑ p ∈ B w, weight p) :
    (∑ w : V, mass w) ≤ ∑ p : P, weight p := by
  classical
  calc
    (∑ w : V, mass w) ≤
        ∑ w : V, mass w * (∑ p ∈ B w, weight p) := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hzero : mass w = 0
      · simp [hzero]
      · have hpos : 0 < mass w := lt_of_le_of_ne (hmass w) (Ne.symm hzero)
        exact (le_mul_iff_one_le_right hpos).2 (hcover w hpos)
    _ = ∑ p : P, weight p *
        (∑ w ∈ Finset.univ.filter fun z => p ∈ B z, mass w) := by
      calc
        (∑ w : V, mass w * (∑ p ∈ B w, weight p)) =
            ∑ w : V, ∑ p : P,
              if p ∈ B w then mass w * weight p else 0 := by
          apply Finset.sum_congr rfl
          intro w _
          rw [Finset.mul_sum]
          rw [← Finset.sum_filter]
          simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
        _ = ∑ p : P, ∑ w : V,
              if p ∈ B w then mass w * weight p else 0 := by
          exact Finset.sum_comm
        _ = ∑ p : P, weight p *
            (∑ w ∈ Finset.univ.filter fun z => p ∈ B z, mass w) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.mul_sum]
          rw [← Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro w _
          by_cases hp : p ∈ B w <;> simp [mul_comm]
    _ ≤ ∑ p : P, weight p := by
      apply Finset.sum_le_sum
      intro p _
      calc
        weight p * (∑ w ∈ Finset.univ.filter fun z => p ∈ B z, mass w)
            ≤ weight p * 1 :=
          mul_le_mul_of_nonneg_left (hcapacity p) (hweight p)
        _ = weight p := by ring

/-- A symmetric fractional residual relation with exact row degrees and the
ordered point capacities forced by the Gram law.  Unlike the one-row
canonical relaxation, the same mass variable is shared by both orientations
of every residual edge. -/
def IsSymmetricFractionalPointPacking
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (mass : V → V → ℚ) : Prop :=
  (∀ u v, 0 ≤ mass u v) ∧
  (∀ u, (∑ v : V, mass u v) = d u) ∧
  (∀ u v, 0 < mass u v → H u v) ∧
  (∀ u p,
    (∑ v ∈ Finset.univ.filter fun w => p ∈ B w, mass u v) ≤ 1) ∧
  ∀ u v, mass u v = mass v u

/-- Global row/point-price weak duality for a symmetric fractional residual
packing.  This is the exact Farkas consumer exposed by the q=9 B.3 symmetric
point-mass probe. -/
theorem weightedDegree_le_totalPointPrice_of_symmetricFractionalPacking
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (mass : V → V → ℚ) (rowPrice : V → ℚ)
    (pointPrice : V → P → ℚ)
    (hmass : IsSymmetricFractionalPointPacking H d B mass)
    (hpointPrice : ∀ u p, 0 ≤ pointPrice u p)
    (hedge : ∀ u v, H u v →
      rowPrice u + rowPrice v ≤
        (∑ p ∈ B v, pointPrice u p) +
        ∑ p ∈ B u, pointPrice v p) :
    (∑ u : V, (d u : ℚ) * rowPrice u) ≤
      ∑ u : V, ∑ p : P, pointPrice u p := by
  classical
  rcases hmass with ⟨hnonneg, hdegree, hsupport, hcapacity, hsymm⟩
  have hcolumn (v : V) : (∑ u : V, mass u v) = d v := by
    calc
      (∑ u : V, mass u v) = ∑ u : V, mass v u := by
        apply Finset.sum_congr rfl
        intro u _
        exact hsymm u v
      _ = d v := hdegree v
  have hedgeWeighted (u v : V) :
      mass u v * (rowPrice u + rowPrice v) ≤
        mass u v * ((∑ p ∈ B v, pointPrice u p) +
          ∑ p ∈ B u, pointPrice v p) := by
    by_cases hzero : mass u v = 0
    · simp [hzero]
    · have hpos : 0 < mass u v :=
        lt_of_le_of_ne (hnonneg u v) (Ne.symm hzero)
      exact mul_le_mul_of_nonneg_left (hedge u v (hsupport u v hpos))
        (hnonneg u v)
  have hweightedEdge :
      (∑ u : V, ∑ v : V, mass u v * (rowPrice u + rowPrice v)) ≤
        ∑ u : V, ∑ v : V,
          mass u v * ((∑ p ∈ B v, pointPrice u p) +
            ∑ p ∈ B u, pointPrice v p) := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact hedgeWeighted u v
  have hleft :
      (∑ u : V, ∑ v : V, mass u v * (rowPrice u + rowPrice v)) =
        2 * ∑ u : V, (d u : ℚ) * rowPrice u := by
    calc
      (∑ u : V, ∑ v : V, mass u v * (rowPrice u + rowPrice v)) =
          (∑ u : V, rowPrice u * ∑ v : V, mass u v) +
          ∑ v : V, rowPrice v * ∑ u : V, mass u v := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro u _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          ring
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          ring
      _ = (∑ u : V, rowPrice u * d u) +
          ∑ v : V, rowPrice v * d v := by
        simp_rw [hdegree, hcolumn]
      _ = 2 * ∑ u : V, (d u : ℚ) * rowPrice u := by
        simp_rw [mul_comm (rowPrice _) (d _ : ℚ)]
        ring
  have hright :
      (∑ u : V, ∑ v : V,
        mass u v * ((∑ p ∈ B v, pointPrice u p) +
          ∑ p ∈ B u, pointPrice v p)) ≤
        2 * ∑ u : V, ∑ p : P, pointPrice u p := by
    have hfirst :
        (∑ u : V, ∑ v : V,
          mass u v * ∑ p ∈ B v, pointPrice u p) ≤
          ∑ u : V, ∑ p : P, pointPrice u p := by
      apply Finset.sum_le_sum
      intro u _
      calc
        (∑ v : V, mass u v * ∑ p ∈ B v, pointPrice u p) =
            ∑ p : P, pointPrice u p *
              (∑ v ∈ Finset.univ.filter fun w => p ∈ B w, mass u v) := by
          calc
            (∑ v : V, mass u v * ∑ p ∈ B v, pointPrice u p) =
                ∑ v : V, ∑ p : P,
                  if p ∈ B v then mass u v * pointPrice u p else 0 := by
              apply Finset.sum_congr rfl
              intro v _
              rw [Finset.mul_sum]
              rw [← Finset.sum_filter]
              simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
            _ = ∑ p : P, ∑ v : V,
                  if p ∈ B v then mass u v * pointPrice u p else 0 := by
              exact Finset.sum_comm
            _ = ∑ p : P, pointPrice u p *
                  (∑ v ∈ Finset.univ.filter fun w => p ∈ B w,
                    mass u v) := by
              apply Finset.sum_congr rfl
              intro p _
              rw [Finset.mul_sum]
              rw [← Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro v _
              by_cases hp : p ∈ B v <;> simp [mul_comm]
        _ ≤ ∑ p : P, pointPrice u p := by
          apply Finset.sum_le_sum
          intro p _
          calc
            pointPrice u p *
                (∑ v ∈ Finset.univ.filter fun w => p ∈ B w, mass u v)
                ≤ pointPrice u p * 1 :=
              mul_le_mul_of_nonneg_left (hcapacity u p) (hpointPrice u p)
            _ = pointPrice u p := by ring
    have hsecond :
        (∑ u : V, ∑ v : V,
          mass u v * ∑ p ∈ B u, pointPrice v p) ≤
          ∑ u : V, ∑ p : P, pointPrice u p := by
      calc
        (∑ u : V, ∑ v : V,
          mass u v * ∑ p ∈ B u, pointPrice v p) =
            ∑ u : V, ∑ v : V,
              mass u v * ∑ p ∈ B v, pointPrice u p := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro v _
          rw [hsymm v u]
        _ ≤ ∑ u : V, ∑ p : P, pointPrice u p := hfirst
    calc
      (∑ u : V, ∑ v : V,
        mass u v * ((∑ p ∈ B v, pointPrice u p) +
          ∑ p ∈ B u, pointPrice v p)) =
          (∑ u : V, ∑ v : V,
            mass u v * ∑ p ∈ B v, pointPrice u p) +
          ∑ u : V, ∑ v : V,
            mass u v * ∑ p ∈ B u, pointPrice v p := by
        simp_rw [mul_add, Finset.sum_add_distrib]
      _ ≤
          (∑ u : V, ∑ p : P, pointPrice u p) +
          ∑ u : V, ∑ p : P, pointPrice u p :=
        add_le_add hfirst hsecond
      _ = 2 * ∑ u : V, ∑ p : P, pointPrice u p := by ring
  rw [hleft] at hweightedEdge
  have htwice :
      2 * (∑ u : V, (d u : ℚ) * rowPrice u) ≤
        2 * ∑ u : V, ∑ p : P, pointPrice u p :=
    hweightedEdge.trans hright
  linarith

/-- A strict global row/point price certificate excludes every symmetric
fractional point packing. -/
theorem no_symmetricFractionalPointPacking_of_rowPointPrices
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (rowPrice : V → ℚ) (pointPrice : V → P → ℚ)
    (hpointPrice : ∀ u p, 0 ≤ pointPrice u p)
    (hedge : ∀ u v, H u v →
      rowPrice u + rowPrice v ≤
        (∑ p ∈ B v, pointPrice u p) +
        ∑ p ∈ B u, pointPrice v p)
    (hstrict :
      (∑ u : V, ∑ p : P, pointPrice u p) <
        ∑ u : V, (d u : ℚ) * rowPrice u) :
    ¬ ∃ mass, IsSymmetricFractionalPointPacking H d B mass := by
  rintro ⟨mass, hmass⟩
  have hdual :=
    weightedDegree_le_totalPointPrice_of_symmetricFractionalPacking
      H d B mass rowPrice pointPrice hmass hpointPrice hedge
  exact (not_lt_of_ge hdual) hstrict

/-- **Reduced common-fiber price certificate.**  Rows in `S` carry local
point covers `localPrice`; rows outside `S` may only pay at the common point
`p`, through `compensation`.  Consequently the global edge inequalities
reduce to internal edges of `S` and cross edges leaving `S`.  This is the
four-row certificate shape isolated by the q=9 B.3 diagnostics. -/
theorem no_symmetricFractionalPointPacking_of_commonFiberPrices
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (S : Finset V) (p : P) (rowPrice : V → ℚ)
    (localPrice : V → P → ℚ) (compensation : V → ℚ)
    (hcommon : ∀ u ∈ S, p ∈ B u)
    (hlocalNonneg : ∀ u q, 0 ≤ localPrice u q)
    (hcompNonneg : ∀ u, 0 ≤ compensation u)
    (hinternal : ∀ u ∈ S, ∀ v ∈ S, H u v →
      rowPrice u + rowPrice v ≤
        (∑ q ∈ B v, localPrice u q) +
        ∑ q ∈ B u, localPrice v q)
    (hcross : ∀ u ∈ S, ∀ v, v ∉ S → (H u v ∨ H v u) →
      rowPrice u ≤
        (∑ q ∈ B v, localPrice u q) + compensation v)
    (hstrict :
      (∑ u : V, if u ∈ S then (∑ q : P, localPrice u q)
        else compensation u) <
      ∑ u : V, (d u : ℚ) * if u ∈ S then rowPrice u else 0) :
    ¬ ∃ mass, IsSymmetricFractionalPointPacking H d B mass := by
  classical
  let globalRowPrice : V → ℚ := fun u =>
    if u ∈ S then rowPrice u else 0
  let globalPointPrice : V → P → ℚ := fun u q =>
    if u ∈ S then localPrice u q
    else if q = p then compensation u else 0
  have hglobalNonneg : ∀ u q, 0 ≤ globalPointPrice u q := by
    intro u q
    by_cases hu : u ∈ S
    · simp [globalPointPrice, hu, hlocalNonneg u q]
    · by_cases hq : q = p <;>
        simp [globalPointPrice, hu, hq, hcompNonneg u]
  apply no_symmetricFractionalPointPacking_of_rowPointPrices
    H d B globalRowPrice globalPointPrice
  · exact hglobalNonneg
  · intro u v huv
    by_cases hu : u ∈ S
    · by_cases hv : v ∈ S
      · simpa [globalRowPrice, globalPointPrice, hu, hv] using
          hinternal u hu v hv huv
      · have hp := hcommon u hu
        simpa [globalRowPrice, globalPointPrice, hu, hv, hp] using
          hcross u hu v hv (Or.inl huv)
    · by_cases hv : v ∈ S
      · have hp := hcommon v hv
        simpa [globalRowPrice, globalPointPrice, hu, hv, hp, add_comm] using
          hcross v hv u hu (Or.inr huv)
      · have hleft : globalRowPrice u + globalRowPrice v = 0 := by
          simp [globalRowPrice, hu, hv]
        rw [hleft]
        exact add_nonneg
          (Finset.sum_nonneg fun q _ => hglobalNonneg u q)
          (Finset.sum_nonneg fun q _ => hglobalNonneg v q)
  · simpa [globalRowPrice, globalPointPrice] using hstrict

/-- **Fiber-plus-auxiliary price certificate.**  This generalizes the common
fiber adapter to a support `R` which may contain one row not incident with
`p`.  Outside compensation contributes to a cross edge exactly when the
supported endpoint's block contains `p`; hence fiber rows receive it while a
nonincident auxiliary row must be covered entirely by its local prices. -/
theorem no_symmetricFractionalPointPacking_of_supportWithPointCompensation
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (R : Finset V) (p : P) (rowPrice : V → ℚ)
    (localPrice : V → P → ℚ) (compensation : V → ℚ)
    (hlocalNonneg : ∀ u q, 0 ≤ localPrice u q)
    (hcompNonneg : ∀ u, 0 ≤ compensation u)
    (hinternal : ∀ u ∈ R, ∀ v ∈ R, H u v →
      rowPrice u + rowPrice v ≤
        (∑ q ∈ B v, localPrice u q) +
        ∑ q ∈ B u, localPrice v q)
    (hcross : ∀ u ∈ R, ∀ v, v ∉ R → (H u v ∨ H v u) →
      rowPrice u ≤
        (∑ q ∈ B v, localPrice u q) +
        if p ∈ B u then compensation v else 0)
    (hstrict :
      (∑ u : V, if u ∈ R then (∑ q : P, localPrice u q)
        else compensation u) <
      ∑ u : V, (d u : ℚ) * if u ∈ R then rowPrice u else 0) :
    ¬ ∃ mass, IsSymmetricFractionalPointPacking H d B mass := by
  classical
  let globalRowPrice : V → ℚ := fun u =>
    if u ∈ R then rowPrice u else 0
  let globalPointPrice : V → P → ℚ := fun u q =>
    if u ∈ R then localPrice u q
    else if q = p then compensation u else 0
  have hglobalNonneg : ∀ u q, 0 ≤ globalPointPrice u q := by
    intro u q
    by_cases hu : u ∈ R
    · simp [globalPointPrice, hu, hlocalNonneg u q]
    · by_cases hq : q = p <;>
        simp [globalPointPrice, hu, hq, hcompNonneg u]
  apply no_symmetricFractionalPointPacking_of_rowPointPrices
    H d B globalRowPrice globalPointPrice hglobalNonneg
  · intro u v huv
    by_cases hu : u ∈ R
    · by_cases hv : v ∈ R
      · simpa [globalRowPrice, globalPointPrice, hu, hv] using
          hinternal u hu v hv huv
      · simpa [globalRowPrice, globalPointPrice, hu, hv] using
          hcross u hu v hv (Or.inl huv)
    · by_cases hv : v ∈ R
      · simpa [globalRowPrice, globalPointPrice, hu, hv, add_comm] using
          hcross v hv u hu (Or.inr huv)
      · have hleft : globalRowPrice u + globalRowPrice v = 0 := by
          simp [globalRowPrice, hu, hv]
        rw [hleft]
        exact add_nonneg
          (Finset.sum_nonneg fun q _ => hglobalNonneg u q)
          (Finset.sum_nonneg fun q _ => hglobalNonneg v q)
  · simpa [globalRowPrice, globalPointPrice] using hstrict
/-- Unit row prices on a finite support set.  This is the direct formal
interface for the q=9 non-diagonal-fiber prize-cover certificates. -/
theorem no_symmetricFractionalPointPacking_of_unitSupportPointPrices
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (S : Finset V) (pointPrice : V → P → ℚ)
    (hpointPrice : ∀ u p, 0 ≤ pointPrice u p)
    (hedge : ∀ u v, H u v →
      (if u ∈ S then (1 : ℚ) else 0) + (if v ∈ S then 1 else 0) ≤
        (∑ p ∈ B v, pointPrice u p) +
        ∑ p ∈ B u, pointPrice v p)
    (hstrict :
      (∑ u : V, ∑ p : P, pointPrice u p) <
        ∑ u ∈ S, (d u : ℚ)) :
    ¬ ∃ mass, IsSymmetricFractionalPointPacking H d B mass := by
  apply no_symmetricFractionalPointPacking_of_rowPointPrices
    H d B (fun u => if u ∈ S then 1 else 0) pointPrice
    hpointPrice hedge
  convert hstrict using 1
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Denominator-cleared unit-support certificate.  `weight` stores natural
point-price numerators and `scale` their common positive denominator. -/
theorem no_symmetricFractionalPointPacking_of_scaledUnitSupportPointPrices
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (S : Finset V) (weight : V → P → ℕ) (scale : ℕ)
    (hscale : 0 < scale)
    (hedge : ∀ u v, H u v →
      scale * ((if u ∈ S then 1 else 0) + (if v ∈ S then 1 else 0)) ≤
        (∑ p ∈ B v, weight u p) + ∑ p ∈ B u, weight v p)
    (hstrict :
      (∑ u : V, ∑ p : P, weight u p) <
        scale * ∑ u ∈ S, d u) :
    ¬ ∃ mass, IsSymmetricFractionalPointPacking H d B mass := by
  let pointPrice : V → P → ℚ := fun u p => weight u p / (scale : ℚ)
  have hqpos : (0 : ℚ) < scale := Nat.cast_pos.mpr hscale
  have hqne : (scale : ℚ) ≠ 0 := hqpos.ne'
  apply no_symmetricFractionalPointPacking_of_unitSupportPointPrices
    H d B S pointPrice
  · intro u p
    exact div_nonneg (Nat.cast_nonneg _) hqpos.le
  · intro u v huv
    have hcast :
        (scale : ℚ) *
            ((if u ∈ S then (1 : ℚ) else 0) +
              if v ∈ S then 1 else 0) ≤
          (∑ p ∈ B v, (weight u p : ℚ)) +
            ∑ p ∈ B u, (weight v p : ℚ) := by
      exact_mod_cast hedge u v huv
    calc
      (if u ∈ S then (1 : ℚ) else 0) +
          (if v ∈ S then 1 else 0) =
          ((scale : ℚ) *
            ((if u ∈ S then (1 : ℚ) else 0) +
              if v ∈ S then 1 else 0)) / scale := by field_simp
      _ ≤ ((∑ p ∈ B v, (weight u p : ℚ)) +
            ∑ p ∈ B u, (weight v p : ℚ)) / scale :=
        (div_le_div_iff_of_pos_right hqpos).2 hcast
      _ = (∑ p ∈ B v, pointPrice u p) +
            ∑ p ∈ B u, pointPrice v p := by
        simp [pointPrice, add_div, Finset.sum_div]
  · have hcast :
        (∑ u : V, ∑ p : P, (weight u p : ℚ)) <
          (scale : ℚ) * ∑ u ∈ S, (d u : ℚ) := by
      exact_mod_cast hstrict
    have hdiv := (div_lt_div_iff_of_pos_right hqpos).2 hcast
    rw [mul_div_cancel_left₀ _ hqne] at hdiv
    simpa [pointPrice, Finset.sum_div] using hdiv

/-- Any strict point cover of every positive-mass-eligible block rules out a
full-demand canonical fractional interval extension.  This is the direct
dual-side consumer complementary to the forced-shared-point obstruction. -/
theorem no_canonicalFractionalIntervalExtension_of_pointCover
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H W : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (u : V) (weight : P → ℚ)
    (hweight : ∀ p, 0 ≤ weight p)
    (hcover : ∀ w, H u w → 1 ≤ ∑ p ∈ B w, weight p)
    (htotal : (∑ p : P, weight p) < d u) :
    ¬ ∃ mass, IsCanonicalFractionalIntervalExtension H W d B u mass := by
  rintro ⟨mass, hmass⟩
  rcases hmass with ⟨hbounds, hdemand, heligible, hcapacity, _, _⟩
  have hdual : (∑ w : V, mass w) ≤ ∑ p : P, weight p :=
    totalMass_le_totalPointWeight B mass weight
      (fun w => (hbounds w).1) hweight hcapacity
      (fun w hw => hcover w (heligible w hw))
  rw [hdemand] at hdual
  exact (not_lt_of_ge hdual) htotal

/-- A strict point cover only on the residual candidates after contracting
the canonical reverse-forced fiber also rules out the canonical fractional
primal.  Forced rows already carry unit mass; point capacity makes every
other positive-mass block disjoint from all forced blocks. -/
theorem no_canonicalFractionalIntervalExtension_of_contractedPointCover
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H W : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (u : V) (weight : P → ℚ)
    (hweight : ∀ p, 0 ≤ weight p)
    (hcover : ∀ x, H u x →
      x ∉ reverseForcedLocalGramNeighborFinset H W d u →
      x ∉ reverseImpossibleLocalGramNeighborFinset H W d u →
      (∀ f ∈ reverseForcedLocalGramNeighborFinset H W d u,
        f ≠ x → Disjoint (B f) (B x)) →
      1 ≤ ∑ p ∈ B x, weight p)
    (htotal :
      (reverseForcedLocalGramNeighborFinset H W d u).card +
        (∑ p : P, weight p) < d u) :
    ¬ ∃ mass, IsCanonicalFractionalIntervalExtension H W d B u mass := by
  classical
  let F := reverseForcedLocalGramNeighborFinset H W d u
  let I := reverseImpossibleLocalGramNeighborFinset H W d u
  rintro ⟨mass, hmass⟩
  rcases hmass with
    ⟨hbounds, hdemand, heligible, hcapacity, hforced, himpossible⟩
  let residualMass : V → ℚ := fun x => if x ∈ F then 0 else mass x
  have hresidualNonneg : ∀ x, 0 ≤ residualMass x := by
    intro x
    by_cases hx : x ∈ F <;> simp [residualMass, hx, (hbounds x).1]
  have hresidualCapacity : ∀ p,
      (∑ x ∈ Finset.univ.filter fun z => p ∈ B z, residualMass x) ≤ 1 := by
    intro p
    refine le_trans (Finset.sum_le_sum fun x _ => ?_) (hcapacity p)
    by_cases hx : x ∈ F
    · simp [residualMass, hx, (hbounds x).1]
    · simp [residualMass, hx]
  have hresidualCover : ∀ x, 0 < residualMass x →
      1 ≤ ∑ p ∈ B x, weight p := by
    intro x hx
    have hxF : x ∉ F := by
      intro hxF
      simp [residualMass, hxF] at hx
    have hxmass : 0 < mass x := by simpa [residualMass, hxF] using hx
    have hxI : x ∉ I := by
      intro hxI
      have hzero : mass x = 0 := by
        apply himpossible x
        simpa [I, reverseImpossibleLocalGramNeighborFinset] using hxI
      linarith
    apply hcover x (heligible x hxmass) hxF hxI
    intro f hfF hfx
    by_contra hblocks
    rw [Finset.not_disjoint_iff] at hblocks
    obtain ⟨p, hpf, hpx⟩ := hblocks
    have hfmass : mass f = 1 := by
      apply hforced f
      simpa [F, reverseForcedLocalGramNeighborFinset] using hfF
    let S := Finset.univ.filter fun z => p ∈ B z
    have hfS : f ∈ S := by simp [S, hpf]
    have hxS : x ∈ S := by simp [S, hpx]
    have hpairSubset : ({f, x} : Finset V) ⊆ S := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hfS
      · exact hxS
    have hpairLe : mass f + mass x ≤ ∑ z ∈ S, mass z := by
      calc
        mass f + mass x = ∑ z ∈ ({f, x} : Finset V), mass z := by
          simp [hfx]
        _ ≤ ∑ z ∈ S, mass z := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hpairSubset
            (fun z _ _ => (hbounds z).1)
    have hcap : (∑ z ∈ S, mass z) ≤ 1 := by
      simpa [S] using hcapacity p
    rw [hfmass] at hpairLe
    linarith
  have hdual : (∑ x : V, residualMass x) ≤ ∑ p : P, weight p :=
    totalMass_le_totalPointWeight B residualMass weight
      hresidualNonneg hweight hresidualCapacity hresidualCover
  have hFmass : (∑ f ∈ F, mass f) = (F.card : ℚ) := by
    calc
      (∑ f ∈ F, mass f) = ∑ _f ∈ F, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro f hfF
        apply hforced f
        simpa [F, reverseForcedLocalGramNeighborFinset] using hfF
      _ = (F.card : ℚ) := by simp
  have hresidualSum :
      (∑ x : V, residualMass x) =
        ∑ x ∈ Finset.univ.filter (fun z => z ∉ F), mass x := by
    calc
      (∑ x : V, residualMass x) =
          ∑ x : V, if x ∉ F then mass x else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ F <;> simp [residualMass, hx]
      _ = ∑ x ∈ Finset.univ.filter (fun z => z ∉ F), mass x := by
        rw [Finset.sum_filter]
  have hsplit :
      (∑ x : V, mass x) =
        (∑ x ∈ F, mass x) +
          ∑ x ∈ Finset.univ.filter (fun z => z ∉ F), mass x := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun z => z ∈ F) (f := mass)]
    simp
  have hmassDecomp :
      (d u : ℚ) = (F.card : ℚ) + ∑ x : V, residualMass x := by
    rw [← hdemand, hsplit, hFmass, hresidualSum]
  have htotal' :
      (F.card : ℚ) + (∑ p : P, weight p) < d u := htotal
  linarith

/-- Denominator-cleared wrapper for the contracted fractional obstruction.
It accepts exactly the natural numerator/scale certificates emitted by the
q=9 diagnostics. -/
theorem no_canonicalFractionalIntervalExtension_of_scaledContractedPointCover
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H W : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (u : V) (weight : P → ℕ) (scale : ℕ)
    (hscale : 0 < scale)
    (hcover : ∀ x, H u x →
      x ∉ reverseForcedLocalGramNeighborFinset H W d u →
      x ∉ reverseImpossibleLocalGramNeighborFinset H W d u →
      (∀ f ∈ reverseForcedLocalGramNeighborFinset H W d u,
        f ≠ x → Disjoint (B f) (B x)) →
      scale ≤ ∑ p ∈ B x, weight p)
    (htotal :
      (reverseForcedLocalGramNeighborFinset H W d u).card * scale +
        (∑ p : P, weight p) < d u * scale) :
    ¬ ∃ mass, IsCanonicalFractionalIntervalExtension H W d B u mass := by
  let rationalWeight : P → ℚ := fun p => weight p / (scale : ℚ)
  have hqpos : (0 : ℚ) < scale := Nat.cast_pos.mpr hscale
  have hqne : (scale : ℚ) ≠ 0 := hqpos.ne'
  apply no_canonicalFractionalIntervalExtension_of_contractedPointCover
    H W d B u rationalWeight
  · intro p
    exact div_nonneg (Nat.cast_nonneg _) hqpos.le
  · intro x hxH hxF hxI hxdisjoint
    have hcast : (scale : ℚ) ≤ ∑ p ∈ B x, (weight p : ℚ) := by
      exact_mod_cast hcover x hxH hxF hxI hxdisjoint
    calc
      (1 : ℚ) = (scale : ℚ) / scale := by field_simp
      _ ≤ (∑ p ∈ B x, (weight p : ℚ)) / scale :=
        (div_le_div_iff_of_pos_right hqpos).2 hcast
      _ = ∑ p ∈ B x, rationalWeight p := by
        simp [rationalWeight, Finset.sum_div]
  · have hcast :
        ((reverseForcedLocalGramNeighborFinset H W d u).card : ℚ) * scale +
            (∑ p : P, (weight p : ℚ)) < (d u : ℚ) * scale := by
      exact_mod_cast htotal
    have hdiv := (div_lt_div_iff_of_pos_right hqpos).2 hcast
    rw [add_div, mul_div_cancel_right₀ _ hqne,
      mul_div_cancel_right₀ _ hqne, Finset.sum_div] at hdiv
    simpa [rationalWeight] using hdiv

omit [Fintype V] in
/-- **Fractional point-cover counting engine.**  If the point sets attached
to selected rows are pairwise disjoint and each receives weight at least one,
then the number of selected rows is bounded by the total nonnegative point
weight. -/
theorem card_le_totalWeight_of_pairwiseDisjointPointCover
    {P : Type*} [Fintype P] [DecidableEq P]
    (B : V → Finset P) (weight : P → ℚ) (S : Finset V)
    (hnonneg : ∀ p, 0 ≤ weight p)
    (hdisjoint : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (B x) (B y))
    (hcover : ∀ x ∈ S, 1 ≤ ∑ p ∈ B x, weight p) :
    (S.card : ℚ) ≤ ∑ p : P, weight p := by
  classical
  have hpairwise : (S : Set V).Pairwise fun x y => Disjoint (B x) (B y) := by
    intro x hx y hy hxy
    exact hdisjoint x hx y hy hxy
  calc
    (S.card : ℚ) = ∑ _x ∈ S, (1 : ℚ) := by simp
    _ ≤ ∑ x ∈ S, ∑ p ∈ B x, weight p := by
      exact Finset.sum_le_sum fun x hx => hcover x hx
    _ = ∑ p ∈ S.biUnion B, weight p := by
      symm
      exact Finset.sum_biUnion hpairwise
    _ ≤ ∑ p : P, weight p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro p _ _
      exact hnonneg p

omit [Fintype V] in
/-- Denominator-cleared form of the fractional point-cover count.  It is
convenient for exact certificates: `scale` is the common denominator and
`weight` stores the integer numerators. -/
theorem card_mul_le_totalWeight_of_pairwiseDisjointPointCover
    {P : Type*} [Fintype P] [DecidableEq P]
    (B : V → Finset P) (weight : P → ℕ) (scale : ℕ) (S : Finset V)
    (hdisjoint : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (B x) (B y))
    (hcover : ∀ x ∈ S, scale ≤ ∑ p ∈ B x, weight p) :
    S.card * scale ≤ ∑ p : P, weight p := by
  classical
  have hpairwise : (S : Set V).Pairwise fun x y => Disjoint (B x) (B y) := by
    intro x hx y hy hxy
    exact hdisjoint x hx y hy hxy
  calc
    S.card * scale = ∑ _x ∈ S, scale := by simp
    _ ≤ ∑ x ∈ S, ∑ p ∈ B x, weight p := by
      exact Finset.sum_le_sum fun x hx => hcover x hx
    _ = ∑ p ∈ S.biUnion B, weight p := by
      symm
      exact Finset.sum_biUnion hpairwise
    _ ≤ ∑ p : P, weight p := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- A fractional point cover of the contracted residual candidates supplies
the strict reverse-interval rank certificate.  Shared points must imply a
`W`-conflict, so a prepacking uses pairwise disjoint point sets. -/
theorem reverseIntervalRankDeficit_of_fractionalPointCover
    {P : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (H W : V → V → Prop) (d : V → ℕ) (u : V)
    (B : V → Finset P) (weight : P → ℚ)
    (hnonneg : ∀ p, 0 ≤ weight p)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (hcover : ∀ x, H u x →
      x ∉ reverseForcedLocalGramNeighborFinset H W d u →
      x ∉ reverseImpossibleLocalGramNeighborFinset H W d u →
      (∀ f ∈ reverseForcedLocalGramNeighborFinset H W d u,
        f ≠ x → ¬ W f x) →
      1 ≤ ∑ p ∈ B x, weight p)
    (htotal :
      (reverseForcedLocalGramNeighborFinset H W d u).card +
        (∑ p : P, weight p) < d u) :
    HasReverseIntervalRankDeficitAt H W d u := by
  classical
  let F := reverseForcedLocalGramNeighborFinset H W d u
  let I := reverseImpossibleLocalGramNeighborFinset H W d u
  intro X hpre hFsub hdisjI
  let S := X \ F
  have hSX : S ⊆ X := Finset.sdiff_subset
  have hblockDisjoint : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (B x) (B y) := by
    intro x hx y hy hxy
    by_contra hblocks
    exact (hpre.2 x (hSX hx) y (hSX hy) hxy) (hshared x y hxy hblocks)
  have hcovered : ∀ x ∈ S, 1 ≤ ∑ p ∈ B x, weight p := by
    intro x hx
    have hxX : x ∈ X := hSX hx
    have hxF : x ∉ F := (Finset.mem_sdiff.mp hx).2
    have hxI : x ∉ I := by
      intro hxI
      exact (Finset.disjoint_left.mp hdisjI) hxX hxI
    apply hcover x (hpre.1 x hxX) hxF hxI
    intro f hfF hfx
    exact hpre.2 f (hFsub hfF) x hxX hfx
  have hweightBound : (S.card : ℚ) ≤ ∑ p : P, weight p :=
    card_le_totalWeight_of_pairwiseDisjointPointCover
      B weight S hnonneg hblockDisjoint hcovered
  have hunion : F ∪ S = X := Finset.union_sdiff_of_subset hFsub
  have hdisjFS : Disjoint F S := by
    apply Finset.disjoint_left.mpr
    intro x hxF hxS
    exact (Finset.mem_sdiff.mp hxS).2 hxF
  have hcard : X.card = F.card + S.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisjFS]
  have hrat : (X.card : ℚ) < d u := by
    rw [hcard, Nat.cast_add]
    calc
      (F.card : ℚ) + S.card ≤
          (F.card : ℚ) + ∑ p : P, weight p :=
        add_le_add_right hweightBound (F.card : ℚ)
      _ < d u := htotal
  exact Nat.cast_lt.mp hrat

/-- Integer-scaled certificate interface for the reverse-interval rank
deficit.  For example, thirds are represented by `scale = 3`; no rational
arithmetic or division is needed in a concrete certificate. -/
theorem reverseIntervalRankDeficit_of_scaledPointCover
    {P : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (H W : V → V → Prop) (d : V → ℕ) (u : V)
    (B : V → Finset P) (weight : P → ℕ) (scale : ℕ)
    (hscale : 0 < scale)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (hcover : ∀ x, H u x →
      x ∉ reverseForcedLocalGramNeighborFinset H W d u →
      x ∉ reverseImpossibleLocalGramNeighborFinset H W d u →
      (∀ f ∈ reverseForcedLocalGramNeighborFinset H W d u,
        f ≠ x → ¬ W f x) →
      scale ≤ ∑ p ∈ B x, weight p)
    (htotal :
      (reverseForcedLocalGramNeighborFinset H W d u).card * scale +
        (∑ p : P, weight p) < d u * scale) :
    HasReverseIntervalRankDeficitAt H W d u := by
  classical
  let F := reverseForcedLocalGramNeighborFinset H W d u
  let I := reverseImpossibleLocalGramNeighborFinset H W d u
  intro X hpre hFsub hdisjI
  let S := X \ F
  have hSX : S ⊆ X := Finset.sdiff_subset
  have hblockDisjoint : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (B x) (B y) := by
    intro x hx y hy hxy
    by_contra hblocks
    exact (hpre.2 x (hSX hx) y (hSX hy) hxy) (hshared x y hxy hblocks)
  have hcovered : ∀ x ∈ S, scale ≤ ∑ p ∈ B x, weight p := by
    intro x hx
    have hxX : x ∈ X := hSX hx
    have hxF : x ∉ F := (Finset.mem_sdiff.mp hx).2
    have hxI : x ∉ I := by
      intro hxI
      exact (Finset.disjoint_left.mp hdisjI) hxX hxI
    apply hcover x (hpre.1 x hxX) hxF hxI
    intro f hfF hfx
    exact hpre.2 f (hFsub hfF) x hxX hfx
  have hweightBound : S.card * scale ≤ ∑ p : P, weight p :=
    card_mul_le_totalWeight_of_pairwiseDisjointPointCover
      B weight scale S hblockDisjoint hcovered
  have hunion : F ∪ S = X := Finset.union_sdiff_of_subset hFsub
  have hdisjFS : Disjoint F S := by
    apply Finset.disjoint_left.mpr
    intro x hxF hxS
    exact (Finset.mem_sdiff.mp hxS).2 hxF
  have hcard : X.card = F.card + S.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisjFS]
  have hmul : X.card * scale < d u * scale := by
    rw [hcard, Nat.add_mul]
    exact lt_of_le_of_lt (Nat.add_le_add_left hweightBound _) htotal
  exact (Nat.mul_lt_mul_right hscale).mp hmul

/-- A finite set of reverse-impossible candidates hits every demanded
packing at one row.  Singleton hitting sets are the old reciprocity horn;
the q=9 durable survivor first exposes a hitting set of size two. -/
def HasLocalGramPackingHittingSetReciprocityObstruction
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) : Prop :=
  ∃ (u : V) (S : Finset V),
    (∀ X : Finset V, IsLocalGramPacking H W d u X →
      ∃ w ∈ S, w ∈ X) ∧
    ∀ w ∈ S, ∀ Y : Finset V,
      IsLocalGramPacking H W d w Y → u ∉ Y

/-- The hitting set can be chosen canonically: it is the complement of the
reverse-possible candidates.  Thus the obstruction is exactly a local
packing deficit after pruning every candidate which no reverse packing can
contain. -/
theorem hasLocalGramPackingHittingSetReciprocityObstruction_iff
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) :
    HasLocalGramPackingHittingSetReciprocityObstruction H W d ↔
      ∃ u, ∀ X : Finset V, IsLocalGramPacking H W d u X →
        ∃ w ∈ X, ¬ HasLocalGramPackingContaining H W d w u := by
  constructor
  · rintro ⟨u, S, hhit, hreverse⟩
    refine ⟨u, ?_⟩
    intro X hX
    obtain ⟨w, hwS, hwX⟩ := hhit X hX
    refine ⟨w, hwX, ?_⟩
    rintro ⟨Y, hY, huY⟩
    exact hreverse w hwS Y hY huY
  · rintro ⟨u, hbad⟩
    classical
    let S : Finset V := Finset.univ.filter fun w =>
      ¬ HasLocalGramPackingContaining H W d w u
    refine ⟨u, S, ?_, ?_⟩
    · intro X hX
      obtain ⟨w, hwX, hreverse⟩ := hbad X hX
      exact ⟨w, by simp [S, hreverse], hwX⟩
    · intro w hwS Y hY huY
      have hreverse : ¬ HasLocalGramPackingContaining H W d w u := by
        simpa [S] using hwS
      exact hreverse ⟨Y, hY, huY⟩

/-- A simultaneous choice of demanded local packings whose membership
relation is symmetric.  This is the exact global compatibility retained by
the neighborhoods of an undirected residual graph. -/
def IsSymmetricLocalGramPackingSelection (H W : V → V → Prop)
    (d : V → ℕ) (X : V → Finset V) : Prop :=
  (∀ u, IsLocalGramPacking H W d u (X u)) ∧
  ∀ u v, v ∈ X u ↔ u ∈ X v

/-- Every symmetric simultaneous integral selection supplies a canonical
fractional interval extension: use its characteristic function as the mass.
The only extra input is that two distinct blocks sharing a point conflict,
which turns local `W`-independence into the point-capacity inequalities. -/
theorem exists_canonicalFractionalIntervalExtension_of_symmetricSelection
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H W : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (X : V → Finset V)
    (hX : IsSymmetricLocalGramPackingSelection H W d X)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (u : V) :
    ∃ mass, IsCanonicalFractionalIntervalExtension H W d B u mass := by
  classical
  let mass : V → ℚ := fun w => if w ∈ X u then 1 else 0
  refine ⟨mass, ?_⟩
  constructor
  · intro w
    by_cases hw : w ∈ X u <;> simp [mass, hw]
  constructor
  · simpa [mass] using congrArg (fun n : ℕ => (n : ℚ)) (hX.1 u).1
  constructor
  · intro w hw
    have hwu : w ∈ X u := by
      by_contra hn
      simp [mass, hn] at hw
    exact (hX.1 u).2.1 w hwu
  constructor
  · intro p
    let S := (Finset.univ.filter fun z => p ∈ B z) ∩ X u
    have hcard : S.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      have hx' := Finset.mem_inter.mp hx
      have hy' := Finset.mem_inter.mp hy
      have hxp : p ∈ B x := (Finset.mem_filter.mp hx'.1).2
      have hyp : p ∈ B y := (Finset.mem_filter.mp hy'.1).2
      have hxX : x ∈ X u := hx'.2
      have hyX : y ∈ X u := hy'.2
      by_contra hxy
      have hnotDisjoint : ¬ Disjoint (B x) (B y) := by
        rw [Finset.not_disjoint_iff]
        exact ⟨p, hxp, hyp⟩
      exact (hX.1 u).2.2 x hxX y hyX hxy
        (hshared x y hxy hnotDisjoint)
    have hsum :
        (∑ w ∈ Finset.univ.filter fun z => p ∈ B z, mass w) =
          (S.card : ℚ) := by
      simp [mass, S]
    rw [hsum]
    exact_mod_cast hcard
  constructor
  · intro w hforced
    have huw : u ∈ X w := hforced (X w) (hX.1 w)
    have hwu : w ∈ X u := (hX.2 u w).mpr huw
    simp [mass, hwu]
  · intro w himpossible
    have hwu : w ∉ X u := by
      intro hwu
      have huw : u ∈ X w := (hX.2 u w).mp hwu
      exact himpossible (X w) (hX.1 w) huw
    simp [mass, hwu]

/-- A row with no canonical fractional interval extension rules out every
symmetric simultaneous integral selection. -/
theorem not_symmetricLocalGramPackingSelection_of_no_canonicalFractionalExtension
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (H W : V → V → Prop) (d : V → ℕ) (B : V → Finset P)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (hbad : ∃ u, ¬ ∃ mass,
      IsCanonicalFractionalIntervalExtension H W d B u mass)
    (X : V → Finset V) :
    ¬ IsSymmetricLocalGramPackingSelection H W d X := by
  intro hX
  obtain ⟨u, hu⟩ := hbad
  exact hu (exists_canonicalFractionalIntervalExtension_of_symmetricSelection
    H W d B X hX hshared u)

omit [Fintype V] in
/-- Forced membership is exactly the nonexistence of a demanded packing
which omits the candidate. -/
theorem isForcedLocalGramNeighbor_iff_not_hasLocalGramPackingAvoiding
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) (u w : V) :
    IsForcedLocalGramNeighbor H W d u w ↔
      ¬ HasLocalGramPackingAvoiding H W d u w := by
  constructor
  · intro hforced ⟨X, hX, hw⟩
    exact hw (hforced X hX)
  · intro havoid X hX
    by_contra hw
    exact havoid ⟨X, hX, hw⟩

omit [Fintype V] in
/-- **Existential negation interface for the reciprocity horn.**  Avoiding a
forced-forward/impossible-reverse obstruction means that every ordered pair
admits either a forward omitting packing or a reverse containing packing. -/
theorem not_hasLocalGramPackingReciprocityObstruction_iff
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) :
    ¬ HasLocalGramPackingReciprocityObstruction H W d ↔
      ∀ u w,
        HasLocalGramPackingAvoiding H W d u w ∨
        HasLocalGramPackingContaining H W d w u := by
  constructor
  · intro hno u w
    by_cases havoid : HasLocalGramPackingAvoiding H W d u w
    · exact Or.inl havoid
    · right
      by_contra hcontain
      apply hno
      refine ⟨u, w,
        (isForcedLocalGramNeighbor_iff_not_hasLocalGramPackingAvoiding
          H W d u w).2 havoid, ?_⟩
      intro Y hY huY
      exact hcontain ⟨Y, hY, huY⟩
  · intro halt ⟨u, w, huw, hreverse⟩
    rcases halt u w with havoid | ⟨Y, hY, huY⟩
    · exact (isForcedLocalGramNeighbor_iff_not_hasLocalGramPackingAvoiding
        H W d u w).1 huw havoid
    · exact hreverse Y hY huY

omit [Fintype V] in
/-- **Existential negation interface for one-row compatibility.**  Avoiding
the obstruction is exactly the ability, at every row, to choose one demanded
packing such that each of its membership bits is individually realizable in
the corresponding reverse local family. -/
theorem not_hasLocalGramPackingOneRowCompatibilityObstruction_iff
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) :
    ¬ HasLocalGramPackingOneRowCompatibilityObstruction H W d ↔
      ∀ u, ∃ X : Finset V,
        IsLocalGramPacking H W d u X ∧
        ∀ w,
          (w ∈ X → HasLocalGramPackingContaining H W d w u) ∧
          (w ∉ X → HasLocalGramPackingAvoiding H W d w u) := by
  constructor
  · intro hno u
    by_contra hchoice
    apply hno
    refine ⟨u, ?_⟩
    intro X hX
    by_contra hbad
    apply hchoice
    refine ⟨X, hX, ?_⟩
    intro w
    constructor
    · intro hwX
      by_contra hcontain
      apply hbad
      refine ⟨w, Or.inl ⟨hwX, ?_⟩⟩
      intro Y hY huY
      exact hcontain ⟨Y, hY, huY⟩
    · intro hwX
      by_contra havoid
      apply hbad
      refine ⟨w, Or.inr ⟨hwX, ?_⟩⟩
      exact (isForcedLocalGramNeighbor_iff_not_hasLocalGramPackingAvoiding
        H W d w u).2 havoid
  · intro hchoice ⟨u, hbad⟩
    obtain ⟨X, hX, hcompatible⟩ := hchoice u
    obtain ⟨w, hselected | homitted⟩ := hbad X hX
    · obtain ⟨hwX, hreverse⟩ := hselected
      obtain ⟨Y, hY, huY⟩ := (hcompatible w).1 hwX
      exact hreverse Y hY huY
    · obtain ⟨hwX, hforced⟩ := homitted
      obtain ⟨Y, hY, huY⟩ := (hcompatible w).2 hwX
      exact huY (hforced Y hY)

omit [Fintype V] in
/-- **Full reverse-interval deficit equivalence.**  A one-row compatibility
obstruction is exactly a row having no demanded packing between its reverse-
forced lower bound and reverse-impossible upper exclusion. -/
theorem hasLocalGramPackingOneRowCompatibilityObstruction_iff_no_reverseInterval
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) :
    HasLocalGramPackingOneRowCompatibilityObstruction H W d ↔
      ∃ u, ∀ X : Finset V,
        ¬ IsReverseIntervalLocalGramPacking H W d u X := by
  classical
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    intro X hinterval
    obtain ⟨hX, hlower, hupper⟩ := hinterval
    obtain ⟨w, hselected | homitted⟩ := hu X hX
    · exact (hupper w hselected.2) hselected.1
    · exact homitted.1 (hlower w homitted.2)
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    intro X hX
    by_contra hbad
    apply hu X
    refine ⟨hX, ?_, ?_⟩
    · intro w hforced
      by_contra hwX
      apply hbad
      exact ⟨w, Or.inr ⟨hwX, hforced⟩⟩
    · intro w hreverse hwX
      apply hbad
      exact ⟨w, Or.inl ⟨hwX, hreverse⟩⟩

/-- Reverse-interval demanded packings are exactly contracted residual
extensions.  In the reverse direction the canonical residual witness is
`X \ F_u`. -/
theorem exists_reverseIntervalLocalGramPacking_iff_contractedExtension
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) (u : V) :
    (∃ X : Finset V, IsReverseIntervalLocalGramPacking H W d u X) ↔
      ∃ Y : Finset V, IsReverseIntervalContractedExtension H W d u Y := by
  classical
  let F := reverseForcedLocalGramNeighborFinset H W d u
  let I := reverseImpossibleLocalGramNeighborFinset H W d u
  constructor
  · rintro ⟨X, hX, hlower, hupper⟩
    have hFsub : F ⊆ X := by
      intro w hwF
      apply hlower w
      simpa [F, reverseForcedLocalGramNeighborFinset] using hwF
    have hunion : F ∪ (X \ F) = X := Finset.union_sdiff_of_subset hFsub
    have hdisj : Disjoint X I := by
      rw [Finset.disjoint_left]
      intro w hwX hwI
      have himpossible : ∀ Y : Finset V,
          IsLocalGramPacking H W d w Y → u ∉ Y := by
        simpa [I, reverseImpossibleLocalGramNeighborFinset] using hwI
      exact hupper w himpossible hwX
    refine ⟨X \ F, ?_⟩
    change IsLocalGramPrepacking H W u (F ∪ (X \ F)) ∧
      (F ∪ (X \ F)).card = d u ∧ Disjoint (F ∪ (X \ F)) I
    rw [hunion]
    exact ⟨⟨hX.2.1, hX.2.2⟩, hX.1, hdisj⟩
  · rintro ⟨Y, hpre, hcard, hdisj⟩
    refine ⟨F ∪ Y, ?_⟩
    change IsLocalGramPacking H W d u (F ∪ Y) ∧
      (∀ w, IsForcedLocalGramNeighbor H W d w u → w ∈ F ∪ Y) ∧
      ∀ w, (∀ Z : Finset V,
        IsLocalGramPacking H W d w Z → u ∉ Z) → w ∉ F ∪ Y
    refine ⟨⟨hcard, hpre.1, hpre.2⟩, ?_, ?_⟩
    · intro w hforced
      apply Finset.mem_union_left
      simpa [F, reverseForcedLocalGramNeighborFinset] using hforced
    · intro w himpossible hw
      have hwI : w ∈ I := by
        simpa [I, reverseImpossibleLocalGramNeighborFinset] using himpossible
      exact (Finset.disjoint_left.mp hdisj) hw hwI

/-- **Correct contracted-deficit target.**  The desired one-row obstruction
is an existential failure of residual extension: at some row, every proposed
contracted residual witness fails.  Its negation, used by the SAT probe,
requires an extension at every row. -/
theorem hasLocalGramPackingOneRowCompatibilityObstruction_iff_no_contractedExtension
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) :
    HasLocalGramPackingOneRowCompatibilityObstruction H W d ↔
      ∃ u, ∀ Y : Finset V,
        ¬ IsReverseIntervalContractedExtension H W d u Y := by
  constructor
  · intro hbad
    obtain ⟨u, hu⟩ :=
      (hasLocalGramPackingOneRowCompatibilityObstruction_iff_no_reverseInterval
        H W d).1 hbad
    refine ⟨u, ?_⟩
    intro Y hY
    obtain ⟨X, hX⟩ :=
      (exists_reverseIntervalLocalGramPacking_iff_contractedExtension
        H W d u).2 ⟨Y, hY⟩
    exact hu X hX
  · rintro ⟨u, hu⟩
    apply (hasLocalGramPackingOneRowCompatibilityObstruction_iff_no_reverseInterval
      H W d).2
    refine ⟨u, ?_⟩
    intro X hX
    obtain ⟨Y, hY⟩ :=
      (exists_reverseIntervalLocalGramPacking_iff_contractedExtension
        H W d u).1 ⟨X, hX⟩
    exact hu Y hY

/-- A strict reverse-interval rank bound rules out every contracted residual
extension at that row. -/
theorem no_contractedExtension_of_reverseIntervalRankDeficit
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) (u : V)
    (hdeficit : HasReverseIntervalRankDeficitAt H W d u) :
    ∀ Y : Finset V, ¬ IsReverseIntervalContractedExtension H W d u Y := by
  classical
  let F := reverseForcedLocalGramNeighborFinset H W d u
  let I := reverseImpossibleLocalGramNeighborFinset H W d u
  intro Y hY
  change IsLocalGramPrepacking H W u (F ∪ Y) ∧
    (F ∪ Y).card = d u ∧ Disjoint (F ∪ Y) I at hY
  have hlt : (F ∪ Y).card < d u :=
    hdeficit (F ∪ Y) hY.1 (Finset.subset_union_left) hY.2.2
  omega

/-- The reverse-interval leaf subsumes the old forced-collision horn.  Two
conflicting rows forced toward the same neighbor both enter that neighbor's
reverse lower fiber, so no prepacking can contain the fiber. -/
theorem no_contractedExtension_of_common_forcedLocalGramNeighbor
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ)
    (hW : Std.Irrefl W) (u v w : V)
    (huv : W u v)
    (huw : IsForcedLocalGramNeighbor H W d u w)
    (hvw : IsForcedLocalGramNeighbor H W d v w) :
    ∀ Y : Finset V, ¬ IsReverseIntervalContractedExtension H W d w Y := by
  classical
  let F := reverseForcedLocalGramNeighborFinset H W d w
  let I := reverseImpossibleLocalGramNeighborFinset H W d w
  have huF : u ∈ F := by
    simpa [F, reverseForcedLocalGramNeighborFinset] using huw
  have hvF : v ∈ F := by
    simpa [F, reverseForcedLocalGramNeighborFinset] using hvw
  have huv_ne : u ≠ v := by
    intro huv_eq
    subst v
    exact hW.irrefl u huv
  intro Y hY
  change IsLocalGramPrepacking H W w (F ∪ Y) ∧
    (F ∪ Y).card = d w ∧ Disjoint (F ∪ Y) I at hY
  have hu : u ∈ F ∪ Y := Finset.mem_union_left Y huF
  have hv : v ∈ F ∪ Y := Finset.mem_union_left Y hvF
  exact (hY.1.2 u hu v hv huv_ne) huv

omit [Fintype V] in
/-- The configuration-level obstruction contains the earlier forced-edge
reciprocity horn as a special case. -/
theorem oneRowCompatibilityObstruction_of_reciprocityObstruction
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ)
    (hbad : HasLocalGramPackingReciprocityObstruction H W d) :
    HasLocalGramPackingOneRowCompatibilityObstruction H W d := by
  obtain ⟨u, w, hforced, hreverse⟩ := hbad
  refine ⟨u, ?_⟩
  intro X hX
  exact ⟨w, Or.inl ⟨hforced X hX, hreverse⟩⟩

omit [Fintype V] in
/-- The original reciprocity obstruction is precisely the singleton case of
the reverse-impossible hitting-set obstruction. -/
theorem hittingSetReciprocityObstruction_of_reciprocityObstruction
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ)
    (hbad : HasLocalGramPackingReciprocityObstruction H W d) :
    HasLocalGramPackingHittingSetReciprocityObstruction H W d := by
  obtain ⟨u, w, hforced, hreverse⟩ := hbad
  refine ⟨u, {w}, ?_, ?_⟩
  · intro X hX
    exact ⟨w, by simp, hforced X hX⟩
  · intro v hv
    have hvw : v = w := Finset.mem_singleton.mp hv
    subst v
    exact hreverse

omit [Fintype V] in
/-- A reverse-impossible hitting set is a selected-bit instance of the
one-row compatibility obstruction. -/
theorem oneRowCompatibilityObstruction_of_hittingSetReciprocityObstruction
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ)
    (hbad : HasLocalGramPackingHittingSetReciprocityObstruction H W d) :
    HasLocalGramPackingOneRowCompatibilityObstruction H W d := by
  obtain ⟨u, S, hhit, hreverse⟩ := hbad
  refine ⟨u, ?_⟩
  intro X hX
  obtain ⟨w, hwS, hwX⟩ := hhit X hX
  exact ⟨w, Or.inl ⟨hwX, hreverse w hwS⟩⟩

omit [Fintype V] in
/-- **Existential negation interface for the outer-design problem.**  The
failure of the deficit/forced-collision alternative is precisely a demanded
packing at every row together with an omitting packing at one endpoint for
every conflicting pair and candidate. -/
theorem not_hasLocalGramPackingObstruction_iff
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) :
    ¬ HasLocalGramPackingObstruction H W d ↔
      (∀ u, ∃ X : Finset V, IsLocalGramPacking H W d u X) ∧
      ∀ u v w, W u v →
        HasLocalGramPackingAvoiding H W d u w ∨
        HasLocalGramPackingAvoiding H W d v w := by
  constructor
  · intro hno
    constructor
    · intro u
      by_contra hpack
      apply hno
      left
      refine ⟨u, ?_⟩
      intro X hX
      exact hpack ⟨X, hX⟩
    · intro u v w huv
      by_contra homit
      have hnou : ¬ HasLocalGramPackingAvoiding H W d u w := by
        intro hu
        exact homit (Or.inl hu)
      have hnov : ¬ HasLocalGramPackingAvoiding H W d v w := by
        intro hv
        exact homit (Or.inr hv)
      apply hno
      right
      exact ⟨u, v, w, huv,
        (isForcedLocalGramNeighbor_iff_not_hasLocalGramPackingAvoiding
          H W d u w).2 hnou,
        (isForcedLocalGramNeighbor_iff_not_hasLocalGramPackingAvoiding
          H W d v w).2 hnov⟩
  · rintro ⟨hpacks, homit⟩ (⟨u, hu⟩ | ⟨u, v, w, huv, huw, hvw⟩)
    · obtain ⟨X, hX⟩ := hpacks u
      exact hu X hX
    · rcases homit u v w huv with hu | hv
      · exact (isForcedLocalGramNeighbor_iff_not_hasLocalGramPackingAvoiding
          H W d u w).1 huw hu
      · exact (isForcedLocalGramNeighbor_iff_not_hasLocalGramPackingAvoiding
          H W d v w).1 hvw hv

omit [Fintype V] in
/-- Distinct forced neighbors at a feasible row cannot conflict.  In the
outer block-hypergraph interpretation, this says that the forced kernel is
itself a matching. -/
theorem not_conflict_of_forcedLocalGramNeighbors
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) (u x y : V)
    (hpack : ∃ X : Finset V, IsLocalGramPacking H W d u X)
    (hx : IsForcedLocalGramNeighbor H W d u x)
    (hy : IsForcedLocalGramNeighbor H W d u y)
    (hxy : x ≠ y) :
    ¬ W x y := by
  obtain ⟨X, hX⟩ := hpack
  exact hX.2.2 x (hx X hX) y (hy X hX) hxy

omit [Fintype V] in
/-- Under the negation of the obstruction, the rows which force one common
candidate are pairwise nonconflicting.  Together with
`not_conflict_of_forcedLocalGramNeighbors`, this makes the forced-neighbor
relation packing-like in both its rows and its columns. -/
theorem not_conflict_of_common_forcedLocalGramNeighbor
    (H W : V → V → Prop) (d : V → ℕ) (u v w : V)
    (hno : ¬ HasLocalGramPackingObstruction H W d)
    (huw : IsForcedLocalGramNeighbor H W d u w)
    (hvw : IsForcedLocalGramNeighbor H W d v w) :
    ¬ W u v := by
  intro huv
  apply hno
  exact Or.inr ⟨u, v, w, huv, huw, hvw⟩

omit [Fintype V] in
/-- Under the negation of the obstruction, every forced-neighbor incidence
lies in the eligible relation. -/
theorem eligible_of_forcedLocalGramNeighbor_of_noObstruction
    (H W : V → V → Prop) [DecidableRel H] (d : V → ℕ) (u w : V)
    (hno : ¬ HasLocalGramPackingObstruction H W d)
    (huw : IsForcedLocalGramNeighbor H W d u w) :
    H u w := by
  by_contra hnH
  apply hno
  left
  refine ⟨u, ?_⟩
  intro X hX
  exact hnH (hX.2.1 w (huw X hX))

/-- Under the old deficit/collision negation, the reverse-forced lower bound
is already an eligible conflict-free prepacking.  This is the part which may
be safely contracted before proving the remaining matching-rank bound. -/
theorem reverseForcedLocalGramNeighborFinset_isPrepacking
    [DecidableEq V] (H W : V → V → Prop) [DecidableRel H]
    (d : V → ℕ) (u : V)
    (hH : Std.Symm H)
    (hno : ¬ HasLocalGramPackingObstruction H W d) :
    IsLocalGramPrepacking H W u
      (reverseForcedLocalGramNeighborFinset H W d u) := by
  classical
  constructor
  · intro w hw
    have hforced : IsForcedLocalGramNeighbor H W d w u := by
      simpa [reverseForcedLocalGramNeighborFinset] using hw
    exact hH.symm w u (eligible_of_forcedLocalGramNeighbor_of_noObstruction
      H W d w u hno hforced)
  · intro x hx y hy hxy
    have hforcedx : IsForcedLocalGramNeighbor H W d x u := by
      simpa [reverseForcedLocalGramNeighborFinset] using hx
    have hforcedy : IsForcedLocalGramNeighbor H W d y u := by
      simpa [reverseForcedLocalGramNeighborFinset] using hy
    exact not_conflict_of_common_forcedLocalGramNeighbor
      H W d x y u hno hforcedx hforcedy

/-- With no deficient row, a reverse row cannot simultaneously force and
forbid the same incidence.  Hence the contraction lower bound and deletion
upper bound are disjoint. -/
theorem reverseForcedLocalGramNeighborFinset_disjoint_reverseImpossible
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) (u : V)
    (hno : ¬ HasLocalGramPackingObstruction H W d) :
    Disjoint (reverseForcedLocalGramNeighborFinset H W d u)
      (reverseImpossibleLocalGramNeighborFinset H W d u) := by
  classical
  rw [Finset.disjoint_left]
  intro w hwforced hwimpossible
  have hforced : IsForcedLocalGramNeighbor H W d w u := by
    simpa [reverseForcedLocalGramNeighborFinset] using hwforced
  have himpossible : ∀ Y : Finset V,
      IsLocalGramPacking H W d w Y → u ∉ Y := by
    simpa [reverseImpossibleLocalGramNeighborFinset] using hwimpossible
  have hpack : ∃ Y : Finset V, IsLocalGramPacking H W d w Y := by
    by_contra hnpack
    apply hno
    left
    refine ⟨w, ?_⟩
    intro Y hY
    exact hnpack ⟨Y, hY⟩
  obtain ⟨Y, hY⟩ := hpack
  exact himpossible Y hY (hforced Y hY)

/-- The neighborhood finset of an arbitrary decidable relation. -/
def relationNeighborFinset (A : V → V → Prop) [DecidableRel A]
    (u : V) : Finset V :=
  Finset.univ.filter (A u)

/-- Exact candidate load of the row fiber carrying a point `p`.  For the
q=9 application, `H` is mutual trace eligibility and `B u` is the U1 block
of row `u`. -/
def relationFiberLoad
    {P : Type*} [DecidableEq P]
    (H : V → V → Prop) [DecidableRel H]
    (B : V → Finset P) (p : P) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u => p ∈ B u),
    (relationNeighborFinset H u).card

/-- Fiber-load Fubini identity.  For a symmetric candidate relation, summing
the number of fiber rows visible from every row equals the sum of candidate
degrees over the fiber itself.  This is the formal generic version of
`L = Qᵀ H 1` used by the minimum-load branch-four selector. -/
theorem sum_card_relationNeighborFinset_inter_fiber_eq_relationFiberLoad
    {P : Type*} [DecidableEq V] [DecidableEq P]
    (H : V → V → Prop) [DecidableRel H]
    (B : V → Finset P) (p : P)
    (hsymm : Std.Symm H) :
    let F := Finset.univ.filter fun u => p ∈ B u
    (∑ t : V, (relationNeighborFinset H t ∩ F).card) =
      relationFiberLoad H B p := by
  classical
  dsimp only
  let F := Finset.univ.filter fun u => p ∈ B u
  change (∑ t : V, (relationNeighborFinset H t ∩ F).card) =
    ∑ u ∈ F, (relationNeighborFinset H u).card
  calc
    (∑ t : V, (relationNeighborFinset H t ∩ F).card) =
        ∑ t : V, ∑ u ∈ F, if H t u then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      have hinter : relationNeighborFinset H t ∩ F = F.filter (H t) := by
        ext u
        simp [relationNeighborFinset, and_comm]
      rw [hinter, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ u ∈ F, ∑ t : V, if H t u then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ u ∈ F, (relationNeighborFinset H u).card := by
      apply Finset.sum_congr rfl
      intro u _
      calc
        (∑ t : V, if H t u then 1 else 0) =
            ∑ t : V, if H u t then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro t _
          by_cases htu : H t u
          · have hut : H u t := @Std.Symm.symm V H hsymm t u htu
            simp [htu, hut]
          · have hut : ¬ H u t := by
              intro hut
              exact htu (@Std.Symm.symm V H hsymm u t hut)
            simp [htu, hut]
        _ = (relationNeighborFinset H u).card := by
          rw [relationNeighborFinset, Finset.card_eq_sum_ones,
            Finset.sum_filter]

/-- A symmetric residual relation satisfying the Gram law supplies a local
packing at every row. -/
theorem relationNeighborFinset_isLocalGramPacking
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (u : V) :
    IsLocalGramPacking H W d u (relationNeighborFinset A u) := by
  refine ⟨hdegree u, ?_, ?_⟩
  · intro x hx
    exact hsupport u x (Finset.mem_filter.mp hx).2
  · intro x hx y hy hxy hW
    have hux : A u x := (Finset.mem_filter.mp hx).2
    have huy : A u y := (Finset.mem_filter.mp hy).2
    exact hgram x y u hW (hsymm.symm u x hux) (hsymm.symm u y huy)

/-- The Gram law and the fact that a shared block point creates a conflict
imply the numeric point-capacity condition for characteristic neighborhood
masses. -/
theorem relationIndicator_pointCapacity_of_sharedPoint
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A W : V → V → Prop) [DecidableRel A] (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (u : V) (p : P) :
    (∑ w ∈ Finset.univ.filter fun z => p ∈ B z,
      if A u w then (1 : ℚ) else 0) ≤ 1 := by
  classical
  let S := Finset.univ.filter fun z => p ∈ B z
  let T := S.filter fun z => A u z
  have hcard : T.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
    have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
    have hpx : p ∈ B x := by simpa [S] using hxS
    have hpy : p ∈ B y := by simpa [S] using hyS
    have hnotDisjoint : ¬ Disjoint (B x) (B y) := by
      exact Finset.not_disjoint_iff.mpr ⟨p, hpx, hpy⟩
    have hux : A u x := (Finset.mem_filter.mp hx).2
    have huy : A u y := (Finset.mem_filter.mp hy).2
    exact hgram x y u (hshared x y hxy hnotDisjoint)
      (hsymm.symm u x hux) (hsymm.symm u y huy)
  rw [show (∑ w ∈ Finset.univ.filter fun z => p ∈ B z,
        if A u w then (1 : ℚ) else 0) = (T.card : ℚ) by
      simp [T, S]]
  exact_mod_cast hcard

/-- The characteristic matrix of an actual symmetric residual relation is a
symmetric fractional point packing. -/
theorem relationIndicator_isSymmetricFractionalPointPacking
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hpointCapacity : ∀ u p,
      (∑ w ∈ Finset.univ.filter fun z => p ∈ B z,
        if A u w then (1 : ℚ) else 0) ≤ 1) :
    IsSymmetricFractionalPointPacking H d B
      (fun u v => if A u v then 1 else 0) := by
  refine ⟨?_, ?_, ?_, hpointCapacity, ?_⟩
  · intro u v
    by_cases huv : A u v <;> simp [huv]
  · intro u
    rw [show (∑ v : V, if A u v then (1 : ℚ) else 0) =
        ((relationNeighborFinset A u).card : ℚ) by
          simp [relationNeighborFinset]]
    simp [hdegree u]
  · intro u v huv
    by_cases hA : A u v
    · exact hsupport u v hA
    · simp [hA] at huv
  · intro u v
    by_cases huv : A u v
    · simp [huv, hsymm.symm u v huv]
    · have hvu : ¬ A v u := by
        intro hvu
        exact huv (hsymm.symm v u hvu)
      simp [huv, hvu]

/-- End-to-end global price consumer for an actual symmetric residual
relation obeying the shared-point Gram law. -/
theorem false_of_symmetricRowPointPriceCertificate
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (rowPrice : V → ℚ) (pointPrice : V → P → ℚ)
    (hpointPrice : ∀ u p, 0 ≤ pointPrice u p)
    (hedge : ∀ u v, H u v →
      rowPrice u + rowPrice v ≤
        (∑ p ∈ B v, pointPrice u p) +
        ∑ p ∈ B u, pointPrice v p)
    (hstrict :
      (∑ u : V, ∑ p : P, pointPrice u p) <
        ∑ u : V, (d u : ℚ) * rowPrice u) :
    False := by
  apply no_symmetricFractionalPointPacking_of_rowPointPrices
    H d B rowPrice pointPrice hpointPrice hedge hstrict
  refine ⟨fun u v => if A u v then 1 else 0, ?_⟩
  apply relationIndicator_isSymmetricFractionalPointPacking
    A H d B hsymm hdegree hsupport
  exact relationIndicator_pointCapacity_of_sharedPoint
    A W B hsymm hgram hshared

/-- End-to-end actual-relation consumer whose row-price dual is supported on
two named rows, with independent rational weights.  This is the natural
interface for a two-row Farkas certificate; unlike the two-unit-support
specialization below, the two row weights need not agree. -/
theorem false_of_twoRowSupportPointPriceCertificate
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (s t : V) (a b : ℚ)
    (pointPrice : V → P → ℚ)
    (hpointPrice : ∀ u p, 0 ≤ pointPrice u p)
    (hedge : ∀ u v, H u v →
      ((if u = s then a else 0) + (if u = t then b else 0)) +
          ((if v = s then a else 0) + (if v = t then b else 0)) ≤
        (∑ p ∈ B v, pointPrice u p) +
          ∑ p ∈ B u, pointPrice v p)
    (hstrict :
      (∑ u : V, ∑ p : P, pointPrice u p) <
        (d s : ℚ) * a + (d t : ℚ) * b) :
    False := by
  let rowPrice : V → ℚ := fun u =>
    (if u = s then a else 0) + (if u = t then b else 0)
  apply false_of_symmetricRowPointPriceCertificate
    A H W d B hsymm hdegree hsupport hgram hshared rowPrice pointPrice
    hpointPrice
  · intro u v huv
    exact hedge u v huv
  · simpa [rowPrice, mul_add, Finset.sum_add_distrib] using hstrict

/-- Branch-4 fixed-price specialization of the two-row certificate.  A
regular triple row has residual degree five and an exceptional triple row
has residual degree six; row prices one and two therefore give the constant
strict target `5 + 2 * 6 = 17`.  This is the exact consumer for the `(13ar)`
selector isolated by the branch-4 outer-design audit. -/
theorem false_of_regularExceptionalFixedPriceCertificate
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (regular exceptional : V)
    (hregularDegree : d regular = 5)
    (hexceptionalDegree : d exceptional = 6)
    (pointPrice : V → P → ℚ)
    (hpointPrice : ∀ u p, 0 ≤ pointPrice u p)
    (hedge : ∀ u v, H u v →
      ((if u = regular then 1 else 0) +
          (if u = exceptional then 2 else 0)) +
        ((if v = regular then 1 else 0) +
          (if v = exceptional then 2 else 0)) ≤
        (∑ p ∈ B v, pointPrice u p) +
          ∑ p ∈ B u, pointPrice v p)
    (hstrict : (∑ u : V, ∑ p : P, pointPrice u p) < 17) :
    False := by
  apply false_of_twoRowSupportPointPriceCertificate
    A H W d B hsymm hdegree hsupport hgram hshared
    regular exceptional 1 2 pointPrice hpointPrice
  · intro u v huv
    simpa using hedge u v huv
  · norm_num [hregularDegree, hexceptionalDegree]
    exact hstrict

/-- End-to-end actual-relation consumer whose row-price dual is supported on
three named rows, with independent rational weights.  This is the direct
interface for the branch-3 exceptional/diagonal/incident-class certificate. -/
theorem false_of_threeRowSupportPointPriceCertificate
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (r s t : V) (a b c : ℚ)
    (pointPrice : V → P → ℚ)
    (hpointPrice : ∀ u p, 0 ≤ pointPrice u p)
    (hedge : ∀ u v, H u v →
      ((if u = r then a else 0) + (if u = s then b else 0) +
          (if u = t then c else 0)) +
        ((if v = r then a else 0) + (if v = s then b else 0) +
          (if v = t then c else 0)) ≤
        (∑ p ∈ B v, pointPrice u p) +
          ∑ p ∈ B u, pointPrice v p)
    (hstrict :
      (∑ u : V, ∑ p : P, pointPrice u p) <
        (d r : ℚ) * a + (d s : ℚ) * b + (d t : ℚ) * c) :
    False := by
  let rowPrice : V → ℚ := fun u =>
    (if u = r then a else 0) + (if u = s then b else 0) +
      (if u = t then c else 0)
  apply false_of_symmetricRowPointPriceCertificate
    A H W d B hsymm hdegree hsupport hgram hshared rowPrice pointPrice
    hpointPrice
  · intro u v huv
    exact hedge u v huv
  · simpa [rowPrice, mul_add, Finset.sum_add_distrib] using hstrict

/-- End-to-end actual-relation consumer with unit row prices on `S`. -/
theorem false_of_unitSupportPointPriceCertificate
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (S : Finset V) (pointPrice : V → P → ℚ)
    (hpointPrice : ∀ u p, 0 ≤ pointPrice u p)
    (hedge : ∀ u v, H u v →
      (if u ∈ S then (1 : ℚ) else 0) + (if v ∈ S then 1 else 0) ≤
        (∑ p ∈ B v, pointPrice u p) +
        ∑ p ∈ B u, pointPrice v p)
    (hstrict :
      (∑ u : V, ∑ p : P, pointPrice u p) <
        ∑ u ∈ S, (d u : ℚ)) :
    False := by
  apply no_symmetricFractionalPointPacking_of_unitSupportPointPrices
    H d B S pointPrice hpointPrice hedge hstrict
  refine ⟨fun u v => if A u v then 1 else 0, ?_⟩
  apply relationIndicator_isSymmetricFractionalPointPacking
    A H d B hsymm hdegree hsupport
  exact relationIndicator_pointCapacity_of_sharedPoint
    A W B hsymm hgram hshared

/-- Joint two-support actual-relation consumer.  Rows in the overlap carry
price two, so a single point-price cover can exploit shared capacity across
two fibers directly; no reduction to an individually strict fiber is
required. -/
theorem false_of_twoUnitSupportsPointPriceCertificate
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (S T : Finset V) (pointPrice : V → P → ℚ)
    (hpointPrice : ∀ u p, 0 ≤ pointPrice u p)
    (hedge : ∀ u v, H u v →
      ((if u ∈ S then (1 : ℚ) else 0) + (if u ∈ T then 1 else 0)) +
        ((if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0)) ≤
          (∑ p ∈ B v, pointPrice u p) +
            ∑ p ∈ B u, pointPrice v p)
    (hstrict :
      (∑ u : V, ∑ p : P, pointPrice u p) <
        (∑ u ∈ S, (d u : ℚ)) + ∑ u ∈ T, (d u : ℚ)) :
    False := by
  let rowPrice : V → ℚ := fun u =>
    (if u ∈ S then 1 else 0) + (if u ∈ T then 1 else 0)
  apply false_of_symmetricRowPointPriceCertificate
    A H W d B hsymm hdegree hsupport hgram hshared rowPrice pointPrice
    hpointPrice
  · intro u v huv
    exact hedge u v huv
  · simpa [rowPrice, mul_add, Finset.sum_add_distrib] using hstrict

/-- Denominator-cleared joint two-support consumer.  This is the literal
interface for an integer certificate emitted by a joint two-fiber verifier. -/
theorem false_of_scaledTwoUnitSupportsPointPriceCertificate
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (S T : Finset V) (weight : V → P → ℕ) (scale : ℕ)
    (hscale : 0 < scale)
    (hedge : ∀ u v, H u v →
      scale * (((if u ∈ S then 1 else 0) + (if u ∈ T then 1 else 0)) +
        ((if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0))) ≤
          (∑ p ∈ B v, weight u p) + ∑ p ∈ B u, weight v p)
    (hstrict :
      (∑ u : V, ∑ p : P, weight u p) <
        scale * ((∑ u ∈ S, d u) + ∑ u ∈ T, d u)) :
    False := by
  let pointPrice : V → P → ℚ := fun u p => weight u p / (scale : ℚ)
  have hqpos : (0 : ℚ) < scale := Nat.cast_pos.mpr hscale
  have hqne : (scale : ℚ) ≠ 0 := hqpos.ne'
  apply false_of_twoUnitSupportsPointPriceCertificate
    A H W d B hsymm hdegree hsupport hgram hshared S T pointPrice
  · intro u p
    exact div_nonneg (Nat.cast_nonneg _) hqpos.le
  · intro u v huv
    have hcast :
        (scale : ℚ) *
            (((if u ∈ S then (1 : ℚ) else 0) + (if u ∈ T then 1 else 0)) +
              ((if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0))) ≤
          (∑ p ∈ B v, (weight u p : ℚ)) +
            ∑ p ∈ B u, (weight v p : ℚ) := by
      exact_mod_cast hedge u v huv
    calc
      ((if u ∈ S then (1 : ℚ) else 0) + (if u ∈ T then 1 else 0)) +
          ((if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0)) =
        ((scale : ℚ) *
          (((if u ∈ S then (1 : ℚ) else 0) + (if u ∈ T then 1 else 0)) +
            ((if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0)))) / scale := by
              field_simp
      _ ≤ ((∑ p ∈ B v, (weight u p : ℚ)) +
            ∑ p ∈ B u, (weight v p : ℚ)) / scale :=
        (div_le_div_iff_of_pos_right hqpos).2 hcast
      _ = (∑ p ∈ B v, pointPrice u p) +
            ∑ p ∈ B u, pointPrice v p := by
        simp [pointPrice, add_div, Finset.sum_div]
  · have hcast :
        (∑ u : V, ∑ p : P, (weight u p : ℚ)) <
          (scale : ℚ) *
            ((∑ u ∈ S, (d u : ℚ)) + ∑ u ∈ T, (d u : ℚ)) := by
      exact_mod_cast hstrict
    have hdiv := (div_lt_div_iff_of_pos_right hqpos).2 hcast
    rw [mul_div_cancel_left₀ _ hqne] at hdiv
    simpa [pointPrice, Finset.sum_div] using hdiv

/-- Full-fiber specialization of the scaled joint two-support consumer.  Both
row supports are inferred from their common block points. -/
theorem false_of_scaledTwoCommonPointFibersPriceCertificate
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (p q : P) (weight : V → P → ℕ) (scale : ℕ)
    (hscale : 0 < scale)
    (hedge : ∀ u v, H u v →
      scale * (((if p ∈ B u then 1 else 0) + (if q ∈ B u then 1 else 0)) +
        ((if p ∈ B v then 1 else 0) + (if q ∈ B v then 1 else 0))) ≤
          (∑ r ∈ B v, weight u r) + ∑ r ∈ B u, weight v r)
    (hstrict :
      (∑ u : V, ∑ r : P, weight u r) <
        scale *
          ((∑ u ∈ Finset.univ.filter (fun u => p ∈ B u), d u) +
            ∑ u ∈ Finset.univ.filter (fun u => q ∈ B u), d u)) :
    False := by
  let S := Finset.univ.filter fun u => p ∈ B u
  let T := Finset.univ.filter fun u => q ∈ B u
  apply false_of_scaledTwoUnitSupportsPointPriceCertificate
    A H W d B hsymm hdegree hsupport hgram hshared S T weight scale hscale
  · intro u v huv
    simpa [S, T] using hedge u v huv
  · simpa [S, T] using hstrict

/-- End-to-end actual-relation consumer for a denominator-cleared unit-support
certificate.  This is the literal interface produced by the finite q=9
full-fiber verifier: `weight` is integral and `scale` is its positive common
denominator. -/
theorem false_of_scaledUnitSupportPointPriceCertificate
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (S : Finset V) (weight : V → P → ℕ) (scale : ℕ)
    (hscale : 0 < scale)
    (hedge : ∀ u v, H u v →
      scale * ((if u ∈ S then 1 else 0) + (if v ∈ S then 1 else 0)) ≤
        (∑ p ∈ B v, weight u p) + ∑ p ∈ B u, weight v p)
    (hstrict :
      (∑ u : V, ∑ p : P, weight u p) <
        scale * ∑ u ∈ S, d u) :
    False := by
  apply no_symmetricFractionalPointPacking_of_scaledUnitSupportPointPrices
    H d B S weight scale hscale hedge hstrict
  refine ⟨fun u v => if A u v then 1 else 0, ?_⟩
  apply relationIndicator_isSymmetricFractionalPointPacking
    A H d B hsymm hdegree hsupport
  exact relationIndicator_pointCapacity_of_sharedPoint
    A W B hsymm hgram hshared

/-- Full-fiber specialization of the denominator-cleared actual-relation
consumer.  The unit row support is inferred from a common block point rather
than supplied as a separate finset, matching the q=9 hole-fiber certificates
without an additional support-identification obligation. -/
theorem false_of_scaledCommonPointFiberPriceCertificate
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (point : P) (weight : V → P → ℕ) (scale : ℕ)
    (hscale : 0 < scale)
    (hedge : ∀ u v, H u v →
      scale * ((if point ∈ B u then 1 else 0) +
        (if point ∈ B v then 1 else 0)) ≤
        (∑ p ∈ B v, weight u p) + ∑ p ∈ B u, weight v p)
    (hstrict :
      (∑ u : V, ∑ p : P, weight u p) <
        scale * ∑ u ∈ Finset.univ.filter (point ∈ B ·), d u) :
    False := by
  apply false_of_scaledUnitSupportPointPriceCertificate
    A H W d B hsymm hdegree hsupport hgram hshared
    (Finset.univ.filter (point ∈ B ·)) weight scale hscale
  · intro u v huv
    simpa using hedge u v huv
  · exact hstrict

/-- The characteristic function of an actual symmetric neighborhood is a
canonical fractional interval extension.  The point-capacity hypothesis is
the numeric form of the Gram disjointness law for the block model. -/
theorem relationIndicator_isCanonicalFractionalIntervalExtension
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hpointCapacity : ∀ u p,
      (∑ w ∈ Finset.univ.filter fun z => p ∈ B z,
        if A u w then (1 : ℚ) else 0) ≤ 1)
    (u : V) :
    IsCanonicalFractionalIntervalExtension H W d B u
      (fun w => if A u w then 1 else 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    by_cases huw : A u w <;> simp [huw]
  · rw [show (∑ w : V, if A u w then (1 : ℚ) else 0) =
        ((relationNeighborFinset A u).card : ℚ) by
          simp [relationNeighborFinset]]
    simp [hdegree u]
  · intro w hw
    by_cases huw : A u w
    · exact hsupport u w huw
    · simp [huw] at hw
  · exact hpointCapacity u
  · intro w hw
    have hpack := relationNeighborFinset_isLocalGramPacking
      A H W d hsymm hdegree hsupport hgram w
    have huw : u ∈ relationNeighborFinset A w := hw _ hpack
    have hwu : A w u := (Finset.mem_filter.mp huw).2
    simp [hsymm.symm w u hwu]
  · intro w hw
    by_cases huw : A u w
    · have hwu : A w u := hsymm.symm u w huw
      have hpack := relationNeighborFinset_isLocalGramPacking
        A H W d hsymm hdegree hsupport hgram w
      exact False.elim ((hw _ hpack)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hwu⟩))
    · simp [huw]

/-- Actual neighborhoods of a symmetric residual relation form a symmetric
simultaneous selection of demanded local packings. -/
theorem relationNeighborFinset_isSymmetricLocalGramPackingSelection
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False) :
    IsSymmetricLocalGramPackingSelection H W d
      (relationNeighborFinset A) := by
  constructor
  · exact relationNeighborFinset_isLocalGramPacking
      A H W d hsymm hdegree hsupport hgram
  · intro u v
    constructor
    · intro huv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u,
        hsymm.symm u v (Finset.mem_filter.mp huv).2⟩
    · intro hvu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
        hsymm.symm v u (Finset.mem_filter.mp hvu).2⟩

/-- **Canonical fractional-interval consumer.**  If one row admits no full
canonical fractional extension, no symmetric residual relation can realize
the prescribed degrees, eligible support, Gram law, and point-block conflict
model. -/
theorem false_of_no_canonicalFractionalIntervalExtension
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (hbad : ∃ u, ¬ ∃ mass,
      IsCanonicalFractionalIntervalExtension H W d B u mass) :
    False := by
  apply not_symmetricLocalGramPackingSelection_of_no_canonicalFractionalExtension
    H W d B hshared hbad (relationNeighborFinset A)
  exact relationNeighborFinset_isSymmetricLocalGramPackingSelection
    A H W d hsymm hdegree hsupport hgram

/-- **Global compatibility consumer.**  If the eligible local packing
families admit no symmetric simultaneous selection, no symmetric residual
relation can realize the prescribed degrees, support, and Gram law. -/
theorem false_of_no_symmetricLocalGramPackingSelection
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hbad : ∀ X : V → Finset V,
      ¬ IsSymmetricLocalGramPackingSelection H W d X) :
    False :=
  hbad (relationNeighborFinset A)
    (relationNeighborFinset_isSymmetricLocalGramPackingSelection
      A H W d hsymm hdegree hsupport hgram)

omit [Fintype V] in
/-- For an irreflexive conflict relation, a symmetric simultaneous selection
rules out both local obstruction horns.  Thus the restored global target
strictly subsumes the local deficit/forced-collision certificate. -/
theorem not_hasLocalGramPackingObstruction_of_symmetricSelection
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ)
    (hirr : ∀ u, ¬ W u u) (X : V → Finset V)
    (hX : IsSymmetricLocalGramPackingSelection H W d X) :
    ¬ HasLocalGramPackingObstruction H W d := by
  rintro (⟨u, hu⟩ | ⟨u, v, w, huv, huw, hvw⟩)
  · exact hu (X u) (hX.1 u)
  · have hwu : w ∈ X u := huw (X u) (hX.1 u)
    have hwv : w ∈ X v := hvw (X v) (hX.1 v)
    have huw' : u ∈ X w := (hX.2 u w).mp hwu
    have hvw' : v ∈ X w := (hX.2 v w).mp hwv
    have huv_ne : u ≠ v := by
      intro huv_eq
      subst v
      exact hirr u huv
    exact (hX.1 w).2.2 u huw' v hvw' huv_ne huv

omit [Fintype V] in
/-- A forced incidence whose reverse is absent from every demanded packing
rules out a symmetric simultaneous selection. -/
theorem not_symmetricLocalGramPackingSelection_of_forced_not_reverse
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ) (u w : V)
    (huw : IsForcedLocalGramNeighbor H W d u w)
    (hreverse : ∀ Y : Finset V,
      IsLocalGramPacking H W d w Y → u ∉ Y)
    (X : V → Finset V) :
    ¬ IsSymmetricLocalGramPackingSelection H W d X := by
  intro hX
  have hwu : w ∈ X u := huw (X u) (hX.1 u)
  have huw' : u ∈ X w := (hX.2 u w).mp hwu
  exact hreverse (X w) (hX.1 w) huw'

/-- **Forced-forward/impossible-reverse consumer.**  This two-row reciprocity
obstruction excludes every symmetric supported Gram-compatible residual
relation. -/
theorem false_of_forcedLocalGramNeighbor_not_reverse
    (A H W : V → V → Prop) [DecidableEq V] [DecidableRel A]
    (d : V → ℕ)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (u w : V)
    (huw : IsForcedLocalGramNeighbor H W d u w)
    (hreverse : ∀ Y : Finset V,
      IsLocalGramPacking H W d w Y → u ∉ Y) :
    False :=
  false_of_no_symmetricLocalGramPackingSelection
    A H W d hsymm hdegree hsupport hgram
    (not_symmetricLocalGramPackingSelection_of_forced_not_reverse
      H W d u w huw hreverse)

/-- Bundled consumer for the reciprocity obstruction. -/
theorem false_of_localGramPackingReciprocityObstruction
    (A H W : V → V → Prop) [DecidableEq V] [DecidableRel A]
    (d : V → ℕ)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hbad : HasLocalGramPackingReciprocityObstruction H W d) :
    False := by
  rcases hbad with ⟨u, w, huw, hreverse⟩
  exact false_of_forcedLocalGramNeighbor_not_reverse
    A H W d hsymm hdegree hsupport hgram u w huw hreverse

omit [Fintype V] in
/-- A one-row reverse-compatibility obstruction rules out every symmetric
simultaneous selection. -/
theorem not_symmetricLocalGramPackingSelection_of_oneRowCompatibilityObstruction
    [DecidableEq V] (H W : V → V → Prop) (d : V → ℕ)
    (hbad : HasLocalGramPackingOneRowCompatibilityObstruction H W d)
    (X : V → Finset V) :
    ¬ IsSymmetricLocalGramPackingSelection H W d X := by
  intro hX
  obtain ⟨u, hu⟩ := hbad
  obtain ⟨w, hselected | homitted⟩ := hu (X u) (hX.1 u)
  · obtain ⟨hwu, hreverse⟩ := hselected
    exact hreverse (X w) (hX.1 w) ((hX.2 u w).mp hwu)
  · obtain ⟨hwu, hforced⟩ := homitted
    have huw : u ∈ X w := hforced (X w) (hX.1 w)
    exact hwu ((hX.2 u w).mpr huw)

/-- **One-row compatibility consumer.**  If every demanded packing at one
row contains a reverse-incompatible bit, no symmetric supported
Gram-compatible residual relation exists. -/
theorem false_of_localGramPackingOneRowCompatibilityObstruction
    (A H W : V → V → Prop) [DecidableEq V] [DecidableRel A]
    (d : V → ℕ)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hbad : HasLocalGramPackingOneRowCompatibilityObstruction H W d) :
    False :=
  false_of_no_symmetricLocalGramPackingSelection
    A H W d hsymm hdegree hsupport hgram
    (not_symmetricLocalGramPackingSelection_of_oneRowCompatibilityObstruction
      H W d hbad)

/-- **Contracted residual-deficit consumer.**  Once the outer-design
argument produces one row with no contracted extension, the actual symmetric
residual relation is impossible. -/
theorem false_of_localGramPackingContractedExtensionDeficit
    (A H W : V → V → Prop) [DecidableEq V] [DecidableRel A]
    (d : V → ℕ)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hdeficit : ∃ u, ∀ Y : Finset V,
      ¬ IsReverseIntervalContractedExtension H W d u Y) :
    False :=
  false_of_localGramPackingOneRowCompatibilityObstruction
    A H W d hsymm hdegree hsupport hgram
    ((hasLocalGramPackingOneRowCompatibilityObstruction_iff_no_contractedExtension
      H W d).2 hdeficit)

/-- **Reverse-interval rank-deficit consumer.**  A Hall/rank certificate at
one row supplies the contracted deficit required by the actual-graph
contradiction. -/
theorem false_of_localGramPackingReverseIntervalRankDeficit
    (A H W : V → V → Prop) [DecidableEq V] [DecidableRel A]
    (d : V → ℕ)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hdeficit : ∃ u, HasReverseIntervalRankDeficitAt H W d u) :
    False := by
  obtain ⟨u, hu⟩ := hdeficit
  apply false_of_localGramPackingContractedExtensionDeficit
    A H W d hsymm hdegree hsupport hgram
  exact ⟨u, no_contractedExtension_of_reverseIntervalRankDeficit H W d u hu⟩

/-- **Canonical fractional-interval consumer.**  Actual symmetric
neighborhoods give characteristic feasible masses at every row.  Therefore
one row with no canonical fractional extension contradicts the actual
residual relation directly. -/
theorem false_of_noCanonicalFractionalIntervalExtension
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hpointCapacity : ∀ u p,
      (∑ w ∈ Finset.univ.filter fun z => p ∈ B z,
        if A u w then (1 : ℚ) else 0) ≤ 1)
    (hbad : ∃ u, ∀ mass,
      ¬ IsCanonicalFractionalIntervalExtension H W d B u mass) :
    False := by
  obtain ⟨u, hu⟩ := hbad
  exact hu _ (relationIndicator_isCanonicalFractionalIntervalExtension
    A H W d B hsymm hdegree hsupport hgram hpointCapacity u)

/-- Shared block points imply conflicts, so the abstract Gram law supplies
the point capacities required by the canonical fractional consumer. -/
theorem false_of_noCanonicalFractionalIntervalExtension_of_sharedPoint
    {P : Type*} [Fintype P] [DecidableEq V] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (B : V → Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (hbad : ∃ u, ∀ mass,
      ¬ IsCanonicalFractionalIntervalExtension H W d B u mass) :
    False :=
  false_of_noCanonicalFractionalIntervalExtension
    A H W d B hsymm hdegree hsupport hgram
    (relationIndicator_pointCapacity_of_sharedPoint A W B hsymm hgram hshared)
    hbad

/-- **Forced hitting-set reciprocity consumer.**  If a finite set of
reverse-impossible candidates meets every demanded packing at one row, no
symmetric supported Gram-compatible residual relation exists. -/
theorem false_of_localGramPackingHittingSetReciprocityObstruction
    (A H W : V → V → Prop) [DecidableEq V] [DecidableRel A]
    (d : V → ℕ)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hbad : HasLocalGramPackingHittingSetReciprocityObstruction H W d) :
    False :=
  false_of_localGramPackingOneRowCompatibilityObstruction
    A H W d hsymm hdegree hsupport hgram
    (oneRowCompatibilityObstruction_of_hittingSetReciprocityObstruction
      H W d hbad)

/-- **Capacity-deficit / forced-collision consumer.**  If the eligible local
packing system has either no demanded packing at one row, or two
`W`-conflicting rows force the same neighbor, then no symmetric residual
relation can realize the degrees, support, and Gram law. -/
theorem false_of_localGramPacking_deficit_or_forced_collision
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ)
    (hsymm : Std.Symm A)
    (hdegree : ∀ u, (relationNeighborFinset A u).card = d u)
    (hsupport : ∀ u v, A u v → H u v)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hbad :
      (∃ u, ∀ X : Finset V, ¬ IsLocalGramPacking H W d u X) ∨
      ∃ u v w, W u v ∧
        IsForcedLocalGramNeighbor H W d u w ∧
        IsForcedLocalGramNeighbor H W d v w) :
    False := by
  rcases hbad with ⟨u, hu⟩ | ⟨u, v, w, huv, huw, hvw⟩
  · exact hu (relationNeighborFinset A u)
      (relationNeighborFinset_isLocalGramPacking
        A H W d hsymm hdegree hsupport hgram u)
  · have hpacku := relationNeighborFinset_isLocalGramPacking
      A H W d hsymm hdegree hsupport hgram u
    have hpackv := relationNeighborFinset_isLocalGramPacking
      A H W d hsymm hdegree hsupport hgram v
    have hwu : w ∈ relationNeighborFinset A u :=
      huw (relationNeighborFinset A u) hpacku
    have hwv : w ∈ relationNeighborFinset A v :=
      hvw (relationNeighborFinset A v) hpackv
    have huwA : A u w := (Finset.mem_filter.mp hwu).2
    have hvwA : A v w := (Finset.mem_filter.mp hwv).2
    exact hgram u v w huv huwA hvwA

#print axioms relationNeighborFinset_isLocalGramPacking
#print axioms sum_card_relationNeighborFinset_inter_fiber_eq_relationFiberLoad
#print axioms relationIndicator_pointCapacity_of_sharedPoint
#print axioms relationIndicator_isCanonicalFractionalIntervalExtension
#print axioms false_of_localGramPacking_deficit_or_forced_collision
#print axioms isForcedLocalGramNeighbor_iff_not_hasLocalGramPackingAvoiding
#print axioms not_hasLocalGramPackingObstruction_iff
#print axioms not_conflict_of_common_forcedLocalGramNeighbor
#print axioms eligible_of_forcedLocalGramNeighbor_of_noObstruction
#print axioms not_conflict_of_forcedLocalGramNeighbors
#print axioms relationNeighborFinset_isSymmetricLocalGramPackingSelection
#print axioms exists_canonicalFractionalIntervalExtension_of_symmetricSelection
#print axioms not_symmetricLocalGramPackingSelection_of_no_canonicalFractionalExtension
#print axioms false_of_no_canonicalFractionalIntervalExtension
#print axioms false_of_twoRowSupportPointPriceCertificate
#print axioms false_of_regularExceptionalFixedPriceCertificate
#print axioms false_of_threeRowSupportPointPriceCertificate
#print axioms false_of_twoUnitSupportsPointPriceCertificate
#print axioms false_of_scaledTwoUnitSupportsPointPriceCertificate
#print axioms false_of_scaledTwoCommonPointFibersPriceCertificate
#print axioms false_of_no_symmetricLocalGramPackingSelection
#print axioms not_hasLocalGramPackingObstruction_of_symmetricSelection
#print axioms not_symmetricLocalGramPackingSelection_of_forced_not_reverse
#print axioms not_hasLocalGramPackingOneRowCompatibilityObstruction_iff
#print axioms hasLocalGramPackingOneRowCompatibilityObstruction_iff_no_reverseInterval
#print axioms exists_reverseIntervalLocalGramPacking_iff_contractedExtension
#print axioms hasLocalGramPackingOneRowCompatibilityObstruction_iff_no_contractedExtension
#print axioms no_contractedExtension_of_reverseIntervalRankDeficit
#print axioms no_contractedExtension_of_common_forcedLocalGramNeighbor
#print axioms card_le_totalWeight_of_pairwiseDisjointPointCover
#print axioms card_mul_le_totalWeight_of_pairwiseDisjointPointCover
#print axioms reverseIntervalRankDeficit_of_fractionalPointCover
#print axioms reverseIntervalRankDeficit_of_scaledPointCover
#print axioms no_canonicalFractionalIntervalExtension_of_forced_sharedPoint
#print axioms totalMass_le_totalPointWeight
#print axioms weightedDegree_le_totalPointPrice_of_symmetricFractionalPacking
#print axioms no_symmetricFractionalPointPacking_of_rowPointPrices
#print axioms no_symmetricFractionalPointPacking_of_commonFiberPrices
#print axioms no_symmetricFractionalPointPacking_of_supportWithPointCompensation
#print axioms no_symmetricFractionalPointPacking_of_unitSupportPointPrices
#print axioms no_symmetricFractionalPointPacking_of_scaledUnitSupportPointPrices
#print axioms relationIndicator_isSymmetricFractionalPointPacking
#print axioms false_of_symmetricRowPointPriceCertificate
#print axioms false_of_unitSupportPointPriceCertificate
#print axioms false_of_scaledUnitSupportPointPriceCertificate
#print axioms false_of_scaledCommonPointFiberPriceCertificate
#print axioms no_canonicalFractionalIntervalExtension_of_pointCover
#print axioms no_canonicalFractionalIntervalExtension_of_contractedPointCover
#print axioms no_canonicalFractionalIntervalExtension_of_scaledContractedPointCover
#print axioms reverseForcedLocalGramNeighborFinset_isPrepacking
#print axioms reverseForcedLocalGramNeighborFinset_disjoint_reverseImpossible
#print axioms oneRowCompatibilityObstruction_of_reciprocityObstruction
#print axioms hasLocalGramPackingHittingSetReciprocityObstruction_iff
#print axioms hittingSetReciprocityObstruction_of_reciprocityObstruction
#print axioms oneRowCompatibilityObstruction_of_hittingSetReciprocityObstruction
#print axioms false_of_localGramPackingOneRowCompatibilityObstruction
#print axioms false_of_localGramPackingContractedExtensionDeficit
#print axioms false_of_localGramPackingReverseIntervalRankDeficit
#print axioms false_of_noCanonicalFractionalIntervalExtension
#print axioms false_of_noCanonicalFractionalIntervalExtension_of_sharedPoint
#print axioms false_of_localGramPackingHittingSetReciprocityObstruction
#print axioms false_of_forcedLocalGramNeighbor_not_reverse
#print axioms not_hasLocalGramPackingReciprocityObstruction_iff
#print axioms false_of_localGramPackingReciprocityObstruction

end Erdos85
