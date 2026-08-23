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
#print axioms false_of_localGramPacking_deficit_or_forced_collision
#print axioms isForcedLocalGramNeighbor_iff_not_hasLocalGramPackingAvoiding
#print axioms not_hasLocalGramPackingObstruction_iff
#print axioms not_conflict_of_common_forcedLocalGramNeighbor
#print axioms eligible_of_forcedLocalGramNeighbor_of_noObstruction
#print axioms not_conflict_of_forcedLocalGramNeighbors
#print axioms relationNeighborFinset_isSymmetricLocalGramPackingSelection
#print axioms false_of_no_symmetricLocalGramPackingSelection
#print axioms not_hasLocalGramPackingObstruction_of_symmetricSelection
#print axioms not_symmetricLocalGramPackingSelection_of_forced_not_reverse
#print axioms not_hasLocalGramPackingOneRowCompatibilityObstruction_iff
#print axioms hasLocalGramPackingOneRowCompatibilityObstruction_iff_no_reverseInterval
#print axioms exists_reverseIntervalLocalGramPacking_iff_contractedExtension
#print axioms hasLocalGramPackingOneRowCompatibilityObstruction_iff_no_contractedExtension
#print axioms no_contractedExtension_of_reverseIntervalRankDeficit
#print axioms card_le_totalWeight_of_pairwiseDisjointPointCover
#print axioms card_mul_le_totalWeight_of_pairwiseDisjointPointCover
#print axioms reverseIntervalRankDeficit_of_fractionalPointCover
#print axioms reverseIntervalRankDeficit_of_scaledPointCover
#print axioms reverseForcedLocalGramNeighborFinset_isPrepacking
#print axioms reverseForcedLocalGramNeighborFinset_disjoint_reverseImpossible
#print axioms oneRowCompatibilityObstruction_of_reciprocityObstruction
#print axioms hasLocalGramPackingHittingSetReciprocityObstruction_iff
#print axioms hittingSetReciprocityObstruction_of_reciprocityObstruction
#print axioms oneRowCompatibilityObstruction_of_hittingSetReciprocityObstruction
#print axioms false_of_localGramPackingOneRowCompatibilityObstruction
#print axioms false_of_localGramPackingContractedExtensionDeficit
#print axioms false_of_localGramPackingReverseIntervalRankDeficit
#print axioms false_of_localGramPackingHittingSetReciprocityObstruction
#print axioms false_of_forcedLocalGramNeighbor_not_reverse
#print axioms not_hasLocalGramPackingReciprocityObstruction_iff
#print axioms false_of_localGramPackingReciprocityObstruction

end Erdos85
