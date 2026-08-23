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
#print axioms oneRowCompatibilityObstruction_of_reciprocityObstruction
#print axioms hasLocalGramPackingHittingSetReciprocityObstruction_iff
#print axioms oneRowCompatibilityObstruction_of_hittingSetReciprocityObstruction
#print axioms false_of_localGramPackingOneRowCompatibilityObstruction
#print axioms false_of_localGramPackingHittingSetReciprocityObstruction
#print axioms false_of_forcedLocalGramNeighbor_not_reverse
#print axioms not_hasLocalGramPackingReciprocityObstruction_iff
#print axioms false_of_localGramPackingReciprocityObstruction

end Erdos85
