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

/-- The exact local alternative consumed by the Gram obstruction theorem. -/
def HasLocalGramPackingObstruction (H W : V → V → Prop)
    (d : V → ℕ) : Prop :=
  (∃ u, ∀ X : Finset V, ¬ IsLocalGramPacking H W d u X) ∨
  ∃ u v w, W u v ∧
    IsForcedLocalGramNeighbor H W d u w ∧
    IsForcedLocalGramNeighbor H W d v w

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

end Erdos85
