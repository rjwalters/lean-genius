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

end Erdos85
