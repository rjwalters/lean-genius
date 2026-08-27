import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveSixthStructural
import Proofs.Erdos85OrderFortyNineSignedStateTransport

/-! # Explicit orbit generators for the adaptive sixth frontier -/

namespace Erdos85

/-- The three matching-pair symmetries and the swap of the two sixth rows. -/
abbrev OrderFortyNineAdaptiveSixthOrbitGenerator := Fin 4

def orderFortyNineAdaptiveSixthOrbitValueMap
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator) (i : Fin 8) : Fin 8 :=
  match g.val with
  | 0 => if i = 4 then 5 else if i = 5 then 4 else i
  | 1 => if i = 6 then 7 else if i = 7 then 6 else i
  | 2 =>
      if i = 4 then 6 else if i = 6 then 4 else
      if i = 5 then 7 else if i = 7 then 5 else i
  | _ => i

def orderFortyNineAdaptiveSixthOrbitVertexMap
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator) (v : Fin 49) : Fin 49 :=
  match g.val with
  | 0 =>
      if v = 14 then 15 else if v = 15 then 14 else
      if v = 20 then 21 else if v = 21 then 20 else v
  | 1 =>
      if v = 16 then 17 else if v = 17 then 16 else
      if v = 22 then 23 else if v = 23 then 22 else v
  | 2 =>
      if v = 14 then 16 else if v = 16 then 14 else
      if v = 15 then 17 else if v = 17 then 15 else
      if v = 20 then 22 else if v = 22 then 20 else
      if v = 21 then 23 else if v = 23 then 21 else v
  | _ => if v = 24 then 25 else if v = 25 then 24 else v

theorem orderFortyNineAdaptiveSixthOrbitVertexMap_involutive :
    ∀ g v,
      orderFortyNineAdaptiveSixthOrbitVertexMap g
        (orderFortyNineAdaptiveSixthOrbitVertexMap g v) = v := by
  native_decide

def orderFortyNineAdaptiveSixthOrbitVertexPerm
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator) : Equiv.Perm (Fin 49) :=
  { toFun := orderFortyNineAdaptiveSixthOrbitVertexMap g
    invFun := orderFortyNineAdaptiveSixthOrbitVertexMap g
    left_inv := orderFortyNineAdaptiveSixthOrbitVertexMap_involutive g
    right_inv := orderFortyNineAdaptiveSixthOrbitVertexMap_involutive g }

def orderFortyNineAdaptiveSixthOrbitTransform
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator)
    (li ri ai bi ci di ei : Fin 8) :
    Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8 :=
  let p := orderFortyNineAdaptiveSixthOrbitValueMap g
  match g.val with
  | 0 => (p li, p ai, p ri, p bi, p ci, p di, p ei)
  | 1 => (p li, p ri, p ai, p ci, p bi, p di, p ei)
  | 2 => (p li, p bi, p ci, p ri, p ai, p di, p ei)
  | _ => (li, ri, ai, bi, ci, ei, di)

theorem orderFortyNineAdaptiveSixthOrbitFixedEdge_invariant :
    ∀ g i j,
      orderFortyNineThreeHighB1AdaptiveFourthFixedEdge
          (orderFortyNineAdaptiveSixthOrbitVertexPerm g i)
          (orderFortyNineAdaptiveSixthOrbitVertexPerm g j) =
        orderFortyNineThreeHighB1AdaptiveFourthFixedEdge i j := by
  native_decide

theorem orderFortyNineAdaptiveSixthOrbitHighOneCandidate_covariant :
    ∀ g i,
      orderFortyNineAdaptiveSixthOrbitVertexPerm g
          (orderFortyNineThreeHighB1AdaptiveCandidates i) =
        orderFortyNineThreeHighB1AdaptiveCandidates
          (orderFortyNineAdaptiveSixthOrbitValueMap g i) := by
  native_decide

theorem orderFortyNineAdaptiveSixthOrbitHighTwoCandidate_covariant :
    ∀ g i,
      orderFortyNineAdaptiveSixthOrbitVertexPerm g
          (orderFortyNineThreeHighB1AdaptiveHighTwoCandidates i) =
        orderFortyNineThreeHighB1AdaptiveHighTwoCandidates
          (orderFortyNineAdaptiveSixthOrbitValueMap g i) := by
  native_decide

private def orderFortyNineAdaptiveSixthOrbitEdge
    (a b i j : Fin 49) : Bool :=
  (i = a && j = b) || (j = a && i = b)

private theorem orderFortyNineAdaptiveSixthOrbitEdge_transport
    (p : Equiv.Perm (Fin 49)) (a b i j : Fin 49) :
    orderFortyNineAdaptiveSixthOrbitEdge (p a) (p b) (p i) (p j) =
      orderFortyNineAdaptiveSixthOrbitEdge a b i j := by
  simp [orderFortyNineAdaptiveSixthOrbitEdge]

private theorem orderFortyNineAdaptiveSixthOrbitEdge_transport_to
    (p : Equiv.Perm (Fin 49)) (a b a' b' i j : Fin 49)
    (ha : p a = a') (hb : p b = b') :
    orderFortyNineAdaptiveSixthOrbitEdge a' b' (p i) (p j) =
      orderFortyNineAdaptiveSixthOrbitEdge a b i j := by
  rw [← ha, ← hb]
  exact orderFortyNineAdaptiveSixthOrbitEdge_transport p a b i j

private def orderFortyNineAdaptiveSixthOrbitEdgePairs
    (li ri ai bi ci di ei : Fin 8) : List (Fin 49 × Fin 49) :=
  [(18, orderFortyNineThreeHighB1AdaptiveCandidates li),
   (20, orderFortyNineThreeHighB1AdaptiveCandidates ri),
   (21, orderFortyNineThreeHighB1AdaptiveCandidates ai),
   (22, orderFortyNineThreeHighB1AdaptiveCandidates bi),
   (23, orderFortyNineThreeHighB1AdaptiveCandidates ci),
   (24, orderFortyNineThreeHighB1AdaptiveHighTwoCandidates di),
   (25, orderFortyNineThreeHighB1AdaptiveHighTwoCandidates ei)]

private def orderFortyNineAdaptiveSixthOrbitEdges
    (xs : List (Fin 49 × Fin 49)) (i j : Fin 49) : Bool :=
  xs.any fun ab => orderFortyNineAdaptiveSixthOrbitEdge ab.1 ab.2 i j

private theorem orderFortyNineAdaptiveSixthOrbitEdges_transport
    (p : Equiv.Perm (Fin 49)) (xs : List (Fin 49 × Fin 49)) (i j : Fin 49) :
    orderFortyNineAdaptiveSixthOrbitEdges
        (xs.map fun ab => (p ab.1, p ab.2)) (p i) (p j) =
      orderFortyNineAdaptiveSixthOrbitEdges xs i j := by
  induction xs with
  | nil => rfl
  | cons ab xs ih =>
      change
        (orderFortyNineAdaptiveSixthOrbitEdge (p ab.1) (p ab.2) (p i) (p j) ||
          orderFortyNineAdaptiveSixthOrbitEdges
            (xs.map fun ab => (p ab.1, p ab.2)) (p i) (p j)) =
        (orderFortyNineAdaptiveSixthOrbitEdge ab.1 ab.2 i j ||
          orderFortyNineAdaptiveSixthOrbitEdges xs i j)
      rw [orderFortyNineAdaptiveSixthOrbitEdge_transport, ih]

private theorem orderFortyNineAdaptiveSixthOrbitEdges_perm
    {xs ys : List (Fin 49 × Fin 49)} (h : xs.Perm ys) (i j : Fin 49) :
    orderFortyNineAdaptiveSixthOrbitEdges xs i j =
      orderFortyNineAdaptiveSixthOrbitEdges ys i j := by
  induction h with
  | nil => rfl
  | cons x h ih =>
      change
        (orderFortyNineAdaptiveSixthOrbitEdge x.1 x.2 i j ||
          orderFortyNineAdaptiveSixthOrbitEdges _ i j) =
        (orderFortyNineAdaptiveSixthOrbitEdge x.1 x.2 i j ||
          orderFortyNineAdaptiveSixthOrbitEdges _ i j)
      rw [ih]
  | swap x y xs =>
      simp [orderFortyNineAdaptiveSixthOrbitEdges, Bool.or_left_comm]
  | trans hxy hyz ihxy ihyz => exact ihxy.trans ihyz

private theorem orderFortyNineAdaptiveSixthOrbitAvailableEdge_eq :
    ∀ li ri ai bi ci di ei i j,
      orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
          li ri ai bi ci di ei i j =
        (orderFortyNineThreeHighB1AdaptiveFourthFixedEdge i j ||
          orderFortyNineAdaptiveSixthOrbitEdges
            (orderFortyNineAdaptiveSixthOrbitEdgePairs li ri ai bi ci di ei)
            i j) := by
  simp [orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge,
    orderFortyNineThreeHighB1AdaptiveFifthAvailableEdge,
    orderFortyNineThreeHighB1AdaptiveFourthAvailableEdge,
    orderFortyNineAdaptiveSixthOrbitEdges,
    orderFortyNineAdaptiveSixthOrbitEdgePairs,
    orderFortyNineAdaptiveSixthOrbitEdge, Bool.or_assoc]

private theorem orderFortyNineAdaptiveSixthOrbitEdgePairs_covariant :
    ∀ g li ri ai bi ci di ei,
      let t := orderFortyNineAdaptiveSixthOrbitTransform
        g li ri ai bi ci di ei
      (orderFortyNineAdaptiveSixthOrbitEdgePairs
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
            t.2.2.2.2.2.1 t.2.2.2.2.2.2).Perm
        ((orderFortyNineAdaptiveSixthOrbitEdgePairs li ri ai bi ci di ei).map
          fun ab =>
            (orderFortyNineAdaptiveSixthOrbitVertexPerm g ab.1,
             orderFortyNineAdaptiveSixthOrbitVertexPerm g ab.2)) := by
  intro g li ri ai bi ci di ei
  fin_cases g <;>
    simp only [orderFortyNineAdaptiveSixthOrbitTransform,
      orderFortyNineAdaptiveSixthOrbitEdgePairs,
      orderFortyNineAdaptiveSixthOrbitHighOneCandidate_covariant,
      orderFortyNineAdaptiveSixthOrbitHighTwoCandidate_covariant,
      List.map_cons, List.map_nil] <;>
    simp [orderFortyNineAdaptiveSixthOrbitValueMap,
      orderFortyNineAdaptiveSixthOrbitVertexPerm,
      orderFortyNineAdaptiveSixthOrbitVertexMap]
  case «0» => apply List.Perm.swap
  case «1» => apply List.Perm.swap
  case «2» => grind
  case «3» => apply List.Perm.swap

/-- Each explicit generator carries the forced-edge predicate of a sixth
cell to the forced-edge predicate of its transformed selector tuple. -/
theorem orderFortyNineAdaptiveSixthOrbitAvailableEdge_covariant
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator)
    (li ri ai bi ci di ei : Fin 8) (i j : Fin 49) :
    let t := orderFortyNineAdaptiveSixthOrbitTransform
      g li ri ai bi ci di ei
    orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
        t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
          t.2.2.2.2.2.1 t.2.2.2.2.2.2
        (orderFortyNineAdaptiveSixthOrbitVertexPerm g i)
        (orderFortyNineAdaptiveSixthOrbitVertexPerm g j) =
      orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
        li ri ai bi ci di ei i j := by
  dsimp only
  rw [orderFortyNineAdaptiveSixthOrbitAvailableEdge_eq,
    orderFortyNineAdaptiveSixthOrbitAvailableEdge_eq,
    orderFortyNineAdaptiveSixthOrbitFixedEdge_invariant]
  rw [orderFortyNineAdaptiveSixthOrbitEdges_perm
    (orderFortyNineAdaptiveSixthOrbitEdgePairs_covariant
      g li ri ai bi ci di ei)]
  exact congrArg
    (orderFortyNineThreeHighB1AdaptiveFourthFixedEdge i j || ·)
    (orderFortyNineAdaptiveSixthOrbitEdges_transport
      (orderFortyNineAdaptiveSixthOrbitVertexPerm g)
      (orderFortyNineAdaptiveSixthOrbitEdgePairs li ri ai bi ci di ei) i j)

end Erdos85
