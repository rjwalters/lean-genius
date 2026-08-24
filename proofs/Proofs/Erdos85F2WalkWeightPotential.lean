import Proofs.Erdos85ActiveBrokenRelayEulerization

/-!
# Path-independent binary edge weights are vertex potentials

This is the additive branch of the paired-star price gauge.  If the F2
weight of a walk depends only on its endpoints, choose one path from a root
to every vertex.  Its weight is a potential whose endpoint difference (the
same as endpoint sum in characteristic two) recovers every edge weight.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Sum of directed edge weights along a walk. -/
def f2WalkWeight {V : Type*} {G : SimpleGraph V}
    (k : V → V → ZMod 2) {u v} (p : G.Walk u v) : ZMod 2 :=
  (p.darts.map fun d => k d.fst d.snd).sum

@[simp] theorem f2WalkWeight_nil
    {V : Type*} {G : SimpleGraph V} (k : V → V → ZMod 2) (u : V) :
    f2WalkWeight k (SimpleGraph.Walk.nil : G.Walk u u) = 0 := by
  simp [f2WalkWeight]

@[simp] theorem f2WalkWeight_cons
    {V : Type*} {G : SimpleGraph V} (k : V → V → ZMod 2)
    {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    f2WalkWeight k (.cons h p) = k u v + f2WalkWeight k p := by
  simp [f2WalkWeight]

theorem f2WalkWeight_append
    {V : Type*} {G : SimpleGraph V} (k : V → V → ZMod 2)
    {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    f2WalkWeight k (p.append q) = f2WalkWeight k p + f2WalkWeight k q := by
  simp [f2WalkWeight, List.map_append, List.sum_append]

theorem f2WalkWeight_reverse
    {V : Type*} {G : SimpleGraph V} (k : V → V → ZMod 2)
    (hsymm : ∀ u v, k u v = k v u)
    {u v : V} (p : G.Walk u v) :
    f2WalkWeight k p.reverse = f2WalkWeight k p := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      rw [SimpleGraph.Walk.reverse_cons, f2WalkWeight_append, ih]
      simp [hsymm, add_comm]

/-- Additive edge prices telescope along every walk: only the two endpoint
potentials remain. -/
theorem f2WalkWeight_eq_endpointPotentialSum
    {V : Type*} {G : SimpleGraph V} (k : V → V → ZMod 2)
    (lam : V → ZMod 2)
    (hpotential : ∀ {u v}, G.Adj u v → k u v = lam u + lam v)
    {u v : V} (p : G.Walk u v) :
    f2WalkWeight k p = lam u + lam v := by
  induction p with
  | nil =>
      rw [f2WalkWeight_nil]
      have hchar : (2 : ZMod 2) = 0 := by decide
      rw [← two_mul, hchar, zero_mul]
  | @cons u v w huv p ih =>
      rw [f2WalkWeight_cons, hpotential huv, ih]
      have hchar : (2 : ZMod 2) = 0 := by decide
      rw [add_assoc, ← add_assoc (lam v), ← two_mul, hchar, zero_mul,
        zero_add]

/-- In particular, every closed walk has zero weight in the additive branch. -/
theorem f2WalkWeight_closed_eq_zero_of_endpointPotential
    {V : Type*} {G : SimpleGraph V} (k : V → V → ZMod 2)
    (lam : V → ZMod 2)
    (hpotential : ∀ {u v}, G.Adj u v → k u v = lam u + lam v)
    {u : V} (p : G.Walk u u) :
    f2WalkWeight k p = 0 := by
  rw [f2WalkWeight_eq_endpointPotentialSum k lam hpotential p]
  have hchar : (2 : ZMod 2) = 0 := by decide
  rw [← two_mul, hchar, zero_mul]

/-- Vanishing weight on every closed walk implies path independence. -/
theorem f2WalkWeight_pathIndependent_of_closed_eq_zero
    {V : Type*} {G : SimpleGraph V} (k : V → V → ZMod 2)
    (hsymm : ∀ u v, k u v = k v u)
    (hclosed : ∀ {u} (p : G.Walk u u), f2WalkWeight k p = 0)
    {u v : V} (p q : G.Walk u v) :
    f2WalkWeight k p = f2WalkWeight k q := by
  have hsum : f2WalkWeight k p + f2WalkWeight k q = 0 := by
    have h := hclosed (p.reverse.append q)
    rw [f2WalkWeight_append, f2WalkWeight_reverse k hsymm] at h
    exact h
  have hadd := congrArg (fun z : ZMod 2 => f2WalkWeight k p + z) hsum
  have hchar : (2 : ZMod 2) = 0 := by decide
  rw [← add_assoc, ← two_mul, hchar, zero_mul, zero_add, add_zero] at hadd
  exact hadd.symm

/-- A chosen root path in a connected component presented by explicit
root-to-vertex reachability. -/
def chosenRootWalk {V : Type*} {G : SimpleGraph V} (root : V)
    (hconn : ∀ v, Nonempty (G.Walk root v)) (v : V) : G.Walk root v :=
  Classical.choice (hconn v)

/-- Potential obtained by integrating `k` along chosen root paths. -/
def f2WalkWeightPotential {V : Type*} {G : SimpleGraph V}
    (k : V → V → ZMod 2) (root : V)
    (hconn : ∀ v, Nonempty (G.Walk root v)) (v : V) : ZMod 2 :=
  f2WalkWeight k (chosenRootWalk root hconn v)

/-- **Path-independent price is additive.**  On a connected graph, if every
two walks with the same endpoints have equal F2 weight, then the edge weight
is the sum of endpoint potentials.  This is `(73rnz_cjibkq)` with path
independence as its exact additive-branch hypothesis. -/
theorem exists_vertexPotential_of_f2WalkWeight_pathIndependent
    {V : Type*} {G : SimpleGraph V} (k : V → V → ZMod 2)
    (root : V) (hconn : ∀ v, Nonempty (G.Walk root v))
    (hpath : ∀ {u v} (p q : G.Walk u v),
      f2WalkWeight k p = f2WalkWeight k q) :
    ∃ lam : V → ZMod 2, ∀ {u v}, G.Adj u v →
      k u v = lam u + lam v := by
  let lam := f2WalkWeightPotential k root hconn
  refine ⟨lam, ?_⟩
  intro u v huv
  let p := chosenRootWalk root hconn u
  let q := chosenRootWalk root hconn v
  have hq : f2WalkWeight k q = f2WalkWeight k p + k u v := by
    have h := hpath q (p.append huv.toWalk)
    simpa [f2WalkWeight_append] using h
  have hadd := congrArg (fun z : ZMod 2 => f2WalkWeight k p + z) hq
  have hchar : (2 : ZMod 2) = 0 := by decide
  have hsolve : f2WalkWeight k p + f2WalkWeight k q = k u v := by
    rw [hadd, ← add_assoc, ← two_mul, hchar, zero_mul, zero_add]
  exact hsolve.symm

/-- Cycle/closed-walk annihilation form of the additive potential theorem. -/
theorem exists_vertexPotential_of_f2WalkWeight_closed_eq_zero
    {V : Type*} {G : SimpleGraph V} (k : V → V → ZMod 2)
    (hsymm : ∀ u v, k u v = k v u)
    (root : V) (hconn : ∀ v, Nonempty (G.Walk root v))
    (hclosed : ∀ {u} (p : G.Walk u u), f2WalkWeight k p = 0) :
    ∃ lam : V → ZMod 2, ∀ {u v}, G.Adj u v →
      k u v = lam u + lam v := by
  apply exists_vertexPotential_of_f2WalkWeight_pathIndependent k root hconn
  exact fun p q => f2WalkWeight_pathIndependent_of_closed_eq_zero
    k hsymm hclosed p q

/-- **Odd holonomy or additive potential.**  On a connected graph, a
symmetric binary edge price either has a closed walk of odd total price, or
is the coboundary of a vertex potential.  This is the exact global
cycle-gauge dichotomy in `(73rnz_cjibkq)`. -/
theorem exists_closedWalk_weight_one_or_exists_vertexPotential
    {V : Type*} {G : SimpleGraph V} (k : V → V → ZMod 2)
    (hsymm : ∀ u v, k u v = k v u)
    (root : V) (hconn : ∀ v, Nonempty (G.Walk root v)) :
    (∃ (u : V) (p : G.Walk u u), f2WalkWeight k p = 1) ∨
      ∃ lam : V → ZMod 2, ∀ {u v}, G.Adj u v →
        k u v = lam u + lam v := by
  by_cases hzero : ∀ {u} (p : G.Walk u u), f2WalkWeight k p = 0
  · right
    exact exists_vertexPotential_of_f2WalkWeight_closed_eq_zero
      k hsymm root hconn hzero
  · left
    obtain ⟨u, hu⟩ := not_forall.mp hzero
    obtain ⟨p, hp⟩ := not_forall.mp hu
    refine ⟨u, p, ?_⟩
    have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hbinary (f2WalkWeight k p) with hz | hone
    · exact (hp hz).elim
    · exact hone

end

end Erdos85

#print axioms Erdos85.f2WalkWeight_append
#print axioms Erdos85.exists_vertexPotential_of_f2WalkWeight_pathIndependent
#print axioms Erdos85.exists_vertexPotential_of_f2WalkWeight_closed_eq_zero
#print axioms Erdos85.exists_closedWalk_weight_one_or_exists_vertexPotential
#print axioms Erdos85.f2WalkWeight_eq_endpointPotentialSum
#print axioms Erdos85.f2WalkWeight_closed_eq_zero_of_endpointPotential
