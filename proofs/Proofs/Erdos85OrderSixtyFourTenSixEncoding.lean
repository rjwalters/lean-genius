import Proofs.Erdos85OrderSixtyFourOutsideEdgeBijection
import Proofs.Erdos85OrderSixtyFourTenSixLrat

/-! # Exact finite coordinates for the order-64 `[10,6]` certificates -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The exact Python `combinations(range(16), 2)` order used for variables
`1,...,120` in the `R` completeness certificate. -/
def tenSixPairs : Array (Fin 16 × Fin 16) :=
  ((List.finRange 16).flatMap fun u =>
    ((List.finRange 16).filter fun v => u < v).map fun v => (u, v)).toArray

/-- Zero-based position of `(u,v)`, for `u<v`, in `tenSixPairs`. -/
def tenSixPairIndex (u v : Fin 16) : Nat :=
  u.val * 15 - u.val * (u.val - 1) / 2 + (v.val - u.val - 1)

theorem tenSixPairs_size : tenSixPairs.size = 120 := by
  native_decide

/-- The closed finite audit connecting the arithmetic index formula to the
actual array order. -/
theorem tenSixPairs_getD_pairIndex :
    ∀ u v : Fin 16, u < v →
      tenSixPairs.getD (tenSixPairIndex u v) (0, 0) = (u, v) := by
  native_decide

/-- Boolean adjacency for the disjoint union `C₁₀ ⊔ C₆`, in precisely the
vertex order used by `order64_outside_classifier.py`. -/
def tenSixHAdj (u v : Fin 16) : Bool :=
  if u.val < 10 then
    v.val < 10 &&
      (v.val = (u.val + 1) % 10 || u.val = (v.val + 1) % 10)
  else
    10 ≤ v.val &&
      ((v.val - 10) = (u.val - 10 + 1) % 6 ||
        (u.val - 10) = (v.val - 10 + 1) % 6)

theorem tenSixHAdj_symmetric :
    ∀ u v : Fin 16, tenSixHAdj u v = tenSixHAdj v u := by
  native_decide

theorem tenSixHAdj_loopless : ∀ u : Fin 16, tenSixHAdj u u = false := by
  native_decide

/-- The fixed labeled `C₁₀ ⊔ C₆` graph underlying all seven certificates. -/
def tenSixCycleGraph : SimpleGraph (Fin 16) where
  Adj u v := tenSixHAdj u v = true
  symm := ⟨by
    intro u v huv
    rw [← tenSixHAdj_symmetric]
    exact huv⟩
  loopless := ⟨by
    intro u hu
    rw [tenSixHAdj_loopless] at hu
    contradiction⟩

instance tenSixCycleGraph_adjDecidable :
    DecidableRel tenSixCycleGraph.Adj := by
  intro u v
  change Decidable (tenSixHAdj u v = true)
  infer_instance

@[simp] theorem tenSixCycleGraph_adj_iff (u v : Fin 16) :
    tenSixCycleGraph.Adj u v ↔ tenSixHAdj u v = true := Iff.rfl

theorem tenSixCycleGraph_degree :
    ∀ u : Fin 16, tenSixCycleGraph.degree u = 2 := by
  native_decide

/-- A graph on a 16-element component has the certificate's `[10,6]`
labeling when its adjacency relation transports to `tenSixCycleGraph`. -/
structure TenSixComponentLabeling
    {V : Type*} (H : SimpleGraph V) where
  toEquiv : V ≃ Fin 16
  map_adj_iff : ∀ u v,
    H.Adj u v ↔ tenSixCycleGraph.Adj (toEquiv u) (toEquiv v)

/-- Relabel a graph on a `[10,6]` component into the certificate coordinates. -/
def tenSixRelabeledGraph
    {V : Type*} (R : SimpleGraph V) (e : V ≃ Fin 16) :
    SimpleGraph (Fin 16) where
  Adj u v := R.Adj (e.symm u) (e.symm v)
  symm := ⟨by
    intro u v huv
    exact huv.symm⟩
  loopless := ⟨by
    intro u hu
    exact R.loopless.irrefl (e.symm u) hu⟩

@[simp] theorem tenSixRelabeledGraph_adj
    {V : Type*} (R : SimpleGraph V) (e : V ≃ Fin 16)
    (u v : Fin 16) :
    (tenSixRelabeledGraph R e).Adj u v ↔ R.Adj (e.symm u) (e.symm v) := by
  rfl

/-- Assignment to the first 120 DIMACS variables induced by a labeled `R`.
All other variables are false; the completeness CNF itself has only these
120 variables before inert LRAT padding. -/
def tenSixRDimacsValuation (R : SimpleGraph (Fin 16))
    [DecidableRel R.Adj] : Nat → Bool :=
  fun n =>
    if 1 ≤ n ∧ n ≤ 120 then
      let p := tenSixPairs.getD (n - 1) (0, 0)
      decide (R.Adj p.1 p.2)
    else false

theorem tenSixPairIndex_lt :
    ∀ u v : Fin 16, u < v → tenSixPairIndex u v < 120 := by
  native_decide

theorem tenSixRDimacsValuation_pair
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (u v : Fin 16) (huv : u < v) :
    tenSixRDimacsValuation R (tenSixPairIndex u v + 1) =
      decide (R.Adj u v) := by
  have hidx := tenSixPairIndex_lt u v huv
  simp [tenSixRDimacsValuation, hidx,
    tenSixPairs_getD_pairIndex u v huv]

end

end Erdos85
