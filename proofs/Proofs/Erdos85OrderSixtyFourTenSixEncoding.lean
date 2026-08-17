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

/-- Assignment to the 120 internally zero-based DIMACS variables induced by
a labeled `R`.  The runtime parser maps external identifier `k+1` to Lean
variable `k`; all other variables are false. -/
def tenSixRDimacsValuation (R : SimpleGraph (Fin 16))
    [DecidableRel R.Adj] : Nat → Bool :=
  fun n =>
    if n < 120 then
      let p := tenSixPairs.getD n (0, 0)
      decide (R.Adj p.1 p.2)
    else false

theorem tenSixPairIndex_lt :
    ∀ u v : Fin 16, u < v → tenSixPairIndex u v < 120 := by
  native_decide

theorem tenSixRDimacsValuation_pair
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (u v : Fin 16) (huv : u < v) :
    tenSixRDimacsValuation R (tenSixPairIndex u v) =
      decide (R.Adj u v) := by
  have hidx := tenSixPairIndex_lt u v huv
  simp [tenSixRDimacsValuation, hidx,
    tenSixPairs_getD_pairIndex u v huv]

/-- The six labeled `R` models excluded by the final six clauses of
`r_complete.cnf`, recorded as zero-based indices into `tenSixPairs`. -/
def tenSixRModelEdgeIndices : Fin 6 → List Nat := ![
  [0, 4, 8, 10, 12, 14, 15, 19, 23, 25, 27, 29, 33, 37, 39, 41,
    42, 46, 48, 50, 52, 54, 58, 60, 62, 64, 65, 69, 71, 73, 75, 79,
    81, 83, 84, 86, 88, 90, 92, 94, 96, 98, 99, 101, 103, 107, 112, 116],
  [2, 4, 6, 10, 12, 14, 17, 19, 21, 23, 25, 27, 31, 33, 35, 37,
    39, 41, 44, 46, 48, 50, 52, 56, 58, 60, 62, 64, 67, 69, 71, 73,
    77, 79, 81, 83, 86, 88, 90, 94, 96, 98, 99, 101, 103, 107, 112, 116],
  [2, 4, 6, 9, 11, 13, 17, 19, 21, 24, 26, 28, 31, 33, 35, 36,
    38, 40, 44, 46, 49, 51, 53, 56, 58, 59, 61, 63, 67, 70, 72, 74,
    77, 78, 80, 82, 87, 89, 91, 93, 95, 97, 100, 102, 104, 107, 112, 116],
  [0, 4, 8, 9, 11, 13, 15, 19, 24, 26, 28, 29, 33, 36, 38, 40,
    42, 46, 49, 51, 53, 54, 58, 59, 61, 63, 65, 70, 72, 74, 75, 78,
    80, 82, 84, 87, 89, 91, 92, 93, 95, 97, 100, 102, 104, 107, 112, 116],
  [3, 4, 5, 9, 11, 13, 18, 19, 20, 24, 26, 28, 32, 33, 34, 36,
    38, 40, 45, 46, 47, 49, 51, 53, 57, 58, 59, 61, 63, 68, 70, 72,
    74, 78, 80, 82, 87, 89, 91, 93, 95, 97, 100, 102, 104, 107, 112, 116],
  [3, 4, 5, 10, 12, 14, 18, 19, 20, 23, 25, 27, 32, 33, 34, 37,
    39, 41, 45, 46, 47, 48, 50, 52, 57, 58, 60, 62, 64, 68, 69, 71,
    73, 79, 81, 83, 86, 88, 90, 94, 96, 98, 99, 101, 103, 107, 112, 116]
]

theorem tenSixRModelEdgeIndices_audit :
    ∀ i : Fin 6,
      (tenSixRModelEdgeIndices i).length = 48 ∧
      (tenSixRModelEdgeIndices i).Nodup ∧
      ∀ k ∈ tenSixRModelEdgeIndices i, k < 120 := by
  native_decide

/-- Boolean bit of model `i` at a zero-based unordered-pair index. -/
def tenSixRModelBit (i : Fin 6) (k : Nat) : Bool :=
  decide (k ∈ tenSixRModelEdgeIndices i)

/-- Equality of a labeled graph with one of the six certificate models. -/
def IsTenSixRModel (i : Fin 6) (R : SimpleGraph (Fin 16)) : Prop :=
  ∀ u v : Fin 16, u < v →
    (R.Adj u v ↔ tenSixRModelBit i (tenSixPairIndex u v) = true)

/-- The final completeness-certificate clause excluding labeled model `i`.
It contains the opposite polarity of each of the model's 120 adjacency bits. -/
def tenSixRModelExclusionClause (i : Fin 6) : Std.Sat.CNF.Clause Nat :=
  (List.range 120).map fun k ↦ (k, !(tenSixRModelBit i k))

/-- A numeric valuation agrees with all 120 adjacency bits of model `i`. -/
def TenSixRValuationMatchesModel (i : Fin 6) (val : Nat → Bool) : Prop :=
  ∀ k, k < 120 → val k = tenSixRModelBit i k

/-- Exact semantics of each of the six model-exclusion clauses: it is false
precisely on the one 120-bit assignment it was generated to exclude. -/
theorem tenSixRModelExclusionClause_eval_eq_false_iff
    (i : Fin 6) (val : Nat → Bool) :
    Std.Sat.CNF.Clause.eval val (tenSixRModelExclusionClause i) = false ↔
      TenSixRValuationMatchesModel i val := by
  simp only [tenSixRModelExclusionClause, Std.Sat.CNF.Clause.eval,
    List.any_map, List.any_eq_false,
    TenSixRValuationMatchesModel, List.mem_range]
  constructor
  · intro h k hk
    have hk' := h k hk
    simpa using hk'
  · intro h k hk
    have hk' := h k hk
    cases hv : tenSixRModelBit i k <;> simp_all

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Closed audit that the last six clauses parsed from the checked
`r_complete.cnf` are exactly the model-exclusion clauses defined above. -/
theorem tenSixRCompletenessCnf_final_six_clauses :
    tenSixRCompletenessCnf.clauses.size = 446402 ∧
    ∀ i : Fin 6,
      tenSixRCompletenessCnf.clauses.getD (446396 + i.val) [] =
        tenSixRModelExclusionClause i := by
  native_decide

/-- Every zero-based pair position decodes to a strictly ordered pair and
re-encodes to the same position. -/
theorem tenSixPairIndex_getD_inverse :
    ∀ k, k < 120 →
      let p := tenSixPairs.getD k (0, 0)
      p.1 < p.2 ∧ tenSixPairIndex p.1 p.2 = k := by
  native_decide

set_option maxRecDepth 100000 in
/-- The numeric 120-bit matching predicate is exactly equality with the
corresponding labeled exterior-pair graph. -/
theorem tenSixRValuationMatchesModel_iff
    (i : Fin 6) (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj] :
    TenSixRValuationMatchesModel i (tenSixRDimacsValuation R) ↔
      IsTenSixRModel i R := by
  constructor
  · intro hmatch u v
    intro huv
    have hv := hmatch (tenSixPairIndex u v) (tenSixPairIndex_lt u v huv)
    rw [tenSixRDimacsValuation_pair R u v huv] at hv
    cases hb : tenSixRModelBit i (tenSixPairIndex u v) <;> simp_all
  · intro hmodel k hk
    let p := tenSixPairs.getD k (0, 0)
    have hp := tenSixPairIndex_getD_inverse k hk
    have hbit := (hmodel p.1 p.2) hp.1
    have hval := tenSixRDimacsValuation_pair R p.1 p.2 hp.1
    have hpk : tenSixPairIndex p.1 p.2 = k := by simpa [p] using hp.2
    rw [hpk] at hval hbit
    rw [hval]
    cases hb : tenSixRModelBit i k <;> simp_all

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- The checked padded formula is exactly the parsed completeness CNF plus
one inert extension-variable tautology. -/
theorem tenSixRCompletenessPaddedCnf_eq_add_tautology :
    tenSixRCompletenessPaddedCnf =
      tenSixRCompletenessCnf.add [(138, true), (138, false)] := by
  have hclauses : tenSixRCompletenessPaddedCnf.clauses =
      (tenSixRCompletenessCnf.add [(138, true), (138, false)]).clauses := by
    native_decide
  exact congrArg Std.Sat.CNF.mk hclauses

/-- Remove the LRAT checker's inert padding and expose UNSAT for the actual
parsed `r_complete.cnf`. -/
theorem tenSixRCompletenessCnf_unsat : tenSixRCompletenessCnf.Unsat := by
  intro val
  have hu := tenSixRCompletenessPaddedCnf_unsat val
  rw [tenSixRCompletenessPaddedCnf_eq_add_tautology,
    Std.Sat.CNF.eval_add] at hu
  have ht : Std.Sat.CNF.Clause.eval val
      [(138, true), (138, false)] = true := by
    cases h : val 138 <;> simp [Std.Sat.CNF.Clause.eval, h]
  rw [ht] at hu
  exact hu

end

end Erdos85
