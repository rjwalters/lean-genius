import Proofs.Erdos85SignedSRGBridge

/-!
# Six-vertex local cycle certificate

A loopless symmetric 2-regular triangle-free graph on six vertices is a
six-cycle.  The small finite core is checked by the verified bit-vector
decision procedure and then bridged back to Boolean relations.
-/

namespace Erdos85

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

def adj36 (a : BitVec 36) (x y : Fin 6) : Bool :=
  a.getLsbD (x.val * 6 + y.val)

def row36 (a : BitVec 36) (x : Fin 6) : BitVec 6 :=
  (a.ushiftRight (x.val * 6)).truncate 6

def LocalTwoRegularTriangleFree (a : BitVec 36) : Prop :=
  (∀ x, adj36 a x x = false) ∧
  (∀ x y, adj36 a x y = adj36 a y x) ∧
  (∀ x, (row36 a x).cpop = 2) ∧
  (∀ x y z, x ≠ y → x ≠ z → y ≠ z →
    ¬ (adj36 a x y = true ∧ adj36 a x z = true ∧
      adj36 a y z = true))

def HasCycleOrder6 (a : BitVec 36) : Prop :=
  ∃ p1 p2 p3 p4 p5 : Fin 6,
    0 ≠ p1 ∧ 0 ≠ p2 ∧ 0 ≠ p3 ∧ 0 ≠ p4 ∧ 0 ≠ p5 ∧
    p1 ≠ p2 ∧ p1 ≠ p3 ∧ p1 ≠ p4 ∧ p1 ≠ p5 ∧
    p2 ≠ p3 ∧ p2 ≠ p4 ∧ p2 ≠ p5 ∧
    p3 ≠ p4 ∧ p3 ≠ p5 ∧ p4 ≠ p5 ∧
    adj36 a 0 p1 = true ∧ adj36 a p1 p2 = true ∧
    adj36 a p2 p3 = true ∧ adj36 a p3 p4 = true ∧
    adj36 a p4 p5 = true ∧ adj36 a p5 0 = true

/-- Verified finite classification core. -/
theorem localTwoRegularTriangleFree_hasCycleOrder6 :
    ∀ a : BitVec 36,
      LocalTwoRegularTriangleFree a → HasCycleOrder6 a := by
  simp only [LocalTwoRegularTriangleFree, HasCycleOrder6, adj36, row36]
  simp (config := { maxSteps := 10000000 }) [Fin.forall_fin_succ,
    Fin.exists_fin_succ]
  bv_decide (config := { timeout := 300 })

def matrixBV36 (r : Fin 6 → Fin 6 → Bool) : BitVec 36 :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 36 =>
    r ⟨i.val / 6, by omega⟩ ⟨i.val % 6, Nat.mod_lt _ (by omega)⟩)).cast (by
      rw [List.length_ofFn])

theorem adj36_matrixBV36 (r : Fin 6 → Fin 6 → Bool) (x y : Fin 6) :
    adj36 (matrixBV36 r) x y = r x y := by
  simp only [adj36, matrixBV36, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn]
  have hlt : x.val * 6 + y.val < 36 := by omega
  simp only [hlt, ↓reduceDIte, Option.getD_some]
  congr 2 <;> omega

theorem row36_matrixBV36_getLsbD
    (r : Fin 6 → Fin 6 → Bool) (x y : Fin 6) :
    (row36 (matrixBV36 r) x).getLsbD y = r x y := by
  rw [show (row36 (matrixBV36 r) x).getLsbD y =
      adj36 (matrixBV36 r) x y by simp [row36, adj36]]
  exact adj36_matrixBV36 r x y

theorem cpop6_eq_filter_card : ∀ v : BitVec 6,
    v.cpop.toNat =
      (Finset.univ.filter fun i : Fin 6 => v.getLsbD i).card := by
  native_decide

def BoolLocalTwoRegularTriangleFree (r : Fin 6 → Fin 6 → Bool) : Prop :=
  (∀ x, r x x = false) ∧
  (∀ x y, r x y = r y x) ∧
  (∀ x, (Finset.univ.filter fun y => r x y).card = 2) ∧
  (∀ x y z, x ≠ y → x ≠ z → y ≠ z →
    ¬ (r x y = true ∧ r x z = true ∧ r y z = true))

def BoolHasCycleOrder6 (r : Fin 6 → Fin 6 → Bool) : Prop :=
  ∃ p1 p2 p3 p4 p5 : Fin 6,
    0 ≠ p1 ∧ 0 ≠ p2 ∧ 0 ≠ p3 ∧ 0 ≠ p4 ∧ 0 ≠ p5 ∧
    p1 ≠ p2 ∧ p1 ≠ p3 ∧ p1 ≠ p4 ∧ p1 ≠ p5 ∧
    p2 ≠ p3 ∧ p2 ≠ p4 ∧ p2 ≠ p5 ∧
    p3 ≠ p4 ∧ p3 ≠ p5 ∧ p4 ≠ p5 ∧
    r 0 p1 = true ∧ r p1 p2 = true ∧ r p2 p3 = true ∧
    r p3 p4 = true ∧ r p4 p5 = true ∧ r p5 0 = true

theorem boolLocalTwoRegularTriangleFree_hasCycleOrder6
    {r : Fin 6 → Fin 6 → Bool}
    (hr : BoolLocalTwoRegularTriangleFree r) : BoolHasCycleOrder6 r := by
  have hbv : LocalTwoRegularTriangleFree (matrixBV36 r) := by
    rcases hr with ⟨hloop, hsym, hdeg, htri⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [adj36_matrixBV36] using hloop
    · simpa only [adj36_matrixBV36] using hsym
    · intro x
      apply BitVec.eq_of_toNat_eq
      rw [cpop6_eq_filter_card]
      simp only [row36_matrixBV36_getLsbD]
      simpa using hdeg x
    · simpa only [adj36_matrixBV36] using htri
  simpa only [BoolHasCycleOrder6, HasCycleOrder6, adj36_matrixBV36] using
    localTwoRegularTriangleFree_hasCycleOrder6 (matrixBV36 r) hbv

def next6 (x : Fin 6) : Fin 6 := ⟨(x.val + 1) % 6, by omega⟩

def prev6 (x : Fin 6) : Fin 6 := ⟨(x.val + 5) % 6, by omega⟩

def opposite6 (x : Fin 6) : Fin 6 := ⟨(x.val + 3) % 6, by omega⟩

/-- Every pair of positions on a six-cycle has one of the six oriented
cyclic separations used by the residual incidence arguments. -/
theorem fin6_pair_classification (i j : Fin 6) :
    j = i ∨ j = next6 i ∨ i = next6 j ∨ j = opposite6 i ∨
      j = next6 (next6 i) ∨ i = next6 (next6 j) := by
  fin_cases i <;> fin_cases j <;> decide

theorem finEquiv_next6 (x : Fin 6) :
    ZMod.finEquiv 6 (next6 x) = ZMod.finEquiv 6 x + 1 := by
  letI : Fact (1 < 6) := ⟨by omega⟩
  apply ZMod.val_injective
  have hval (i : Fin 6) : (ZMod.finEquiv 6 i).val = i.val := by rfl
  rw [ZMod.val_add, hval, ZMod.val_one]
  rfl

theorem finEquiv_prev6 (x : Fin 6) :
    ZMod.finEquiv 6 (prev6 x) = ZMod.finEquiv 6 x - 1 := by
  apply ZMod.val_injective
  have hval (i : Fin 6) : (ZMod.finEquiv 6 i).val = i.val := by rfl
  rw [sub_eq_add_neg, ZMod.val_add]
  change (x.val + 5) % 6 = ((ZMod.finEquiv 6 x).val + 5) % 6
  rw [hval x]

/-- A symmetric loopless one-factor disjoint from the fixed six-cycle. -/
def LocalPerfectMatchingOffCycle (m : BitVec 36) : Prop :=
  (∀ x, adj36 m x x = false) ∧
  (∀ x y, adj36 m x y = adj36 m y x) ∧
  (∀ x, (row36 m x).cpop = 1) ∧
  (∀ x, adj36 m x (next6 x) = false ∧
    adj36 m x (prev6 x) = false)

/-- The two dihedral types of perfect matching disjoint from a six-cycle:
either all three opposite chords, or one opposite chord and the two
distance-two chords on the remaining four vertices. -/
def HasSixCycleMatchingNormalForm (m : BitVec 36) : Prop :=
  (∀ x, adj36 m x (opposite6 x) = true) ∨
  ∃ k,
    adj36 m k (opposite6 k) = true ∧
    adj36 m (next6 k) (prev6 k) = true ∧
    adj36 m (next6 (next6 k)) (prev6 (prev6 k)) = true

/-- Verified finite classification of one-factors in the complement of
`C₆`. -/
theorem localPerfectMatchingOffCycle_normalForm :
    ∀ m : BitVec 36,
      LocalPerfectMatchingOffCycle m → HasSixCycleMatchingNormalForm m := by
  simp only [LocalPerfectMatchingOffCycle, HasSixCycleMatchingNormalForm,
    adj36, row36, next6, prev6, opposite6]
  simp (config := { maxSteps := 10000000 }) [Fin.forall_fin_succ,
    Fin.exists_fin_succ]
  bv_decide (config := { timeout := 300 })

def BoolLocalPerfectMatchingOffCycle (r : Fin 6 → Fin 6 → Bool) : Prop :=
  (∀ x, r x x = false) ∧
  (∀ x y, r x y = r y x) ∧
  (∀ x, (Finset.univ.filter fun y => r x y).card = 1) ∧
  (∀ x, r x (next6 x) = false ∧ r x (prev6 x) = false)

def BoolHasSixCycleMatchingNormalForm (r : Fin 6 → Fin 6 → Bool) : Prop :=
  (∀ x, r x (opposite6 x) = true) ∨
  ∃ k,
    r k (opposite6 k) = true ∧
    r (next6 k) (prev6 k) = true ∧
    r (next6 (next6 k)) (prev6 (prev6 k)) = true

/-- Relation-facing bridge for the verified matching classifier. -/
theorem boolLocalPerfectMatchingOffCycle_normalForm
    {r : Fin 6 → Fin 6 → Bool}
    (hr : BoolLocalPerfectMatchingOffCycle r) :
    BoolHasSixCycleMatchingNormalForm r := by
  have hbv : LocalPerfectMatchingOffCycle (matrixBV36 r) := by
    rcases hr with ⟨hloop, hsym, hdeg, hoff⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [adj36_matrixBV36] using hloop
    · simpa only [adj36_matrixBV36] using hsym
    · intro x
      apply BitVec.eq_of_toNat_eq
      rw [cpop6_eq_filter_card]
      simp only [row36_matrixBV36_getLsbD]
      simpa using hdeg x
    · simpa only [adj36_matrixBV36] using hoff
  simpa only [BoolHasSixCycleMatchingNormalForm,
    HasSixCycleMatchingNormalForm, adj36_matrixBV36] using
      localPerfectMatchingOffCycle_normalForm (matrixBV36 r) hbv

/-- Graph-facing form of the six-cycle matching classifier. -/
theorem oneRegular_off_sixCycle_normalForm
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (f : Fin 6 → V) (hfinj : Function.Injective f)
    (hclosed : ∀ i, C.neighborFinset (f i) ⊆ Finset.univ.image f)
    (hdegree : ∀ i, C.degree (f i) = 1)
    (hoff : ∀ i, ¬ C.Adj (f i) (f (next6 i)) ∧
      ¬ C.Adj (f i) (f (prev6 i))) :
    (∀ i, C.Adj (f i) (f (opposite6 i))) ∨
    ∃ k,
      C.Adj (f k) (f (opposite6 k)) ∧
      C.Adj (f (next6 k)) (f (prev6 k)) ∧
      C.Adj (f (next6 (next6 k))) (f (prev6 (prev6 k))) := by
  classical
  let r : Fin 6 → Fin 6 → Bool := fun i j => decide (C.Adj (f i) (f j))
  have hrow : ∀ i, (Finset.univ.filter fun j => r i j).card = 1 := by
    intro i
    have hcard : (Finset.univ.filter fun j => r i j).card =
        (C.neighborFinset (f i)).card := by
      apply Finset.card_bij (fun j _hj => f j)
      · intro j hj
        have : C.Adj (f i) (f j) := by
          simpa [r] using (Finset.mem_filter.mp hj).2
        exact (C.mem_neighborFinset (f i) (f j)).mpr this
      · intro j hj k hk hjk
        exact hfinj hjk
      · intro y hy
        have hyRange := hclosed i hy
        obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hyRange
        refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩, rfl⟩
        have hij : C.Adj (f i) (f j) :=
          (C.mem_neighborFinset (f i) (f j)).mp hy
        simp [r, hij]
    rw [hcard, C.card_neighborFinset_eq_degree, hdegree]
  have hr : BoolLocalPerfectMatchingOffCycle r := by
    refine ⟨?_, ?_, hrow, ?_⟩
    · intro i
      simp [r, C.loopless.irrefl]
    · intro i j
      simp only [r, decide_eq_decide]
      exact C.adj_comm (f i) (f j)
    · intro i
      constructor
      · simp [r, (hoff i).1]
      · simp [r, (hoff i).2]
  have hnormal := boolLocalPerfectMatchingOffCycle_normalForm hr
  simpa only [BoolHasSixCycleMatchingNormalForm, r, decide_eq_true_eq] using hnormal

end Erdos85
