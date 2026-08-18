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

end Erdos85
