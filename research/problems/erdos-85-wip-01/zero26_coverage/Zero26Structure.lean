import Zero26Data
import Proofs.Erdos85FiniteRowCoverAssembly
namespace Zero26Structure
open Erdos85 Zero26
set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000
def pairs : List (Fin 8 × Fin 8) := [(2,3),(4,5),(6,7)]
def reject (k : Nat) (columns : Fin 8 → Finset (Fin 15)) (reason : ThreeHighColumnCut) : Bool :=
  threeHighColumnCutCheck U R pairs threeHighColumnScore k
    (threeHighCrossOfColumns columns) reason
def accept (columns : Fin 8 → Finset (Fin 15)) (entry : Fin 0) : Bool :=
  decide (∀ i j, threeHighCrossOfColumns columns i j = table entry i j)
def base : Fin 8 → Finset (Fin 15) := fun _ => ∅
def prefix0 : Fin 8 → Finset (Fin 15) := ![∅,{5,11},∅,∅,∅,∅,∅,∅]
def prefix1 : Fin 8 → Finset (Fin 15) := ![∅,{5,13},∅,∅,∅,∅,∅,∅]
def prefix2 : Fin 8 → Finset (Fin 15) := ![∅,{5,14},∅,∅,∅,∅,∅,∅]
def prefix3 : Fin 8 → Finset (Fin 15) := ![∅,{6,10},∅,∅,∅,∅,∅,∅]
def prefix4 : Fin 8 → Finset (Fin 15) := ![∅,{6,13},∅,∅,∅,∅,∅,∅]
def prefix5 : Fin 8 → Finset (Fin 15) := ![∅,{7,13},∅,∅,∅,∅,∅,∅]
def prefix6 : Fin 8 → Finset (Fin 15) := ![∅,{7,14},∅,∅,∅,∅,∅,∅]
def prefix7 : Fin 8 → Finset (Fin 15) := ![∅,{8,10},∅,∅,∅,∅,∅,∅]
def prefix8 : Fin 8 → Finset (Fin 15) := ![∅,{8,11},∅,∅,∅,∅,∅,∅]
def prefix9 : Fin 8 → Finset (Fin 15) := ![∅,{8,12},∅,∅,∅,∅,∅,∅]
def prefix10 : Fin 8 → Finset (Fin 15) := ![∅,{9,10},∅,∅,∅,∅,∅,∅]
def prefix11 : Fin 8 → Finset (Fin 15) := ![∅,{9,12},∅,∅,∅,∅,∅,∅]
def prefix12 : Fin 8 → Finset (Fin 15) := ![∅,{0,10},∅,∅,∅,∅,∅,∅]
def prefix13 : Fin 8 → Finset (Fin 15) := ![∅,{0,12},∅,∅,∅,∅,∅,∅]
def prefix14 : Fin 8 → Finset (Fin 15) := ![∅,{0,5},∅,∅,∅,∅,∅,∅]
def prefix15 : Fin 8 → Finset (Fin 15) := ![∅,{0,7},∅,∅,∅,∅,∅,∅]
def prefix16 : Fin 8 → Finset (Fin 15) := ![∅,{1,13},∅,∅,∅,∅,∅,∅]
def prefix17 : Fin 8 → Finset (Fin 15) := ![∅,{1,14},∅,∅,∅,∅,∅,∅]
def prefix18 : Fin 8 → Finset (Fin 15) := ![∅,{1,8},∅,∅,∅,∅,∅,∅]
def prefix19 : Fin 8 → Finset (Fin 15) := ![∅,{1,9},∅,∅,∅,∅,∅,∅]
def prefix20 : Fin 8 → Finset (Fin 15) := ![∅,{2,10},∅,∅,∅,∅,∅,∅]
def prefix21 : Fin 8 → Finset (Fin 15) := ![∅,{2,12},∅,∅,∅,∅,∅,∅]
def prefix22 : Fin 8 → Finset (Fin 15) := ![∅,{2,5},∅,∅,∅,∅,∅,∅]
def prefix23 : Fin 8 → Finset (Fin 15) := ![∅,{2,7},∅,∅,∅,∅,∅,∅]
def prefix24 : Fin 8 → Finset (Fin 15) := ![∅,{3,11},∅,∅,∅,∅,∅,∅]
def prefix25 : Fin 8 → Finset (Fin 15) := ![∅,{3,13},∅,∅,∅,∅,∅,∅]
def prefix26 : Fin 8 → Finset (Fin 15) := ![∅,{3,14},∅,∅,∅,∅,∅,∅]
def prefix27 : Fin 8 → Finset (Fin 15) := ![∅,{3,6},∅,∅,∅,∅,∅,∅]
def prefix28 : Fin 8 → Finset (Fin 15) := ![∅,{3,8},∅,∅,∅,∅,∅,∅]
def prefix29 : Fin 8 → Finset (Fin 15) := ![∅,{3,9},∅,∅,∅,∅,∅,∅]
def prefix30 : Fin 8 → Finset (Fin 15) := ![∅,{4,11},∅,∅,∅,∅,∅,∅]
def prefix31 : Fin 8 → Finset (Fin 15) := ![∅,{4,13},∅,∅,∅,∅,∅,∅]
def prefix32 : Fin 8 → Finset (Fin 15) := ![∅,{4,14},∅,∅,∅,∅,∅,∅]
def prefix33 : Fin 8 → Finset (Fin 15) := ![∅,{4,6},∅,∅,∅,∅,∅,∅]
def prefix34 : Fin 8 → Finset (Fin 15) := ![∅,{4,8},∅,∅,∅,∅,∅,∅]
def prefix35 : Fin 8 → Finset (Fin 15) := ![∅,{4,9},∅,∅,∅,∅,∅,∅]
theorem assemble (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 : FiniteRowCoverCertificate ThreeHighColumnCut (Fin 0))
    (h0 : finiteRowCoverCheck domains reject accept 6 2 prefix0 c0 = true)
    (h1 : finiteRowCoverCheck domains reject accept 6 2 prefix1 c1 = true)
    (h2 : finiteRowCoverCheck domains reject accept 6 2 prefix2 c2 = true)
    (h3 : finiteRowCoverCheck domains reject accept 6 2 prefix3 c3 = true)
    (h4 : finiteRowCoverCheck domains reject accept 6 2 prefix4 c4 = true)
    (h5 : finiteRowCoverCheck domains reject accept 6 2 prefix5 c5 = true)
    (h6 : finiteRowCoverCheck domains reject accept 6 2 prefix6 c6 = true)
    (h7 : finiteRowCoverCheck domains reject accept 6 2 prefix7 c7 = true)
    (h8 : finiteRowCoverCheck domains reject accept 6 2 prefix8 c8 = true)
    (h9 : finiteRowCoverCheck domains reject accept 6 2 prefix9 c9 = true)
    (h10 : finiteRowCoverCheck domains reject accept 6 2 prefix10 c10 = true)
    (h11 : finiteRowCoverCheck domains reject accept 6 2 prefix11 c11 = true)
    (h12 : finiteRowCoverCheck domains reject accept 6 2 prefix12 c12 = true)
    (h13 : finiteRowCoverCheck domains reject accept 6 2 prefix13 c13 = true)
    (h14 : finiteRowCoverCheck domains reject accept 6 2 prefix14 c14 = true)
    (h15 : finiteRowCoverCheck domains reject accept 6 2 prefix15 c15 = true)
    (h16 : finiteRowCoverCheck domains reject accept 6 2 prefix16 c16 = true)
    (h17 : finiteRowCoverCheck domains reject accept 6 2 prefix17 c17 = true)
    (h18 : finiteRowCoverCheck domains reject accept 6 2 prefix18 c18 = true)
    (h19 : finiteRowCoverCheck domains reject accept 6 2 prefix19 c19 = true)
    (h20 : finiteRowCoverCheck domains reject accept 6 2 prefix20 c20 = true)
    (h21 : finiteRowCoverCheck domains reject accept 6 2 prefix21 c21 = true)
    (h22 : finiteRowCoverCheck domains reject accept 6 2 prefix22 c22 = true)
    (h23 : finiteRowCoverCheck domains reject accept 6 2 prefix23 c23 = true)
    (h24 : finiteRowCoverCheck domains reject accept 6 2 prefix24 c24 = true)
    (h25 : finiteRowCoverCheck domains reject accept 6 2 prefix25 c25 = true)
    (h26 : finiteRowCoverCheck domains reject accept 6 2 prefix26 c26 = true)
    (h27 : finiteRowCoverCheck domains reject accept 6 2 prefix27 c27 = true)
    (h28 : finiteRowCoverCheck domains reject accept 6 2 prefix28 c28 = true)
    (h29 : finiteRowCoverCheck domains reject accept 6 2 prefix29 c29 = true)
    (h30 : finiteRowCoverCheck domains reject accept 6 2 prefix30 c30 = true)
    (h31 : finiteRowCoverCheck domains reject accept 6 2 prefix31 c31 = true)
    (h32 : finiteRowCoverCheck domains reject accept 6 2 prefix32 c32 = true)
    (h33 : finiteRowCoverCheck domains reject accept 6 2 prefix33 c33 = true)
    (h34 : finiteRowCoverCheck domains reject accept 6 2 prefix34 c34 = true)
    (h35 : finiteRowCoverCheck domains reject accept 6 2 prefix35 c35 = true)
    : threeHighColumnCoverCheck U R pairs threeHighColumnScore domains table
      (.branch [.branch [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35]]) = true := by
  have level_one : finiteRowCoverCheck domains reject accept 7 1 base (.branch [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35]) = true := by
    apply finiteRowCoverCheck_branch domains reject accept 6 1 (by omega) base [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil))))))))))))))))))))))))))))))))))))
    · have hp : Function.update base (1 : Fin 8) {5,11} = prefix0 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c0 = true) hp) h0
    · have hp : Function.update base (1 : Fin 8) {5,13} = prefix1 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c1 = true) hp) h1
    · have hp : Function.update base (1 : Fin 8) {5,14} = prefix2 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c2 = true) hp) h2
    · have hp : Function.update base (1 : Fin 8) {6,10} = prefix3 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c3 = true) hp) h3
    · have hp : Function.update base (1 : Fin 8) {6,13} = prefix4 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c4 = true) hp) h4
    · have hp : Function.update base (1 : Fin 8) {7,13} = prefix5 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c5 = true) hp) h5
    · have hp : Function.update base (1 : Fin 8) {7,14} = prefix6 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c6 = true) hp) h6
    · have hp : Function.update base (1 : Fin 8) {8,10} = prefix7 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c7 = true) hp) h7
    · have hp : Function.update base (1 : Fin 8) {8,11} = prefix8 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c8 = true) hp) h8
    · have hp : Function.update base (1 : Fin 8) {8,12} = prefix9 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c9 = true) hp) h9
    · have hp : Function.update base (1 : Fin 8) {9,10} = prefix10 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c10 = true) hp) h10
    · have hp : Function.update base (1 : Fin 8) {9,12} = prefix11 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c11 = true) hp) h11
    · have hp : Function.update base (1 : Fin 8) {0,10} = prefix12 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c12 = true) hp) h12
    · have hp : Function.update base (1 : Fin 8) {0,12} = prefix13 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c13 = true) hp) h13
    · have hp : Function.update base (1 : Fin 8) {0,5} = prefix14 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c14 = true) hp) h14
    · have hp : Function.update base (1 : Fin 8) {0,7} = prefix15 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c15 = true) hp) h15
    · have hp : Function.update base (1 : Fin 8) {1,13} = prefix16 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c16 = true) hp) h16
    · have hp : Function.update base (1 : Fin 8) {1,14} = prefix17 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c17 = true) hp) h17
    · have hp : Function.update base (1 : Fin 8) {1,8} = prefix18 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c18 = true) hp) h18
    · have hp : Function.update base (1 : Fin 8) {1,9} = prefix19 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c19 = true) hp) h19
    · have hp : Function.update base (1 : Fin 8) {2,10} = prefix20 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c20 = true) hp) h20
    · have hp : Function.update base (1 : Fin 8) {2,12} = prefix21 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c21 = true) hp) h21
    · have hp : Function.update base (1 : Fin 8) {2,5} = prefix22 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c22 = true) hp) h22
    · have hp : Function.update base (1 : Fin 8) {2,7} = prefix23 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c23 = true) hp) h23
    · have hp : Function.update base (1 : Fin 8) {3,11} = prefix24 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c24 = true) hp) h24
    · have hp : Function.update base (1 : Fin 8) {3,13} = prefix25 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c25 = true) hp) h25
    · have hp : Function.update base (1 : Fin 8) {3,14} = prefix26 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c26 = true) hp) h26
    · have hp : Function.update base (1 : Fin 8) {3,6} = prefix27 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c27 = true) hp) h27
    · have hp : Function.update base (1 : Fin 8) {3,8} = prefix28 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c28 = true) hp) h28
    · have hp : Function.update base (1 : Fin 8) {3,9} = prefix29 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c29 = true) hp) h29
    · have hp : Function.update base (1 : Fin 8) {4,11} = prefix30 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c30 = true) hp) h30
    · have hp : Function.update base (1 : Fin 8) {4,13} = prefix31 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c31 = true) hp) h31
    · have hp : Function.update base (1 : Fin 8) {4,14} = prefix32 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c32 = true) hp) h32
    · have hp : Function.update base (1 : Fin 8) {4,6} = prefix33 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c33 = true) hp) h33
    · have hp : Function.update base (1 : Fin 8) {4,8} = prefix34 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c34 = true) hp) h34
    · have hp : Function.update base (1 : Fin 8) {4,9} = prefix35 := by
        funext j
        fin_cases j <;> rfl
      exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 6 2 rows c35 = true) hp) h35
  change finiteRowCoverCheck domains reject accept 8 0 base (.branch [.branch [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35]]) = true
  apply finiteRowCoverCheck_branch domains reject accept 7 0 (by omega) base [.branch [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35]]
  refine .cons ?_ .nil
  have hp : Function.update base (0 : Fin 8) (∅ : Finset (Fin 15)) = base := by
    funext j
    fin_cases j <;> rfl
  exact Eq.mpr (congrArg (fun rows => finiteRowCoverCheck domains reject accept 7 1 rows (.branch [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35]) = true) hp) level_one
end Zero26Structure
#print axioms Zero26Structure.assemble
