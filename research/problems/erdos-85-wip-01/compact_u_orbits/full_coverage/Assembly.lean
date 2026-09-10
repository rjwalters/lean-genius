import Proofs.Erdos85ThreeBlockRestrictedOrbitCover
import Full_3_3
import Full_3_4
import Full_3_5
import Full_3_6
import Full_3_7
import Full_3_8
import Full_3_9
import Full_3_10
import Full_3_12
import Full_3_13
import Full_4_3
import Full_4_4
import Full_4_5
import Full_4_6
import Full_4_7
import Full_4_8
import Full_4_9
import Full_4_10
import Full_4_12
import Full_4_13
import Full_5_3
import Full_5_4
import Full_5_5
import Full_5_6
import Full_5_7
import Full_5_8
import Full_5_9
import Full_5_10
import Full_5_12
import Full_5_13
import Full_6_3
import Full_6_4
import Full_6_5
import Full_6_6
import Full_6_7
import Full_6_8
import Full_6_9
import Full_6_10
import Full_6_12
import Full_6_13
import Full_7_3
import Full_7_4
import Full_7_5
import Full_7_6
import Full_7_7
import Full_7_8
import Full_7_9
import Full_7_10
import Full_7_12
import Full_7_13
import Full_8_3
import Full_8_4
import Full_8_5
import Full_8_6
import Full_8_7
import Full_8_8
import Full_8_9
import Full_8_10
import Full_8_12
import Full_8_13
import Full_9_3
import Full_9_4
import Full_9_5
import Full_9_6
import Full_9_7
import Full_9_8
import Full_9_9
import Full_9_10
import Full_9_12
import Full_9_13
import Full_10_3
import Full_10_4
import Full_10_5
import Full_10_6
import Full_10_7
import Full_10_8
import Full_10_9
import Full_10_10
import Full_10_12
import Full_10_13
import Full_12_3
import Full_12_4
import Full_12_5
import Full_12_6
import Full_12_7
import Full_12_8
import Full_12_9
import Full_12_10
import Full_12_12
import Full_12_13
import Full_13_3
import Full_13_4
import Full_13_5
import Full_13_6
import Full_13_7
import Full_13_8
import Full_13_9
import Full_13_10
import Full_13_12
import Full_13_13

namespace FullURestrictedAssembly
open Erdos85
def representative := FullUShard_3_3.representative
def cert (a b : Fin 15) (p : Fin 120) : ThreeBlockOrbitCertificate 55 :=
  match a.val,b.val with
  | 3,3 => FullUShard_3_3.cert p
  | 3,4 => FullUShard_3_4.cert p
  | 3,5 => FullUShard_3_5.cert p
  | 3,6 => FullUShard_3_6.cert p
  | 3,7 => FullUShard_3_7.cert p
  | 3,8 => FullUShard_3_8.cert p
  | 3,9 => FullUShard_3_9.cert p
  | 3,10 => FullUShard_3_10.cert p
  | 3,12 => FullUShard_3_12.cert p
  | 3,13 => FullUShard_3_13.cert p
  | 4,3 => FullUShard_4_3.cert p
  | 4,4 => FullUShard_4_4.cert p
  | 4,5 => FullUShard_4_5.cert p
  | 4,6 => FullUShard_4_6.cert p
  | 4,7 => FullUShard_4_7.cert p
  | 4,8 => FullUShard_4_8.cert p
  | 4,9 => FullUShard_4_9.cert p
  | 4,10 => FullUShard_4_10.cert p
  | 4,12 => FullUShard_4_12.cert p
  | 4,13 => FullUShard_4_13.cert p
  | 5,3 => FullUShard_5_3.cert p
  | 5,4 => FullUShard_5_4.cert p
  | 5,5 => FullUShard_5_5.cert p
  | 5,6 => FullUShard_5_6.cert p
  | 5,7 => FullUShard_5_7.cert p
  | 5,8 => FullUShard_5_8.cert p
  | 5,9 => FullUShard_5_9.cert p
  | 5,10 => FullUShard_5_10.cert p
  | 5,12 => FullUShard_5_12.cert p
  | 5,13 => FullUShard_5_13.cert p
  | 6,3 => FullUShard_6_3.cert p
  | 6,4 => FullUShard_6_4.cert p
  | 6,5 => FullUShard_6_5.cert p
  | 6,6 => FullUShard_6_6.cert p
  | 6,7 => FullUShard_6_7.cert p
  | 6,8 => FullUShard_6_8.cert p
  | 6,9 => FullUShard_6_9.cert p
  | 6,10 => FullUShard_6_10.cert p
  | 6,12 => FullUShard_6_12.cert p
  | 6,13 => FullUShard_6_13.cert p
  | 7,3 => FullUShard_7_3.cert p
  | 7,4 => FullUShard_7_4.cert p
  | 7,5 => FullUShard_7_5.cert p
  | 7,6 => FullUShard_7_6.cert p
  | 7,7 => FullUShard_7_7.cert p
  | 7,8 => FullUShard_7_8.cert p
  | 7,9 => FullUShard_7_9.cert p
  | 7,10 => FullUShard_7_10.cert p
  | 7,12 => FullUShard_7_12.cert p
  | 7,13 => FullUShard_7_13.cert p
  | 8,3 => FullUShard_8_3.cert p
  | 8,4 => FullUShard_8_4.cert p
  | 8,5 => FullUShard_8_5.cert p
  | 8,6 => FullUShard_8_6.cert p
  | 8,7 => FullUShard_8_7.cert p
  | 8,8 => FullUShard_8_8.cert p
  | 8,9 => FullUShard_8_9.cert p
  | 8,10 => FullUShard_8_10.cert p
  | 8,12 => FullUShard_8_12.cert p
  | 8,13 => FullUShard_8_13.cert p
  | 9,3 => FullUShard_9_3.cert p
  | 9,4 => FullUShard_9_4.cert p
  | 9,5 => FullUShard_9_5.cert p
  | 9,6 => FullUShard_9_6.cert p
  | 9,7 => FullUShard_9_7.cert p
  | 9,8 => FullUShard_9_8.cert p
  | 9,9 => FullUShard_9_9.cert p
  | 9,10 => FullUShard_9_10.cert p
  | 9,12 => FullUShard_9_12.cert p
  | 9,13 => FullUShard_9_13.cert p
  | 10,3 => FullUShard_10_3.cert p
  | 10,4 => FullUShard_10_4.cert p
  | 10,5 => FullUShard_10_5.cert p
  | 10,6 => FullUShard_10_6.cert p
  | 10,7 => FullUShard_10_7.cert p
  | 10,8 => FullUShard_10_8.cert p
  | 10,9 => FullUShard_10_9.cert p
  | 10,10 => FullUShard_10_10.cert p
  | 10,12 => FullUShard_10_12.cert p
  | 10,13 => FullUShard_10_13.cert p
  | 12,3 => FullUShard_12_3.cert p
  | 12,4 => FullUShard_12_4.cert p
  | 12,5 => FullUShard_12_5.cert p
  | 12,6 => FullUShard_12_6.cert p
  | 12,7 => FullUShard_12_7.cert p
  | 12,8 => FullUShard_12_8.cert p
  | 12,9 => FullUShard_12_9.cert p
  | 12,10 => FullUShard_12_10.cert p
  | 12,12 => FullUShard_12_12.cert p
  | 12,13 => FullUShard_12_13.cert p
  | 13,3 => FullUShard_13_3.cert p
  | 13,4 => FullUShard_13_4.cert p
  | 13,5 => FullUShard_13_5.cert p
  | 13,6 => FullUShard_13_6.cert p
  | 13,7 => FullUShard_13_7.cert p
  | 13,8 => FullUShard_13_8.cert p
  | 13,9 => FullUShard_13_9.cert p
  | 13,10 => FullUShard_13_10.cert p
  | 13,12 => FullUShard_13_12.cert p
  | 13,13 => FullUShard_13_13.cert p
  | _,_ => .cycle 0 0 0 0

theorem checked (a b : Fin 15) (p : Fin 120) (h : (a,b) ∈ threeBlockDisjointMaskPairs) :
    (cert a b p).Valid (threeBlockCompactAdj (threeBlockCompactCode a b p)) representative := by
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp h
  rw [threeBlockDisjointMaskCodes_eq] at ha hb
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
  · subst a
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
    · subst b
      exact FullUShard_3_3.checked p
    · subst b
      exact FullUShard_3_4.checked p
    · subst b
      exact FullUShard_3_5.checked p
    · subst b
      exact FullUShard_3_6.checked p
    · subst b
      exact FullUShard_3_7.checked p
    · subst b
      exact FullUShard_3_8.checked p
    · subst b
      exact FullUShard_3_9.checked p
    · subst b
      exact FullUShard_3_10.checked p
    · subst b
      exact FullUShard_3_12.checked p
    · subst b
      exact FullUShard_3_13.checked p
  · subst a
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
    · subst b
      exact FullUShard_4_3.checked p
    · subst b
      exact FullUShard_4_4.checked p
    · subst b
      exact FullUShard_4_5.checked p
    · subst b
      exact FullUShard_4_6.checked p
    · subst b
      exact FullUShard_4_7.checked p
    · subst b
      exact FullUShard_4_8.checked p
    · subst b
      exact FullUShard_4_9.checked p
    · subst b
      exact FullUShard_4_10.checked p
    · subst b
      exact FullUShard_4_12.checked p
    · subst b
      exact FullUShard_4_13.checked p
  · subst a
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
    · subst b
      exact FullUShard_5_3.checked p
    · subst b
      exact FullUShard_5_4.checked p
    · subst b
      exact FullUShard_5_5.checked p
    · subst b
      exact FullUShard_5_6.checked p
    · subst b
      exact FullUShard_5_7.checked p
    · subst b
      exact FullUShard_5_8.checked p
    · subst b
      exact FullUShard_5_9.checked p
    · subst b
      exact FullUShard_5_10.checked p
    · subst b
      exact FullUShard_5_12.checked p
    · subst b
      exact FullUShard_5_13.checked p
  · subst a
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
    · subst b
      exact FullUShard_6_3.checked p
    · subst b
      exact FullUShard_6_4.checked p
    · subst b
      exact FullUShard_6_5.checked p
    · subst b
      exact FullUShard_6_6.checked p
    · subst b
      exact FullUShard_6_7.checked p
    · subst b
      exact FullUShard_6_8.checked p
    · subst b
      exact FullUShard_6_9.checked p
    · subst b
      exact FullUShard_6_10.checked p
    · subst b
      exact FullUShard_6_12.checked p
    · subst b
      exact FullUShard_6_13.checked p
  · subst a
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
    · subst b
      exact FullUShard_7_3.checked p
    · subst b
      exact FullUShard_7_4.checked p
    · subst b
      exact FullUShard_7_5.checked p
    · subst b
      exact FullUShard_7_6.checked p
    · subst b
      exact FullUShard_7_7.checked p
    · subst b
      exact FullUShard_7_8.checked p
    · subst b
      exact FullUShard_7_9.checked p
    · subst b
      exact FullUShard_7_10.checked p
    · subst b
      exact FullUShard_7_12.checked p
    · subst b
      exact FullUShard_7_13.checked p
  · subst a
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
    · subst b
      exact FullUShard_8_3.checked p
    · subst b
      exact FullUShard_8_4.checked p
    · subst b
      exact FullUShard_8_5.checked p
    · subst b
      exact FullUShard_8_6.checked p
    · subst b
      exact FullUShard_8_7.checked p
    · subst b
      exact FullUShard_8_8.checked p
    · subst b
      exact FullUShard_8_9.checked p
    · subst b
      exact FullUShard_8_10.checked p
    · subst b
      exact FullUShard_8_12.checked p
    · subst b
      exact FullUShard_8_13.checked p
  · subst a
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
    · subst b
      exact FullUShard_9_3.checked p
    · subst b
      exact FullUShard_9_4.checked p
    · subst b
      exact FullUShard_9_5.checked p
    · subst b
      exact FullUShard_9_6.checked p
    · subst b
      exact FullUShard_9_7.checked p
    · subst b
      exact FullUShard_9_8.checked p
    · subst b
      exact FullUShard_9_9.checked p
    · subst b
      exact FullUShard_9_10.checked p
    · subst b
      exact FullUShard_9_12.checked p
    · subst b
      exact FullUShard_9_13.checked p
  · subst a
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
    · subst b
      exact FullUShard_10_3.checked p
    · subst b
      exact FullUShard_10_4.checked p
    · subst b
      exact FullUShard_10_5.checked p
    · subst b
      exact FullUShard_10_6.checked p
    · subst b
      exact FullUShard_10_7.checked p
    · subst b
      exact FullUShard_10_8.checked p
    · subst b
      exact FullUShard_10_9.checked p
    · subst b
      exact FullUShard_10_10.checked p
    · subst b
      exact FullUShard_10_12.checked p
    · subst b
      exact FullUShard_10_13.checked p
  · subst a
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
    · subst b
      exact FullUShard_12_3.checked p
    · subst b
      exact FullUShard_12_4.checked p
    · subst b
      exact FullUShard_12_5.checked p
    · subst b
      exact FullUShard_12_6.checked p
    · subst b
      exact FullUShard_12_7.checked p
    · subst b
      exact FullUShard_12_8.checked p
    · subst b
      exact FullUShard_12_9.checked p
    · subst b
      exact FullUShard_12_10.checked p
    · subst b
      exact FullUShard_12_12.checked p
    · subst b
      exact FullUShard_12_13.checked p
  · subst a
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
    · subst b
      exact FullUShard_13_3.checked p
    · subst b
      exact FullUShard_13_4.checked p
    · subst b
      exact FullUShard_13_5.checked p
    · subst b
      exact FullUShard_13_6.checked p
    · subst b
      exact FullUShard_13_7.checked p
    · subst b
      exact FullUShard_13_8.checked p
    · subst b
      exact FullUShard_13_9.checked p
    · subst b
      exact FullUShard_13_10.checked p
    · subst b
      exact FullUShard_13_12.checked p
    · subst b
      exact FullUShard_13_13.checked p

theorem covered (p : ThreeBlockFirstRowParameters)
    (hfree : encodedC4Free (threeBlockCompactAdj p) = true) :
    ∃ (r : Fin 55) (q : Fin 120) (sw : Bool), ∀ x y,
      threeBlockCompactAdj p x y =
        representative r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y) :=
  threeBlockRestrictedOrbitCover representative cert checked p hfree
end FullURestrictedAssembly
#print axioms FullURestrictedAssembly.checked
#print axioms FullURestrictedAssembly.covered
