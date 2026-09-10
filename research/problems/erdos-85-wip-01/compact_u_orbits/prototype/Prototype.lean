import Proofs.Erdos85ThreeBlockCandidateDomains
namespace UPrototype
open Erdos85
def fw : Fin 120 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,1,2,4,3],![0,1,3,2,4],![0,1,3,4,2],![0,1,4,2,3],![0,1,4,3,2],![0,2,1,3,4],![0,2,1,4,3],![0,2,3,1,4],![0,2,3,4,1],![0,2,4,1,3],![0,2,4,3,1],![0,3,1,2,4],![0,3,1,4,2],![0,3,2,1,4],![0,3,2,4,1],![0,3,4,1,2],![0,3,4,2,1],![0,4,1,2,3],![0,4,1,3,2],![0,4,2,1,3],![0,4,2,3,1],![0,4,3,1,2],![0,4,3,2,1],![1,0,2,3,4],![1,0,2,4,3],![1,0,3,2,4],![1,0,3,4,2],![1,0,4,2,3],![1,0,4,3,2],![1,2,0,3,4],![1,2,0,4,3],![1,2,3,0,4],![1,2,3,4,0],![1,2,4,0,3],![1,2,4,3,0],![1,3,0,2,4],![1,3,0,4,2],![1,3,2,0,4],![1,3,2,4,0],![1,3,4,0,2],![1,3,4,2,0],![1,4,0,2,3],![1,4,0,3,2],![1,4,2,0,3],![1,4,2,3,0],![1,4,3,0,2],![1,4,3,2,0],![2,0,1,3,4],![2,0,1,4,3],![2,0,3,1,4],![2,0,3,4,1],![2,0,4,1,3],![2,0,4,3,1],![2,1,0,3,4],![2,1,0,4,3],![2,1,3,0,4],![2,1,3,4,0],![2,1,4,0,3],![2,1,4,3,0],![2,3,0,1,4],![2,3,0,4,1],![2,3,1,0,4],![2,3,1,4,0],![2,3,4,0,1],![2,3,4,1,0],![2,4,0,1,3],![2,4,0,3,1],![2,4,1,0,3],![2,4,1,3,0],![2,4,3,0,1],![2,4,3,1,0],![3,0,1,2,4],![3,0,1,4,2],![3,0,2,1,4],![3,0,2,4,1],![3,0,4,1,2],![3,0,4,2,1],![3,1,0,2,4],![3,1,0,4,2],![3,1,2,0,4],![3,1,2,4,0],![3,1,4,0,2],![3,1,4,2,0],![3,2,0,1,4],![3,2,0,4,1],![3,2,1,0,4],![3,2,1,4,0],![3,2,4,0,1],![3,2,4,1,0],![3,4,0,1,2],![3,4,0,2,1],![3,4,1,0,2],![3,4,1,2,0],![3,4,2,0,1],![3,4,2,1,0],![4,0,1,2,3],![4,0,1,3,2],![4,0,2,1,3],![4,0,2,3,1],![4,0,3,1,2],![4,0,3,2,1],![4,1,0,2,3],![4,1,0,3,2],![4,1,2,0,3],![4,1,2,3,0],![4,1,3,0,2],![4,1,3,2,0],![4,2,0,1,3],![4,2,0,3,1],![4,2,1,0,3],![4,2,1,3,0],![4,2,3,0,1],![4,2,3,1,0],![4,3,0,1,2],![4,3,0,2,1],![4,3,1,0,2],![4,3,1,2,0],![4,3,2,0,1],![4,3,2,1,0]]
def inv : Fin 120 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,1,2,4,3],![0,1,3,2,4],![0,1,4,2,3],![0,1,3,4,2],![0,1,4,3,2],![0,2,1,3,4],![0,2,1,4,3],![0,3,1,2,4],![0,4,1,2,3],![0,3,1,4,2],![0,4,1,3,2],![0,2,3,1,4],![0,2,4,1,3],![0,3,2,1,4],![0,4,2,1,3],![0,3,4,1,2],![0,4,3,1,2],![0,2,3,4,1],![0,2,4,3,1],![0,3,2,4,1],![0,4,2,3,1],![0,3,4,2,1],![0,4,3,2,1],![1,0,2,3,4],![1,0,2,4,3],![1,0,3,2,4],![1,0,4,2,3],![1,0,3,4,2],![1,0,4,3,2],![2,0,1,3,4],![2,0,1,4,3],![3,0,1,2,4],![4,0,1,2,3],![3,0,1,4,2],![4,0,1,3,2],![2,0,3,1,4],![2,0,4,1,3],![3,0,2,1,4],![4,0,2,1,3],![3,0,4,1,2],![4,0,3,1,2],![2,0,3,4,1],![2,0,4,3,1],![3,0,2,4,1],![4,0,2,3,1],![3,0,4,2,1],![4,0,3,2,1],![1,2,0,3,4],![1,2,0,4,3],![1,3,0,2,4],![1,4,0,2,3],![1,3,0,4,2],![1,4,0,3,2],![2,1,0,3,4],![2,1,0,4,3],![3,1,0,2,4],![4,1,0,2,3],![3,1,0,4,2],![4,1,0,3,2],![2,3,0,1,4],![2,4,0,1,3],![3,2,0,1,4],![4,2,0,1,3],![3,4,0,1,2],![4,3,0,1,2],![2,3,0,4,1],![2,4,0,3,1],![3,2,0,4,1],![4,2,0,3,1],![3,4,0,2,1],![4,3,0,2,1],![1,2,3,0,4],![1,2,4,0,3],![1,3,2,0,4],![1,4,2,0,3],![1,3,4,0,2],![1,4,3,0,2],![2,1,3,0,4],![2,1,4,0,3],![3,1,2,0,4],![4,1,2,0,3],![3,1,4,0,2],![4,1,3,0,2],![2,3,1,0,4],![2,4,1,0,3],![3,2,1,0,4],![4,2,1,0,3],![3,4,1,0,2],![4,3,1,0,2],![2,3,4,0,1],![2,4,3,0,1],![3,2,4,0,1],![4,2,3,0,1],![3,4,2,0,1],![4,3,2,0,1],![1,2,3,4,0],![1,2,4,3,0],![1,3,2,4,0],![1,4,2,3,0],![1,3,4,2,0],![1,4,3,2,0],![2,1,3,4,0],![2,1,4,3,0],![3,1,2,4,0],![4,1,2,3,0],![3,1,4,2,0],![4,1,3,2,0],![2,3,1,4,0],![2,4,1,3,0],![3,2,1,4,0],![4,2,1,3,0],![3,4,1,2,0],![4,3,1,2,0],![2,3,4,1,0],![2,4,3,1,0],![3,2,4,1,0],![4,2,3,1,0],![3,4,2,1,0],![4,3,2,1,0]]
set_option maxRecDepth 100000 in
private theorem left (p : Fin 120) (i : Fin 5) : inv p (fw p i) = i := by decide +revert
set_option maxRecDepth 100000 in
private theorem right (p : Fin 120) (i : Fin 5) : fw p (inv p i) = i := by decide +revert
def perm (p : Fin 120) : Equiv.Perm (Fin 5) := ⟨fw p,inv p,left p,right p⟩
def repA : Fin 55 → BitVec 10 := ![20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24]
def repB : Fin 55 → BitVec 10 := ![20,20,20,24,24,24,24,24,24,24,24,34,34,40,40,40,40,40,24,24,24,24,24,24,24,24,24,24,40,40,40,40,40,40,66,66,66,68,68,68,260,260,260,260,260,288,288,288,288,288,528,528,528,528,528]
def repP : Fin 55 → Fin 120 := ![14,15,16,5,14,16,20,21,54,55,61,0,1,0,5,21,54,55,5,15,16,21,54,55,58,60,82,94,1,21,54,55,58,79,0,1,14,0,14,16,0,14,15,55,66,0,1,55,67,80,5,14,60,82,90]
def sig : Fin 8 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,1,3,2,4],![1,0,2,3,4],![1,0,3,2,4],![2,3,0,1,4],![2,3,1,0,4],![3,2,0,1,4],![3,2,1,0,4]]
def adj (a b : BitVec 10) (p : Fin 120) (x y : Fin 15) : Bool :=
  threeBlockMatchingAdj ![129,a,b] (perm p) ((@finProdFinEquiv 3 5).symm x) ((@finProdFinEquiv 3 5).symm y)
def label (s : Fin 8) (sw : Bool) (x : Fin 15) : Fin 15 :=
  let t := (@finProdFinEquiv 3 5).symm x
  (@finProdFinEquiv 3 5) ((if sw then Equiv.swap 1 2 t.1 else t.1),sig s t.2)
inductive Cert where
  | cycle (x y a b : Fin 15)
  | orbit (r : Fin 55) (s : Fin 8) (sw : Bool)
def cert : Fin 120 → Cert := ![Cert.cycle 5 12 7 10,Cert.cycle 5 12 7 10,Cert.cycle 2 8 3 12,Cert.cycle 2 13 3 7,Cert.cycle 2 8 3 12,Cert.orbit 18 2 false,Cert.orbit 22 2 false,Cert.orbit 23 2 false,Cert.cycle 2 13 3 7,Cert.cycle 1 9 6 11,Cert.orbit 24 2 false,Cert.cycle 1 9 6 11,Cert.cycle 2 8 3 12,Cert.orbit 24 2 true,Cert.cycle 5 12 7 10,Cert.cycle 1 9 6 11,Cert.orbit 26 2 false,Cert.cycle 1 9 6 11,Cert.cycle 1 14 6 11,Cert.cycle 1 14 6 11,Cert.cycle 1 14 6 11,Cert.cycle 1 9 6 11,Cert.cycle 1 14 6 11,Cert.cycle 1 9 6 11,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 7 5 10,Cert.cycle 0 7 5 10,Cert.cycle 0 11 1 5,Cert.cycle 0 11 1 5,Cert.cycle 0 11 1 5,Cert.cycle 0 11 1 5,Cert.cycle 0 7 5 10,Cert.cycle 0 7 5 10,Cert.cycle 0 11 1 5,Cert.cycle 0 11 1 5,Cert.cycle 0 11 1 5,Cert.cycle 0 11 1 5,Cert.cycle 0 7 5 10,Cert.cycle 0 7 5 10,Cert.cycle 0 11 1 5,Cert.cycle 0 11 1 5,Cert.cycle 0 11 1 5,Cert.cycle 0 11 1 5,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 7 5 10,Cert.cycle 0 7 5 10,Cert.cycle 0 12 5 10,Cert.cycle 0 12 5 10,Cert.cycle 0 12 5 10,Cert.cycle 0 12 5 10,Cert.cycle 0 7 5 10,Cert.cycle 0 7 5 10,Cert.cycle 0 12 5 10,Cert.cycle 0 12 5 10,Cert.cycle 0 12 5 10,Cert.cycle 0 12 5 10,Cert.cycle 0 7 5 10,Cert.cycle 0 7 5 10,Cert.cycle 0 12 5 10,Cert.cycle 0 12 5 10,Cert.cycle 0 12 5 10,Cert.cycle 0 12 5 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 7 5 10,Cert.cycle 0 7 5 10,Cert.cycle 6 14 9 11,Cert.orbit 19 2 false,Cert.orbit 20 2 false,Cert.cycle 2 8 3 12,Cert.cycle 0 7 5 10,Cert.cycle 0 7 5 10,Cert.orbit 25 2 false,Cert.cycle 6 10 9 12,Cert.cycle 1 9 6 11,Cert.cycle 6 10 9 12,Cert.cycle 0 7 5 10,Cert.cycle 0 7 5 10,Cert.cycle 1 14 6 11,Cert.cycle 1 14 6 11,Cert.cycle 1 9 6 11,Cert.cycle 1 14 6 11,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 6 1 10,Cert.cycle 0 7 5 10,Cert.cycle 0 7 5 10,Cert.orbit 19 2 true,Cert.orbit 21 2 false,Cert.cycle 2 13 3 7,Cert.cycle 2 8 3 12,Cert.cycle 0 7 5 10,Cert.cycle 0 7 5 10,Cert.cycle 5 11 7 14,Cert.cycle 5 11 7 14,Cert.cycle 1 9 6 11,Cert.cycle 2 13 3 7,Cert.cycle 0 7 5 10,Cert.cycle 0 7 5 10,Cert.cycle 5 11 7 14,Cert.cycle 2 8 3 12,Cert.cycle 1 9 6 11,Cert.orbit 27 2 false]
def check (p : Fin 120) : Prop :=
  match cert p with
  | .cycle x y a b => x ≠ y ∧ a ≠ b ∧ adj 66 66 p x a = true ∧ adj 66 66 p x b = true ∧ adj 66 66 p y a = true ∧ adj 66 66 p y b = true
  | .orbit r s sw => Function.Bijective (label s sw) ∧ ∀ x y, adj 66 66 p x y = adj (repA r) (repB r) (repP r) (label s sw x) (label s sw y)
instance (p : Fin 120) : Decidable (check p) := by unfold check; split <;> infer_instance
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 50000000 in
theorem checked (p : Fin 120) : check p := by decide +revert
end UPrototype
#print axioms UPrototype.checked

namespace UPrototype
open Erdos85
/-- Decode the checked disjunction using the actual encoded C4-free premise. -/
theorem covered (p : Fin 120) (hf : encodedC4Free (adj 66 66 p) = true) :
    ∃ (r : Fin 55) (s : Fin 8) (sw : Bool), Function.Bijective (label s sw) ∧
      ∀ x y, adj 66 66 p x y = adj (repA r) (repB r) (repP r) (label s sw x) (label s sw y) := by
  have h := checked p
  cases hc : cert p with
  | cycle x y a b =>
    simp only [check,hc] at h
    obtain ⟨hxy,hab,hxa,hxb,hya,hyb⟩ := h
    unfold encodedC4Free at hf
    simp only [decide_eq_true_eq] at hf
    have hbnd := hf x y hxy
    have ha : a ∈ Finset.univ.filter (fun i => adj 66 66 p x i && adj 66 66 p y i) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨hxa,hya⟩
    have hb : b ∈ Finset.univ.filter (fun i => adj 66 66 p x i && adj 66 66 p y i) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨hxb,hyb⟩
    exact False.elim (hab (Finset.card_le_one.mp hbnd a ha b hb))
  | orbit r s sw =>
    exact ⟨r,s,sw,by simpa only [check,hc] using h⟩
end UPrototype
#print axioms UPrototype.covered
