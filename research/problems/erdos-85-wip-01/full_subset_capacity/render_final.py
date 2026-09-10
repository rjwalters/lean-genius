from pathlib import Path
import json
p=Path(__file__).parent
for row in json.loads((p/'MANIFEST.json').read_text()):
 name=row['name'];a,b,c=row['compact'];r,q=row['pair']
 s='import '+name+'Inputs\nimport Proofs.Erdos85ThreeHighColumnSubsetCapacity\nnamespace '+name+'\nopen Erdos85\nattribute [local irreducible] threeHighCrossDomain\n'
 s+='''theorem checked : threeHighColumnSubsetCapacityCheck U domains S caps = true := by
  simp only [threeHighColumnSubsetCapacityCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨deficit, List.all_eq_true.mpr (fun j _ => caps_checked j)⟩
theorem impossible_literal (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) : False :=
  threeHighWitnessedColumnSubsetCapacity_impossible U R domains reasons S caps domains_checked checked cross hc he
'''
 U=f'(threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode {a} {b} {c})))';R=f'(threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative {q}))'
 s+=f'''theorem impossible (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain {U} {R})
    (he : encodedExternalBlockCap (threeHighEmptyAdj {U} {R} cross) threeHighCanonicalRow = true) : False := by
  rw [← U_eq, ← R_eq] at hc he
  exact impossible_literal cross hc he

theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain {U} {R})
    (he : encodedExternalBlockCap (threeHighEmptyAdj {U} {R} cross) threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj {U} {R} cross) := (impossible cross hc he).elim
end {name}
'''
 for th in ['checked','impossible_literal','impossible','no_joint']:s+='#print axioms '+name+'.'+th+'\n'
 (p/(name+'Exclusion.lean')).write_text(s)
