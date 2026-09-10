from pathlib import Path
import json,hashlib
p=Path(__file__).parent;rows=json.loads((p/'MANIFEST.json').read_text())
for r in rows:
 for suffix in ['Data','Inputs','Exclusion']:
  f=p/(r['name']+suffix+'.lean');r['files'][f.name]=hashlib.sha256(f.read_bytes()).hexdigest()
(p/'BATCH_MANIFEST.json').write_text(json.dumps(rows,indent=2)+'\n')
s=''.join('import '+r['name']+'Exclusion\n' for r in rows)+'namespace SubsetCapacityBatch\nopen Erdos85\nattribute [local irreducible] threeHighCrossDomain\n'
s+='def pair : Fin 13 → Fin 55 × Fin 21 := !['+','.join('('+','.join(map(str,r['pair']))+')' for r in rows)+']\n'
s+='def U : Fin 13 → (Fin 15 → Fin 15 → Bool) := !['+','.join('threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode '+' '.join(map(str,r['compact']))+'))' for r in rows)+']\n'
s+='def R : Fin 13 → (Fin 8 → Fin 8 → Bool) := !['+','.join('threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative '+str(r['pair'][1])+')' for r in rows)+']\n'
s+='def pairs : Finset (Fin 55 × Fin 21) := Finset.univ.image pair\ntheorem pairs_card : pairs.card = 13 := by decide\n'
s+='''theorem impossible (i : Fin 13) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (U i) (R i))
    (he : encodedExternalBlockCap (threeHighEmptyAdj (U i) (R i) cross) threeHighCanonicalRow = true) : False := by
  fin_cases i
'''
for r in rows:s+='  · exact '+r['name']+'.impossible cross hc he\n'
s+='''theorem no_joint (i : Fin 13) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (U i) (R i))
    (he : encodedExternalBlockCap (threeHighEmptyAdj (U i) (R i) cross) threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj (U i) (R i) cross) := (impossible i cross hc he).elim
end SubsetCapacityBatch
#print axioms SubsetCapacityBatch.pairs_card
#print axioms SubsetCapacityBatch.impossible
#print axioms SubsetCapacityBatch.no_joint
'''
(p/'SubsetCapacityBatch.lean').write_text(s)
