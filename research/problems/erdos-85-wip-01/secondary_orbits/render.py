from pathlib import Path
import json
import sys
base=Path(__file__).parent;d=json.loads((base/'witnesses.json').read_text())
out='''import Proofs.Erdos85ThreeHighSecondaryDomain

namespace Erdos85

def threeHighSecondaryCode (m : Fin 3) (a b : Fin 7) (e : Bool) : ThreeHighSecondaryTuple :=
  (m,![Fin.cases none some a,Fin.cases none some b],e)

def threeHighSecondaryRepresentative : Fin 21 → ThreeHighSecondaryTuple :=
  !['''
out+=',\n    '.join(f'threeHighSecondaryCode {m} {a} {b} {str(bool(e)).lower()}' for m,a,b,e in d['representatives'])+']\n\n'
out+='private def orbitWitnesses : Array (Fin 21 × (Fin 8 → Fin 8)) := #[\n'
out+=',\n'.join('  ('+str(w['representative'])+',!['+','.join(map(str,w['permutation']))+'])' for w in d['witnesses'])+']\n\n'
out+='''private def orbitWitness (m : Fin 3) (a b : Fin 7) (e : Bool) : Fin 21 × (Fin 8 → Fin 8) :=
  orbitWitnesses.getD (98*m.val + 14*a.val + 2*b.val + if e then 1 else 0) (0,id)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 50000000 in
theorem threeHighSecondaryCode_orbit_certificate (m : Fin 3) (a b : Fin 7) (e : Bool)
    (h : threeHighSecondaryCode m a b e ∈ threeHighSecondaryDomain) :
    let w := orbitWitness m a b e
    let r := threeHighSecondaryRepresentative w.1
    r ∈ threeHighSecondaryDomain ∧ m = r.1 ∧ Function.Bijective w.2 ∧
      (∀ i, (w.2 i).val < 6 ↔ i.val < 6) ∧
      ∀ i j, threeHighSecondaryTupleAdj (threeHighSecondaryCode m a b e) i j =
        threeHighSecondaryTupleAdj r (w.2 i) (w.2 j) := by
  simp only [threeHighSecondaryDomain, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  simp only [Function.Bijective, Function.Injective, Function.Surjective]
  decide +revert

end Erdos85
#print axioms Erdos85.threeHighSecondaryCode_orbit_certificate
'''
if len(sys.argv) != 2:
 raise SystemExit('usage: python3 render.py OUTPUT.lean')
Path(sys.argv[1]).write_text(out)
