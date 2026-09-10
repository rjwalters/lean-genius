from pathlib import Path
import re,json
p=Path(__file__).parent;t=json.loads((p/'tree.json').read_text())
s=(p.parent/'row_cover_certificate/CoverageAssemblyStructure.lean').read_text().replace('import LiteralData','import Zero26Data').replace('ColumnCoverageLiterals','Zero26').replace('ColumnCoverageStructure','Zero26Structure').replace('Fin 140','Fin 0')
for i,x in enumerate(t['subtrees']):
 row='{'+','.join(map(str,x['prefix_columns'][1]))+'}'
 s=re.sub(r'def prefix'+str(i)+r' :[^\n]*',f'def prefix{i} : Fin 8 → Finset (Fin 15) := ![∅,{row},∅,∅,∅,∅,∅,∅]',s)
 s=re.sub(r'Function.update base \(1 : Fin 8\) \{[^}]*\} = prefix'+str(i)+r' :=',f'Function.update base (1 : Fin 8) {row} = prefix{i} :=',s)
(p/'Zero26Structure.lean').write_text(s)
s='import Zero26Structure\n'+''.join(f'import Zero26Shard{i}\n' for i in range(36))+'namespace Zero26Assembly\nopen Erdos85 Zero26\n'
s+='def pairs : List (Fin 8 × Fin 8) := [(2,3),(4,5),(6,7)]\n'
s+='def cert : FiniteRowCoverCertificate ThreeHighColumnCut (Fin 0) := .branch [.branch ['+','.join(f'Zero26Shard{i}.cert' for i in range(36))+']]\n'
s+='theorem checked : threeHighColumnCoverCheck U R pairs threeHighColumnScore domains table cert = true := by\n  exact Zero26Structure.assemble\n'
s+='    '+' '.join(f'Zero26Shard{i}.cert' for i in range(36))+'\n    '+' '.join(f'Zero26Shard{i}.checked' for i in range(36))+'\nend Zero26Assembly\n#print axioms Zero26Assembly.checked\n'
(p/'Zero26Assembly.lean').write_text(s)
s='''import Zero26Assembly
import Zero26Inputs
namespace Zero26
open Erdos85
attribute [local irreducible] threeHighCrossDomain
theorem no_joint_literal (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj U R cross) := by
  exact threeHighWitnessedColumnCover_no_joint U R Zero26Assembly.pairs
    threeHighColumnScore swaps_valid domains reasons domains_checked table
    Zero26Assembly.cert Zero26Assembly.checked table_no_joint cross hc he

theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)))
    (he : encodedExternalBlockCap (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 82)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) cross) := by
  rw [← U_eq, ← R_eq] at hc he ⊢
  exact no_joint_literal cross hc he
end Zero26
#print axioms Zero26.no_joint_literal
#print axioms Zero26.no_joint
'''
(p/'Zero26Exclusion.lean').write_text(s)
