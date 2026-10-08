"""Metadata-only adversarial tests; no Lean, native computation or cloud mutation."""
import copy,json,unittest
from pathlib import Path
from validate_axioms import check_reports,STANDARD
ROOT=Path(__file__).resolve().parent
INV=json.loads((ROOT.parent/'h5_stratum_review_20261008/inventory.json').read_text())
def fixture():
    rows=[];graph={}
    for c in INV['cells']:
        axioms=sorted(STANDARD|{p['expected_native_axiom'] for p in c['parts']})
        rows.append((c['module'],c['representative_export'],axioms))
    all_parts={p['expected_native_axiom'] for c in INV['cells'] for p in c['parts']}
    for i,name in enumerate(INV['stratum_exports']):
        parts={p['expected_native_axiom'] for p in INV['cells'][i]['parts']} if i<3 else all_parts
        extra='TEST_ONLY.reviewed_graph_axiom'
        graph[name]=[extra];rows.append(('Erdos85H5Stratum',name,sorted(STANDARD|parts|{extra})))
    return rows,{'status':'EXACT_GRAPH_AXIOMS_REVIEWED','exports':graph}
def log(rows):
    return '\n'.join(f"info: Proofs/{module}.lean:10:0: '{name}' depends on axioms: [{', '.join(ax)}]" for module,name,ax in rows)
class Checks(unittest.TestCase):
    def test_exact_sets(self):
        rows,review=fixture();r=check_reports(log(rows),INV,review)
        self.assertEqual(r['status'],'AXIOM_SETS_PASS');self.assertEqual(len(r['exports']),7)
    def test_pending_review_never_passes(self):
        rows,_=fixture();self.assertEqual(check_reports(log(rows),INV,{'status':'AWAITING_EXACT_PRINTED_SET_REVIEW'})['status'],'NEEDS_GRAPH_AXIOM_REVIEW')
    def test_missing_part_axiom_rejected(self):
        rows,review=fixture();rows[0][2].remove(INV['cells'][0]['parts'][0]['expected_native_axiom'])
        self.assertEqual(check_reports(log(rows),INV,review)['status'],'REJECTED')
    def test_wrong_cell_part_rejected(self):
        rows,review=fixture();rows[0][2].append(INV['cells'][1]['parts'][0]['expected_native_axiom'])
        self.assertEqual(check_reports(log(rows),INV,review)['status'],'REJECTED')
    def test_extra_graph_axiom_rejected(self):
        rows,review=fixture();rows[-1][2].append('UNREVIEWED.extra')
        self.assertEqual(check_reports(log(rows),INV,review)['status'],'REJECTED')
    def test_missing_graph_axiom_rejected(self):
        rows,review=fixture();rows[-1][2].remove('TEST_ONLY.reviewed_graph_axiom')
        self.assertEqual(check_reports(log(rows),INV,review)['status'],'REJECTED')
    def test_sorry_rejected_even_if_review_claims_it(self):
        rows,review=fixture();rows[-1][2].append('sorryAx');review['exports'][rows[-1][1]].append('sorryAx')
        self.assertEqual(check_reports(log(rows),INV,review)['status'],'REJECTED')
    def test_duplicate_report_rejected(self):
        rows,review=fixture();rows.append(copy.deepcopy(rows[0]))
        self.assertEqual(check_reports(log(rows),INV,review)['status'],'REJECTED')
    def test_duplicate_axiom_rejected(self):
        rows,review=fixture();rows[0][2].append(rows[0][2][0])
        self.assertEqual(check_reports(log(rows),INV,review)['status'],'REJECTED')
    def test_missing_export_rejected(self):
        rows,review=fixture();rows.pop()
        self.assertEqual(check_reports(log(rows),INV,review)['status'],'REJECTED')
    def test_wrong_source_module_rejected(self):
        rows,review=fixture();module,name,ax=rows[0];rows[0]=('WrongModule',name,ax)
        self.assertEqual(check_reports(log(rows),INV,review)['status'],'REJECTED')
    def test_multiline_axiom_report(self):
        rows,review=fixture();raw=log(rows).replace(', ', ',\n ')
        self.assertEqual(check_reports(raw,INV,review)['status'],'AXIOM_SETS_PASS')
if __name__=='__main__':unittest.main()
