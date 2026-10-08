"""Check the pinned H5 source inventory; never execute Lean or finite search.

Usage: python3 -B prepare_inventory.py /path/to/erdos85-h5
Writes immutable inventory.json beside this script. This is source evidence,
not evidence that a part or the final theorem compiled.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

COMMIT = '99bc3e3413008ca13d5efb29bee5e855af961976'
JOB = '20261008T112746-erdos85__h5-formal-20261008-455708'
CELLS = [(0, 4, 16), (1, 6, 16), (2, 12, 8)]
ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    repo = Path(sys.argv[1]).resolve()
    sources = {}

    def source(module):
        relative = 'proofs/Proofs/' + module + '.lean'
        data = subprocess.check_output(['git', '-C', str(repo), 'show', COMMIT + ':' + relative])
        require(data == (repo / relative).read_bytes(), 'Current source drift: ' + module)
        text = data.decode()
        require(not re.search(r'\b(sorry|unsafe|implemented_by)\b', text), 'Source trust escape: ' + module)
        require(not re.search(r'^\s*(?:private\s+)?axiom\s', text, re.M), 'Explicit axiom: ' + module)
        sources[module] = {'path': relative, 'sha256': hashlib.sha256(data).hexdigest()}
        return text

    cells = []
    for c, k, m in CELLS:
        parts = []
        for r in range(m):
            module = f'Erdos85H5T{c}Part{r:02d}'
            theorem = f'cellPartF_{c}_{k}_{m}_{r:02d}'
            text = source(module)
            # Exact generated proof shape, allowing only its descriptive comment.
            body = re.sub(r'/\-!.*?\-/', '', text, flags=re.S)
            expected = (f'import Proofs.Erdos85H5Fast namespace Erdos85 namespace H5 '
                        f'theorem {theorem} : cellPartF {c} {k} {m} {r} = true := by '
                        'native_decide end H5 end Erdos85')
            require(' '.join(body.split()) == expected, 'Unexpected native part source: ' + module)
            parts.append({'module': module, 'residue': r,
                          'theorem': 'Erdos85.H5.' + theorem,
                          'expected_native_axiom': 'Erdos85.H5.' + theorem + '._native.native_decide.ax_1_1'})
        module = f'Erdos85H5T{c}'
        text = source(module)
        require(re.findall(r'^import (\S+)', text, re.M) ==
                ['Proofs.' + p['module'] for p in parts], 'Incomplete or reordered imports: ' + module)
        cases = re.findall(r'^  \| (\d+), _ => (\S+)\s*$', text, re.M)
        require(cases == [(str(p['residue']), p['theorem'].split('.')[-1]) for p in parts],
                'Part case coverage differs: ' + module)
        require(f'∀ r, r < {m} → cellPartF {c} {k} {m} r = true' in text,
                'Wrong all-parts statement: ' + module)
        require(f'| n + {m}, h => absurd h (by omega)' in text, 'Wrong terminal case: ' + module)
        require(f'fiveHighCanonicalRepresentativeExcluded_of_partsF {c} {k} {m} (by norm_num)\n'
                f'    cellPartF_{c}_{k}_{m}_all' in text, 'Wrong soundness instantiation: ' + module)
        export = f'Erdos85.H5.fiveHighCanonicalRepresentativeExcluded_{c}'
        require(re.findall(r'^#print axioms (\S+)\s*$', text, re.M) == [export],
                'Wrong representative export: ' + module)
        cells.append({'index': c, 'prefix': k, 'modulus': m, 'module': module,
                      'representative_export': export, 'parts': parts})

    text = source('Erdos85H5Stratum')
    require(re.findall(r'^import (\S+)', text, re.M) ==
            ['Proofs.Erdos85H5T0', 'Proofs.Erdos85H5T1', 'Proofs.Erdos85H5T2',
             'Proofs.Erdos85OrderFortyNineFiveHighTwoFiber'], 'Wrong stratum imports')
    exports = ['Erdos85.H5.orderFortyNineTripleCellExcluded_five_' + suffix
               for suffix in ('zero', 'one', 'two')]
    exports.append('Erdos85.H5.orderFortyNineStratumExcluded_five')
    require(re.findall(r'^#print axioms (\S+)\s*$', text, re.M) == exports, 'Wrong stratum exports')
    for c in range(3):
        require(f'(fiveHighCanonicalGraphCover_all {c} (by omega))\n'
                f'    fiveHighCanonicalRepresentativeExcluded_{c}' in text,
                'Wrong graph-cover/representative pair')
        require(f'| {c}, _ => fiveHighCanonicalRepresentativeExcluded_{c}' in text,
                'Missing stratum representative case')
    require('| n + 3, h => absurd h (by omega)' in text, 'Wrong stratum terminal case')

    report = {'status': 'PINNED_SOURCE_INVENTORY_VERIFIED', 'execution_commit': COMMIT,
              'intended_job': JOB, 'native_part_count': sum(c['modulus'] for c in cells),
              'source_module_count': len(sources), 'cells': cells, 'stratum_exports': exports,
              'sources': sources,
              'scope': 'Static source coverage only; no compiled part or stratum credit.',
              'terminal_requirements': [
                  'Successful authoritative exit of the pinned job, with no sorry or errors.',
                  'Fresh build records and stable nonempty objects for all 40 parts and four assemblies.',
                  'Source hashes agree with this execution pin; object modification times lie in the job interval.',
                  'Each representative export has exactly the standard three axioms plus its own part axioms.',
                  'The four graph-side exports require separate review of graph-cover native axioms; do not allow arbitrary extras.',
                  'The stratum export includes all 40 part axioms, with no sorryAx or unreviewed assumptions.',
                  'Retain raw logs, job specification, exit record, source snapshots, object hashes and axiom reports.']}
    require(report['native_part_count'] == 40 and len(sources) == 44, 'Wrong module cardinality')
    data = (json.dumps(report, indent=2) + '\n').encode()
    path = ROOT / 'inventory.json'
    if path.exists():
        require(path.read_bytes() == data, 'Refusing to overwrite a different inventory')
    else:
        path.write_bytes(data)
    print(report['status'] + ': 40 parts, 3 representatives, 1 stratum assembly')


if __name__ == '__main__':
    main()
