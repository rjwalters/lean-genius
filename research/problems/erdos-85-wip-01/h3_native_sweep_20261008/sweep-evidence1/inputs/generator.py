"""Freeze the 384-part source inventory and review bundle; runs no Lean search."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[3]
MATH_COMMIT = 'a64f02c30eafde63acece8f251fd98666b757ea7'
MODULUS = 384
SAMPLE = [0, 3, 5, 4, 162]
PREFIX = 'Erdos85H3TripleCompletionPart'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def part_source(r):
    if not isinstance(r, int) or not 0 <= r < MODULUS:
        raise ValueError('Part index must be in 0..383')
    return f'''import Proofs.Erdos85H3TripleCompletionSplit

/- Part {r} of the 384-way completion search. Requires native evaluation. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos85.H3TripleCompletion

theorem triplePart_384_{r:03d} : triplePart 384 {r} = true := by
  native_decide

end Erdos85.H3TripleCompletion

#print axioms Erdos85.H3TripleCompletion.triplePart_384_{r:03d}
'''


def cell_source():
    imports = '\n'.join(f'import Proofs.{PREFIX}{r:03d}' for r in range(MODULUS))
    cases = '\n'.join(f'  | {r}, _ => triplePart_384_{r:03d}' for r in range(MODULUS))
    return imports + f'''

/- Planned composition; uncompiled until all 384 native premises are available. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos85.H3TripleCompletion

theorem tripleParts_384_all : ∀ r, r < 384 → triplePart 384 r = true
{cases}
  | n + 384, h => absurd h (by omega)

theorem threeHighCanonicalRepresentativeExcluded_one :
    ThreeHighCanonicalRepresentativeExcluded 1 :=
  threeHighCanonicalRepresentativeExcluded_one_of_parts 384 (by omega) tripleParts_384_all

theorem orderFortyNineTripleCellExcluded_three_one :
    OrderFortyNineTripleCellExcluded 3 1 :=
  orderFortyNineTripleCellExcluded_three_one_of_parts 384 (by omega) tripleParts_384_all

end Erdos85.H3TripleCompletion

#print axioms Erdos85.H3TripleCompletion.threeHighCanonicalRepresentativeExcluded_one
#print axioms Erdos85.H3TripleCompletion.orderFortyNineTripleCellExcluded_three_one
'''


def write_immutable(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        if path.read_bytes() != data:
            raise ValueError('Refusing to overwrite different bytes: ' + str(path))
    else:
        path.write_bytes(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--emit-part', type=int)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.emit_part is not None:
        if args.output is None:
            parser.error('--emit-part requires --output')
        write_immutable(args.output, part_source(args.emit_part).encode())
        return
    if args.output is not None:
        parser.error('--output requires --emit-part')

    prior = ROOT.parent / 'h3_phase3_runtime_20261008'
    build_path = prior / 'build-evidence/AUDIT.json'
    build = json.loads(build_path.read_text())
    assert build['status'] == 'RUNTIME_HELPERS_CHAIN_BUILD_AUDIT_PASS'
    assert build['execution_commit'] == MATH_COMMIT
    for item in build['results']:
        relative = 'proofs/Proofs/' + item['module'] + '.lean'
        source = subprocess.check_output(['git', '-C', str(REPO), 'show', MATH_COMMIT + ':' + relative])
        assert source == (REPO / relative).read_bytes()
        assert sha(source) == item['source_sha256']

    canary_path = prior / 'canary-evidence/AUDIT.json'
    canary = json.loads(canary_path.read_text())
    run_path = prior / 'canary-evidence/RUN.json'
    run = json.loads(run_path.read_text())
    assert canary['status'] == 'COMPILED' and canary['authoritative_exit'] == 0
    assert sha(run_path.read_bytes()) == canary['retained_sha256']['RUN.json']

    profile_dir = ROOT.parent / 'h3_triple_completion_20261008/profile-fixed-evidence'
    profile_path = profile_dir / 'AUDIT.json'
    profile = json.loads(profile_path.read_text())
    assert sha((profile_dir / 'probe.log').read_bytes()) == profile['retained_sha256']['probe.log']
    buckets = profile['profile']['buckets']
    assert len(buckets) == MODULUS and sum(buckets) == 1088
    assert [buckets[r] for r in SAMPLE] == [4, 0, 1, 3, 11]

    parts = []
    for r in range(MODULUS):
        module = PREFIX + f'{r:03d}'
        theorem = f'Erdos85.H3TripleCompletion.triplePart_384_{r:03d}'
        source = part_source(r).encode()
        parts.append({'residue': r, 'module': 'Proofs.' + module,
                      'source_path': 'Proofs/' + module + '.lean', 'source_sha256': sha(source),
                      'theorem': theorem, 'native_axiom': theorem + '._native.native_decide.ax_1_1',
                      'historical_phase_one_leaves': buckets[r],
                      'production_object_status': 'NOT_BUILT',
                      'prior_diagnostic_status': 'VERIFIED' if r == 0 else 'UNVERIFIED'})
    cell = cell_source().encode()
    imports = re.findall(r'^import (\S+)$', cell.decode(), re.M)
    cases = re.findall(r'^  \| (\d+), _ => triplePart_384_(\d+)$', cell.decode(), re.M)
    assert imports == [p['module'] for p in parts]
    assert [(int(a), int(b)) for a, b in cases] == [(r, r) for r in range(MODULUS)]
    assert len({p['module'] for p in parts}) == len({p['theorem'] for p in parts}) == MODULUS
    report = {
        'status': 'PREPARED_NOT_LAUNCHED', 'modulus': MODULUS, 'math_commit': MATH_COMMIT,
        'source_generator_sha256': sha(Path(__file__).read_bytes()),
        'prerequisite_audit': {'path': str(build_path.relative_to(REPO)), 'sha256': sha(build_path.read_bytes())},
        'verified_diagnostic': {'residue': 0, 'audit_path': str(canary_path.relative_to(REPO)),
                                'audit_sha256': sha(canary_path.read_bytes()),
                                'object': run['artifacts']['Probe384R0.olean'],
                                'lean_elapsed_seconds': run['steps'][1]['elapsed_seconds'],
                                'production_module_reuse': False},
        'historical_profile': {'path': str(profile_path.relative_to(REPO)),
                               'sha256': sha(profile_path.read_bytes()),
                               'scope': 'Historical instrumentation for sample selection only; not exclusion credit or runtime prediction.'},
        'sizing_sample': {'residues_in_order': SAMPLE, 'new_residues': [3, 5, 4, 162],
                          'selection': 'Existing baseline plus historical zero, one, median and maximum phase-one leaf counts; deliberately non-random.',
                          'per_part_seconds': 90, 'library_compile_seconds': 60,
                          'outer_minutes': 10, 'cpus': 2, 'memory_gib': 16,
                          'workers': 1, 'automatic_retry': False, 'execution_status': 'NOT_LAUNCHED'},
        'cell': {'module': 'Proofs.Erdos85H3TripleCompletionCell',
                 'source_sha256': sha(cell), 'compile_status': 'NOT_BUILT'},
        'scope': 'New 384-part completion decomposition only. Does not alter the older 1811-obligation census ledger.',
        'parts': parts}
    write_immutable(ROOT / 'MANIFEST.json', (json.dumps(report, indent=2) + '\n').encode())
    for r in SAMPLE:
        write_immutable(ROOT / 'source-review/Proofs' / (PREFIX + f'{r:03d}.lean'), part_source(r).encode())
    write_immutable(ROOT / 'source-review/Proofs/Erdos85H3TripleCompletionCell.lean', cell)
    print('SOURCE_INVENTORY_PASS: 384 unique parts, exhaustive planned composition, five staged sample sources.')
    print('Computational status: one diagnostic bucket verified; zero production part modules built here.')


if __name__ == '__main__':
    main()
