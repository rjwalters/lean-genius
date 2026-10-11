"""Cloud-only preparation of immutable worker cache inventories; no native search.

Revalidate the previously audited census artifacts, refresh only generic library
targets, copy the complete library, and bind every retained cache file by hash.
Host execution/provenance audit is required before using these inventories.
"""
import argparse
import os
from pathlib import Path
import platform
import sys
import time

sys.dont_write_bytecode = True
import canary
import common
import worker

require, digest, read = worker.require, worker.digest, worker.read
LIBRARY = ['Proofs.Erdos85ThreeHighNativePairSearch',
           'Proofs.Erdos85ThreeBlockCompactCodes',
           'Proofs.Erdos85ThreeHighSecondaryOrbitTable']


def validate_census(manifest):
    full = common.RESEARCH / 'h3_u1r15_census_reduction_20261008/_build/prerequisites'
    deficient = common.RESEARCH / 'h3_deficient_pilot_reduction_20261008/_build/prerequisites/base'
    _, full_audit = canary.previous.census(full / 'base', full / 'final', manifest['base_receipts']['full_final'])
    canary.deficient.validate_base(deficient)
    require(digest(deficient / 'RUN.json') == manifest['base_receipts']['deficient'], 'Wrong deficient receipt')
    return {'full_base': full / 'base', 'full_final': full / 'final', 'deficient_base': deficient}, {
        'full': full_audit, 'deficient_receipt_sha256': digest(deficient / 'RUN.json'),
        'deficient_modules': len(read(deficient / 'RUN.json')['results'])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(platform.system() == 'Linux' and Path('/.dockerenv').exists() and
            Path.cwd().resolve() == Path('/workspace/proofs'), 'Run only inside cloud Docker from proofs')
    manifest = canary.verify_manifest(args.manifest_sha256)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    receipt = {'schema': 'erdos85-h3-cache-preparation-v1', 'status': 'RUNNING',
               'manifest_sha256': args.manifest_sha256, 'source_sha256': digest(Path(__file__)),
               'started_utc': worker.utc(), 'production_native_search': False,
               'scope': 'Cache preparation only. Requires host provenance audit before worker launch.'}
    save = lambda: worker.atomic_json(output / 'RUN.json', receipt)
    save()
    deadline = time.monotonic() + 720
    try:
        roots, census_audit = validate_census(manifest)
        receipt['census_audit'] = census_audit
        env = os.environ.copy()
        env['LEAN_NUM_THREADS'] = '1'
        receipt['dependencies'] = worker.bounded(['lake', 'build', *LIBRARY],
            output / 'dependencies.log', env, deadline)
        save()
        require(receipt['dependencies']['exit_code'] == 0, 'Generic dependency build failed')
        source = Path('.lake/build/lib/lean').resolve()
        before = worker.inventory_files(source)
        require(not any(Path(name).name.startswith('Erdos85ThreeHighCampaign') for name in before),
                'Shared library contains campaign objects')
        receipt['copy'] = worker.bounded(['cp', '-a', '--reflink=auto', str(source), str(output / 'library')],
            output / 'copy.log', env, deadline)
        save()
        require(receipt['copy']['exit_code'] == 0, 'Private library copy failed')
        copied = worker.inventory_files(output / 'library')
        require(copied == before == worker.inventory_files(source), 'Library changed while copying')
        records = {'library': {'path': str(output / 'library'), 'files': copied}}
        for name, root in roots.items():
            records[name] = {'path': str(root), 'files': worker.inventory_files(root)}
        require(canary.verify_manifest(args.manifest_sha256) == manifest, 'Source manifest changed')
        require(validate_census(manifest) == (roots, census_audit), 'Census artifacts changed')
        receipt['inventories'] = {}
        for branch, names in [('full', ('library', 'full_base', 'full_final')),
                              ('deficient', ('library', 'deficient_base'))]:
            inventory = {'schema': 'erdos85-h3-triple-cache-v1',
                         'manifest_sha256': args.manifest_sha256,
                         'base_receipts': manifest['base_receipts'],
                         'roots': {name: records[name] for name in names}}
            path = output / ('CACHE-' + branch + '.json')
            worker.atomic_json(path, inventory)
            case = next(c for c in manifest['cases'] if c['branch'] == branch and c['state'] == 'PENDING')
            worker.cache_roots(inventory, case, manifest)
            receipt['inventories'][branch] = {'sha256': digest(path),
                'files': {name: len(records[name]['files']) for name in names}}
        receipt['status'] = 'CACHE_PREPARED'
        receipt['finished_utc'] = worker.utc()
        save()
        print(__import__('json').dumps(receipt), flush=True)
        return 0
    except BaseException as error:
        receipt['status'] = 'ERROR'
        receipt['error'] = type(error).__name__ + ': ' + str(error)
        receipt['finished_utc'] = worker.utc()
        save()
        raise


if __name__ == '__main__':
    raise SystemExit(main())
