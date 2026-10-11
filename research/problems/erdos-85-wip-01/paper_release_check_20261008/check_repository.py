"""Read-only release-branch content check; no Lean, LaTeX, or solver run."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

R = 'research/problems/erdos-85-wip-01'
DISCLOSURE = 'b0b815e175cbf8b8e46e09028de79c291d98deb3'


def git(*args):
    return subprocess.check_output(['git', *args])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ref', required=True, help='Immutable commit to inspect')
    a = parser.parse_args()
    commit = git('rev-parse', a.ref + '^{commit}').decode().strip()
    advertised = git('ls-remote', 'origin', 'refs/heads/erdos85/integration',
                     'refs/heads/erdos85/paper-v6').decode()
    remote = {line.split()[1]: line.split()[0] for line in advertised.splitlines()}
    assert len(remote) == 2 and set(remote.values()) == {commit}, remote
    subprocess.run(['git', 'merge-base', '--is-ancestor', DISCLOSURE, commit], check=True)
    artifacts = {}
    for name in ['main.tex', 'main.pdf', 'refs.bib', 'anvil-paper.cls']:
        record = R + '/manuscript/paper/' + name
        version = R + '/manuscript/anvil/erdos85-drop.9/' + name
        content = git('show', commit + ':' + record)
        assert content == git('show', commit + ':' + version), name
        if name in {'main.tex', 'main.pdf'}:
            assert content == git('show', DISCLOSURE + ':' + record), name
        artifacts[name] = {'record_path': record, 'version_path': version,
                           'sha256': hashlib.sha256(content).hexdigest(), 'bytes': len(content)}
    tex = git('show', commit + ':' + artifacts['main.tex']['record_path']).decode()
    assert 'none was performed by a human mathematician' in tex and 'AI authors' in tex
    assert 'these arguments have not been refereed' in tex
    rp = re.search(r'\\newcommand\{\\rp\}\{([^}]+)\}', tex).group(1)
    uses = re.findall(r'\\repofile(?:tab)?\{([^}]+)\}', tex)
    paths = sorted({path.replace('\\rp', rp) for path in uses})
    links = []
    for path in paths:
        assert '\\' not in path and '#' not in path, path
        obj = commit + ':' + path.rstrip('/')
        kind = git('cat-file', '-t', obj).decode().strip()
        assert kind in {'blob', 'tree'}, path
        links.append({'path': path, 'type': kind, 'git_object': git('rev-parse', obj).decode().strip()})
    receipt_path = R + '/STRATA_AND_SMALL_ORDERS_20260928.md'
    receipt = git('show', commit + ':' + receipt_path).decode()
    assert '**no SAT verdict or LRAT proof exists for either cell formula**' in receipt
    assert 'superseded 2026-10-07' in receipt
    assert 'orderFortyNineStratumExcluded_one_of_capacityInventory_checked' in receipt
    with tempfile.TemporaryDirectory() as tmp:
        pdf = Path(tmp) / 'main.pdf'
        pdf.write_bytes(git('show', commit + ':' + artifacts['main.pdf']['record_path']))
        text = subprocess.check_output(['pdftotext', str(pdf), '-']).decode()
    assert 'none was performed by a human mathematician' in ' '.join(text.split())
    assert 'these arguments have not been refereed' in ' '.join(text.split())
    assert not any(marker in text for marker in ['??', '[?]', '(?)'])
    print(json.dumps({'status': 'PASS', 'commit': commit, 'remote_refs': remote,
        'disclosure_commit': DISCLOSURE, 'disclosure_is_ancestor': True, 'artifacts': artifacts,
        'link_uses': len(uses), 'distinct_targets': len(paths), 'targets': links,
        'corrected_strata_receipt_sha256': hashlib.sha256(receipt.encode()).hexdigest(),
        'pdf_disclosure_present': True, 'pdf_unresolved_reference_markers': 0,
        'scope': 'Repository content, linked target existence and shipped PDF text only; not a fresh compile, mathematical verification, human approval, or publication.'}, indent=2))


if __name__ == '__main__':
    main()
