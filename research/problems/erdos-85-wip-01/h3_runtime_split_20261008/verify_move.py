"""Verify the runtime move without invoking Lean or any finite search."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[3]


def without_comments(text):
    out = []
    i = 0
    depth = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    assert depth == 0
    return ''.join(''.join(out).split())


def declaration(text, name):
    pattern = (r'^(?:@\[inline\] )?(?:def|abbrev|structure) ' + re.escape(name) +
               r'(?=\s|\().*?(?=\n\n|\n(?:def|abbrev|structure) |\Z)')
    matches = re.findall(pattern, text, re.M | re.S)
    assert len(matches) == 1, name
    return matches[0]


def main():
    manifest = json.loads((ROOT / 'MOVE.json').read_text())
    runtime = (REPO / 'proofs/Proofs/Erdos85H3TripleCompletionRuntime.lean').read_text()
    old = {}
    for path, digest in manifest['old_sources_sha256'].items():
        data = subprocess.check_output(['git', '-C', str(REPO), 'show',
                                        manifest['prior_source_commit'] + ':' + path])
        assert hashlib.sha256(data).hexdigest() == digest, path
        old[path] = data.decode()
    for item in manifest['definitions']:
        chunk = declaration(old[item['source']], item['name'])
        assert hashlib.sha256(chunk.encode()).hexdigest() == item['sha256']
        assert declaration(runtime, item['name']) == chunk, item['name']
        old[item['source']] = old[item['source']].replace(chunk, '', 1)
    for path, remaining in old.items():
        current = (REPO / path).read_text().replace(
            'import Proofs.Erdos85H3TripleCompletionRuntime\n', '', 1)
        assert without_comments(remaining) == without_comments(current), path
    for path, digest in manifest['new_sources_sha256'].items():
        assert hashlib.sha256((REPO / path).read_bytes()).hexdigest() == digest, path
    assert len(manifest['definitions']) == 45
    print('VERBATIM_RUNTIME_MOVE_PASS: 45 declarations; all remaining proof/source tokens unchanged.')


if __name__ == '__main__':
    main()
