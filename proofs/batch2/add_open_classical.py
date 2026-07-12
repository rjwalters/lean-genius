#!/usr/bin/env python3
"""Insert `open scoped Classical` after the import block of each listed module.

usage: add_open_classical.py <modules.txt>
Idempotent: skips files that already contain `open scoped Classical` or
`open Classical`.
"""
import sys, os

os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))

def apply(mod: str) -> str:
    path = f'Proofs/{mod}.lean'
    if not os.path.exists(path):
        return 'MISSING'
    src = open(path, encoding='utf-8', errors='replace').read()
    if 'open scoped Classical' in src or 'open Classical' in src:
        return 'ALREADY'
    lines = src.splitlines(keepends=True)
    last_import = -1
    for i, line in enumerate(lines):
        if line.startswith('import '):
            last_import = i
    if last_import < 0:
        return 'NO-IMPORT'
    lines.insert(last_import + 1, '\nopen scoped Classical\n')
    open(path, 'w', encoding='utf-8').write(''.join(lines))
    return 'EDITED'

if __name__ == '__main__':
    for m in open(sys.argv[1]).read().split():
        print(apply(m), m)
