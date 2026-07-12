#!/bin/bash
# quickcheck.sh <slug> — dump integrity-relevant facts for a gallery entry
set -uo pipefail
R=/Users/rwalters/GitHub/lean-genius
slug="$1"
cd "$R"
python3 - "$slug" <<'PY'
import json,sys,os
slug=sys.argv[1]
m=json.load(open(f'src/data/proofs/{slug}/meta.json'))
meta=m.get('meta',{})
lf=m.get('leanFile',{})
print('TITLE:',m.get('title'))
print('status:',meta.get('status'),'| badge:',meta.get('badge'),'| erdosStatus:',meta.get('erdosProblemStatus'))
print('meta.sorries:',meta.get('sorries'),'| meta.axiomCount:',meta.get('axiomCount'))
print('lf.path:',lf.get('path'),'| lf.sorries:',lf.get('sorries'),'| lf.axiomCount:',lf.get('axiomCount'),'| lf.thm:',lf.get('theoremCount'),'| lf.lines:',lf.get('lineCount'))
af=meta.get('additionalFiles') or lf.get('additionalFiles')
print('additionalFiles:',json.dumps(af)[:300] if af else None)
print('assumptions:',json.dumps(meta.get('assumptions'))[:300])
p=lf.get('path','')
print('__PATH__'+p)
PY
p=$(python3 -c "import json;print(json.load(open('src/data/proofs/$slug/meta.json'))['leanFile'].get('path',''))")
f="proofs/$p"
echo "=== FILE $f ==="
if [ -f "$f" ]; then
  echo "wc-l: $(wc -l < "$f")"
  echo "axioms($(grep -c '^axiom ' "$f")):"; grep -n '^axiom ' "$f"
  echo "sorry: $(grep -c 'sorry' "$f")"; grep -n 'sorry' "$f" | grep -v '^\s*--' | head
  echo "True stubs: $(grep -c ':= trivial\|: True :=\|: True$\|:= by trivial' "$f")"
  echo "native_decide: $(grep -c 'native_decide' "$f")"
  echo "structures/classes:"; grep -n '^structure \|^class ' "$f"
  echo "theorems/lemmas: $(grep -c '^theorem \|^lemma ' "$f")"
else
  echo "FILE MISSING"
fi
