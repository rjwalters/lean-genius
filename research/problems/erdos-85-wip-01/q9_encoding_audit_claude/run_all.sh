#!/bin/zsh
cd /private/tmp/claude-501/-Users-rwalters-GitHub-lean-genius/9d4660cc-e007-48ed-8318-5b8f8816b95f/scratchpad/rev_q9
/opt/homebrew/bin/python3 - <<'PY' > instances.txt
import json
d=json.load(open('/Users/rwalters/lean-genius-q9-known-values-20260911/q9-launch-input-preflight/results.json'))
for i in d['instances']:
    if (i['n'],i['m']) in ((80,10),(80,8)): continue
    print(i['path'].replace('/tmp/','/private/tmp/',1) if i['path'].startswith('/tmp/') else i['path'], i['cnf_sha256'], i['n'], i['m'])
print('/private/tmp/erdos85-sol1-q9-control63-m7-proposed', 'none', 63, 7)
PY
while read path sha n m; do
  samples=200; [ "$m" = "1" ] && samples=100
  out=audit_n${n}_m${m}.log
  if [ "$sha" = "none" ]; then /opt/homebrew/bin/python3 encoding_audit.py "$path" --samples $samples > $out 2>&1; else /opt/homebrew/bin/python3 encoding_audit.py "$path" --ledger-sha $sha --samples $samples > $out 2>&1; fi
  /opt/homebrew/bin/python3 -c "
import json; t=open('$out').read(); i=t.find('{'); pre=t[:i].strip(); r=json.loads(t[i:]) if i>=0 else {}
keys=['n','m','sha_matches_map','sha_matches_ledger','orbit_count','orbits_match_rederivation','nvars','nclauses','every_nonprimary_has_gate','gates_topologically_ordered','degree_output_clauses','degree_outputs_equal_block_count','c4_clauses','tests','mismatches','seconds']
print('SUMMARY', {k:r.get(k) for k in keys}, 'stderr:', pre[:300])
pos={k:(v['degree_ok'],v['c4_ok']) for k,v in r.get('by_tag',{}).items()}; print('  positives(degree_ok,c4_ok) by tag:', pos)
"
done < instances.txt
