import json, subprocess, os, glob
from datetime import datetime, timezone

def to_utc(s):
    if not s: return None
    s = s.strip()
    if s.endswith('Z'): s = s[:-1] + '+00:00'
    try:
        dt = datetime.fromisoformat(s)
    except ValueError:
        return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc)

tracker = json.load(open('src/data/proofs/audit-tracker.json'))
entries = tracker.get('entries', {})

# git commit date for a path (latest commit touching it)
def git_date(path):
    try:
        out = subprocess.check_output(['git','log','-1','--format=%cI','--',path], text=True).strip()
        return to_utc(out) if out else None
    except subprocess.CalledProcessError:
        return None

candidates = []
for meta_path in glob.glob('src/data/proofs/*/meta.json'):
    slug = os.path.basename(os.path.dirname(meta_path))
    ent = entries.get(slug)
    last = to_utc(ent.get('lastAudited')) if ent else None
    # gather lean files from meta
    try:
        m = json.load(open(meta_path))
    except Exception:
        continue
    paths = [meta_path]
    def collect(obj):
        res=[]
        if isinstance(obj,dict):
            p = obj.get('path')
            if isinstance(p,str) and p.endswith('.lean'): res.append(p)
            for v in obj.values(): res+=collect(v)
        elif isinstance(obj,list):
            for v in obj: res+=collect(v)
        return res
    lean_paths = collect(m)
    # also proofRepoPath
    for lp in lean_paths:
        full = lp if os.path.exists(lp) else os.path.join('proofs', lp) if os.path.exists(os.path.join('proofs',lp)) else lp
        paths.append(full)
    newest = None
    for p in paths:
        d = git_date(p)
        if d and (newest is None or d>newest): newest=d
    if newest is None: continue
    if last is None or newest > last:
        candidates.append((slug, newest.isoformat(), last.isoformat() if last else 'never'))

candidates.sort(key=lambda x:x[1], reverse=True)
print(f"CANDIDATES: {len(candidates)}")
for c in candidates[:40]:
    print(c)
