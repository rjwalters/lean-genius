#!/usr/bin/env python3
"""Generate tier-1 certification jobs for every solver-decided v2 proof in the
durable archive (remote-sweeps/), deduplicated against work already done.

Deterministic mapping: the 13,541-row compact inventory (h1-orbit-inventory.jsonl)
is authoritative for tag -> (profile, table). Archive artifacts are evidence:
  proof   = <tag>.v2.drat or <tag>.v2.drat.gz anywhere under remote-sweeps/
  cnf     = <tag>.v2.cnf in the SAME directory as the chosen proof
  mode    = mode:<M> from a <tag>.v2.verdict if one exists, else ARCHIVE
Per-tag artifact choice is deterministic: prefer a proof with a same-dir cnf
(MATCH path is cheaper than Lean-exact emit), then prefer .gz (less volume
I/O), then lexicographically smallest path.

Default is a DRY-RUN census (no writes). --emit writes jobs-archive.tsv and
any missing tables/<tag>.table files (json.dumps of the inventory table --
same format as the existing 472).  Never compresses or rewrites proofs.
"""
import hashlib, json, os, re, sys
from collections import defaultdict

def fingerprint(path):
    """Cheap dup detector: size + sha256(head 64K + tail 64K). Avoids full-file
    reads (hundreds of GB across the archive is the bulk-read pattern that
    ground the host); byte-identical same-tag copies share this fingerprint."""
    size = os.path.getsize(path)
    h = hashlib.sha256()
    with open(path, "rb") as f:
        h.update(f.read(65536))
        if size > 131072:
            f.seek(-65536, 2)
            h.update(f.read(65536))
    return (size, h.hexdigest()[:16])

BASE = "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49"
WORK = BASE + "/v2-tier1-work"
SWEEPS = BASE + "/remote-sweeps"
INV = BASE + "/h1-orbit-inventory.jsonl"
PROFILE_NAMES = ("BBBB", "ABBB", "AABB", "AAAB", "AAAA")
PROFILE_INDEX = {name: i for i, name in enumerate(PROFILE_NAMES)}
TAG_RE = re.compile(r"^([0-9a-f]{16})\.v2\.(drat\.gz|drat|cnf|verdict)$")

def load_inventory():
    inv = {}
    with open(INV) as f:
        for line in f:
            e = json.loads(line)
            inv[e["orbit"]] = (e["profile"], e["table"])
    return inv

def scan_archive():
    # Deterministic: walk order sorted, and mode comes from the
    # lexicographically smallest UNSAT verdict path per tag (codex, 3516).
    proofs, cnfs = defaultdict(list), defaultdict(set)
    mode_src = {}  # tag -> (verdict_path, mode)
    for root, dirs, files in os.walk(SWEEPS):
        dirs.sort()
        for name in sorted(files):
            m = TAG_RE.match(name)
            if not m:
                continue
            tag, kind = m.groups()
            path = os.path.join(root, name)
            if kind in ("drat", "drat.gz"):
                proofs[tag].append(path)
            elif kind == "cnf":
                cnfs[tag].add(root)
            elif kind == "verdict":
                try:
                    head = open(path).read(4096)
                    mm = re.search(r"mode:(\S+)", head)
                    if mm and re.search(r"\bUNSAT\b", head):
                        if tag not in mode_src or path < mode_src[tag][0]:
                            mode_src[tag] = (path, mm.group(1))
                except OSError:
                    pass
    modes = {tag: mode for tag, (_p, mode) in mode_src.items()}
    return proofs, cnfs, modes

def choose(tag, cands, cnf_dirs):
    def key(p):
        d = os.path.dirname(p)
        return (0 if d in cnf_dirs else 1, 0 if p.endswith(".gz") else 1, p)
    return sorted(cands, key=key)[0]

def already_covered():
    accepted, shard = set(), set()
    res = WORK + "/results.tsv"
    if os.path.exists(res):
        for line in open(res):
            f = line.split("\t")
            if len(f) >= 2 and f[1].strip() == "LEAN_ACCEPTED":
                accepted.add(f[0])
    for line in open(WORK + "/jobs.tsv"):
        shard.add(line.split("\t", 1)[0])
    return accepted, shard

def main():
    emit = "--emit" in sys.argv
    inv = load_inventory()
    proofs, cnfs, modes = scan_archive()
    accepted, shard = already_covered()

    jobs, census = [], defaultdict(int)
    per_profile = defaultdict(int)
    unknown, verdict_no_proof = [], []

    for tag in sorted(set(modes) - set(proofs)):
        verdict_no_proof.append(tag)
    for tag in sorted(proofs):
        if tag not in inv:
            unknown.append(tag)
            census["unknown_tag"] += 1
            continue
        if tag in accepted:
            census["already_accepted"] += 1
            continue
        if tag in shard:
            census["in_current_shard"] += 1
            continue
        family, table = inv[tag]
        dpath = choose(tag, proofs[tag], cnfs.get(tag, set()))
        cdir = os.path.dirname(dpath)
        cpath = os.path.join(cdir, tag + ".v2.cnf") if cdir in cnfs.get(tag, set()) else ""
        mode = modes.get(tag, "ARCHIVE")
        tpath = WORK + "/tables/" + tag + ".table"
        jobs.append((tag, str(PROFILE_INDEX[family]), family, mode, tpath, cpath, dpath))
        per_profile[family] += 1
        census["new_job"] += 1
        census["cnf_present" if cpath else "cnf_absent_lean_exact"] += 1
        census["gz" if dpath.endswith(".gz") else "plain_drat"] += 1

    # --- size + duplicate accounting (chosen artifacts and extra copies) ---
    bytes_by_profile = defaultdict(int)
    all_copy_bytes = 0
    dup_tags = dup_identical = 0
    for tag, _pi, family, _m, _t, _c, dpath in jobs:
        bytes_by_profile[family] += os.path.getsize(dpath)
    for tag, cands in proofs.items():
        for p in cands:
            all_copy_bytes += os.path.getsize(p)
        if len(cands) > 1:
            dup_tags += 1
            if len({fingerprint(p) for p in cands}) < len(cands):
                dup_identical += 1

    # --- banked-LRAT stats from completed reps (replay-cost extrapolation) ---
    lrat_dir = BASE + "/v2-lrat"
    lrat_sizes = [os.path.getsize(os.path.join(lrat_dir, n))
                  for n in os.listdir(lrat_dir)] if os.path.isdir(lrat_dir) else []
    lrat_sizes = [s for s in lrat_sizes if s > 1024]  # skip manifests
    actions = []
    if os.path.isdir(lrat_dir):
        for n in os.listdir(lrat_dir):
            if n.endswith(".manifest.txt"):
                mtext = open(os.path.join(lrat_dir, n)).read()
                am = re.search(r"lrat_actions (\d+)", mtext)
                if am:
                    actions.append(int(am.group(1)))

    # --- inventory coverage: proof present / verdict only / no artifact ---
    inv_proof = sum(1 for t in inv if t in proofs)
    inv_verdict_only = sum(1 for t in inv if t not in proofs and t in modes)
    inv_none = len(inv) - inv_proof - inv_verdict_only

    print(f"archive tags with v2 proofs: {len(proofs)}  "
          f"verdict-only (no proof): {len(verdict_no_proof)}")
    print(f"inventory coverage: proof_present={inv_proof}  "
          f"verdict_only={inv_verdict_only}  no_artifact={inv_none}  "
          f"(total {len(inv)})")
    for k in sorted(census):
        print(f"  {k} = {census[k]}")
    for fam in PROFILE_NAMES:
        gb = bytes_by_profile[fam] / 1e9
        print(f"  new jobs {fam} = {per_profile[fam]}  proof_bytes = {gb:.1f} GB")
    print(f"  chosen-proof bytes total = {sum(bytes_by_profile.values())/1e9:.1f} GB; "
          f"all copies on volume = {all_copy_bytes/1e9:.1f} GB")
    print(f"  tags with multiple proof copies = {dup_tags} "
          f"(byte-identical by size+head/tail-64K fingerprint: {dup_identical})")
    if lrat_sizes:
        mean_lrat = sum(lrat_sizes) / len(lrat_sizes)
        proj = mean_lrat * census["new_job"] / 1e9
        print(f"  banked LRATs: n={len(lrat_sizes)}  mean={mean_lrat/1e6:.0f} MB  "
              f"total={sum(lrat_sizes)/1e9:.1f} GB; naive projection for "
              f"{census['new_job']} new jobs = {proj:.0f} GB (BBBB-sample-based)")
    if actions:
        print(f"  banked LRAT actions: n={len(actions)}  "
              f"mean={sum(actions)//len(actions):,}  max={max(actions):,}")
    if unknown:
        print("  UNKNOWN tags (excluded):", ", ".join(unknown[:10]),
              "..." if len(unknown) > 10 else "")
    if not emit:
        print("DRY RUN — no files written. Re-run with --emit to write "
              "jobs-archive.tsv and missing tables.")
        return
    wrote_tables = 0
    for tag, *_rest in jobs:
        tp = WORK + "/tables/" + tag + ".table"
        if not os.path.exists(tp):
            with open(tp, "w") as f:
                f.write(json.dumps(inv[tag][1]) + "\n")
            wrote_tables += 1
    out = WORK + "/jobs-archive.tsv"
    with open(out, "w") as f:
        for row in jobs:
            f.write("\t".join(row) + "\n")
    print(f"wrote {out} ({len(jobs)} rows), {wrote_tables} new table files")

if __name__ == "__main__":
    main()
