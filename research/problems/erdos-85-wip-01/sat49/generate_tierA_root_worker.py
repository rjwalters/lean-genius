#!/usr/bin/env python3
"""Derive a receipt-gated Tier-A worker for the approved 406-job root cover.

The output is an inert worker artifact.  This generator neither materializes a
CNF nor starts a solver.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import tempfile
from pathlib import Path


SOURCE_WORKER_SHA256 = "f3969c22b9e9551685412ddc4af0e626e4732a2e40322d2b0135ed23de9db6d8"
OLD_GENERATOR_PATH = 'C / "generate_small_high_cube_jobs.py"'
OLD_GENERATOR_SHA256 = "e4b7cc03ae1f7915c27dcb5c6ca9932a00e08f6527b84aeac4a8cb06c9c891dd"
OLD_MANIFEST_PATH = 'C / "cube_jobs_manifest.json"'
OLD_MANIFEST_SHA256 = "86edc38a9f0aeee0c3d19bb863685b1f9784acae3f24f988e6ea67a6e2e3e8f4"
OLD_WORK_ROOT = '    work = C / "tierA" / job\n'
OLD_KIND_LINE = '    kind = "third" if ".third." in job else "nested" if ".nested." in job else "root"\n'
ROOT_ONLY_KIND_BLOCK = OLD_KIND_LINE + '''    if kind != "root":
        print("root-only worker rejects nested/third job", file=sys.stderr)
        return 64
'''
OLD_PREFLIGHT_BLOCK = '''    if os.environ.get("TIERA_PREFLIGHT_ONLY") == "1":
        print(f"PREFLIGHT VERIFIED job={job} mode={mode} kind={kind} manifest_sha256={cfg['manifest_sha']}")
        return 0
'''
SCHEMA = "erdos85-tierA-root-worker-receipt-v1"
APPROVED_ROOT_GENERATOR_SHA256 = "a845cb9f6bf1d6046c58aefe9cd6cdd66e80e0fd3670629ba650e9578fe5cb7e"
APPROVED_ROOT_MANIFEST_SHA256 = "05381a1cf5e80eb480b6e78c4a8dada2573c1cf2f0c55d9ac0bcc4367e3bca76"
APPROVED_FREIGHT_RECEIPT_SHA256 = "6084315bc86ad262533a660aad308639d1d087666b965df47569627c6adf2897"
APPROVED_QUEUE_RECEIPT_SHA256 = "fa07876764990816f4d7a5940b09958c33d86676edcc3cddcbabad32b482d103"
APPROVED_QUEUE_SHA256 = "91cd2b14a3d0f5a3b9d30d94a4765928a885da74f428a754aadcda5c9ada504b"
LINEAGE_SCHEMA = "erdos85-tierA-root-lineage-v1"
CONTROLLER_SOURCE = "research/problems/erdos-85-wip-01/sat49/run_tierA_root_queue.py"
SHA_RE = re.compile(r"[0-9a-f]{64}")

OLD_HEADER_BLOCK = '''    emitted_sha = sha(emitted)
    maxvar = 29632 if job.startswith("h5_") else 29500
    solved = work / "job.cnf"
    sed = subprocess.run(["/usr/bin/sed", f"1,3s/^p cnf [0-9][0-9]* /p cnf {maxvar} /", str(emitted)], stdout=subprocess.PIPE)
    if sed.returncode != 0 or not sed.stdout.startswith(b"p cnf "):
        return fail(work, job, "header-rewrite")
    solved.write_bytes(sed.stdout)
    unlink(emitted)
    solved_sha, cnf_bytes = sha(solved), solved.stat().st_size
    header = solved.open().readline().split()
    if len(header) != 4 or header[:2] != ["p", "cnf"] or int(header[2]) != maxvar:
        return fail(work, job, "header-validation")
    clauses = int(header[3])
'''

NEW_HEADER_BLOCK = '''    emitted_sha = sha(emitted)
    manifest_data = json.loads(Path(cfg["manifest"]).read_text())
    root_cell = job.split(".", 1)[0]
    root_record = manifest_data.get("cells", {}).get(root_cell)
    if not isinstance(root_record, dict) or not isinstance(root_record.get("variables"), int):
        return fail(work, job, "manifest-cell-metadata")
    maxvar = root_record["variables"]
    solved = work / "job.cnf"
    publish(emitted, solved)
    solved_sha, cnf_bytes = sha(solved), solved.stat().st_size
    with solved.open() as stream:
        header = stream.readline().split()
    if len(header) != 4 or header[:2] != ["p", "cnf"] or int(header[2]) != maxvar:
        return fail(work, job, "header-validation")
    clauses = int(header[3])
'''


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_json(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    if text.count(old) != 1:
        raise ValueError(f"source worker drift: expected exactly one {label}")
    return text.replace(old, new, 1)


def derive_worker(source: bytes, generator: Path, generator_sha: str,
                  manifest: Path, manifest_sha: str, work_root: Path) -> bytes:
    if sha256_bytes(source) != SOURCE_WORKER_SHA256:
        raise ValueError("source worker SHA-256 does not match audited worker")
    text = source.decode()
    text = replace_once(
        text, f'"generator": {OLD_GENERATOR_PATH}',
        f'"generator": Path({json.dumps(str(generator))})', "root generator path")
    text = replace_once(
        text, f'"generator_sha": "{OLD_GENERATOR_SHA256}"',
        f'"generator_sha": "{generator_sha}"', "root generator SHA")
    text = replace_once(
        text, f'"manifest": {OLD_MANIFEST_PATH}',
        f'"manifest": Path({json.dumps(str(manifest))})', "root manifest path")
    text = replace_once(
        text, f'"manifest_sha": "{OLD_MANIFEST_SHA256}"',
        f'"manifest_sha": "{manifest_sha}"', "root manifest SHA")
    text = replace_once(text, OLD_HEADER_BLOCK, NEW_HEADER_BLOCK, "header rewrite block")
    text = replace_once(text, OLD_KIND_LINE, ROOT_ONLY_KIND_BLOCK, "root-only kind guard")
    preflight_block = f'''    if os.environ.get("TIERA_PREFLIGHT_ONLY") == "1":
        if os.path.lexists(Path({json.dumps(str(work_root))})):
            print("root campaign work namespace is not fresh", file=sys.stderr)
            return 66
        print(f"PREFLIGHT VERIFIED job={{job}} mode={{mode}} kind={{kind}} manifest_sha256={{cfg['manifest_sha']}}")
        return 0
'''
    text = replace_once(text, OLD_PREFLIGHT_BLOCK, preflight_block, "fresh-root preflight")
    lineage_block = f'''    lineage_keys = {{
        "schema", "work_root", "worker_sha256", "worker_receipt_sha256",
        "queue_receipt_sha256", "queue_sha256", "root_manifest_sha256",
        "freight_receipt_sha256", "controller_git_commit", "controller_source",
        "controller_sha256",
    }}
    lineage_path = Path({json.dumps(str(work_root))}) / "lineage.json"
    try:
        lineage_bytes = lineage_path.read_bytes()
        lineage = json.loads(lineage_bytes)
        lineage_matches = (
            isinstance(lineage, dict) and set(lineage) == lineage_keys and
            lineage_bytes == (json.dumps(lineage, sort_keys=True, separators=(",", ":")) + "\\n").encode() and
            lineage["schema"] == "{LINEAGE_SCHEMA}" and
            lineage["work_root"] == {json.dumps(str(work_root))} and
            lineage["worker_sha256"] == sha(Path(__file__)) and
            lineage["queue_receipt_sha256"] == "{APPROVED_QUEUE_RECEIPT_SHA256}" and
            lineage["queue_sha256"] == "{APPROVED_QUEUE_SHA256}" and
            lineage["root_manifest_sha256"] == "{APPROVED_ROOT_MANIFEST_SHA256}" and
            lineage["freight_receipt_sha256"] == "{APPROVED_FREIGHT_RECEIPT_SHA256}" and
            re.fullmatch(r"[0-9a-f]{{64}}", lineage["worker_receipt_sha256"]) is not None and
            re.fullmatch(r"[0-9a-f]{{40}}", lineage["controller_git_commit"]) is not None and
            re.fullmatch(r"[0-9a-f]{{64}}", lineage["controller_sha256"]) is not None and
            lineage["controller_source"] == "{CONTROLLER_SOURCE}"
        )
    except (OSError, ValueError, TypeError, KeyError):
        lineage_matches = False
    if not lineage_matches:
        print("root campaign lineage marker missing or invalid", file=sys.stderr)
        return 66
    work = Path({json.dumps(str(work_root))}) / job
'''
    text = replace_once(text, OLD_WORK_ROOT, lineage_block, "root work namespace")
    if "/usr/bin/sed" in text or '"header-rewrite"' in text:
        raise ValueError("derived root worker retains forbidden header rewrite")
    banner = (
        "# GENERATED exact-406 root worker; "
        f"audited-source-sha256={SOURCE_WORKER_SHA256}\n"
    )
    lines = text.splitlines(keepends=True)
    return (lines[0] + banner + "".join(lines[1:])).encode()


def validate_manifest(path: Path, expected_sha: str,
                      expected_freight_sha: str) -> None:
    if sha256_file(path) != expected_sha:
        raise ValueError("root manifest SHA-256 mismatch")
    manifest = json.loads(path.read_text())
    if manifest.get("schema") != "erdos85-small-high-cube-jobs-v1":
        raise ValueError("root manifest has wrong schema")
    if manifest.get("freight_receipt_sha256") != expected_freight_sha:
        raise ValueError("root manifest has wrong freight receipt pin")
    cells = manifest.get("cells")
    if not isinstance(cells, dict) or len(cells) != 7:
        raise ValueError("root manifest does not have seven cells")
    jobs = [job.get("id") for cell in cells.values() for job in cell.get("jobs", [])]
    if len(jobs) != 406 or len(set(jobs)) != 406 or any(not isinstance(job, str) for job in jobs):
        raise ValueError("root manifest does not contain 406 unique jobs")
    if manifest.get("positive_cube_jobs") != 392 or manifest.get("negative_cover_jobs") != 14:
        raise ValueError("root manifest job-kind totals are wrong")


def validate_approved_pins(generator_sha: str, manifest_sha: str, freight_sha: str) -> None:
    approved = (
        (generator_sha, APPROVED_ROOT_GENERATOR_SHA256, "root generator"),
        (manifest_sha, APPROVED_ROOT_MANIFEST_SHA256, "root manifest"),
        (freight_sha, APPROVED_FREIGHT_RECEIPT_SHA256, "freight receipt"),
    )
    for actual, expected, label in approved:
        if actual != expected:
            raise ValueError(f"{label} is not the approved SHA-256 pin")


def require_absent_work_root(path: Path) -> None:
    if os.path.lexists(path):
        raise ValueError(f"root work namespace already exists: {path}")


def create_only_write(path: Path, data: bytes, mode: int) -> tuple[int, int]:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, raw_temporary = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    temporary = Path(raw_temporary)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.chmod(mode)
        try:
            os.link(temporary, path)
        except FileExistsError as error:
            raise ValueError(f"output already exists: {path}") from error
        published = path.stat()
        return published.st_dev, published.st_ino
    finally:
        temporary.unlink(missing_ok=True)


def unlink_if_same_file(path: Path, identity: tuple[int, int]) -> None:
    """Remove only the exact directory entry published by this process."""
    try:
        current = path.stat()
    except FileNotFoundError:
        return
    if (current.st_dev, current.st_ino) == identity:
        path.unlink()


def git_identity(path: Path) -> tuple[Path, str, str]:
    """Return repo root, relative path, and commit for tracked clean HEAD bytes."""
    resolved = path.resolve()
    root = Path(subprocess.check_output(
        ["git", "-C", resolved.parent, "rev-parse", "--show-toplevel"], text=True).strip())
    relative = str(resolved.relative_to(root))
    subprocess.run(
        ["git", "-C", root, "ls-files", "--error-unmatch", relative],
        check=True, stdout=subprocess.DEVNULL)
    subprocess.run(
        ["git", "-C", root, "diff", "--quiet", "HEAD", "--", relative], check=True)
    commit = subprocess.check_output(
        ["git", "-C", root, "rev-parse", "HEAD"], text=True).strip()
    historical = subprocess.check_output(
        ["git", "-C", root, "show", f"HEAD:{relative}"])
    if historical != resolved.read_bytes():
        raise ValueError(f"tracked path is not HEAD-identical: {relative}")
    return root, relative, commit


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-worker", type=Path, required=True)
    parser.add_argument("--root-generator", type=Path, required=True)
    parser.add_argument("--expected-root-generator-sha256", required=True)
    parser.add_argument("--root-manifest", type=Path, required=True)
    parser.add_argument("--expected-root-manifest-sha256", required=True)
    parser.add_argument("--expected-freight-receipt-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt-output", type=Path, required=True)
    parser.add_argument("--work-root", type=Path, required=True)
    args = parser.parse_args()
    # Freeze every CLI spelling against the invocation cwd before any validation
    # or embedding.  The derived worker may run from an unrelated campaign cwd.
    args.source_worker = args.source_worker.resolve()
    args.root_generator = args.root_generator.resolve()
    args.root_manifest = args.root_manifest.resolve()
    args.output = args.output.resolve()
    args.receipt_output = args.receipt_output.resolve()
    args.work_root = args.work_root.resolve()
    for value in (
        args.expected_root_generator_sha256,
        args.expected_root_manifest_sha256,
        args.expected_freight_receipt_sha256,
    ):
        if not SHA_RE.fullmatch(value):
            raise ValueError("expected hashes must be canonical lowercase SHA-256")
    validate_approved_pins(
        args.expected_root_generator_sha256, args.expected_root_manifest_sha256,
        args.expected_freight_receipt_sha256)
    generator_root, generator_relative, generator_commit = git_identity(args.root_generator)
    worker_root, worker_relative, worker_commit = git_identity(Path(__file__))
    if generator_root != worker_root or generator_commit != worker_commit:
        raise ValueError("worker and root generators must be HEAD-identical at one commit")
    if sha256_file(args.root_generator) != args.expected_root_generator_sha256:
        raise ValueError("root generator SHA-256 mismatch")
    require_absent_work_root(args.work_root)
    validate_manifest(
        args.root_manifest, args.expected_root_manifest_sha256,
        args.expected_freight_receipt_sha256)
    source = args.source_worker.read_bytes()
    worker = derive_worker(
        source, args.root_generator, args.expected_root_generator_sha256,
        args.root_manifest, args.expected_root_manifest_sha256, args.work_root)
    receipt = {
        "schema": SCHEMA,
        "source_worker_sha256": sha256_bytes(source),
        "root_generator_path": str(args.root_generator),
        "root_generator_sha256": args.expected_root_generator_sha256,
        "root_manifest_path": str(args.root_manifest),
        "root_manifest_sha256": args.expected_root_manifest_sha256,
        "freight_receipt_sha256": args.expected_freight_receipt_sha256,
        "output_worker_sha256": sha256_bytes(worker),
        "worker_generator_sha256": sha256_file(Path(__file__)),
        "worker_generator_path": worker_relative,
        "root_generator_repo_path": generator_relative,
        "git_commit": worker_commit,
        "header_rewrite": False,
        "jobs": 406,
        "work_root": str(args.work_root),
        "lineage_schema": LINEAGE_SCHEMA,
        "queue_receipt_sha256": APPROVED_QUEUE_RECEIPT_SHA256,
        "queue_sha256": APPROVED_QUEUE_SHA256,
    }
    # Publish the worker first and its receipt last as the completeness marker.
    worker_identity = create_only_write(
        args.output, worker, stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR |
        stat.S_IRGRP | stat.S_IXGRP | stat.S_IROTH | stat.S_IXOTH)
    try:
        create_only_write(args.receipt_output, canonical_json(receipt), 0o644)
    except BaseException:
        unlink_if_same_file(args.output, worker_identity)
        raise
    print(canonical_json(receipt).decode(), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
