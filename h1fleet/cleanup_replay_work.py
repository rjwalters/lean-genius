#!/usr/bin/env python3
"""Validate accepted evidence and journal removal of one completed job's scratch."""
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from replay_common import (AwsCliObjectStore, LocalObjectStore, ReplayError,
                           atomic_write, canonical_json, load_json, load_manifest,
                           require_tag, sha256_bytes, sha256_file)
from replay_worker import receipt_key

HERE = Path(__file__).resolve().parent
VALIDATOR = HERE / 'validate_replay_receipt.py'
MAX_RETAINED_LOG_BYTES = 16 * 1024 * 1024


def sync_directory(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def checked_directory(path: Path) -> Path:
    if path.is_symlink() or path.resolve() != path.absolute():
        raise ReplayError(f'cleanup directory must be canonical and not symlinked: {path}')
    if not path.is_dir():
        raise ReplayError(f'cleanup directory is absent: {path}')
    return path


def cleanup_accepted_work(args: argparse.Namespace, job: dict, dispatch: dict) -> dict:
    """Called under the dispatcher's host lock, after the worker has exited."""
    tag = require_tag(job.get('tag'))
    manifest = load_manifest(args.manifest)
    manifest_sha = sha256_file(args.manifest)
    if manifest.get('cleanup_accepted_work') is not True:
        raise ReplayError('cleanup is not enabled by the frozen manifest')
    if manifest.get('cleanup_sha256') != sha256_file(Path(__file__)):
        raise ReplayError('cleanup helper differs from frozen manifest')
    if manifest.get('validator_sha256') != sha256_file(VALIDATOR):
        raise ReplayError('cleanup validator differs from frozen manifest')
    if dispatch.get('returncode') != 0 or dispatch.get('tag') != tag:
        raise ReplayError('cleanup requires a successful dispatch for this job')
    state = checked_directory(args.state_dir.absolute())
    work_root = checked_directory(state / 'work')
    work = checked_directory(work_root / tag)
    work_identity = (work.stat().st_dev, work.stat().st_ino)
    journal_root = state / 'cleanup'
    journal_root.mkdir(exist_ok=True)
    checked_directory(journal_root)
    journal = Path(tempfile.mkdtemp(prefix=tag+'-', dir=journal_root))
    receipt_path = journal / 'accepted-receipt.json'
    if args.object_store_root is not None:
        store = LocalObjectStore(args.object_store_root)
        backend = ['--object-store-root', str(args.object_store_root)]
    else:
        store = AwsCliObjectStore(args.s3_bucket, args.aws)
        backend = ['--s3-bucket', args.s3_bucket, '--aws', args.aws]
    store.download(receipt_key(manifest['campaign_prefix'], tag), receipt_path)
    receipt = load_json(receipt_path)
    if (receipt.get('tag') != tag or receipt.get('manifest_sha256') != manifest_sha
            or receipt.get('job_sha256') != sha256_bytes(canonical_json(job))):
        raise ReplayError('cleanup receipt does not bind the dispatched job and manifest')
    command = [sys.executable, str(VALIDATOR), '--manifest', str(args.manifest),
               '--receipt', str(receipt_path), *backend]
    result = subprocess.run(command, capture_output=True, check=False)
    atomic_write(journal/'validator.stdout', result.stdout)
    atomic_write(journal/'validator.stderr', result.stderr)
    validation = {'schema': 'erdos85-h1-scratch-validation-v1', 'tag': tag,
                  'manifest_sha256': manifest_sha, 'receipt_sha256': sha256_file(receipt_path),
                  'validator_sha256': sha256_file(VALIDATOR), 'argv': command,
                  'returncode': result.returncode, 'finished_unix_ns': time.time_ns(),
                  'stdout_sha256': sha256_bytes(result.stdout),
                  'stderr_sha256': sha256_bytes(result.stderr)}
    atomic_write(journal/'validation.json', canonical_json(validation))
    atomic_write(journal/'dispatch.json', canonical_json(dispatch))
    atomic_write(journal/'job.json', canonical_json(job))
    if result.returncode != 0:
        raise ReplayError(f'independent cleanup validation failed; retained scratch and {journal}')
    # Keep small diagnostic records outside the bulky work tree before deleting it.
    retained = []
    for name in ('worker.log', 'axiom-audit.json', 'accepted-ready.json',
                 'accepted-ledger.json', 'existing-ready.json', 'existing-receipt.json'):
        source = work/name
        if not source.exists() and not source.is_symlink():
            continue
        if source.is_symlink() or not source.is_file() or source.stat().st_size > MAX_RETAINED_LOG_BYTES:
            raise ReplayError(f'cleanup diagnostic is unsafe or exceeds retention limit: {source}')
        destination = journal/name
        with source.open('rb') as inp, destination.open('xb') as out:
            shutil.copyfileobj(inp, out, length=1024*1024)
            out.flush(); os.fsync(out.fileno())
        retained.append({'path': name, 'sha256': sha256_file(destination), 'bytes': destination.stat().st_size})
    checked_directory(work_root); checked_directory(work)
    if (work.stat().st_dev, work.stat().st_ino) != work_identity:
        raise ReplayError('cleanup scratch directory changed during validation')
    if sha256_file(args.manifest) != manifest_sha or sha256_file(VALIDATOR) != manifest['validator_sha256']:
        raise ReplayError('cleanup manifest or validator changed during validation')
    if not shutil.rmtree.avoids_symlink_attacks:
        raise ReplayError('cleanup requires fd-based symlink-safe rmtree')
    record = {'schema': 'erdos85-h1-scratch-cleanup-v1', 'tag': tag,
              'manifest_sha256': manifest_sha, 'receipt_sha256': validation['receipt_sha256'],
              'validation_sha256': sha256_file(journal/'validation.json'),
              'dispatch_sha256': sha256_file(journal/'dispatch.json'),
              'job_sha256': sha256_file(journal/'job.json'), 'retained': retained,
              'work_path': str(work), 'work_device': work_identity[0], 'work_inode': work_identity[1],
              'status': 'VALIDATED_DELETE_PENDING'}
    atomic_write(journal/'cleanup.json', canonical_json(record))
    # rmtree does not follow symlinks, including symlink entries below work.
    with receipt_path.open('rb') as stream:
        os.fsync(stream.fileno())
    sync_directory(journal)
    sync_directory(journal_root)
    sync_directory(state)
    shutil.rmtree(work)
    sync_directory(work_root)
    record.update(status='DELETED', finished_unix_ns=time.time_ns())
    atomic_write(journal/'cleanup.json', canonical_json(record))
    sync_directory(journal)
    return {'journal': str(journal/'cleanup.json'), 'sha256': sha256_file(journal/'cleanup.json')}
