#!/usr/bin/env python3
"""Run exactly the fresh H1 Phase B complement through the pinned dispatcher.

This wrapper preserves the reviewed v1 dispatcher source and its historical
configuration identities. It selects H1 rows absent from the 96-row overlay,
requires two solver verdicts, and passes explicit case IDs to the v1 runner.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

import dispatch_verdict_only as dispatch


def select(config_path: Path):
    plan = dispatch.load_plan(config_path.resolve())
    config = plan['config']
    wrapper = config.get('h1_residual')
    expected = {'wrapper_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                'sector': 'H1', 'historical_count': 96, 'fresh_count': 1161,
                'selected_ids_sha256': '8c741b733a27ab75b49bc07e2a5ed7c42658c22ded2c4753a106fb93f5a7adb8',
                'historical_ids_sha256': '04097bb4dec4c381ed614d17937a2d011127ffa6debb1db79f2de85a4cad64f3'}
    if wrapper != expected:
        raise ValueError('H1 residual wrapper identity or census policy mismatch')
    if (len(plan['historical']) != 96 or config['policies']['H1'] !=
            {'crosscheck': True, 'primary_cap_seconds': 14400,
             'crosscheck_cap_seconds': 14400}):
        raise ValueError('H1 residual historical count or two-solver cap mismatch')
    historical = {row['id'] for row in plan['historical']}
    h1 = {row['id'] for row in plan['cases'] if row['sector'] == 'H1'}
    selected = [row for row in plan['cases'] if row['sector'] == 'H1'
                and row['id'] not in historical]
    if (len(h1) != 1257 or len(selected) != 1161 or len(historical) != 96
            or not historical <= h1 or len({row['id'] for row in selected}) != 1161):
        raise ValueError('Frozen H1 source/historical complement is not 1161')
    def id_digest(ids):
        return hashlib.sha256((''.join(name + '\n' for name in sorted(ids))).encode()).hexdigest()
    if (id_digest(row['id'] for row in selected) != expected['selected_ids_sha256']
            or id_digest(historical) != expected['historical_ids_sha256']):
        raise ValueError('H1 residual/historical selected-ID hash mismatch')
    return plan, selected


def pilot_ids(path: Path, config_path: Path, fresh: list[dict]) -> list[str]:
    raw = path.read_bytes()
    value = json.loads(raw)
    if (value.get('schema') != 'erdos85-h1-verdict-pilot-v1'
            or value.get('config_sha256') != hashlib.sha256(config_path.read_bytes()).hexdigest()
            or value.get('selected_census') != 1161
            or not isinstance(value.get('cases'), list) or len(value['cases']) != 24):
        raise ValueError('Pilot configuration identity or census mismatch')
    by_id = {row['id']: row for row in fresh}
    ids = []
    for row in value['cases']:
        if not isinstance(row, dict) or set(row) != {'id', 'profile', 'source_index', 'rank_in_profile'}:
            raise ValueError('Pilot row schema mismatch')
        case = by_id.get(row['id'])
        if (case is None or case['source_index'] != row['source_index']
                or int(case['row']['profile']) != row['profile']):
            raise ValueError('Pilot case is not its frozen H1 residual source row')
        ids.append(row['id'])
    if len(set(ids)) != 24 or [sum(row['profile'] == p for row in value['cases']) for p in range(5)] != [5,5,5,5,4]:
        raise ValueError('Pilot duplicate or profile coverage mismatch')
    return ids


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', required=True, type=Path)
    parser.add_argument('--config-commit')
    parser.add_argument('--execute', action='store_true')
    subset = parser.add_mutually_exclusive_group()
    subset.add_argument('--case-id', action='append')
    subset.add_argument('--pilot', type=Path)
    parser.add_argument('--workers', type=int, choices=range(1, 5), default=1)
    parser.add_argument('--output-dir', type=Path)
    parser.add_argument('--kissat', type=Path)
    parser.add_argument('--cadical', type=Path)
    args = parser.parse_args()
    plan, fresh = select(args.config)
    allowed = {row['id'] for row in fresh}
    if args.pilot:
        ids = pilot_ids(args.pilot.resolve(), args.config.resolve(), fresh)
    elif args.case_id:
        selected = set(args.case_id)
        if len(selected) != len(args.case_id) or not selected <= allowed:
            parser.error('Pilot IDs must be distinct fresh H1 residual cases')
        ids = [row['id'] for row in fresh if row['id'] in selected]
    else:
        ids = [row['id'] for row in fresh]
    if args.execute:
        if not args.config_commit or not args.output_dir:
            parser.error('Execution requires a pinned commit and a new output directory')
        dispatch.runner.require_banked_inventory(Path(__file__).resolve(),
            args.config_commit, expected_bytes=Path(__file__).read_bytes())
        if args.pilot:
            dispatch.runner.require_banked_inventory(args.pilot.resolve(),
                args.config_commit, expected_bytes=args.pilot.read_bytes())
    forwarded = ['dispatch_verdict_only.py', '--config', str(args.config.resolve()),
                 '--workers', str(args.workers)]
    if args.execute:
        forwarded += ['--execute', '--config-commit', args.config_commit,
                      '--output-dir', str(args.output_dir)]
    if args.kissat is not None:
        forwarded += ['--kissat', str(args.kissat)]
    if args.cadical is not None:
        forwarded += ['--cadical', str(args.cadical)]
    for case_id in ids:
        forwarded += ['--case-id', case_id]
    previous = sys.argv
    try:
        sys.argv = forwarded
        return dispatch.main()
    finally:
        sys.argv = previous


if __name__ == '__main__':
    raise SystemExit(main())
