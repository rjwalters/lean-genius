"""Read-only campaign capacity/queue planner. Does not submit or reclaim work."""
import argparse
import hashlib
import json
import math
from pathlib import Path


def capacity(memory_gib, vcpus, reserve_gib=12, slot_gib=16, slot_cpus=2, max_slots=6):
    if not all(math.isfinite(v) and v > 0 for v in [memory_gib, vcpus, reserve_gib, slot_gib, slot_cpus, max_slots]):
        raise ValueError('Positive finite resource values required')
    slots = min(int((memory_gib - reserve_gib) // slot_gib), int(vcpus // slot_cpus), max_slots)
    if slots < 1:
        raise ValueError('No slot fits the specified actual node resources')
    return slots


def plan(manifest, manifest_sha, memory_gib, vcpus, nodes, in_flight=()):
    rows = manifest['cases']
    ids = [r['id'] for r in rows]
    if len(ids) != len(set(ids)) or not rows:
        raise ValueError('Empty or duplicate manifest')
    if any(r['state'] not in ('PENDING', 'REUSED_PASS') for r in rows):
        raise ValueError('Unexpected manifest state')
    if nodes < 1 or nodes > 16:
        raise ValueError('Planning requires 1..16 nodes; not a launch authorization')
    live = set(in_flight)
    if live - set(ids):
        raise ValueError('Unknown in-flight case')
    slots = capacity(memory_gib, vcpus)
    queue = [r['id'] for r in rows if r['state'] == 'PENDING' and r['id'] not in live]
    counts = manifest['compute_counts']
    if counts != {'total': len(rows), 'reused': sum(r['state'] == 'REUSED_PASS' for r in rows), 'pending': sum(r['state'] == 'PENDING' for r in rows)}:
        raise ValueError('Manifest counts differ')
    if any(r['state'] == 'REUSED_PASS' and r['id'] in live for r in rows):
        raise ValueError('A reused case cannot also be in flight')
    scenarios = []
    for slow_fraction in (0, .25, .5, .75, 1):
        avg_minutes = 4 * (1 - slow_fraction) + 90 * slow_fraction
        slot_hours = len(queue) * avg_minutes / 60
        scenarios.append({'assumed_slow_fraction': slow_fraction, 'assumed_mean_pair_minutes': avg_minutes,
                          'idealized_slot_hours': round(slot_hours, 2),
                          'idealized_fleet_hours': round(slot_hours / (slots * nodes), 2),
                          'idealized_billed_vcpu_hours': round(slot_hours * vcpus / slots, 2)})
    return {'status': 'DRY_RUN_ONLY_NOT_EXECUTION_READY', 'manifest_sha256': manifest_sha,
            'nodes_for_scenario': nodes, 'slots_per_node': slots, 'slot_memory_limit_gib': 16,
            'slot_cpu_limit': 2, 'node_reserved_memory_gib': 12, 'pair_wall_cap_seconds': 7200,
            'counts': counts, 'in_flight_excluded': sorted(live), 'queue': queue,
            'illustrative_scenarios_not_forecasts': scenarios,
            'initial_pass_slot_hour_cap': 2 * len(queue),
            'initial_pass_fleet_hours_at_cap_idealized': 2 * math.ceil(len(queue) / (slots * nodes)),
            'limitations': ['Scenarios assume 4/90 minute classes; the selected sample does not establish this distribution.',
                            'Startup, dependency build, verification, storage and residual retries are excluded.',
                            'No price quote, fleet authorization, worker execution or claim mutation is performed.']}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--memory-gib', type=float, required=True, help='actual usable node memory, not advertised nominal memory')
    p.add_argument('--vcpus', type=int, required=True)
    p.add_argument('--nodes', type=int, default=1)
    p.add_argument('--in-flight', action='append', default=[])
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    data = a.manifest.read_bytes()
    if hashlib.sha256(data).hexdigest() != a.manifest_sha256:
        p.error('manifest hash mismatch')
    result = plan(json.loads(data), a.manifest_sha256, a.memory_gib, a.vcpus, a.nodes, a.in_flight)
    encoded = json.dumps(result, indent=2) + '\n'
    if a.output:
        with a.output.open('x') as f:
            f.write(encoded)
    print(json.dumps({k: v for k, v in result.items() if k != 'queue'}, indent=2))


if __name__ == '__main__':
    main()
