# Bounded T0 singleton-layer pilot

Among the 761 joint-host-compatible T0 heavy cores reviewed in 2025, this pilot selects the 30 smallest Cartesian host domains (ties by core bitset). All 30 exhaust with no singleton-layer completion. This provisionally reduces the 761-core domain to 731 untested cores, subject to independent review. No H5 sector or Phase B root is removed.

The necessary model and completeness argument are identical to review 2026, with T0 supports: ten pair-support vertices and twenty singletons (four of each colour), leaving fourteen empty vertices. All hosting partition sizes are included; repeated paired guests across colours are forbidden. BC=J requires each uncovered singleton/high colour entry to receive exactly one reciprocal singleton edge. Empty vertices cannot repair missing colours. Only C4 constraints are used in the edge completion search. Singleton copy labels are normalized before any singleton edges are assigned.

singleton_completion.py is adapted from the reviewed T2 search solely for the T0 source, selected core list, and output count/name. It uses a 100,000-node per-core cap and 60-second total wall cap; neither cap was reached. check_singleton_rejections.py is the separately implemented whole-colour-block algorithm from review 2026 adapted to the same selected domain; all 30 negatives exhaust independently. No capped T2 core was retried. Neither implementation constitutes a Lean proof.

INPUT_PINS.json records the frozen source/input bytes. selection.json includes all host-domain sizes. singleton-t0.json and singleton-rejection-audit.json preserve both results. Run each script from this directory; each writes its own result file.
