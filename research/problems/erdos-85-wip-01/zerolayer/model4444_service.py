#!/usr/bin/env python3
"""(4,4,4,4) H-lift model, STAGE 1: service layer feasibility.

VERDICT (2026-08-10): FEASIBLE.  See squad msg 1851.  Key structure:
for each comp pair {e,f}, the 8 co-linked orphans carry pairwise
distinct difference profiles delta = tau_e - tau_f mod 12, and row
distinctness forces delta not in {0,3,6,9}; so the 8 orphans occupy
the 8 non-3-divisible residues of Z12 exactly once, simultaneously on
all 6 comp pairs.

Fixed structure: 4 used C12 comps e0..e3; 16 orphan C12s, four per
omitted-comp type (K4-PM incidence).  Every link is a cycle isomorphism
(equal sizes, Q=1 both ways, globally oriented per
exists_cycleCoverMap_of_componentQuotient_eq_one +
cycleMap_global_orientation): phi(x) = eps*x + tau on Z12.
Row covers psi_e(y) = eta_e*y + c_e on Z3 (constant slope, verified);
gauge-fixed to eta=+1, c=0.

Shared-pair criterion (derived, slope-independent): two co-linked
orphans share a service pair iff their delta profiles agree mod 12;
forbidden by degree_sixteen_zeroLayer_two_row_service_pair_injective
(a89c4cdd69) via C4.
"""
from ortools.sat.python import cp_model
from itertools import combinations

COMPS = range(4)
ORPHANS = [(i, j) for i in COMPS for j in range(4)]  # (omitted, copy)
def links(o):
    return [e for e in COMPS if e != o[0]]

model = cp_model.CpModel()
slope = {}
tau = {}
for o in ORPHANS:
    slope[o] = model.NewBoolVar(f"s{o}")
    L = links(o)
    for e in L:
        tau[o, e] = model.NewIntVar(0, 11, f"t{o}{e}")
    model.Add(tau[o, L[0]] == 0)          # orphan rotation gauge
    r = {}
    for e in L:                            # row offsets distinct mod 3
        r[e] = model.NewIntVar(0, 2, f"r{o}{e}")
        model.AddModuloEquality(r[e], tau[o, e], 3)
    model.AddAllDifferent([r[e] for e in L])

for i in COMPS:                            # copy-ordering symmetry break
    for j in range(3):
        o1, o2 = (i, j), (i, j + 1)
        L = links(o1)
        model.Add(tau[o1, L[1]] <= tau[o2, L[1]])

# pair injectivity: shared pair iff delta profiles agree mod 12
for o1, o2 in combinations(ORPHANS, 2):
    shared = [e for e in links(o1) if e in links(o2)]
    for e, f in combinations(shared, 2):
        d = model.NewIntVar(-11, 11, f"d{o1}{o2}{e}{f}")
        model.Add(d == (tau[o2, e] - tau[o1, e]) - (tau[o2, f] - tau[o1, f]))
        dm = model.NewIntVar(0, 11, f"dm{o1}{o2}{e}{f}")
        model.AddModuloEquality(dm, d + 12, 12)
        model.Add(dm != 0)

solver = cp_model.CpSolver()
solver.parameters.max_time_in_seconds = 600
solver.parameters.num_search_workers = 8
st = solver.Solve(model)
print("STATUS:", solver.StatusName(st))
if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
    for o in ORPHANS:
        print(o, "s=", solver.Value(slope[o]),
              [(e, solver.Value(tau[o, e])) for e in links(o)])
