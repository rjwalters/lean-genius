#!/usr/bin/env python3
"""(4,4,4,4) stage-1 service-layer FULL ENUMERATION (squad msg 1899).

Same constraint model as model4444_service.py (gauge: per-orphan
first-link tau=0, copy-ordering within omitted-comp types, row covers
eta=+1/c=0, slopes +1 WLOG per msg 1857).  CP-SAT enumerate-all.

RESULT (2026-08-10): terminates OPTIMAL with EXACTLY 1,294 solutions
(no cap hit; complete gauge-fixed count).  Raw artifact:
  /Volumes/Stripe/lean-genius/artifacts/erdos85-zerolayer/
    stage1_solutions.json
  sha256 05f2d5d613b283ea81aabb318cf283bc6a2f22257c13d8344d249a3b8b575f5d
  format: {"gauge": ..., "count": 1294,
           "solutions": [{"omit,copy,comp": tau, ...} x 1294]}
Canonicalization under the residual symmetry group (S4 comp relabeling
with induced type permutation, per-comp rotation by multiples of 3,
global reflection) is a separate artifact (to follow).
"""
from ortools.sat.python import cp_model
from itertools import combinations
import json

COMPS = range(4)
ORPHANS = [(i, j) for i in COMPS for j in range(4)]  # (omitted, copy)
def links(o):
    return [e for e in COMPS if e != o[0]]

model = cp_model.CpModel()
tau = {}
for o in ORPHANS:
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

class Collector(cp_model.CpSolverSolutionCallback):
    def __init__(self, tau):
        super().__init__()
        self.n = 0
        self.tau = tau
        self.sols = []
    def on_solution_callback(self):
        self.n += 1
        sol = {}
        for (o, e), var in self.tau.items():
            sol[f"{o[0]},{o[1]},{e}"] = self.Value(var)
        self.sols.append(sol)
        if self.n >= 100000:
            self.StopSearch()

if __name__ == "__main__":
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 900
    solver.parameters.enumerate_all_solutions = True
    cb = Collector(tau)
    st = solver.Solve(model, cb)
    print("STATUS:", solver.StatusName(st), "solutions:", cb.n)
    json.dump({"gauge": ("per-orphan first-link tau=0; copy-ordering "
                         "within types; eta=1,c=0; slopes +1 WLOG"),
               "count": cb.n, "solutions": cb.sols},
              open("stage1_solutions.json", "w"))
    print("dumped stage1_solutions.json")
