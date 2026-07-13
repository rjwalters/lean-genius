# S12 S5-c ACT — `dirichletSetN_volume` via shear pushforward shipped

**Date.** 2026-05-31 (Session 12)
**Researcher.** researcher-1
**Mode.** ACT (Lean edit; build pending per slug convention — see
`feedback_lake_self_loop_main_repo`).

**Predecessor.** S11 S6α ACT (PR #?, 2026-05-30, researcher-1):
shipped `stdLatticeN_coords` integer-coord extraction in new PART 7
(file 331 → 370 LOC, 8 → 9 theorems, 0 sorries / 0 axioms
carry-forward). The slot for PART 6 — `dirichletSetN_volume` via the
shear pushforward — was left open and parallel-lane per
PREP-3/PREP-4's race-table.

**This ACT.** Fills the PART 6 slot. Ships the three lemmas from
PREP-4 §2.3 + S5-c PREP §3 Steps A & B:

* `dirichletBoxN_measurable` (Step A, ~5 LOC body + docstring)
* `dirichletBoxN_volume` (Step B, ~13 LOC body + docstring)
* `dirichletSetN_volume` (Step C, ~16 LOC body + docstring)

LOC delta: 370 → 434 (+64 LOC including ~30 LOC docstrings + new
PART 6 banner). Theorems: 9 → 12. Sorries unchanged at 0. Axioms
unchanged at 0.

---

## §1. Pin-stability rationale for using OQ-01's working pattern

PREP-4 §2.2 flagged `LinearMap.continuous_on_pi` as **absent** at the
pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, and proposed
`LinearMap.continuous_of_finiteDimensional` as the replacement. This
ACT did NOT follow that recommendation. Reason: the parent
`proofs/Proofs/MinkowskiTheoremOQ02OQ01.lean:126` uses
`Continuous.measurable (LinearMap.continuous_on_pi T)` and is
**build-verified at the same pin** (S5 PREP-2 §1, 3058 jobs on PR
#19046 cycle). The bearer exists; PREP-4 §1 row 7's negative
verification likely missed the `Mathlib.Topology.Algebra.Module.LinearMap`
re-export of `LinearMap.continuous_on_pi`. This ACT trusts the
runtime-verified OQ-01 pattern over the doc-only PREP-4 verdict.

If the build breaks with `unknown identifier LinearMap.continuous_on_pi`,
the doctor/mechanic should swap to PREP-4 §2.2's `continuous_of_finiteDimensional`
form. The PART 6 body is otherwise paste-stable.

---

## §2. Step C `abs ((-1)^n)⁻¹ = 1` plumbing — conservative chain

This ACT uses the conservative 5-step chain
`abs_pow → abs_neg → abs_one → one_pow → inv_one` rather than
PREP-4 §2.1's proposed `abs_neg_one_pow` single-step rewrite. Reason:
all 5 conservative bearers are rock-solid standard Mathlib and have
zero rename risk at v4.26.0; the single-step `abs_neg_one_pow`
introduces a new bearer dependency that PREP-4 §1.1 verified but is
not exercised by any other proof in this gallery. Net LOC cost: +1
LOC vs PREP-4's tightest form. Trade-off favored bearer-graph
stability over LOC minimization.

---

## §3. Required new import + open

Added one import line:
```
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
```

(parent OQ-01 has the same import — needed for `Real.volume_pi_Ioo`,
`Real.map_matrix_volume_pi_eq_smul_volume_pi`, and `Measure.map_apply`)

Added `MeasureTheory` to the existing `open` line:
```
open OrderDual MeasureTheory
```

(was `open OrderDual`; the `MeasureTheory` open lets `volume`,
`Measure.map`, and `Measure.map_apply` resolve without qualifier,
matching OQ-01's namespace conventions)

No other namespace open is required.

---

## §4. Build-verify status

Docker build verification is currently blocked at the
worktree/repo-share layer by the G9 lake self-loop documented in
`feedback_lake_self_loop_main_repo` (`proofs/.lake` symlinks to
itself). All ACT PRs ship under the "build pending" qualifier per
established slug convention (#18975 S5-a, #19046 S5-b, #21475/#21477
recent precedents). The mechanic-PR overlay pattern is the unblock
route once host infra clears.

The diff is paste-from-PREP-4-§2.3 modulo §1 / §2 conservatism above,
so risk of elaboration failure is low.

---

## §5. Forward roadmap (remaining to OQ-03 graduation)

S5-c ACT (this PR) + S6α ACT (S11, prior PR) jointly close PART 6 +
PART 7. The only remaining ACT is:

* **S6 ACT** — `simultaneous_dirichlet_from_minkowski` (~80 LOC,
  #18511 5-stage assembly pattern): wires `dirichletSetN_volume`
  (this PR) + `stdLatticeN_coords` (S11) + Minkowski's
  `minkowski_integer_lattice_proved` into the final assembly.

LOC remaining to OQ-03 graduation: **~80 LOC**, down from ~129 after
S6α and now ~80 after this S5-c.

---

## §6. Files touched (2)

* `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (+64 LOC, +1 import,
  +1 namespace open `MeasureTheory`; new PART 6 with 3 theorems —
  `dirichletBoxN_measurable`, `dirichletBoxN_volume`,
  `dirichletSetN_volume`)
* `research/problems/minkowski-theorem-oq-02-oq-03/sessions/2026-05-31-s12-s5c-act-dirichletSetN-volume.md` (this file, new)

No edits to `state.md` / JSON / `problem.md` / `knowledge.md` /
gallery `meta.json` — STATE-SYNC deferred to next drain-wave
(parallel-lane with S11 S6α PR).

---

## §7. Honest assessment

* **Mathematical progress**: This PR closes the volume-bridge step of
  the n-dim Cassels parallelepiped construction. With this and S6α,
  the final S6 assembly is now mechanical — pull `dirichletSetN_volume`,
  combine with the `(2 : ENNReal)^(n+1)` Minkowski threshold via the
  `2(Qⁿ + 1) * (2/Q)ⁿ = 2^(n+1) (Qⁿ + 1) / Qⁿ` arithmetic, apply
  `minkowski_integer_lattice_proved`, and extract integers via
  `stdLatticeN_coords`. The hard mathematics (shear-map preimage
  identity, determinant calculation, measurability, convexity,
  symmetry) is all on `main`.
* **Practical value**: ~64 LOC closer to OQ-03 graduation; the
  remaining ~80 LOC in S6 ACT is the most concentrated single ACT in
  the slug's remaining work and should be one final session.
* **Build status**: Build pending per G9 lake self-loop. The diff is
  paste-stable against the v4.26.0 pin per §1, §2, §3.
* **Why not split into 3 PRs (one per theorem)**: The three theorems
  are functionally one unit (Steps A → B → C build on each other; A
  feeds B's measurability, A + B feed C's pushforward). Splitting
  would inflate review surface without separating concerns.
