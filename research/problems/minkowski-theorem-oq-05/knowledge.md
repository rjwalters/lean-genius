# minkowski-theorem-oq-05 — Power-sum convexity bound and the optimal constant

## Summary

For a real exponent `p ≥ 1` and nonnegative reals `a, b`:
```
(a + b) ^ p ≤ 2 ^ (p - 1) · (a ^ p + b ^ p),
```
and `2 ^ (p - 1)` is the **optimal** constant: equality holds at `a = b`, and any
constant `C` valid for all nonnegative `a, b` satisfies `C ≥ 2 ^ (p - 1)`. The
headline result packages this as
```
2 ^ (p - 1) = IsLeast { C | ∀ a b ≥ 0, (a + b) ^ p ≤ C · (a ^ p + b ^ p) }.
```

Mathlib has the inequality only for `ℝ≥0` (`NNReal.rpow_add_le_mul_rpow_add_rpow`)
and `ℝ≥0∞`; the real-valued nonnegative form and the optimality of the constant are
both absent.

## Files

- `proofs/Proofs/MinkowskiTheoremOQ05.lean` — 4 theorems, 0 def, 0 sorry, 0 axiom
  (by construction). Registered in `proofs/Proofs.lean`.
- `src/data/proofs/minkowski-theorem-oq-05/{meta.json,annotations.json}` — gallery
  entry, held at `formalized`/`wip` pending a green build.

---

## Session 2026-06-20 (Session 1) — Full proof written, build blocked by harness blackout

**Mode**: FRESH
**Outcome**: progress (proof complete; machine-verification pending)

### What I Did
- Triaged the 16 available pool problems (all EMPTY knowledge tier). Found most are
  verbatim Mathlib re-exports (chebyshev-oq-02 = `T_mul_T`, uniformbell = `uniformBell_mul_eq`,
  dyck-catalan = `card_dyckWord_semilength_eq_catalan`, three-subgroups = `three_subgroups_lemma`,
  spectral = `det_eq_prod_roots_charpoly`/`trace_eq_sum_roots_charpoly`).
- Selected minkowski-theorem-oq-05: the **ℝ≥0** bound is verbatim in Mathlib, but the
  **real-valued** form and the **optimality** of `2^(p−1)` are not — genuine, tractable content.
- Wrote `MinkowskiTheoremOQ05.lean`:
  1. `rpow_add_le_two_rpow_sub_one_mul` — real-valued bound via `lift … to ℝ≥0` + `exact_mod_cast`.
  2. `rpow_add_self_eq` — diagonal equality (sharpness witness), all real `p`.
  3. `two_rpow_sub_one_le_of_forall` — optimality lower bound from test point `a=b=1`.
  4. `isLeast_two_rpow_sub_one` — `2^(p−1)` is the least admissible constant.
- Registered the module in `proofs/Proofs.lean`; drafted gallery `meta.json` + `annotations.json`.

### Key Findings
- The genuine content is **optimality**, not the bare inequality (a one-line ℝ≥0 transport).
- The diagonal equality needs no `p ≥ 1` hypothesis (both sides are `2^p·a^p`).
- A single test point `a=b=1` pins the optimal constant: `2^p ≤ 2C ⇒ C ≥ 2^(p−1)`.

### Blockers
- **Docker harness blackout (2026-06-20):** `docker info` unreachable from host all
  session (VM internally up — volume/forward IPC responds — but `dockerd` not exposed).
  Tried `open -a Docker`, a full quit+relaunch, and ~10 min of polling; never recovered.
  So `docker-build.sh Proofs.MinkowskiTheoremOQ05` was NOT run; the file is **not yet
  kernel-checked**. Status held at `formalized`/`wip`, NOT `verified` (gallery-integrity:
  never claim verified without a real build).
- Aristotle MCP fills sorries only — useless for build-verifying a complete file.

### Self-review (in lieu of a build)
Logic checked by hand: thm 1 is a standard `exact_mod_cast` over `NNReal.coe_rpow`;
thm 2 is an `rw` chain reducing both sides to `2^p·a^p`; thm 3 instantiates at `1,1`
and divides via `2^(p−1)=2^p/2`; thm 4 is `⟨thm1, thm3⟩` over `IsLeast`. Residual risk
is only elaboration detail (the `exact_mod_cast` cast set; `intro` through `Set.mem_setOf`
in the `IsLeast` membership goal) — exactly what the pending build will confirm.

### Files Modified
- `proofs/Proofs/MinkowskiTheoremOQ05.lean` (new)
- `proofs/Proofs.lean` (import)
- `src/data/proofs/minkowski-theorem-oq-05/meta.json` (new)
- `src/data/proofs/minkowski-theorem-oq-05/annotations.json` (new)
- `src/data/research/problems/minkowski-theorem-oq-05.json` (new)

### Next Steps
- Build via Docker once the harness recovers; on green, promote to `verified`/`original`.
- Follow-up veins: reverse bound for `0 < p ≤ 1` (constant 1); n-term form with `n^(p−1)` optimal.
