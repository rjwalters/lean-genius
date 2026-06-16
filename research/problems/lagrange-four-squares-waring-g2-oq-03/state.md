# Research State: lagrange-four-squares-waring-g2-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-14T17:42:09-07:00
**Iteration**: 5

## Session 2026-06-15 (researcher-9) — FRONTIER RE-MAP (corrects stale "Remaining Gap")

ORIENT-only (build host gated — see Blocker). Three corrections to the tracked
state, all verified against the current main checkout:

1. **The line-1927 `sorry` is GONE (merged, not open).** The "Remaining Gap"
   item 3 below (`needs_four_iff_excluded`, "downstream and trivial") was
   discharged by **#24293** and is now a real proof at `ThreeSquares.lean:1964`
   (split_ifs + `excluded_form_not_sum_three_sq` for the ≤2-square branches).
   `ThreeSquares.lean` now has **0 sorry, exactly 2 axioms**:
   `dirichlet_key_lemma` (:648) and `not_excluded_form_is_sum_three_sq` (:1698).
   Do NOT re-attempt the 1927 sorry — it does not exist.

2. **Five companion files are on main, all 0-sorry/0-axiom, but UNREGISTERED and
   never build-verified** (written under prior Docker blackouts; merged via
   #24614/#24628/#24696 etc.). Earlier `grep -c sorry` counts of "1" were comment
   matches ("no `sorry`"); a comment-stripped scan gives 0 real sorries in every
   one. Topological register order (deps resolved) for the next build-host:
   `ThreeSquaresResidue3` (Mathlib-only), `ThreeSquaresResidue3Obstruction`
   (Mathlib-only), `ThreeSquaresSufficiency` (→ThreeSquares),
   `ThreeSquaresSufficiencyCorrected` (→ThreeSquares,ThreeSquaresResidue3),
   `ThreeSquaresWitnessObstruction` (→ThreeSquaresSufficiency). Register = add
   `import Proofs.X` to `Proofs.lean` AFTER a green `docker-build.sh Proofs.X`.

3. **The monolithic witness route is PROVED FALSE (not just numerically).**
   `ThreeSquaresWitnessObstruction.not_dirichletWitnessProperty` derives
   `¬ ThreeSquares.DirichletWitnessProperty` from `witness_obstruction_residue3`
   (concrete falsifier m=11). So `ThreeSquaresSufficiency.lean`'s single-witness
   reduction is a documented DEAD END; the live sufficiency route is
   `ThreeSquaresSufficiencyCorrected.lean` (residue split, m%4=3 dispatched via
   the two-square route, other classes via the guarded witness).

**Sharpened `dirichlet_key_lemma` gap (supersedes "all ingredients proved, just
assemble").** The proved `minkowski_ellipsoid_has_lattice_point` (:983) finds a
lattice point over the **standard** lattice ℤ³ (form `v0²+d·v1²+d·v2² ≤ R`). The
axiom needs a Minkowski point in the **Dirichlet congruence sublattice**
(`dirichletSublatticeReal`, :1560, covolume ∝ p²) so that Q ≡ 0 (mod p) and
`dirichletForm_eq_p_of_lt_two_mul` (:1366) forces Q(v)=p. That **sublattice
Minkowski instance is still missing** — the existing GoN lemma is over the wrong
lattice. This is the distinct open Lean work and is Docker-gated (needs a build
to verify; do not write blind).

## Session 2026-06-15 (researcher-3, later) — residue-3 analytic risk REMOVED

The `t² + 2p` quadratic-deficit route flagged as "the genuine remaining analytic
risk" is unnecessary. It was an artifact of the rigid witness shape `p = d·n − 1`
in `dirichlet_key_lemma`, which forces `p ≡ −1 (mod n)` — the single residue where
the proved obstruction makes `(−n|p) = −1`. Dropping that tie and asking only for
a prime with `(−n|p)=1`, the class `a = 1` is universal: **every prime
`p ≡ 1 (mod 4n)` has `(−n|p)=1`** (one-line reciprocity, see knowledge.md), a
single linear AP straight from Mathlib's `PrimesInAP`. Certificate
`verify_single_ap_residue3.py` PASSES on all 405 square-free `n ≡ 3 mod 8` in
`[3,4000)`. Recommended Lean refactor: generalize `dirichlet_key_lemma`'s prime
hypothesis from `p = d·n−1` to an arbitrary prime with `(−n|p)=1`, instantiated at
`p ≡ 1 (mod 4n)`. No Lean changed this session (build host down: circular `.lake`).

## Session 2026-06-15 (researcher-3) — residue-3 obstruction PROVED (was numerical)

The residue-3 carve-out in `ThreeSquaresSufficiencyCorrected.lean` rests on the
claim that the monolithic Dirichlet witness (`∃ d, p = d·m−1 prime,
legendreSym p (−d)=1`) is UNSATISFIABLE for every 4-free core `m ≡ 3 (mod 8)`.
Across prior sessions this was only a NUMERICAL observation ("0/750"). This
session upgrades it to a THEOREM and formalizes it in Lean (build-pending):

**Key reduction.** Since `p = d·m − 1 ≡ −1 (mod m)`, we have `d·m ≡ 1 (mod p)`,
so `d ≡ m⁻¹ (mod p)` and `legendreSym p (−d) = legendreSym p (−m)`. Thus the
witness condition is exactly **`−m` is a QR mod `p`**.

**Obstruction (proved by Jacobi reciprocity).** For `m ≡ 3 (mod 4)` and any odd
prime `p ≡ −1 (mod m)`:
  `(−m | p) = χ₄(p)·(m | p)`, `(m | p) = ±(p | m)` (sign from `p mod 4`, using
  `m ≡ 3 mod 4`), and `(p | m) = (−1 | m) = χ₄(m) = −1`. The two `p`-dependent
  signs CANCEL in both classes `p ≡ 1, 3 (mod 4)` ⟹ `(−m | p) = −1` identically.
Hence the witness is impossible, and `dirichlet_key_lemma` provably cannot reach
`m ≡ 3 (mod 8)`. The carve-out is a genuine obstruction, not a finite-search
artifact.

**Deliverables (PR this session):**
- `proofs/Proofs/ThreeSquaresResidue3Obstruction.lean` (NEW, unregistered,
  build-pending): `legendreSym_neg_m_eq_neg_one` (the obstruction),
  `legendreSym_neg_d_eq_neg_m` (the `−d`↔`−m` reduction), `no_residue3_witness`
  (witness unsatisfiable). 0 axioms, 0 sorry. All Mathlib bearers name-checked
  @ pinned rev 2df2f0150c (jacobiSym.neg / quadratic_reciprocity_{one,three}_mod_four
  / at_neg_one / mod_left' ; ZMod.χ₄_nat_{one,three}_mod_four ; legendreSym.{mul,mod,
  sq_one,at_one,to_jacobiSym}).
- `verify_residue3_obstruction.py` (NEW): certifies obstruction + identity +
  Residue3Property + good-residue witness existence. PASS for m<20000, d≤3000
  (2499 residue-3 cores, 9999 good cores, 51 986 prime-pair identity checks).

**Build status.** Worktree `.lake` is a circular self-symlink (defeats olean
cache → Mathlib-from-source → OOM on the 7.65GB Docker VM). Verified locally
impossible; deployer cache-warm gate is the verifier.

## (prior) Current Focus
Feasibility / route survey for the "if" direction of Legendre's three-square
theorem ( n ≠ 4^a(8b+7) ⟹ n = x²+y²+z² ).


## Current Focus
Feasibility / route survey for the "if" direction of Legendre's three-square
theorem ( n ≠ 4^a(8b+7) ⟹ n = x²+y²+z² ).

**Key ORIENT finding (corrects problem.md):** the gallery already contains a
substantial implementation in `proofs/Proofs/ThreeSquares.lean` (1956 lines). It
does NOT use the Davenport–Cassels route suggested in problem.md. Instead it
commits to the **Minkowski geometry-of-numbers + Dirichlet-primes-in-AP** route,
and the heavy machinery is already built and *proved*:

- Necessity ("only if") — fully proved, **no axioms**.
- Squares-mod-8 lemmas, descent on the 4^a factor — proved.
- Per-residue prime lemmas (primes p with p%8 ∈ {1,3,5} are sums of three
  squares) — proved (lines 435–562).
- Full ℤ³ lattice / fundamental domain / covolume-1 infrastructure — proved.
- `minkowski_ellipsoid_has_lattice_point` (line 950) — **proved** via Mathlib's
  `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`.
- The Dirichlet congruence-sublattice (`dirichletSublattice`, basis matrix of
  det p², linear independence, real basis, `dirichletForm_eq_p_of_lt_two_mul`)
  — proved (lines 1220–1652).
- `Mathlib.NumberTheory.LSeries.PrimesInAP` (Dirichlet's theorem) is now in
  Mathlib and is already imported (line 3).

## Remaining Gap (the actual open work)
The "if" direction is reduced to exactly **2 axioms + 1 downstream sorry**:

1. `dirichlet_key_lemma` (axiom, line 615): bridges a Minkowski lattice point in
   the congruence-sublattice ellipsoid to a representation `x²+y²+z² = n`. All
   analytic ingredients (Minkowski point + sublattice covolume + "form value =
   p" lemma) are already proved; what is missing is the final assembly.
2. `not_excluded_form_is_sum_three_sq` (axiom, line 1665): the full sufficiency,
   by case analysis on n mod 8 + `PrimesInAP` + `dirichlet_key_lemma`. Its own
   docstring estimates **~150–200 lines** on top of the existing framework.
3. ~~`needs_four_iff_excluded` (sorry, line 1927)~~ — **RESOLVED, merged #24293**
   (now a real proof at `ThreeSquares.lean:1964`). See the researcher-9 session
   block at the top of this file. Only the two axioms above remain.

## Active Approach
Confirm/repair the chosen Minkowski+Dirichlet route (NOT Davenport–Cassels).
The geometry-of-numbers step needs Q(x,y,z)=x²+y²+z² **isotropic mod m**
(a²+b²+1≡0 mod m). Verified fact (corrected an initial wrong guess this session):
isotropy is solvable ⟺ **4∤m**, NOT ⟺ "m non-excluded". So the proof strips 4^a
(n=4^a·m, 4∤m, via proved `sq_mul_*` lemmas) to the 4-free core m, builds the
covolume-m congruence sublattice on which Q≡0 mod m, and Minkowski forces Q(v)=m.
The m≡7 (mod 8) exclusion is a SEPARATE obstruction handled by the strict bound
(Q(v)=2m excluded), not by isotropy — which is why the axioms still need a mod-8
case split.

## Attempt Count
- Total attempts: 0 (ORIENT survey only — no Lean edits this session, Docker down)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- **Docker down** this session (`docker ps` hangs) → cannot build/verify Lean.
  Discharging either axiom requires a build, so the two ACT targets are
  Docker-gated. ORIENT survey + number-theoretic verification are build-free and
  done this session.

## Verification (build-free, durable)
`verify_three_squares_route.py` (committed, `python3`-runnable, stdlib only)
independently checks:
- [A] Legendre characterization n=x²+y²+z² ⟺ n≠4^a(8b+7) by brute force.
- [B] isotropy a²+b²+1≡0 (mod m) solvable ⟺ 4∤m (GoN applies to 4-free core).
- [C] Minkowski volume inequality (4/3)π(2m)^{3/2} > 2³·m (tightest at m=1).
- [D] primes p with p%8∈{1,3,5} are sums of three squares.

(Host CPU starvation from the agent swarm blocked the full-range run this
session; the script is committed as the reproducible artifact and the
representatives above were spot-checked: excluded {7,15,23,28,31,112} not
3-squares, non-excluded {1,2,3,5,6,11,19,43,83,100,101} are, isotropy false
exactly at 4|m.)

## Next Action
**UPDATE (researcher-2, 2026-06-15):** axiom (2) `not_excluded_form_is_sum_three_sq` is
**partially** reduced by PR **#24443** (`ThreeSquaresSufficiency.lean`, unregistered):
it follows from `dirichlet_key_lemma` + an isolated `DirichletWitnessProperty`
(∃ d>0, prime p=d·n−1, `legendreSym p (−d)=1`). **Do NOT re-do the sufficiency descent.**

**CORRECTION (researcher-1, 2026-06-15) — supersedes target 2 below:** the single
`DirichletWitnessProperty` does **NOT** discharge the full descent. It is **provably
UNSATISFIABLE for m ≡ 3 (mod 8)** — in fact for all m ≡ 3 (mod 4): the obstruction
theorem `legendreSym p (−d) = −1` (proved in `ThreeSquaresWitnessObstruction.lean`,
on main, unregistered) is now certified two ways
(`verify_witness_obstruction_residue3.py`: 0/61399 counterexamples + full Jacobi-
reciprocity step check; `verify_three_squares_residue_routes.py`: 750/750 m≡3 mod 8
cores have NO witness). So **do NOT** attempt "a QR residue-class choice making −d a
QR mod p" — no such class exists. The `ThreeSquaresSufficiency.lean` docstring already
flags this (PR #24786). The remaining open targets (both Docker-gated):
1. `dirichlet_key_lemma` (axiom 1, ThreeSquares.lean:615) — assemble the proved
   `minkowski_ellipsoid_has_lattice_point` + `dirichletForm_eq_p_of_lt_two_mul` +
   sublattice covolume into the representation. THE distinct open work for this slug.
2. **(corrected)** Complete the sufficiency reduction by the certified **residue split**,
   not a single witness: guard `DirichletWitnessProperty` with `m % 8 ≠ 3` (covers
   m≡1,2,5,6 mod 8 via Dirichlet/Minkowski), and add the **two-square branch** for
   m ≡ 3 (mod 8): ∃ odd t with `(m−t²)/2 = a²+b²` (Mathlib `Nat.Prime.sq_add_sq`),
   whence `m = t² + (a+b)² + (a−b)²`. Both halves certified PASS in
   `verify_three_squares_residue_routes.py`. Then register the corrected file.
Do NOT restart on Davenport–Cassels — duplicates ~1000 lines of proved GoN infrastructure.

## Session 2026-06-15 (researcher-2) — confirm dischargeable sorry still build-gated

Re-assessed the ACT target. The cleanest actionable item is the `needs_four_iff_excluded`
sorry at `ThreeSquares.lean:1925`, which `L1927-dischargeable.md` already shows is
dischargeable from the **already-proved** easy direction `excluded_form_not_sum_three_sq`
(NOT the hard axiom PR #24149 scopes). A complete hand-verified proof sketch exists there.

Did NOT apply it: both backends gated this session (Aristotle MCP `prove()` -> 404
"Resource not found", live-probed; Docker at 4 `lean-build` containers, above the safe
<=2 threshold — went UP from 3 during the session). The prior session correctly flagged
that the sketch's `split_ifs`/`not_not` shape and `ℕ→ℤ` casts need build-time iteration,
so replacing the `sorry` with uncompiled code would risk breaking the build. No StatementOnly
extraction made either: the lemma needs `squaresNeeded` + `IsExcludedForm` defs + the easy
lemma as context, so the right Aristotle route is `prove()` with
`context_files=[ThreeSquares.lean]` (or `prove_file`) when the backend recovers — not a
self-contained single-theorem file. Stood down; no duplicate artifact.

## Session 2026-06-16 (researcher-11) — Minkowski `Q<2p` step is a 3D dead end; 2D-slice is the fix

**ORIENT finding (verified arithmetic), no Lean changed.** Docker was free this
session — the historical blocker for this slug — so the prior "build-gated stand-down"
no longer applies. But the next planned increment (the S11 sublattice-Minkowski
producing `dirichletForm < 2p`) is *geometrically unattainable* on the existing 3D
index-p² sublattice: the generic 2³-covolume Minkowski bound only gives `Q ≤ R` with
`R ~ p^(4/3) ≫ 2p`. Confirmed by grep (nothing supplies the `Q<2p` hypothesis of
`dirichletForm_eq_p_of_lt_two_mul`; sublattice-Minkowski is only a docstring TODO at
`:1692`) and by `verify_minkowski_2p_gap.py` block [A].

**The fix:** the `Q<2p` point exists only via the 2D slice `z=0` (index-p sublattice
of ℤ², binary form, 2D Hermite bound `(2/√3)√d·p < 2p` for `d ≤ 2`, which covers all
case-split branches). Verified: `Q=p` for every applicable `(p,d∈{1,2})`
(block [B]). Next ACT should build a **2D** Minkowski (reuse
`Proofs/MinkowskiTheoremOQ02OQ01.lean`), not extend the 3D ellipsoid; or pivot to
Davenport–Cassels (`G1-dirichlet-bearer.md`). Details: `G2-minkowski-2p-gap.md`.

**Already-done / do-NOT-redo reminders (unchanged):** `needs_four_iff_excluded` sorry
is discharged on main; file is 0 sorries / 2 axioms (`dirichlet_key_lemma :648`,
`not_excluded_form_is_sum_three_sq :1720`).
