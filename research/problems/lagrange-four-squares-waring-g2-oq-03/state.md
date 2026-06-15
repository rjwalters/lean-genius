# Research State: lagrange-four-squares-waring-g2-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-14T17:42:09-07:00
**Iteration**: 4

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
3. `needs_four_iff_excluded` (sorry, line 1927): downstream and **trivial** once
   `legendre_three_squares` is axiom-free (it is a direct corollary).

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
