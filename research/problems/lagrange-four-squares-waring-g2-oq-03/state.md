# Research State: lagrange-four-squares-waring-g2-oq-03

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14T17:42:09-07:00
**Iteration**: 2

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
already **reduced** by this session's PR **#24443** (`ThreeSquaresSufficiency.lean`,
unregistered): it now follows from `dirichlet_key_lemma` + an isolated
`DirichletWitnessProperty` (∃ d>0, prime p=d·n−1, `legendreSym p (−d)=1`), with the whole
mod-8 / 4-stripping descent discharged (0 new axioms, 0 sorry). **Do NOT re-do the
sufficiency descent.** The two remaining open targets (both Docker-gated):
1. `dirichlet_key_lemma` (axiom 1, ThreeSquares.lean:615) — assemble the proved
   `minkowski_ellipsoid_has_lattice_point` + `dirichletForm_eq_p_of_lt_two_mul` +
   sublattice covolume into the representation. THE distinct open work for this slug.
2. `DirichletWitnessProperty` — `Nat.infinite_setOf_prime_and_eq_mod` (PrimesInAP, imported)
   + a QR residue-class choice making `−d` a QR mod `p`.
Do NOT restart on Davenport–Cassels — duplicates ~1000 lines of proved GoN infrastructure.
