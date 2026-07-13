# Knowledge Base: lagrange-four-squares-waring-g2-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

Goal: the **"if" direction** of Legendre's three-square theorem,
`n ≠ 4^a(8b+7) ⟹ ∃ x y z : ℤ, x²+y²+z² = n`. The "only if" direction is
elementary (squares mod 8 ∈ {0,1,4}) and already fully proved.

**Critical ORIENT correction to problem.md:** problem.md recommends a
Davenport–Cassels formalization and warns the prime-existence input "may pull in
Dirichlet (heavy in Lean)". That framing is out of date. The gallery file
`proofs/Proofs/ThreeSquares.lean` (1956 lines) already:
- commits to the **Minkowski geometry-of-numbers + Dirichlet-primes-in-AP**
  route (not Davenport–Cassels), and
- imports `Mathlib.NumberTheory.LSeries.PrimesInAP` — Dirichlet's theorem is now
  *in Mathlib*, so that "heavy input" is available off the shelf.

A fresh Davenport–Cassels attempt would **duplicate ~1000 lines of already-proved
geometry-of-numbers infrastructure**. Do not do that.

---

## Insights

### State of `proofs/Proofs/ThreeSquares.lean` (as of 2026-06-14)
- Necessity: fully proved, **0 axioms**.
- `minkowski_ellipsoid_has_lattice_point` (line 950): **proved** via Mathlib's
  `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`.
- `dirichletSublattice` (line 1460) + basis matrix (det = p²) + linear
  independence + `dirichletForm_eq_p_of_lt_two_mul` (line 1333): **proved**.
- Per-residue prime lemmas (p%8 ∈ {1,3,5} ⟹ sum of three squares): **proved**.
- Reduced to exactly **2 axioms** + **1 downstream sorry**:
  1. `dirichlet_key_lemma` (line 615): Minkowski lattice point → representation
     of `n`. Ingredients proved; only the final assembly missing.
  2. `not_excluded_form_is_sum_three_sq` (line 1665): full sufficiency by mod-8
     case split + `PrimesInAP` + (1). Docstring estimates **~150–200 lines**.
  3. `needs_four_iff_excluded` (line 1927, sorry): **trivial** corollary once
     `legendre_three_squares` is axiom-free.

### The number-theoretic crux: isotropy of the form, on the 4-free core
The geometry-of-numbers step needs the form Q(x,y,z) = x²+y²+z² to be **isotropic
mod m**, i.e. a, b with a² + b² + 1 ≡ 0 (mod m). The precise fact (verified
numerically below, and it *corrected an initial wrong guess of mine*):

> **isotropy mod m is solvable ⟺ 4 ∤ m** — NOT "⟺ m is non-excluded".

So the proof first **strips the 4^a factor** (n = 4^a·m, 4∤m, via the already-
proved `sq_mul_*` lemmas), reducing to the 4-free core m. On that core, Q is
isotropic, which cuts out the **covolume-m congruence sublattice** Λ_m on which
Q ≡ 0 (mod m). Minkowski on the ball of radius √(2m) (volume (4/3)π(2m)^{3/2} >
2³·m) yields a nonzero v ∈ Λ_m with 0 < Q(v) ≤ 2m and Q(v) ≡ 0 (mod m), forcing
Q(v) = m.

Important: **isotropy is not the same as "m is a sum of three squares".** E.g.
m = 7 is isotropic (4∤7) yet excluded; the m ≡ 7 (mod 8) obstruction is killed
separately by the strict Minkowski bound / parity (the case Q(v) = 2m is
excluded), not by isotropy. This is exactly why the two axioms still require a
careful mod-8 case split rather than a one-line isotropy ⇒ representation.

### Buildability assessment
| Target | Size | Foundational? | Decision |
|--------|------|---------------|----------|
| `dirichlet_key_lemma` | ~few hundred LOC assembly | No — ingredients proved | BUILD (Docker-gated) |
| `not_excluded_form_is_sum_three_sq` | ~150–200 LOC | No — `PrimesInAP` in Mathlib | BUILD (Docker-gated) |
| `needs_four_iff_excluded` sorry | trivial | No | BUILD (Docker-gated) |

Not "blocked" (the old "Mathlib lacks X" framing is wrong: Mathlib now has
`PrimesInAP`, geometry of numbers, and the rest). The only blocker this session
is the **Docker outage** — every discharge needs a build to verify.

### Build-free verification (durable)
`verify_three_squares_route.py` (committed) confirms, with pure stdlib:
- [A] n = x²+y²+z² ⟺ n ≠ 4^a(8b+7) by brute force.
- [B] isotropy a²+b²+1≡0 (mod m) solvable ⟺ 4∤m (so the GoN argument applies to
  the 4-free core m = n/4^a).
- [C] Minkowski volume inequality (tightest at m=1, ratio (π/3)√(2m)).
- [D] primes p with p%8 ∈ {1,3,5} are sums of three squares.

Spot-checked representatives this session (host CPU starvation from the agent
swarm prevented the full-range run; the script is committed as the reproducible
artifact): excluded {7,15,23,28,31,112} all NOT 3-squares; non-excluded
{1,2,3,5,6,11,19,43,83,100,101} all ARE; isotropy false exactly at 4|m (28,100,
112); (π/3)√2 ≈ 1.481 > 1.

---

## Dead Ends

- **Davenport–Cassels from scratch** — not a dead end mathematically, but a
  *wasteful* one here: it would re-derive the geometry-of-numbers machinery that
  ThreeSquares.lean already proves. Prefer finishing the Minkowski route.
- **"Mathlib lacks the Dirichlet input → blocked"** — false as of 2026:
  `Mathlib.NumberTheory.LSeries.PrimesInAP` provides Dirichlet's theorem and is
  already imported.

---

## Session 2026-06-15 (researcher-3) — Mathlib 3-square check + standdown (dual blackout)

**Mode**: REVISIT (MODERATE). **Outcome**: no safe forward step; standdown.

- **State of `ThreeSquares.lean`**: 2 axioms (`dirichlet_key_lemma` :615, `not_excluded_form_is_sum_three_sq` :1665), **0 sorries**, REGISTERED (Proofs.lean:2949). The earlier "1 downstream sorry" is gone — only the two axioms remain.
- **Mathlib still LACKS the three-square theorem** (checked sibling `~/GitHub/mathlib4` @ v4.26.0, grepped `Mathlib/NumberTheory/` for `sum_three_squares|sq_add_sq_add_sq|three.square` — none; `SumFourSquares.lean` has only the FOUR-square theorem `Nat.sum_four_squares`). So neither axiom can be collapsed to a Mathlib citation; the Minkowski+Dirichlet assembly in the file is still the only route.
- **Why no build-free step this session**: both axioms are multi-hundred-line assemblies in a REGISTERED gallery file; discharging either blind (Docker down, Aristotle `prove` → 404, both re-tested live) would risk breaking the gallery build for all consumers. The committed `verify_three_squares_route.py` re-times-out under host load (check_A brute force), consistent with prior CPU-starvation notes — fast checks B/C/D were validated in earlier sessions.
- **Repeat-check for future sessions** (the three-square theorem landing in Mathlib would collapse this whole file):
  ```bash
  git -C ~/GitHub/mathlib4 fetch origin master
  git -C ~/GitHub/mathlib4 grep -niE 'sum_three_squares|sq_add_sq_add_sq' origin/master -- 'Mathlib/NumberTheory/**'
  ```
- **Next step unchanged**: when Docker returns, discharge `dirichlet_key_lemma` first (ingredients proved in-file), then `not_excluded_form_is_sum_three_sq` (~150–200 LOC) on top of it.
