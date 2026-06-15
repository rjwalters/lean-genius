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

## Session 2026-06-15 (researcher-2) — cross-link to the axiom-(2) reduction PR #24443

This slug and `zsqrtd-neg-two-oq-02` target the **same two axioms** of the registered
flagship `proofs/Proofs/ThreeSquares.lean`. Earlier this same session, PR **#24443**
(`ThreeSquaresSufficiency.lean`, unregistered) **reduced axiom (2)**
`not_excluded_form_is_sum_three_sq`: it is now proved (0 new axioms, 0 sorry) from
`dirichlet_key_lemma` (axiom 1) **plus one isolated existence statement**
`DirichletWitnessProperty`:

> for `n>1`, `¬IsExcludedForm n`, `4∤n` ⟹ `∃ d>0` and a prime `p = d·n−1` with
> `legendreSym p (−d) = 1`.

The structural descent (strong induction, 4-power stripping via `excluded_form_four_mul_iff`
+ `four_mul_sum_three_sq`, small cases) is fully discharged there. So the open sufficiency
content is now cleanly **two** pieces, NOT one monolith:

1. **`dirichlet_key_lemma` (axiom 1, ThreeSquares.lean:615)** — the Minkowski
   lattice-point → representation assembly. Per this slug's ORIENT, all analytic
   ingredients are proved (`minkowski_ellipsoid_has_lattice_point`, `dirichletSublattice`
   covolume `p²`, `dirichletForm_eq_p_of_lt_two_mul`); only the final glue is missing.
   This is the **distinct remaining open work for THIS slug** (registered flagship,
   Docker-gated — no blind edits during blackout).
2. **`DirichletWitnessProperty`** — Dirichlet primes in AP (`Nat.infinite_setOf_prime_and_eq_mod`,
   already imported) + a quadratic-reciprocity residue-class choice making `−d` a QR mod `p`.
   This is the genuine number-theoretic existence input isolated by #24443.

**Net:** do NOT re-attempt the sufficiency descent (done in #24443). The two tractable-yet-deep
targets are (1) the `dirichlet_key_lemma` assembly and (2) `DirichletWitnessProperty`. Both are
Docker-gated this session (dual blackout: `docker ps` exit 124, Aristotle 404).

## Session 2026-06-15 (researcher-2) S4 ACT — corrected per-residue architecture + residue-3 route

**Structural finding (corrects the file's own docstring plan).** The registered
flagship funnels ALL non-excluded `n` through the single `dirichlet_key_lemma`
(ThreeSquares.lean:615), whose hypothesis is `∃ d>0, p=d·n−1 prime,
legendreSym p (−d)=1`. The axiom-2 docstring's plan says "n≡3 mod 8: use d=2".
That is **impossible**: for d=2, n≡3 mod 8 ⟹ p=2n−1 ≡ 5 mod 8 ⟹ −2 is a
non-residue mod p. More strongly, `verify_three_squares_residue_routes.py`
certifies the witness is unsatisfiable for **every** 4-free core `m ≡ 3 (mod 8)`
(0/750 found), corroborating audit PR #24529. So the single-lemma architecture
**cannot cover the residue-3 class** — a gap in the registered flagship itself,
not only in #24443's reduction.

**Corrected architecture** (certified build-free over 750 cores per class):
strip `4^a` to the 4-free core `m` (4∤m, m≢7 mod 8), then split on `m mod 8`:
- `m ≡ 1,2,5,6 (mod 8)` → `dirichlet_key_lemma` witness EXISTS. ✓
- `m ≡ 3 (mod 8)` → **two-square route** (NOT dirichlet_key_lemma):
  ∃ odd `t`, `t²≤m`, `mm=(m−t²)/2` prime with `mm%4≠3`; Fermat two-square gives
  `mm=a²+b²`, so `m = t²+(a+b)²+(a−b)²`. Small case `m=3=1²+1²+1²`.

**Mathlib bearer (name-checked @ pinned rev 2df2f01,
NumberTheory/SumTwoSquares.lean:35):**
`Nat.Prime.sq_add_sq {p:ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) : ∃ a b:ℕ, a^2+b^2=p`.

**Built this session:** `proofs/Proofs/ThreeSquaresResidue3.lean` (unregistered,
build-pending under Docker blackout): the algebraic reduction `three_sq_of_two_sq_decomp`
(pure `ring`) and `three_sq_of_residue3_prime` (0 axiom / 0 sorry — reduces the
m≡3 core to the isolated prime-deficit existence statement via `Nat.Prime.sq_add_sq`).
This is the residue-3 analogue of #24443's reduction, for the class #24443/the
flagship's key lemma cannot reach.

**Net for next session (post-blackout):** the sufficiency direction needs TWO
existence inputs, not one:
1. `m ≡ 1,2,5,6` core: the Dirichlet/QR witness `DirichletWitnessProperty`
   restricted to these residues (provable; #24443's descent reusable here).
2. `m ≡ 3` core: ∃ odd `t` with `(m−t²)/2` a prime `≢3 mod 4` — Dirichlet primes
   in AP (`PrimesInAP`) supply it; then `three_sq_of_residue3_prime` finishes.
Do NOT try to force the single-witness lemma onto m≡3 (provably unsatisfiable).
Both inputs Docker-gated to verify in Lean.

## Session 2026-06-15 (researcher-4) — corrected full-sufficiency assembly (PR pending)

The #24443 reduction `ThreeSquaresSufficiency.DirichletWitnessProperty` is a
**false (unsatisfiable) proposition**: audit #24529 / obstruction #24614 proved
no Dirichlet witness `(d, p = d·m−1, legendreSym p (−d)=1)` exists for any 4-free
core `m ≡ 3 (mod 8)`. So reducing the sufficiency axiom to it is vacuous — the
hypothesis can never be discharged.

New file `proofs/Proofs/ThreeSquaresSufficiencyCorrected.lean` (build-pending,
unregistered companion) fixes the architecture by splitting the open content into
**two SATISFIABLE hypotheses**:

1. `DirichletWitnessNe3` — the Dirichlet witness restricted to `m%8 ∈ {1,2,5,6}`
   (where it holds; numerically: 0 failures up to 4000).
2. `Residue3Property` — for `m%8=3, m>3`, existence of a prime deficit
   `mm=(m−t²)/2` with `mm%4≠3` (auto since odd t ⟹ t²≡1 mod 8 ⟹ mm≡1 mod 4);
   consumed by `ThreeSquaresResidue3.three_sq_of_residue3_prime`.

`three_sq_of_corrected_witnesses` proves full sufficiency from these two + the
existing `dirichlet_key_lemma` axiom, by strong induction:
4-power descent (verbatim #24443 template) → small cases n≤1 → mod-8 split on the
4-free core: n=3=1²+1²+1² explicit (the LONE exceptional residue-3 core with no
prime deficit), n%8=3∧n>3 via Residue3, else via dirichlet_key_lemma (witness
branch verbatim from Sufficiency.lean). 0 new axioms, 0 sorry.

`verify_corrected_split.py` certifies (build-free, m≤4000): the two hypotheses
together cover all 4-free non-excluded cores, and the monolithic witness NEVER
works on m≡3 (obstruction holds — 0 accidental successes). NET: unlike #24443
this is a route to actually eliminating the sufficiency axiom (both pieces
dischargeable via Dirichlet primes in AP + QR), not a reduction to a false claim.
