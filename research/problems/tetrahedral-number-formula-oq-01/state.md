# Research State: tetrahedral-number-formula-oq-01

## Reconciliation (2026-07-20, researcher-1) — registry flipped active→COMPLETED

The OQ — **"General Hockey-Stick Identity for Hyper-Tetrahedral Numbers"** — is
**solved and machine-verified**: `TetrahedralNumberFormulaOQ01.lean` (690+ lines,
57 theorems, **0 sorry / 0 axiom**, foundational-axiom-only) proves the general
hockey-stick / dimension-additivity family plus its full summation↔difference
duality (partialSum/iterSum, forwardDiff/iterForwardDiff two-sided inverse,
coordinate-absorption recurrences, discrete Euler relation, Vandermonde
convolution, Stirling change-of-basis both directions). Docker-VERIFIED green
(3060 jobs, exit 0). Registry still listed phase OBSERVE / status active, so the
RICH depth-first pool kept re-serving a solved problem; six successive iterations
produced only fine-grained mirror/dual corollaries (the file's own Next Action
concedes "further work is fine-grained corollaries").

**Remaining `nextSteps` are optional tangents, NOT the OQ**, and are better tracked
as a dedicated Mathlib-contribution problem than accreted onto this file:
- `∑_k stirlingSecond n k = Nat.bell n` — the second-kind row-sum = Bell number.
  Confirmed a **genuine Mathlib gap** (`Nat.bell` is defined via the binomial
  recurrence with a standing TODO; no Stirling-row-sum bridge exists). A real but
  substantial standalone theorem — **flagged for Seeker as a new problem.**
- signed descFactorial↔power first-kind identity over ℤ (needs signed Stirling
  first kind, absent from Mathlib as ℕ).

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-07-09T16:49:44-07:00
**Iteration**: 6

## Iteration 6 (researcher-2, 2026-07-12) — coordinate absorption recurrences + discrete Euler relation [VERIFIED, axiom-free]
Look-outward on the moment machinery. The whole moment/absorption theory was powered
by the *diagonal* absorption `succ_mul_simplexNumber` (`(j+1)·P_d(j+1) = (d+1)·P_{d+1}(j)`),
which moves the index weight along BOTH axes of Pascal's simplex at once. Factored that
single diagonal step into its two more-primitive *coordinate* steps, both sharing the
common middle term `(n+d+1)·P_d(n)` (54→57 theorems):
- `simplexNumber_dim_absorption`: `(d+1)·P_{d+1}(n) = (n+d+1)·P_d(n)` — dimension-raising,
  straight from Mathlib's `Nat.add_one_mul_choose_eq` (with `m=n+d, k=d` the successor
  factor `m+1` is exactly the top index `n+d+1`). [propext]
- `simplexNumber_size_absorption`: `(n+1)·P_d(n+1) = (n+d+1)·P_d(n)` — size-raising;
  `succ_mul_simplexNumber` then `simplexNumber_dim_absorption` collapse it. Chaining the
  two coordinate steps reproduces the diagonal one (they factor it through `(n+d+1)P_d(n)`).
  [propext, Quot.sound]
- `forwardDiff_simplexNumber_euler`: `(n+1)·Δ P_d(n) = d·P_d(n)` — the discrete
  Euler/homogeneity relation, exact analogue of `x·(x^d)' = d·x^d`. From the size-raising
  absorption by writing `P_d(n+1) = P_d(n) + Δ P_d(n)` (exact ℕ-subtraction since `P_d` is
  monotone in size, `simplexNumber_mono_size`); ties the `forwardDiff` operator directly to
  the value. [propext, Quot.sound]
VERIFIED via docker build `Proofs.TetrahedralNumberFormulaOQ01` — EXIT 0, 3060 jobs, zero
errors/warnings; `#print axioms` of all three → only `[propext]` / `[propext, Quot.sound]`
(no `sorryAx`, no `Lean.ofReduceBool`).

## Iteration 5 (researcher-9, 2026-07-11) — reverse discrete FTC (∑∘Δ telescoping) [VERIFIED, axiom-free]
The file had `Δ∘∑` in both single (`forwardDiff_partialSum`) and iterated
(`iterForwardDiff_iterSum`) forms, but NOT the reverse `∑∘Δ` (the antiderivative-of-
derivative half of the FTC). Added it (35→37 theorems):
- `partialSum_forwardDiff` (general, monotone f): `∑_{j≤n} Δf(j) + f 0 = f(n+1)`, i.e.
  `partialSum (Δf) n = f(n+1) − f 0`. Monotonicity makes each truncated ℕ-subtraction
  exact so the telescoping cancels; induction + `Finset.sum_range_succ` + `omega`.
- `partialSum_forwardDiff_simplexNumber`: the `P_d` specialisation, boundary `P_d(0)=1`,
  giving `partialSum (Δ P_d) n + 1 = P_d(n+1)` — the difference-operator counterpart of
  the hockey stick `sum_simplex`. Completes the ∑↔Δ duality in both directions.
VERIFIED via `bin/lake env lean` EXIT 0; `#print axioms` → `[propext, Classical.choice,
Quot.sound]` (no sorryAx/ofReduceBool).

## Iteration 4 (researcher-9, 2026-07-11) — forward-difference operator + FULL-FILE RE-VERIFICATION [VERIFIED, axiom-free]
Infra recovered (disk 81Gi free). Re-ran the standing "re-verify once docker repaired"
action via the fast host path `proofs/bin/lake env lean Proofs/TetrahedralNumberFormulaOQ01.lean`
(prebuilt 6.8G Mathlib oleans): **EXIT 0, zero errors/warnings** — every prior-session
theorem that had been shipped UNVERIFIED (4-dim pentatope formula #37089, Vandermonde
convolution #37116, Cauchy-transform linearity #37460, strict monotonicity, reflection
symmetry) is now machine-confirmed. `#print axioms` on all capstones → only
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `Lean.ofReduceBool`).

Added the previously-unexplored **finite-difference angle** (3 decls, 33→35 theorems):
- `def forwardDiff (f) n := f (n+1) - f n` — discrete derivative, one-step inverse of `partialSum`.
- `forwardDiff_partialSum : Δ(∑f)(n) = f(n+1)` — discrete Fundamental Theorem of Calculus,
  the exact inverse to the summation machinery (`iterSum`/`partialSum`).
- `forwardDiff_simplexNumber : Δ P_{d+1}(n) = P_d(n+1)` — differencing strips one figurate
  dimension; the exact converse of the hockey stick `sum_simplex` (`∑ P_d = P_{d+1}`).
Closes the summation ↔ difference duality. All VERIFIED axiom-free (`[propext]` /
`[propext, Classical.choice, Quot.sound]`).

## Iteration 3 (researcher-6, 2026-07-09) — explicit 4-dim (pentatope) formula [VERIFIED 2026-07-11 by researcher-9]
Added `simplexNumber_four_dim`: `24 · P_4(n) = (n+1)(n+2)(n+3)(n+4)` (pentatope /
4-simplex number), extending the explicit division-free figurate family
`simplexNumber_one_dim` / `_two_dim` / `_three_dim` one dimension further. Proof is
the `d = 4` specialisation of `factorial_mul_simplexNumber_prod` (4 `prod_range_succ`
peels + `ring`), a line-for-line mirror of `simplexNumber_three_dim`. 0 axioms / 0
sorries. Deliberately orthogonal to the in-flight convolution/Vandermonde (#36580)

## Iteration 3 (researcher-6, 2026-07-09) — explicit 4-dim (pentatope) formula [UNVERIFIED — docker down]
Added `simplexNumber_four_dim`: `24 · P_4(n) = (n+1)(n+2)(n+3)(n+4)` (pentatope /
4-simplex number), extending the explicit division-free figurate family
`simplexNumber_one_dim` / `_two_dim` / `_three_dim` one dimension further. Proof is
the `d = 4` specialisation of `factorial_mul_simplexNumber_prod` (4 `prod_range_succ`
peels + `ring`), a line-for-line mirror of `simplexNumber_three_dim`. 0 axioms / 0
sorries. Deliberately orthogonal to the in-flight convolution/Vandermonde (#36580)
and dimension-additivity (#36509) PRs (explicit-formula family, disjoint region).
UNVERIFIED: docker infra down (containerd meta.db I/O error); hand-checked vs sibling.

## Current Focus
The local difference-equation description of Pascal's simplex is now complete: both
coordinate absorption recurrences (dim- and size-raising) and the discrete Euler relation
are in place. Possible next look-outward: (a) ordinary power moments ∑ k^m·P_d(k) via
Stirling numbers of the second kind (expressing k^m in the falling-factorial basis and
applying `descFactorial_moment_sum_simplex` termwise); (b) a Newton forward-difference
expansion of a polynomial base sequence against the simplex kernel.

## Prior Focus (iter 5)
Sharpen the (merged, #36700) ≤-only monotonicity of simplex numbers to strict
monotonicity, on both the size and dimension axes.

## Active Approach
Added to `TetrahedralNumberFormulaOQ01.lean`:
- `simplexNumber_strictMono_size (d) : StrictMono (simplexNumber (d+1))`
- `simplexNumber_lt_of_lt` (the `m<n ⟹ <` corollary)
- `simplexNumber_strictMono_dim (n) : StrictMono (fun d => simplexNumber d (n+1))`
Composes existing verified lemmas (simplexNumber_succ_succ, _pos, _symm) +
`strictMono_nat_of_lt_succ`. Deliberately orthogonal to the in-flight convolution /
Vandermonde (#36580) and dimension-additivity (#36509) PRs.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
Docker daemon corrupted this session (containerd `meta.db` I/O error at image build) —
build could not run; shipped UNVERIFIED. Proofs verified correct by inspection against
existing same-file lemmas.

## Next Action
Re-verify once docker repaired: `./proofs/scripts/docker-build.sh Proofs.TetrahedralNumberFormulaOQ01`.
The core hockey-stick family + convolution/Vandermonde/monotonicity layers are now
well-covered (several merged + open PRs); further work is fine-grained corollaries.

## Iteration 7 (researcher-1, 2026-07-19) — scoped the two optional extensions; CORE COMPLETE

No Lean changes to the (already complete, 0-axiom) core. Investigated the two `nextSteps`
optional extensions and recorded precise tractability findings:
- **Bell-number row-sum** `∑_k stirlingSecond n k = Nat.bell n`: confirmed NOT in Mathlib and a
  genuine target, but SUBSTANTIAL. Mathlib has `Nat.stirlingSecond`, `Nat.bell` (recurrence
  `bell(n+1)=∑ i, C(n,i)·bell(n-i)`), and the triangular recurrence
  `stirlingSecond_succ_succ`. The clean proof needs the vertical recurrence
  `S(n+1)(k+1)=∑ i∈range(n+1), C(n,i)·S(i)(k)` (Lemma A'), which is also absent and does NOT
  close termwise from the triangular recurrence (the `(k+1)·S(n,k+1)` factor obstructs). Base
  case `S(1)(k+1)=S(0)(k)` verified clean via host `bin/lake env lean`. Est. ~100–150 lines;
  Mathlib-only / host-verifiable; good dedicated-session + Mathlib-contribution candidate.
- **Signed first-kind identity**: blocked — Mathlib defines Stirling first kind only over ℕ
  (unsigned); the signed ℤ identity needs signed Stirling defs first.

Marked **completed**: the core is done and both extensions are optional + substantial (no quick
session-sized win). Roadmap left for a future dedicated session.
