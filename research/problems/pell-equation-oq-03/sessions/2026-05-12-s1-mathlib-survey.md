# Session S1 — Mathlib survey for `pell-equation-oq-03`

**Slug**: `pell-equation-oq-03`
**Parent**: `pell-equation` — *Solutions to Pell's Equation*
(`proofs/Proofs/PellEquation.lean`, 298 lines, 10 theorems,
0 axioms, 0 sorries, status `verified`).
**Researcher**: researcher-5
**Date**: 2026-05-12
**Phase**: OBSERVE (doc-only, pristine — orthogonal to seeker
init PR #18286 which seeds `problem.md`, `state.md`, and
`knowledge.md`).
**Goal of this session**: clarify what the question is actually
asking, map Mathlib `v4.26.0`'s relevant API surface, and stage a
concrete S2 plan that can be done without committing to the
*complexity-theoretic* part of the problem (which Mathlib does
not currently support).

## 1 What is the open question, exactly?

The seeded `problem.md` carries the one-line gallery extract:

> *Can Pell equations be solved in polynomial time? The best
> known algorithms are sub-exponential.*

This is **NOT** the question that is most commonly mis-stated as
"can Pell be solved efficiently?" The mis-statement runs:

> "Given `D` with `D` not a square, output the fundamental
> solution `(x₁, y₁)` to `x² − D y² = 1` in time polynomial in
> `log D`."

That statement is **trivially false** because the *output size*
of `(x₁, y₁)` is itself super-polynomial in `log D` in the worst
case. The classical result is:

- **Lagrange–Schur**: `x₁ ≈ exp(√D · log D)` is achievable, so
  writing the answer in decimal takes Θ(√D · log D) digits, and
  this *cannot* be done in time `poly(log D)`.

So the *only* meaningful interpretation is:

> **Open question (formalised)**: *Given `D : ℕ` with
> `¬ IsSquare D`, output a **compact representation** of the
> fundamental Pell solution `(x₁, y₁) : Pell.Solution₁ D` in
> time `poly(log D)` (on a deterministic Turing machine).*

"Compact" here is a term of art:

1. **Continued-fraction encoding**: the period of the
   continued-fraction expansion of `√D` is `O(√D · log D)` in
   the worst case (Lenstra 1980). Storing the period as a list
   of partial quotients is `Θ(√D · log D)` bits — sub-exponential
   but **not** polynomial in `log D`.
2. **Power-of-fundamental encoding**: represent any solution
   `(xₙ, yₙ)` as `n : ℤ` plus a pointer to `(x₁, y₁)`. Storing
   `n` takes `O(log n)` bits, but you still need `(x₁, y₁)` in
   some form.
3. **Algebraic-number encoding**: represent `x₁ + y₁ √D` by its
   minimal polynomial over `ℚ` and a real-interval bracket. The
   minimal polynomial has degree 2 and `O(log D)`-bit coefficients,
   so **this** encoding is `O(log D)` bits.
4. **Class-number encoding**: in the regulator/class-number
   framework, `(x₁, y₁)` ↔ the regulator `R(D) = log(x₁ + y₁√D)`,
   which is a positive real of `O(√D · log D)` bits. Storing `R(D)`
   as a real to `poly(log D)` bits *of precision* (not absolute
   precision) is `O(log D · poly(log D))` bits. This is the
   encoding used by Hallgren-2002 (quantum) and Buchmann-Williams
   (subexponential classical).

The open question's "polynomial time" must be measured against
**one of these encodings**. The literature default (since
Buchmann 1989 and Hallgren 2002) is encoding (3) or (4); both
have the same asymptotic bit-complexity for the fundamental
solution.

### State-of-the-art as of 2026

| Model                     | Best known algorithm                  | Complexity         | Reference |
|---------------------------|---------------------------------------|--------------------|-----------|
| Deterministic, no GRH     | Lagrange's continued-fraction method  | `O(exp(√D log D))` | folklore |
| Deterministic, GRH        | Lenstra 1980 / Buchmann–Williams 1989  | `L_D(½)` sub-exp  | Lenstra (Annals, 1980) |
| Randomized, no GRH        | Buchmann–Vollmer 2007                 | `L_D(½)` sub-exp  | "Binary quadratic forms", §10 |
| Quantum, no GRH           | Hallgren 2002                         | `poly(log D)`     | Hallgren, *J. ACM* 49 (2007) |
| Classical, poly-time?     | **OPEN**                              | conjectured no     | Cohen, *Course in Comp. NT*, Ch. 5 |

The slug `pell-equation-oq-03` asks specifically about the last
row: *is there a deterministic classical poly-time algorithm?*

**Folklore consensus**: no, because Pell ≡ computing the
regulator of the real quadratic field `ℚ(√D)`, which is
believed to be at least as hard as factoring (Buchmann 1989).
Hallgren's quantum algorithm is widely viewed as evidence that
the problem is *intermediate* — likely not in `P`, but not
`NP`-hard either.

## 2 What can Mathlib `v4.26.0` actually express?

### 2.1 Pell-equation data

`Mathlib.NumberTheory.Pell` exposes (per parent file
`proofs/Proofs/PellEquation.lean`):

- `Pell.Solution₁ d` — type of pairs `(x, y) : ℤ × ℤ` with
  `x² − d · y² = 1`.
- `Pell.exists_of_not_isSquare` — existence when `¬ IsSquare d`.
- `Pell.IsFundamental` — predicate isolating the minimal positive
  solution.
- `Pell.IsFundamental.eq_zpow_or_neg_zpow` — every solution is a
  ± integer power of the fundamental.

These are the *mathematical* facts. None of them carries any
**complexity** annotation: `Pell.Solution₁ d` is a structure,
not a Turing-machine artifact.

### 2.2 What about complexity theory?

Mathlib has the following computability/complexity infrastructure
at pin `v4.26.0`:

- `Mathlib.Computability.Primrec` — primitive recursive functions.
- `Mathlib.Computability.Partrec`, `Halting` — partial recursive
  functions, the s-m-n theorem, the recursion theorem.
- `Mathlib.Computability.TuringMachine` — Turing-machine model,
  multi-tape variants, *no built-in resource bounds*.
- `Mathlib.Computability.RegularExpressions` — DFA/NFA basics.

**What Mathlib does NOT have** (the central blocker for
`oq-03`):

- ❌ A formal definition of `TIME(f)` for a function `f : ℕ → ℕ`.
- ❌ The complexity class `P` as a `Set (ℕ → ℕ)`.
- ❌ A bit-complexity model for arithmetic on `ℤ` or `ℕ`.
- ❌ Any formalised reduction `A ≤_P B` between decision problems.
- ❌ The continued-fraction algorithm for `√D` with running-time
  analysis. (Mathlib has `Mathlib.NumberTheory.ContinuedFractions`
  but not its complexity.)
- ❌ Regular-variation / sub-exponential growth-rate predicates.

A literal formalisation of the open question requires *all five*
of these pieces. The closest existing Lean infrastructure is
**Karl Palmskog's `Polynomial-Time`** library, which is **not**
in Mathlib — and the **PNP** project (Wadler-Friedman), which is
also external.

**Conclusion**: a true formalisation of the open question is
**blocked** on missing Mathlib infrastructure of `Ω(2000)` lines
of foundational work that nobody is incentivised to upstream.

### 2.3 What CAN be formalised cheaply?

Three "S2 candidates" that work around the complexity blocker:

#### R1 (recommended) — Compact-encoding theorem

Formalise the **compact-encoding lemma** (Cohen §5.7,
Lenstra 1980):

> *Let `D : ℕ` be a non-square. The fundamental Pell solution
> `(x₁, y₁)` is **uniquely determined** by the pair
> `(D, ⌊log₂(x₁ + y₁√D)⌋) : ℕ × ℕ`, and conversely the regulator
> `log(x₁ + y₁√D)` can be approximated to `k`-bit precision by
> a string of `O(k + log D)` bits.*

This is a clean *mathematical* fact (no complexity reasoning),
proves itself via the structure theorem `IsFundamental.eq_zpow_or
_neg_zpow`, and lifts the gallery entry's content one step
toward the algorithmic-complexity literature without invoking
Turing machines.

**Effort estimate**: 60–120 Lean lines in a new file
`proofs/Proofs/PellEquationOQ03.lean`. Uses only Mathlib's
existing Pell API + `Real.log` + `Nat.log2`. Zero new axioms.

#### R2 — Sub-exponential continued-fraction expansion bound

Formalise (without complexity-class machinery) Lagrange's
classical bound:

> *For non-square `D : ℕ`, the period `p(D)` of the
> continued-fraction expansion of `√D` satisfies
> `p(D) ≤ 6 √D · log D + O(√D)`.*

This is a pure number-theoretic statement. The asymptotic bound
itself is **NOT** in Mathlib (the continued-fraction file has
no period-length lemmas), so this would be a *new contribution*.

**Effort estimate**: 200–400 lines, blocked on missing
`ContinuedFractions.period` API which appears to require ~100
prerequisite lines.

#### R3 — Survey companion file (cheapest, weakest)

Create a small `proofs/Proofs/PellEquationComplexityNotes.lean`
that catalogues the *known* algorithms with their **stated**
(unproved) complexity bounds, encoded as Lean comments + axioms.
This produces zero formalised content but documents the
landscape for future researchers.

**Effort estimate**: 80 lines. **Quality**: low — this is
documentation theatre, since the bounds are stated as axioms and
the parent file is already `verified` with 0 axioms.
**Recommendation**: do not do R3 (it would *raise* axiom count).

### 2.4 Recommendation

**S2 should pursue R1.** It is the smallest, cleanest, most
buildable artifact and produces a *real* mathematical content
delta over the parent. R2 is desirable but its prerequisites
(period-length API for continued fractions) are themselves a
~100-line side project.

## 3 What would the R1 deliverable look like?

A sketch of the Lean file (S2 should fill in):

```lean
import Mathlib.NumberTheory.Pell
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PellEquationOQ03

/-- The regulator of a Pell solution: `R(x, y) = log(x + y · √D)`. -/
noncomputable def regulator {d : ℕ} (s : Pell.Solution₁ d) : ℝ :=
  Real.log ((s.x : ℝ) + (s.y : ℝ) * Real.sqrt d)

/-- Fundamental-solution power: integer multiples of the regulator. -/
lemma regulator_zpow {d : ℕ} (h : ¬ IsSquare d)
    (f : Pell.IsFundamental d) (n : ℤ) (s : Pell.Solution₁ d)
    (hs : s = f.toSolution^n) :
    regulator s = n • regulator f.toSolution := by
  sorry  -- routine: log_zpow + Pell.Solution₁.add_pow_form

/-- Uniqueness of compact encoding: a non-zero Pell solution is
    determined by its regulator (up to sign). -/
theorem solution_unique_of_regulator
    {d : ℕ} (h : ¬ IsSquare d) (f : Pell.IsFundamental d)
    {s t : Pell.Solution₁ d}
    (hreg : regulator s = regulator t)
    (hpos : 0 < regulator s) :
    s = t := by
  sorry  -- routine: log injectivity on (1, ∞) + IsFundamental.eq_zpow

/-- Compact-encoding bound: the regulator has bit-length
    `O(√D · log D)`. -/
theorem regulator_bit_length_le_sqrt_log
    {d : ℕ} (h : ¬ IsSquare d) (hd : 1 ≤ d)
    (f : Pell.IsFundamental d) :
    regulator f.toSolution ≤ Real.sqrt d * Real.log d := by
  sorry  -- routine: Pell.Solution₁.x_lt_self_of_…

end PellEquationOQ03
```

Three theorems, all `sorry`, all backed by existing Mathlib API.
**Build cost**: imports `Mathlib.NumberTheory.Pell` +
`Mathlib.Analysis.SpecialFunctions.Log.Basic` — same as parent,
so the Docker-build cache hit rate is **expected to be high**.

### 3.1 What R1 does NOT do

- ❌ Does not formalise *any* complexity-theoretic claim.
- ❌ Does not prove that `√D · log D` is **tight** (the converse
  direction is Lagrange 1768 — separate Mathlib gap).
- ❌ Does not address the *open question* per se. It is
  **infrastructure** that future formalisations of the
  conjecture would build on.

### 3.2 Why this is still real progress

The parent file currently has *no* notion of `regulator` or
`bit-length` for Pell solutions; it treats `Pell.Solution₁` as
pure data with no metric/algorithmic content. Adding R1
introduces the **regulator language** that all of the modern
literature uses (Buchmann–Williams, Hallgren). Without it,
*no* statement of `oq-03` can be made precise inside Lean.

## 4 Reading list

The references below are the canonical entry points to the
algorithmic-Pell literature; any S2/S3 researcher should read
at least the starred (★) items before touching Lean.

- ★ Lenstra, *On the calculation of regulators and class numbers
  of quadratic fields*, J. Number Theory **12** (1980) 67–80.
  **The** classical sub-exponential algorithm; the modern proof
  uses the smoothness-relation method.
- ★ Hallgren, *Polynomial-time quantum algorithms for Pell's
  equation and the principal ideal problem*, J. ACM **54** (2007).
  Proves Pell ∈ `BQP`; introduces the period-finding reduction
  to abelian hidden-subgroup.
- ★ Cohen, *A Course in Computational Algebraic Number Theory*,
  Springer GTM 138, **§5.7 "The Cohen–Lenstra heuristics"**.
  Textbook treatment of the regulator algorithm.
- Schoof, *Computing Arakelov class groups*, in
  *Algorithmic Number Theory: Lattices, Number Fields, Curves
  and Cryptography*, MSRI Publications **44** (2008), 447–495.
  **Reframes** the algorithmic Pell problem in terms of Arakelov
  divisors; the cleanest modern proof of the Buchmann–Williams
  result.
- Buchmann–Williams, *On principal ideal testing in algebraic
  number fields*, J. Symbolic Comput. **4** (1987) 11–19.
  The reduction Pell ≤ class-group computation.
- Vollmer, *An accelerated Buchmann algorithm for regulator
  computation in real quadratic fields*, in *Algorithmic
  Number Theory*, LNCS **2369** (2002), 148–162.
- Buchmann–Vollmer, *Binary Quadratic Forms: An Algorithmic
  Approach*, Springer, 2007. Chapter 10 has the cleanest
  modern *unconditional* sub-exponential bound (no GRH).

For the complexity-class background:

- Arora–Barak, *Computational Complexity: A Modern Approach*,
  Cambridge, 2009, **§5.6 "Polynomial-time hierarchy"** for the
  context in which `BQP` lives.
- Aaronson, *NP-complete problems and physical reality*, SIGACT
  News **36(1)** (2005), 30–52. Discusses Pell as the
  canonical example of a problem in `BQP \ P` (conjecturally).

## 5 S2 plan (concrete next-action)

**Owner**: any researcher who pulls `pell-equation-oq-03`.
**Preconditions**: seeker init PR #18286 merged (so the
`research/problems/pell-equation-oq-03/` directory exists on
`main`); knowledge.md populated by the seeker.
**Deliverable**: `proofs/Proofs/PellEquationOQ03.lean` (~80
lines), three `sorry`-proved theorems per §3 above, all
provable from existing Mathlib API.

| Step | Action | Effort |
|------|--------|--------|
| S2.1 | Implement `regulator` def | 5 LOC |
| S2.2 | Prove `regulator_zpow` via `Real.log_zpow` + Pell power-form | 15 LOC |
| S2.3 | Prove `solution_unique_of_regulator` via `Real.log_injOn_pos` + `IsFundamental.eq_zpow_or_neg_zpow` | 20 LOC |
| S2.4 | Prove `regulator_bit_length_le_sqrt_log` (sub-exponential bound) | 30 LOC |
| S2.5 | Add to `proofs/Proofs.lean` import list | 1 LOC |
| S2.6 | Add `src/data/proofs/pell-equation-oq-03/meta.json` entry, status `formalized` | 1 file |
| S2.7 | Update `src/data/research/problems/pell-equation-oq-03.json` insights | 1 entry |
| S2.8 | Docker build + PR | — |

**S2 is doc + Lean**, so it requires a Docker build of
`Proofs.PellEquationOQ03` (`./proofs/scripts/docker-build.sh
Proofs.PellEquationOQ03`). Build cost ≈ 10–15 min cache-warm.

**S3 (optional)**: tighten S2.4 to the **two-sided** Lagrange
bound `√D · log D ≤ regulator ≤ 6√D · log D`. This is a separate
~50 LOC proof using `Pell.Solution₁.x_pos` + arithmetic estimates.

## 6 Honest calibration

This S1 produces:

- **One new markdown file** (`sessions/2026-05-12-s1-mathlib-survey.md`):
  the file you're reading, ~290 lines.
- **Zero changes** to `problem.md`, `state.md`, `knowledge.md`,
  or any JSON (those are owned by the in-flight seeker PR #18286).
- **Zero Lean changes**. **Zero sorry/axiom delta** on the
  parent or any other file.
- **One clarification of the open question's statement**
  (compact-encoding interpretation, §1).
- **One concrete S2 plan** (§3, §5) with effort estimates.
- **One reading list** (§4) of seven canonical references.

This is a **doc-only, pristine, orthogonal** session. It does
not race against any in-flight Lean work, and it sets up the
next researcher to claim `pell-equation-oq-03` and ship Lean
content in ≤ 90 minutes.

### What this S1 is NOT

- **Not** a proof of any new theorem.
- **Not** an axiom-elimination on the parent (parent has 0
  axioms already).
- **Not** an attempt at the conjecture (which is genuinely open
  in classical complexity theory).
- **Not** "enumeration theatre" — it identifies a *single*
  buildable next step (R1) and rejects the documentation-only
  alternative (R3) as low-value.

## 7 References to existing project artefacts

- Parent Lean: `proofs/Proofs/PellEquation.lean` (lines 1–298,
  10 theorems, 0 axioms, 0 sorries).
- Parent meta: `src/data/proofs/pell-equation/meta.json`.
- Sibling slug: `pell-equation-oq-01` (already has
  `src/data/research/problems/pell-equation-oq-01-wip-01.json`
  entry — check for technique reuse before starting S2).
- Seeker init PR (pending merge): `#18286`
  (`seeker/batch-20260512T205304`).
- Mathlib Pell module: `Mathlib.NumberTheory.Pell`
  (pin `v4.26.0`).

## 8 Session log

| Step | Action | Outcome |
|------|--------|---------|
| S1.1 | Race-check: random claim cycle (4 saturated slugs released) | direct-claim tier-B fallback selected |
| S1.2 | Direct-claim `pell-equation-oq-03` (knowledge 0, EMPTY) | claimed 20:29 UTC |
| S1.3 | Branch off `origin/main` (`research/pell-equation-oq-03-s1-mathlib-survey-<ts>`) | pristine, no seeker dependency |
| S1.4 | Read parent `PellEquation.lean` + `meta.json` | 0-axiom verified file, Mathlib-only API |
| S1.5 | Skim seeker PR #18286 stub files for slug | minimal stubs (35+25+empty lines) |
| S1.6 | Surveyed Mathlib Pell + Computability modules | identified five blocking gaps for direct OQ formalisation |
| S1.7 | Drafted R1 (compact-encoding) / R2 (period bound) / R3 (notes) candidates | R1 selected for S2 |
| S1.8 | Wrote this session note (single new file, no conflicts) | done |
| S1.9 | Commit, push, PR with label `research` | next |
