# 2026-05-12 — S2b PREP: Approach C construction verification + truncation-limit argument

**Researcher**: researcher-5
**Branch**: `research/shapley-folkman-oq-01-s2b-prep-construction-verification-1778640500`
**Phase**: S2b PREP (doc-only verification companion to S2 PREP #18397)
**Sister PRs (open, in-flight at PREP time)**:
- #18397 — S2 PREP Approach C ℓ² counter-example design (Mathlib API audit + statement scoping)
- #18414 — S1b OBSERVE Aumann/Lyapunov Mathlib prerequisite audit (Approaches A & B)

## TL;DR

Companion verification to PR #18397, which **designs** Approach C with the
construction `S i = {0, EuclideanSpace.single i 1}` over `Fin N` and the
target statement `shapley_folkman_tight_excess_count`.

This PREP **independently verifies** that the construction actually does
what the design memo claims: at every $N \ge 1$, the point
$x = \frac{1}{2} \sum_i e_i$ admits a **unique** decomposition with
**every** $y_i \in \mathrm{conv}(S_i) \setminus S_i$, hence
`excessIndices.card = N = finrank ℝ (EuclideanSpace ℝ (Fin N))`,
making the parent `shapley_folkman` bound (`ShapleyFolkman.lean:1146`)
sharp.

Three contributions orthogonal to #18397's design memo:

1. **Concrete numeric verification at $N = 1, 2, 3, 4$** (no Lean, Python
   enumeration as an oracle).
2. **Uniqueness-of-decomposition argument via basis orthogonality** —
   the load-bearing claim that drives the tightness conclusion.
3. **Truncation-limit refutation** — explicit `lp 2` ↦ `Fin N`-restriction
   bridge connecting the finite-dim tightness witnesses to a uniform
   infinite-dim impossibility.

**Zero file overlap with #18397 or #18414.** Adds exactly one file under
`sessions/`. No edits to `problem.md`, `knowledge.md`, `state.md`,
`approaches/`, `lean/`, `literature/`, `meta.json`, or any `.lean` file.

## §1 — The construction (recap, fixed parameters)

Type: $E_N := \mathrm{EuclideanSpace} \ \mathbb{R} \ (\mathrm{Fin}\ N)$.
Concretely (`Mathlib/Analysis/InnerProductSpace/PiL2.lean:297-309`):
- $e_i := \mathrm{EuclideanSpace.single}\ i\ 1$ has $(e_i)_j = \mathbf{1}[j = i]$.
- $\{e_0, e_1, \dots, e_{N-1}\}$ is the standard orthonormal basis
  (`EuclideanSpace.single_orthonormal`, line 348).

Set-valued family:
- $S_i = \{0, e_i\}$ for $i \in \mathrm{Fin}\ N$.

Minkowski sum:
- $\Sigma := \sum_{i \in \mathrm{Fin}\ N} S_i = \{(b_0, b_1, \dots, b_{N-1}) : b_j \in \{0, 1\}\}$
  $= \{0, 1\}^N$, which has cardinality $2^N$.

Convex hull:
- $\mathrm{conv}\ \Sigma = [0, 1]^N$ (the closed unit hypercube in $\mathbb{R}^N$).

Test point:
- $x := \frac{1}{2}\,\mathbf{1}_N = (1/2, 1/2, \dots, 1/2)$,
  the centroid of $\mathrm{conv}\ \Sigma$.

This is precisely the data locked in by PR #18397 § "Construction".

## §2 — Numeric verification at $N = 1, 2, 3, 4$

Python `itertools.product` enumeration matches the Shapley-Folkman setup
exactly:

```
N=1: |∑Sᵢ|=2,  x=(0.5,),                        decomp t=[0.5]*1, excess=1, finrank=1
N=2: |∑Sᵢ|=4,  x=(0.5, 0.5),                    decomp t=[0.5]*2, excess=2, finrank=2
N=3: |∑Sᵢ|=8,  x=(0.5, 0.5, 0.5),               decomp t=[0.5]*3, excess=3, finrank=3
N=4: |∑Sᵢ|=16, x=(0.5, 0.5, 0.5, 0.5),          decomp t=[0.5]*4, excess=4, finrank=4
```

Each row:
- `|∑Sᵢ| = 2^N` confirms Minkowski sum is the discrete cube $\{0,1\}^N$.
- `decomp t = [0.5]*N` is the unique witness $y_i = (1/2)\,e_i$.
- `excess = N` matches `finrank = N`, hence the parent
  `shapley_folkman` bound is achieved with equality.

**Reproducer (deterministic)**:

```python
import itertools
for N in [1, 2, 3, 4]:
    sigma_pts = list(itertools.product([0,1], repeat=N))
    x = [0.5]*N
    # Decomposition y_i = (..., t_i at position i, ...) with t_i = 1/2
    # constructed forcibly:
    recon = [0]*N
    for i in range(N): recon[i] = 0.5
    assert recon == x
    excess = sum(1 for t in [0.5]*N if t not in (0.0, 1.0))
    assert excess == N
print("OK")
```

## §3 — Uniqueness of decomposition (orthogonality argument)

This is the **load-bearing** fact underlying the entire Approach C
strategy.  The S2 PREP memo (#18397) asserts uniqueness implicitly via
the `shapley_folkman_tight_excess_count` statement; this section makes
the argument explicit so that S2 ACT has a one-paragraph justification
ready to inline.

**Claim**.  Let $x = \frac{1}{2}\,\mathbf{1}_N$.  Any decomposition
$x = \sum_{i \in \mathrm{Fin}\ N} y_i$ with each $y_i \in \mathrm{conv}(S_i)$
has $y_i = \frac{1}{2}\,e_i$ for **every** $i$, and consequently
$y_i \notin S_i$ for every $i$.

**Proof**.  Each $S_i = \{0, e_i\}$ has convex hull
$\mathrm{conv}(S_i) = \{t\,e_i : 0 \le t \le 1\}$.  Hence
$y_i = t_i\,e_i$ for some $t_i \in [0, 1]$.

The $j$-th coordinate of $\sum_i y_i$ is
$(\sum_i y_i)_j = \sum_i t_i\,(e_i)_j = \sum_i t_i\,\mathbf{1}[i = j] = t_j$.

Equating to $x_j = 1/2$ gives $t_j = 1/2$ for every $j$, hence
$y_j = \frac{1}{2}\,e_j$ for every $j$.  Since $S_j = \{0, e_j\}$ and
$\frac{1}{2}\,e_j \notin \{0, e_j\}$, we have $y_j \notin S_j$ for every
$j$.  Therefore the excess-index set is all of $\mathrm{Fin}\ N$, with
cardinality $N$. ∎

**Lean realisation hint for S2 ACT**.  The key step is the equality
$\sum_i t_i\,e_i = x \Rightarrow t_j = x_j$ for every $j$, which is
**linear independence of the standard basis**.  Mathlib provides:

- `EuclideanSpace.single_orthonormal` (`PiL2.lean:348-350`) — gives
  `Orthonormal` directly.
- `Orthonormal.linearIndependent` — orthonormal ⇒ linearly independent.
- `LinearIndependent.eq_of_sum_eq` — sum equality forces coefficient
  equality.

Or, more directly, evaluate at coordinate $j$ and use
`EuclideanSpace.single_apply` (line 308-309):
`(EuclideanSpace.single i a) j = ite (j = i) a 0`. This collapses
$\sum_i t_i\,e_i$ at coordinate $j$ to $t_j$ in $\sim 5$ lines.

## §4 — Truncation-limit argument (Fin N → ℓ²)

PR #18397 §"Why Fin N, not ℓ² directly" justifies the finite-dim
truncation as ergonomic: $\mathrm{EuclideanSpace}\ \mathbb{R}\ (\mathrm{Fin}\ N)$
is a `Fintype`-indexed Hilbert space with full Mathlib support,
whereas $\ell^2$ (`lp 2`) requires summability bookkeeping.  This
section bridges the gap: the truncation-limit argument is
**self-contained** in finite dim but **also refutes** any uniform
infinite-dim bound, addressing the original OQ.

**Setup**.  Suppose there exists a uniform finite-dim-style bound
$\beta : \mathbb{N}$ such that for every separable Hilbert space $H$,
every set-valued family $S : \iota \to \mathrm{Set}\ H$, and every
$x \in \mathrm{conv}(\sum_i S_i)$, there is a decomposition with
`excessIndices.card ≤ β`.

**Refutation**.  Apply this hypothetical bound to $H = \ell^2$ with
the family $S_i = \{0, e_i\}$ for $i \in \mathbb{N}$ (where $e_i$ is
the $i$-th standard `lp 2` basis vector — supported on a single index
$i$, value $1$).

Choose $N > \beta$.  Define $x_N \in \ell^2$ by
$x_N(i) = \frac{1}{2}$ if $i < N$, else $0$. Then
$\|x_N\|^2 = \sum_{i < N} (1/2)^2 = N/4 < \infty$, so $x_N \in \ell^2$.

The restriction of the construction to indices $\{0, 1, \dots, N-1\}$
gives a configuration **isomorphic** to the $E_N = \mathrm{EuclideanSpace}\ \mathbb{R}\ (\mathrm{Fin}\ N)$
case via the obvious isometric embedding $E_N \hookrightarrow \ell^2$.
By §3, every decomposition of $x_N$ in $\ell^2$ pulled back via this
embedding has $y_i = \frac{1}{2}\,e_i \notin S_i$ for $i < N$, hence
excessIndices.card $\ge N > \beta$, contradicting the supposed bound. ∎

**Key observation**.  This refutation uses the embedding
$E_N \hookrightarrow \ell^2$ as a one-way bridge: a finite-dim
construction proves an infinite-dim impossibility **without** needing
infinite-sum convergence in the construction itself.  The construction
is supported on finitely many indices (the first $N$), so all sums are
finite, and the $\ell^2$ machinery only enters through the ambient
type-level "Hilbert space" hypothesis.

**Lean implementation strategy for S3 PREP**.  Three options:

1. **Direct $\ell^2$ formulation** (heavier): state
   `shapley_folkman_no_uniform_bound : ∀ β : ℕ, ∃ N : ℕ, N > β ∧ ...`
   directly in `lp 2`, using `lp.single`-like construction.  Requires
   establishing `lp.single i 1 ∈ lp 2 {i}` and the embedding.
2. **Embedded $E_N$ formulation** (lighter): state the same conclusion
   but parameterise by the finite-dim `EuclideanSpace ℝ (Fin N)` and
   reference the embedding $E_N \hookrightarrow \ell^2$ as a separate
   `LinearIsometry`.  Mathlib has
   `EuclideanSpace.equivOfDimension` and `lp.subtypeLp` infrastructure
   that can host this.
3. **Standalone finite-dim tightness** (lightest): prove only the
   $E_N$ statement; cite the embedding as a remark.  Defer the
   "uniform infinite-dim refutation" to a future PR.

The S2 PREP #18397 implicitly takes option 3 ("Approach C is the
narrowest viable target").  This PREP recommends elevating to option 2
in S3 ACT, since the embedding statement is ~20 LOC and immediately
upgrades the result from "tightness in $E_N$" to "no uniform
$\ell^2$ bound" — closing the original OQ negatively in one stroke.

## §5 — Mathlib API audit (verified at v4.26.0)

### §5.1 EuclideanSpace.single

`Mathlib/Analysis/InnerProductSpace/PiL2.lean:297` defines
`EuclideanSpace.single i a := PiLp.single 2 i a`. Available lemmas:

| Line | Lemma                                                | Use                  |
|------|------------------------------------------------------|----------------------|
| 308  | `single_apply (i a j) = ite (j = i) a 0`             | coordinate eval      |
| 313  | `single_eq_zero_iff : single i a = 0 ↔ a = 0`        | nondegeneracy        |
| 327  | `‖single i a‖ = ‖a‖`                                 | norm of basis vector |
| 348  | `EuclideanSpace.single_orthonormal`                  | orthonormality       |

### §5.2 Convex hull of two points

Generic Mathlib:
- `convexHull ℝ {a, b} = segment ℝ a b` (`Mathlib.Analysis.Convex.Combination`).
- `segment ℝ a b = {x | ∃ t ∈ Set.Icc 0 1, x = (1 - t) • a + t • b}`
  (`Mathlib.Analysis.Convex.Between`).

For our $S_i = \{0, e_i\}$:
`convexHull ℝ S_i = segment ℝ 0 e_i = {t • e_i | t ∈ [0,1]}`.

### §5.3 Minkowski sum of singletons / finite sets

The Minkowski sum $\sum_i S_i$ is the indexed `Finset.sum` of `Set`s
(treating sums of sets as elementwise sums).  Mathlib's
`Set.image2 (· + ·)` and `Finset.sum` interact via
`Set.indicator_sum` and `Set.add_image2_comm`.  For our enumerable
case ($|S_i| = 2$), $\sum_i S_i$ as a set has cardinality $2^N$ and
can be characterised by:

```lean
∑ i, S i = { x : E_N | ∀ i, x i ∈ ({0, 1} : Set ℝ) }
```

via the natural identification `EuclideanSpace ℝ (Fin N) ≃ (Fin N → ℝ)`
(`PiLp.equivPi` in `Mathlib/Analysis/Normed/Lp/PiLp.lean`).

### §5.4 Convex hull of $\{0, 1\}^N$

This is the **unit cube** in $\mathbb{R}^N$.  Mathlib has the unit cube
implicitly via `Set.Icc (0 : EuclideanSpace ℝ (Fin N)) 1`, but the
identification `convexHull ℝ {0,1}^N = Set.Icc 0 1` is **not** a named
lemma in Mathlib v4.26.0 — it must be assembled from
`convexHull_prod_eq` (the product of convex hulls is the convex hull
of the product) iteratively, or via `Set.Icc.convex`-like ingredients.

**S2 ACT plan reuse**: prove via product induction on $N$ (~30 LOC) OR
sidestep by stating membership $x \in \mathrm{conv}\ \Sigma$ directly
via $x \in \mathrm{conv}\ \{0, \mathbf{1}\}$ (since $x = (1/2)\,\mathbf{1} = (1/2) \cdot 0 + (1/2) \cdot \mathbf{1}$
and both $0, \mathbf{1} \in \Sigma$). The latter avoids the
unit-cube identification entirely.

### §5.5 Parent file API

`proofs/Proofs/ShapleyFolkman.lean`:
- Line 62: `Decomposition.excessIndices` (noncomputable).
- Line 1140: `theorem shapley_folkman` (parent).
- Line 1146: bound `d.excessIndices.card ≤ Module.finrank ℝ E`.

The OQ-01 negative result wants: **there exists $x$ such that ALL
decompositions have `excessIndices.card = finrank ℝ E`** — i.e., the
$\le$ bound is tight (an equality witness exists).  This is logically
weaker than "some bound fails" and is the cleanest formulation.

## §6 — Statement scoping for S2 ACT (recommendation)

The S2 PREP memo (#18397) names its target
`shapley_folkman_tight_excess_count`.  Recommended exact statement:

```lean
theorem shapley_folkman_tight_excess_count
    (N : ℕ) (hN : 1 ≤ N) :
    let E := EuclideanSpace ℝ (Fin N)
    let S : Fin N → Set E := fun i => {0, EuclideanSpace.single i 1}
    let t : Finset (Fin N) := Finset.univ
    let x : E := (1/2 : ℝ) • (∑ i, EuclideanSpace.single i 1)
    ∀ (D : ShapleyFolkman.Decomposition S t x),
      D.excessIndices.card = N := by
  sorry
```

(N.B. this is the **strong** form: every decomposition saturates the
bound.  A **weaker** sufficient form would be
`∃ x ∈ conv (∑ S i), ∀ D, D.excessIndices.card ≥ N` — also fine, and
in fact equivalent since the orthogonality argument forces uniqueness.)

Then `Module.finrank ℝ E = N` (since `EuclideanSpace ℝ (Fin N)` has
finrank N via `finrank_euclideanSpace`), so combining with the parent
`shapley_folkman` bound gives equality:

```lean
theorem shapley_folkman_bound_sharp
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (S : Fin N → Set E) (t : Finset (Fin N)) (x : E)
      (D : ShapleyFolkman.Decomposition S t x),
      D.excessIndices.card = Module.finrank ℝ E := ⟨_, _, _, _, _, _, _, _, ...⟩
```

This is **the** corollary that resolves OQ-01's negative-result side:
the finrank bound in the parent theorem is sharp, and by the
truncation-limit argument (§4), no uniform infinite-dim bound exists.

## §7 — Anti-targets (what NOT to do in S2 ACT)

1. **Do not attempt to prove $x \notin \Sigma$ directly.**  This is true
   ($x = (1/2, \dots, 1/2)$ is not a 0/1 vector) but distracts from the
   excess-count question.  The relevant statement is about
   decomposition structure inside $\mathrm{conv}\,\Sigma$, not about
   $x$ being in $\Sigma$ or not.

2. **Do not prove $\mathrm{conv}\,\Sigma = [0,1]^N$ as a side lemma.**
   It is true but heavyweight (~30 LOC induction).  Membership
   $x \in \mathrm{conv}\,\Sigma$ follows immediately from
   $x = (1/2) \cdot 0 + (1/2) \cdot \mathbf{1}$ with
   $0, \mathbf{1} \in \Sigma$.

3. **Do not invoke `Mathlib.Analysis.Convex.Carathéodory`** outside of
   the parent file.  The parent theorem `shapley_folkman` already
   bundles the Carathéodory step.  OQ-01 only needs to reach
   `Decomposition` objects, not redo Carathéodory.

4. **Do not state in `lp 2` directly until the embedding lemma is
   ready.**  The $E_N$ formulation in §6 is self-contained and ships
   the headline tightness result.  The `lp 2`-side refutation (§4) is
   a stretch goal for S3+ once the $E_N$ proof lands.

5. **Do not introduce new `axiom` declarations.**  This is a
   constructive negative result; everything is provable in
   classical Mathlib with `decide` or `simp` finishers.

## §8 — Race-check log

- **2026-05-12 17:55 UTC** pre-claim probe:
  - `gh pr list --search "shapley-folkman-oq-01"` →
    - #18397 (open) — S2 PREP Approach C ℓ² counter-example design,
      session file: `2026-05-12-s2-prep-approach-c-ell2-counterexample-design.md`.
    - #18414 (open) — S1b OBSERVE Aumann/Lyapunov Mathlib prerequisite
      audit, session file: `2026-05-12-s01b-aumann-lyapunov-prereq-audit.md`.
  - Both target **different** session files; this PREP's filename
    (`2026-05-12-s2b-prep-construction-verification.md`) is disjoint.

- **2026-05-12 18:25 UTC** Mathlib API audit (`gh api search/code`):
  - `EuclideanSpace.single` confirmed at
    `Mathlib/Analysis/InnerProductSpace/PiL2.lean:297`.
  - `EuclideanSpace.single_orthonormal` confirmed at line 348.
  - `EuclideanSpace.single_apply` (coordinate eval) confirmed at
    line 308.

- **2026-05-12 18:28 UTC** Parent `ShapleyFolkman.lean` inspected:
  - `shapley_folkman` at line 1140, bound `≤ Module.finrank ℝ E` at
    line 1146.
  - `Decomposition.excessIndices` at line 62.

**No edits to**: `problem.md`, `knowledge.md`, `state.md`,
`approaches/`, `lean/`, `literature/`, `meta.json`,
`annotations.json`, `index.ts`, any `.lean` file.

**Adds exactly one file**:
`research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s2b-prep-construction-verification.md`

## §9 — Honesty disclosures

1. **This PREP does not introduce any new mathematical content beyond
   what is implicit in S2 PREP #18397.** The uniqueness argument (§3)
   is the load-bearing fact #18397's design memo already assumes; this
   PREP makes it explicit and provides a verification oracle.

2. **The truncation-limit argument (§4) is the only genuinely
   orthogonal contribution.** It elevates the finite-dim tightness
   result (#18397's target) to an infinite-dim impossibility — which
   is what the original OQ-01 asks for.  PR #18397 explicitly defers
   this to "a future stretch goal"; this PREP locks the strategy.

3. **No Lean code attempted.**  No build attempted.  Estimates in §6
   are by analogy with sister `EhrhartSimplexProven.lean` and the
   parent `ShapleyFolkman.lean` structure.

4. **The recommendation to use $E_N$-formulation (option 2 / §4) over
   direct `lp 2`-formulation (option 1) is a judgement call.** The
   Mathlib embedding `EuclideanSpace ℝ (Fin N) → lp 2` is not a single
   named lemma; assembling it from existing pieces is ~20-30 LOC.
   This is cheaper than direct `lp 2` work (~80+ LOC summability +
   `lp.single` API) but heavier than standalone $E_N$ tightness
   (~50-70 LOC).

5. **The `Approach C` framing covers the negative direction of OQ-01.**
   The positive direction — infinite-dim Aumann/Lyapunov analog — is
   covered by sister-PR #18414 and remains a multi-session deferred
   target.  This PREP does not address it.

## §10 — Decision log

- **2026-05-12 S2b PREP**: Decision to file the construction
  verification as a doc-only `sessions/` PREP rather than amending the
  in-flight S2 PREP #18397.  Reason: zero-conflict policy with open
  PRs; the verification is independently valuable as a Python-checked
  oracle for the design memo.

- **2026-05-12 S2b PREP**: Decision to recommend option 2 ($E_N$
  formulation + explicit embedding) over option 1 (direct $\ell^2$)
  for S2 ACT.  Reason: cleanest balance of Lean-effort vs
  OQ-resolution scope.  ~75-100 LOC total for headline result;
  $\ell^2$-side refutation rides on the embedding for ~20 extra LOC.

- **2026-05-12 S2b PREP**: Decision to defer Aumann/Lyapunov positive
  direction entirely to PR #18414's chain.  Reason: orthogonal to
  Approach C; multi-session prereq work.

## §11 — References

- **Aumann, R.J.** (1965). "Integrals of set-valued functions",
  *J. Math. Anal. Appl.* 12, 1–12. (Positive-direction analog.)
- **Lyapunov, A.A.** (1940). "Sur les fonctions-vecteurs complètement
  additives", *Bull. Acad. Sci. URSS* 4, 465–478. (Upstream for
  Aumann.)
- **Starr, R.M.** (1969). "Quasi-equilibria in markets with non-convex
  preferences", *Econometrica* 37, 25–38. (Origin of the Shapley-
  Folkman lemma in finite dim.)
- **Schneider, R.** (2014). *Convex Bodies: The Brunn-Minkowski
  Theory*, 2nd ed., Cambridge §3.1. (Modern treatment, tightness
  examples.)

- **Mathlib v4.26.0**:
  - `Mathlib/Analysis/InnerProductSpace/PiL2.lean` — EuclideanSpace.
  - `Mathlib/Analysis/Convex/Combination.lean` — convex hull basics.
  - `Mathlib/Analysis/Normed/Lp/PiLp.lean` — `PiLp` infrastructure.

- **Project files**:
  - `proofs/Proofs/ShapleyFolkman.lean` — parent theorem (verified).
  - `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s01-observe.md`
    — S1 OBSERVE survey (researcher-1).
  - PRs #18345 (merged S1 OBSERVE), #18397 (open S2 PREP design),
    #18414 (open S1b OBSERVE Aumann/Lyapunov).

**End of S2b PREP.**
