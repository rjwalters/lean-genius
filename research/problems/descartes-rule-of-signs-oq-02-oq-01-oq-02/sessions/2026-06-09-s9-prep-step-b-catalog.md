# S9 PREP — Step B of Sturm exact-count: design + bearer catalog (doc-only)

**Slug**: `descartes-rule-of-signs-oq-02-oq-01-oq-02`
**Researcher**: researcher-1
**Date**: 2026-06-09
**Phase**: S9 PREP (doc-only; design and bearer catalog for the Step B
lemma needed to discharge `sturm_exact_count_axiom`).
**Type**: Doc-only. No edits to
`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`, gallery
`meta.json`, `knowledge.md`, or `problem.md`. Edits limited to this
session log + `state.md` (S9 PREP entry + header refresh) +
`src/data/research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02.json`
(`currentState.{iteration, phase, focus, nextAction}` + `updatedAt`).
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged since S5).
**Base HEAD**: `58bdf51bc62` (current `origin/main`).

## §1 Where the slug stands

After S7 ACT (PR #21825, 2026-06-01) repaired 21 v4.26.0 build errors
and S8 STATE-SYNC (PR #22023, 2026-06-02) absorbed it, the file is
**build-clean at 3058/3058 jobs at lake-pinned SHA**:

* 513 LOC, 0 sorries, 1 local axiom (`sturm_exact_count_axiom` at line
  332-336).
* Step A complete: `sturmVariations_locally_constant` (lines 220-277,
  ~58 LOC; uses `intermediate_value_Icc` + `intermediate_value_Icc'`
  on `Set.Icc` continuity).
* §5 structural lemmas complete: `mod_eval_at_root` (line 285),
  `sturm_interior_sign_property` (line 295),
  `sturm_neighbors_opposite_at_root` (line 302).
* §6 axiomatic main theorem: `sturm_exact_count_axiom` (additive form
  `σ(a) = σ(b) + #roots(a,b]`) + the derived `sturm_exact_count`
  theorem.
* §7 corollaries: `sturm_no_roots`, `sturm_unique_root`,
  `sturm_two_roots`, `sturm_count_le_variations`,
  `sturmVariations_antitone` — all derived from the axiom.

**Goal of the multi-step program** (per `sturm_exact_count_axiom`'s
docstring lines 326-329): discharge the axiom by proving three claims
explicitly:

1. **Step A** — `σ_p` is piecewise constant on subintervals avoiding
   zeros of any Sturm term. **DONE** (S5 ACT, PR #21477; survived S7
   build-repair).
2. **Step B** — `σ_p` decreases by exactly 1 as `x` passes through
   each real root of `p`. **Open. This PREP designs it.**
3. **Step C** — `σ_p` is unchanged as `x` passes through roots of
   interior Sturm terms. **Open.**

After Steps B and C land, the axiom is discharged by a transition
argument: between `a` and `b`, the only places `σ_p` changes are at
zeros of Sturm-sequence members; each such zero is either a root of
`p` (Step B: −1) or a root of an interior Sturm term (Step C: no
change).

## §2 Step B — statement design

### 2.1 The proposition

The right Lean signature for Step B follows the same pattern as Step
A (closed-interval, post-S7 cleanup form):

```lean
/-- **Step B** of Sturm's theorem. If `r ∈ (a, b)` is a root of `p`
    (with `p(r) = 0`, `p ≠ 0`, `p` squarefree), and the interval
    `[a, b]` contains **only** `r` as a zero of any Sturm-sequence
    member, then the Sturm sign-variation count drops by exactly 1
    across `r`:

      `σ_p(a) = σ_p(b) + 1`

    Argument sketch: by squarefreeness, `p'(r) ≠ 0` (so `p` and `p'`
    have opposite signs near `r` — one sign on `(a, r)` and the
    opposite on `(r, b)`). The first two Sturm terms `[p, p']`
    contribute one sign-change near `r` on one side and none on the
    other; all later Sturm terms have constant sign across the
    interval (by Step A applied to the sub-intervals avoiding the
    isolated root). The net change in the sign-variation count is
    exactly −1.
-/
private lemma sturmVariations_step_through_root_of_p
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    {a b r : ℝ} (har : a < r) (hrb : r < b)
    (hp_root : p.eval r = 0)
    (h_only_root_of_p : ∀ s ∈ Set.Icc a b, p.eval s = 0 → s = r)
    (h_no_zero_else : ∀ q ∈ (sturmSeq p).tail, ∀ z ∈ Set.Icc a b,
                        q.eval z ≠ 0) :
    sturmVariations p a = sturmVariations p b + 1
```

**Key hypotheses notation**:
* `h_only_root_of_p`: `r` is the **unique** zero of `p` in `[a, b]`.
* `h_no_zero_else`: no member of `sturmSeq p` **other than `p` itself**
  vanishes on `[a, b]` (the tail begins at `p'`, the derivative).

Lighter, equivalent formulations are possible (e.g. swap `Set.Ioo a b`
for `Set.Icc` plus an `r ≠ a` / `r ≠ b` hypothesis) but the
`Set.Icc`-based form mirrors Step A's signature for easy assembly.

### 2.2 Why squarefreeness is load-bearing

Step B uses the squarefreeness hypothesis essentially. The key
consequence: `gcd(p, p') = 1` (up to scaling), so `p` and `p'` share
**no common root**; in particular, `p(r) = 0 ⇒ p'(r) ≠ 0`.

Without squarefree: `r` could be a multiple root, `p'(r) = 0` too,
and the first sign-change in the Sturm sequence's first two terms is
not the unique mechanism for the count drop.

**Mathlib bearer for the squarefree → coprime derivatives chain**:
`Polynomial.Squarefree.isCoprime_derivative` (location TBD; this is
the standard Mathlib lemma for squarefree `p` over a field) +
`IsCoprime.mul_left` / `IsCoprime.eval` family for the value at `r`.

### 2.3 Decomposition into sub-claims

The clean proof structure is to factor Step B through three named
helpers, each provable separately:

**B.1 — `p(r) = 0` ⇒ `p'(r) ≠ 0` (under squarefree p)**:
```lean
private lemma squarefree_root_has_nonzero_derivative
    {p : ℝ[X]} (hp : p ≠ 0) (hpsc : Squarefree p) {r : ℝ}
    (hpr : p.eval r = 0) : p.derivative.eval r ≠ 0
```
Sources: Mathlib's `Polynomial.Squarefree.isCoprime_derivative`
(verify name at v4.26.0) plus `IsCoprime.eval` (evaluating coprime
relation at `r`).

**B.2 — sign of `p · p'` on `(a, r)` and `(r, b)`**:
```lean
private lemma sign_p_times_deriv_around_root
    {p : ℝ[X]} (hp : p ≠ 0) (hpsc : Squarefree p) {a b r : ℝ}
    (har : a < r) (hrb : r < b)
    (hpr : p.eval r = 0)
    (h_only_root_of_p : ∀ s ∈ Set.Icc a b, p.eval s = 0 → s = r) :
    (∀ x ∈ Set.Ioo a r, p.eval x * p.derivative.eval x < 0) ∧
    (∀ x ∈ Set.Ioo r b, p.eval x * p.derivative.eval x > 0)
```

Argument: `p'(r) ≠ 0` (B.1), so `p'` has constant sign on a
neighborhood of `r`. On `(a, r)` and `(r, b)`, `p` is nonzero
(uniqueness of root); IVT applied separately to each side gives `p`'s
sign there. Then the standard "left-of-root: `p · p' < 0`; right-of-
root: `p · p' > 0`" alternation follows.

**B.3 — sign-variation count for the first two Sturm terms**:

If `p · p'` is negative at `x = a`, then the pair `[p(a), p'(a)]`
contributes 1 sign change. If `p · p'` is positive at `x = b`, then
`[p(b), p'(b)]` contributes 0 sign changes. So the first-pair
contribution drops by 1 across the root.

For the rest of the Sturm sequence (`(sturmSeq p).tail.tail`), Step A
applies on `[a, b]` (the tail of the tail has no zero on `[a, b]` by
hypothesis); their sign-pattern is constant, so they contribute the
same number of sign changes at `a` and at `b`.

```lean
private lemma sturmVariations_first_pair_decreases_at_root
    {p : ℝ[X]} (hp : p ≠ 0) (hpsc : Squarefree p) {a b r : ℝ}
    (har : a < r) (hrb : r < b)
    (hpr : p.eval r = 0)
    (h_only_root_of_p : ∀ s ∈ Set.Icc a b, p.eval s = 0 → s = r) :
    -- the contribution to σ from the prefix [p, p'] at a vs b
    countSignAlts (sign_list_prefix p a) = countSignAlts (sign_list_prefix p b) + 1
```

(Naming `sign_list_prefix p x := [sign p(x), sign p'(x)]`-ish; the
exact form follows the existing `signVariations` definition at line
95.)

**B (top-level) — assembly**:

Combine B.1 + B.2 + B.3 + Step A (on the tail of the tail) into the
full Step B statement of §2.1.

### 2.4 LOC estimate

* B.1: ~10 LOC (one bearer lookup + `IsCoprime.eval` chain).
* B.2: ~40-60 LOC (two IVT applications + the `p · p'` sign analysis,
  similar in flavor to Step A's IVT-based locally-constant proof).
* B.3: ~30-50 LOC (list-level sign-count discharge using the existing
  `countSignAlts` / `signVariations` definitions).
* Step B assembly: ~20 LOC.

**Total Step B estimate**: ~100-140 LOC across 4 named declarations.
File 513 → ~620 LOC, sorries 0 → 0 (if successful), axioms 1 → 1
(`sturm_exact_count_axiom` still pending Step C + assembly).

## §3 Mathlib bearer catalog for Step B

All bearers should be verified at lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= Mathlib v4.26.0)
before paste-ready code is shipped. **This S9 PREP does NOT do the
verification**; it lists the bearers a S10 PREP would re-pin.

| Bearer (Mathlib v4.26.0) | Module | Use |
|---|---|---|
| `Polynomial.Squarefree.isCoprime_derivative` (name TBD; the canonical squarefree-coprime-with-derivative lemma over a field) | `Mathlib/RingTheory/Polynomial/Squarefree.lean` (TBD) | B.1 (squarefree ⇒ `gcd(p, p') = 1`) |
| `IsCoprime.eval` (or `IsCoprime.mul_eval_ne_zero`) | `Mathlib/Algebra/IsCoprime.lean` or `Polynomial/Algebra/Group.lean` (TBD) | B.1 (evaluate coprime relation at `r` to get `p'(r) ≠ 0`) |
| `intermediate_value_Icc` / `intermediate_value_Icc'` | `Mathlib/Topology/Algebra/Order/IntermediateValue.lean` | B.2 (IVT for sign of `p`) — already used by Step A. |
| `Polynomial.continuousOn` (or `Polynomial.continuous` via continuous-on coercion) | `Mathlib/Analysis/Polynomial/Continuity.lean` | B.2 (polynomial continuity, already used by Step A). |
| `mul_self_pos` (or `mul_self_nonneg`) | `Mathlib/Algebra/Order/Ring/Lemmas.lean` | B.2 sign-product reasoning (already used by `sturm_neighbors_opposite_at_root` at line 305). |
| `List.countSignAlts` (or local `countSignAlts`) | local to this file (line 86) | B.3 (sign-count primitive). |
| `signVariations` | local to this file (line 95) | B.3 (sign-count primitive). |
| `sturmVariations_locally_constant` (S5 ACT result) | local to this file (line 220) | B (assembly): apply Step A to the tail of the tail. |

### 3.1 Likely bearer-name corrections at v4.26.0

The S6 AUDIT (PR #21705) identified a heavy v4.26.0 API drift on this
file (21 errors). Some squarefreeness lemmas were renamed (the S7 ACT
notes mention `Mathlib.RingTheory.Squarefree.Basic` →
`Mathlib.Algebra.Squarefree.Basic` migration). Step B's bearers may
have similar moves. A S10 PREP iteration should do the explicit
re-pin via GitHub raw at the v4.26.0 tag (researcher worktree's
`.lake/packages/mathlib/` is unusable through the `.lake` self-loop;
basel iter44 and abel-ruffini S10 PREP used GitHub raw audit
successfully).

## §4 Step C — preview (not designed this iteration)

Step C is analogous to Step B but applies at zeros of **interior**
Sturm terms (positions `1..length-2` of `sturmSeq p`). The key
mechanism: `sturm_neighbors_opposite_at_root` (line 302) shows that
when `q.eval r = 0` for an interior Sturm term `q` and the previous
term `p₀` has `p₀(r) ≠ 0`, the two neighbors of `q` have opposite
signs — so the sign-pattern around `q`'s zero is symmetric, and the
sign-variation count is unchanged.

**Cleaner statement** (preview; full design deferred to S10 PREP):

```lean
private lemma sturmVariations_step_through_interior_root
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    {a b r : ℝ} (har : a < r) (hrb : r < b)
    (h_p_nz : p.eval r ≠ 0)
    (h_some_interior_root : ∃ i, 0 < i ∧ i < (sturmSeq p).length - 1 ∧
                                ((sturmSeq p).get ⟨i, _⟩).eval r = 0)
    (h_only_root : ∀ q ∈ sturmSeq p, ∀ s ∈ Set.Icc a b,
                     q.eval s = 0 → s = r) :
    sturmVariations p a = sturmVariations p b
```

**Estimated Step C LOC**: ~80-120 LOC (smaller than Step B because
`sturm_neighbors_opposite_at_root` already does the heavy lifting in
§5 of the file).

## §5 The axiom-discharge plan

After Steps B and C land, the axiom discharge proceeds via case split
on what's between `a` and `b`:

```lean
theorem sturm_exact_count_proved
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    sturmVariations p a = sturmVariations p b + rootsInInterval p a b := by
  -- Strategy: induction on the number of zeros of any Sturm term in [a, b].
  -- Base case: no zeros ⇒ Step A ⇒ σ(a) = σ(b) ⇒ rootsInInterval = 0.
  -- Inductive step: pick the leftmost zero r ∈ (a, b]; apply Step B or C
  -- depending on whether r is a root of p or of an interior Sturm term;
  -- recurse on (r + ε, b].
  sorry  -- (assembly: ~40-70 LOC)
```

This assembly step requires picking a leftmost zero in an open
interval, which is a finite-degree-polynomial argument (each Sturm
term has finitely many roots; the union is finite; pick the min).

**Total program estimate from current state**:
* Step B: ~100-140 LOC (this PREP designed it).
* Step C: ~80-120 LOC (S10/S11 PREP will design it).
* Assembly: ~40-70 LOC (S11/S12 PREP will design it).
* **Grand total**: ~220-330 LOC across 3-4 ACT iterations to fully
  discharge the axiom. File 513 → ~750-850 LOC.

After full discharge: 0 axioms, 0 sorries, all derived corollaries
unchanged. Slug status `axiomatized → verified`.

## §6 Race-safety log

* **Pre-claim probe** (2026-06-09 ~18:00Z):
  `gh pr list --search "descartes-rule-of-signs-oq-02-oq-01-oq-02 in:title" --state open`
  → 0 open PRs on this slug.
* **Pre-edit probe**: file unchanged on `origin/main` since S7 ACT
  PR #21825 (2026-06-01T06:05Z); S8 STATE-SYNC #22023 (2026-06-02)
  touched only state.md + JSON, not the `.lean` file.
* **HEAD probe**: `origin/main` at `58bdf51bc62`; this S9 PREP
  branches from there.
* **Build state**: file build-clean at 3058 jobs per S7 ACT (2026-06-01);
  no rebuild attempted this session (researcher worktree `.lake`
  self-loop blocker; same status as basel iter44 INFRA-SIGNAL).

## §7 What this PREP does NOT include

1. **No Lean edits**. File byte-identical to S7 ACT / S8 STATE-SYNC
   state.
2. **No paste-ready Lean code**. §2 and §4 give the design and
   sub-claim structure; §3 gives the bearer list. A future S10/S11
   PREP iteration produces paste-ready bodies (after bearer-pin
   verification at v4.26.0).
3. **No bearer verification at v4.26.0**. The bearer table in §3
   gives Mathlib v4.26.0 expected locations but does not re-pin them.
   The next PREP iteration should do this via GitHub raw audit
   (researcher worktree `.lake` symlink unusable; same trap as
   basel iter44 / abel-ruffini S10 PREP).
4. **No Step C design**. §4 is a preview only; full Step C design
   is deferred to a later PREP.
5. **No assembly-step design**. §5 sketches the case-split structure
   but no Lean code.
6. **No gallery `meta.json` edits**.
7. **No `knowledge.md` / `problem.md` body edits**. The 254-line
   knowledge.md remains the strategic-level record.
8. **No build verification.** `.lake` self-loop blocker.

## §8 Honest framing / self-audit

* **Step A took 75 LOC; Step B is estimated 100-140 LOC**. The
  estimate is realistic but optimistic — Step A's IVT-based proof was
  comparatively clean because the locally-constant claim has no
  asymmetry between endpoints. Step B requires the unique-root /
  derivative-coprime / sign-product chain plus the list-level
  sign-count discharge, all of which add LOC.
* **Step B requires a Mathlib bearer not pre-verified here**. The
  squarefree-coprime-with-derivative bearer name is "TBD" in the
  catalog. If Mathlib does not have a packaged form, a 5-10 LOC
  local lemma using `Polynomial.gcd_isCoprime` (if available) would
  fill the gap, but that's a real risk.
* **The Step B sub-claim decomposition may not be optimal**. The
  B.1 + B.2 + B.3 + assembly factoring is a defensible design but
  the actual proof author may find a cleaner organisation. The
  estimate +20 LOC of slack covers this.
* **Bearer audit at v4.26.0 is the highest-priority follow-up**. The
  S6 AUDIT pattern (#21705) of "21 latent errors masked by the G9
  qualifier" is the canonical risk for this slug. Step B paste-ready
  code MUST be docker-built before merging.

## §9 Cross-references

- S5 ACT (#21477, 2026-05-31): Step A locally-constant lemma.
- S6 AUDIT (#21705, 2026-06-01): 21 v4.26.0 build errors discovered.
- S7 ACT (#21825, 2026-06-01): 21 → 0 build-repair pass.
- S8 STATE-SYNC (#22023, 2026-06-02): absorbed S7 ACT.
- basel-problem Iter 44 INFRA-SIGNAL (2026-06-09, this researcher's
  prior session): `.lake` self-loop status; Path A remediation.
- abel-ruffini-oq-04-oq-09 S10 PREP (2026-06-09, this researcher's
  prior session): GitHub-raw bearer audit pattern for circumventing
  `.lake` symlink loop.
- User memory `[Lake self-loop in main repo (G9-inert)]`: per S7 ACT
  3058-job build evidence the loop did NOT block Docker; this is the
  precedent for the next ACT iteration to attempt docker-build on the
  Step B paste-ready code.

## §10 What the next researcher should do (S10+)

### Option A — Bearer audit + B.1 PREP

1. GitHub raw audit at v4.26.0 for the bearers in §3, especially the
   squarefree-coprime-with-derivative lemma. Confirm exact location
   and signature.
2. Materialise B.1 (`squarefree_root_has_nonzero_derivative`,
   ~10 LOC) as a paste-ready Lean recipe.
3. (Optional) Materialise B.2 and B.3 sketches.

Output: a S10 PREP doc that's the next-step paste-ready recipe.

### Option B — Full Step B PREP (paste-ready)

Skip the bearer audit phase; attempt a paste-ready Step B body
directly. Higher risk (bearer drift), but if Mathlib v4.26.0 names
match the catalog, would deliver a complete Step B in ~100-140 LOC
ready for docker-build verification.

### Option C — Step C PREP (parallel)

Design Step C (preview in §4) in parallel with Option A or B. This
unblocks the assembly step earlier but doesn't directly advance the
axiom discharge.

**Recommendation**: Option A. The slug has a documented history of
v4.26.0 bearer drift (S6 AUDIT 21 errors); the safer path is to
re-pin Mathlib bearers before paste-ready code is shipped. Step B
paste-ready code in Option B carries 2-5 hours of doctor-time risk
if bearer names have drifted; Option A's bearer audit + B.1 sketch
is ~30-45 min of doc work with much lower follow-up cost.
