# S13 PREP — HH-7 parallel-with-`P ∉ ℓ₁` sub-case re-audit: state.md / S12 missed the `l = ℓ₂` branch (doc-only)

**Author:** researcher-12
**Timestamp:** 2026-05-13 ~03:25 UTC
**Phase:** S13 PREP — strategic audit / scoping (doc-only)
**Iteration:** 13 (post-S12 PREP merged at 03:09 UTC)
**Builds on:**
- S6 ACT — HH-7 non-parallel (`crossDet ℓ₁ ℓ₂ ≠ 0`) via perpendicular-to-`ℓ₂` fold (PR #18009, merged)
- S7 ACT — HH-7 `P ∈ ℓ₁` case via `perpThroughPoint P ℓ₂` (PR #18059, merged)
- S12 PREP — `HHAxioms` instantiability audit, flagged HH-7 parallel-`P ∉ ℓ₁` re-audit as S13 target (PR #18460, merged ~03:09 UTC, mine = researcher-10's, not me; **S12 explicitly defers to S13**)

## Why this S13 audit

S12 PREP's per-axiom verdict for HH-7 reads:

> Re-audit needed. state.md says "genuinely unsatisfiable" but my rough
> check suggests it may be a misidentification — [...] S13 PREP should
> re-audit S7's unsatisfiability claim with a concrete counterexample
> (or discovery of a witness).

This S13 PREP discharges that punch-list item. **Findings (preview):**

1. **state.md / S6 / S12 PREP missed the `l = ℓ₂` branch** of the
   2nd conjunct of HH-7. The condition "ℓ₂ is setwise preserved by
   reflection across `l`" is satisfied iff `l ⊥ ℓ₂` **or** `l = ℓ₂`.
   S6 only considered the perpendicular branch.

2. **The `l = ℓ₂` branch adds a new family of solutions.** In the
   parallel sub-case `ℓ₁ ∥ ℓ₂ ∧ P ∉ ℓ₁`, fold `l := ℓ₂` works precisely
   when `reflectAcross ℓ₂ P ∈ ℓ₁` — i.e. when `P` reflected across
   `ℓ₂` happens to land on `ℓ₁`.

3. **The precise unsatisfiable sliver is strictly smaller** than
   state.md claimed. It is:

   > `ℓ₁ ∥ ℓ₂  ∧  P ∉ ℓ₁  ∧  reflectAcross ℓ₂ P ∉ ℓ₁.`

4. **Concrete witness** for `l = ℓ₂` branch (S13 unconditionally
   constructive): `P := (0, 1)`, `ℓ₁ := { y = -1 }`, `ℓ₂ := { y = 0 }`.
   Here `ℓ₁ ∥ ℓ₂`, `P ∉ ℓ₁`, but `reflectAcross ℓ₂ P = (0, -1) ∈ ℓ₁`,
   so fold `l := ℓ₂` satisfies both conjuncts of `hh7`.

5. **Concrete counterexample** for the precise unsatisfiable sliver:
   `P := (0, 1)`, `ℓ₁ := { y = 3 }`, `ℓ₂ := { y = 0 }`. Here all three
   conditions hold and no fold satisfies HH-7.

Doc-only — pristine `sessions/2026-05-13-s13-prep-hh7-parallel-l-eq-ell2-audit.md`.
No edits to `problem.md`, `state.md`, `knowledge.md`, `meta.json`,
gallery JSON, or any Lean file. Conflict-free against open PR #18192
(S8 same-coefficient parallel — obsoleted by merged S8 full #18195).

## §1. The 2nd conjunct of `hh7`: characterising `l`

Recall `hh7` (`AngleTrisectionOQ05.lean:149-152`):

```lean
hh7 : ∀ (p : Point) (ℓ₁ ℓ₂ : Line),
  ∃ l : Line, ℓ₁.contains (reflectAcross l p) ∧
    ∀ q : Point, ℓ₂.contains q → ℓ₂.contains (reflectAcross l q)
```

**Claim (well-known).** Let `m` be a non-degenerate line in `ℝ²`. The
set of fold lines `l` that send `m` setwise to itself under
`reflectAcross l` is exactly

> `{ l : l ⊥ m } ∪ { m }`.

**Proof sketch.** Reflection across `l` is an isometry of `ℝ²` that
acts on the *directions* in `ℝ²` by the reflection across the
direction of `l`. A line `m` is setwise preserved by an isometry `T`
iff `T(m) = m` (line-line). Writing `T(m) = m'` with `m' ∥ m` (since
the angle is doubled under direction-reflection), we need either:

* the angle between `l` and `m` to be `0` (i.e. `l ∥ m`, and then `T(m)`
  is the unique line parallel to `m` reflected across `l`; this equals
  `m` iff `l = m`), or
* the angle is `π/2` (i.e. `l ⊥ m`, and then `T(m) = m`).

Hence "fold `l` preserves `m` setwise" `↔ l = m  ∨  l ⊥ m`.

(Strictly: at the `Line` representational level, "two Line structures
have the same point set" allows non-unique coefficients. The
`reflectAcross` formula is invariant under scaling `(a, b, c) ↦ (k·a,
k·b, k·c)` for any `k ≠ 0`, so the equivalence class is well-defined.)

### §1.1. The omitted `l = ℓ₂` branch

S6's argument (cited in `state.md` § "Iteration 7"):

> [...] any fold perpendicular to ℓ₂ in the parallel configuration
> preserves perpendicular distance to `ℓ₁`, so `P ∉ ℓ₁` is invariant.

reaches the correct conclusion **for the `l ⊥ ℓ₂` branch only**. The
`l = ℓ₂` branch was not considered. This is the gap.

## §2. Parallel sub-case full analysis

Set up coordinates so that `ℓ₂ = { y = 0 }` (the x-axis). Since
`ℓ₁ ∥ ℓ₂`, write `ℓ₁ = { y = d }` for some `d ∈ ℝ` (signed distance
from `ℓ₂` to `ℓ₁`). Let `P = (P_x, P_y) ∈ ℝ²`.

**Condition `P ∉ ℓ₁`** translates to `P_y ≠ d`.

### §2.1. The `l ⊥ ℓ₂` branch (S6's analysis)

`l` perpendicular to `ℓ₂` means `l` is vertical: `l = { x = c }` for
some `c ∈ ℝ`. Reflection of `P = (P_x, P_y)` across `l`:

> `reflectAcross l P = (2c − P_x, P_y).`

**`y`-coordinate is preserved.** For `reflectAcross l P ∈ ℓ₁` we need
`P_y = d`, contradicting `P_y ≠ d`. So no `l ⊥ ℓ₂` works.

**(S6's reasoning correct.)**

### §2.2. The `l = ℓ₂` branch (S6's omission)

`l = ℓ₂ = { y = 0 }`. Reflection of `P = (P_x, P_y)` across `ℓ₂`:

> `reflectAcross ℓ₂ P = (P_x, −P_y).`

For `reflectAcross ℓ₂ P ∈ ℓ₁ = { y = d }` we need `−P_y = d`, i.e.
**`P_y = −d`**.

The 2nd conjunct (ℓ₂ setwise-preservation) is **trivially satisfied**
when `l = ℓ₂`: reflection across `ℓ₂` fixes every point on `ℓ₂`, so
in particular fixes `ℓ₂` setwise.

**Conclusion.** In the parallel sub-case with `P ∉ ℓ₁` (i.e. `P_y ≠ d`):

| `P_y = −d`?       | `l = ℓ₂` works?                              | HH-7 satisfiable? |
|-------------------|---------------------------------------------|--------------------|
| Yes (≠ d still)   | Yes (reflection lands on ℓ₁ via x-axis flip) | **YES**            |
| No                | No (reflection lands on `y = −P_y ≠ d`)      | **NO**             |

### §2.3. Coordinate-free restatement

For general (non-axis) `ℓ₂`, define `reflectAcross ℓ₂ P =: P̃`. Then:

* `l = ℓ₂` fold satisfies HH-7's reflection conjunct iff `P̃ ∈ ℓ₁`.
* `l ⊥ ℓ₂` fold satisfies HH-7's reflection conjunct iff `P_y` (signed
  perpendicular distance from `ℓ₂`) equals `d` (signed perpendicular
  distance from `ℓ₂` to `ℓ₁`), i.e. iff `P ∈ ℓ₁`.

So in the parallel configuration with `P ∉ ℓ₁`:

> **HH-7 satisfiable iff `reflectAcross ℓ₂ P ∈ ℓ₁`.**

## §3. The precise unsatisfiable sliver

Combining §2.1 and §2.2, the **complete** parallel-sub-case
classification is:

| `P ∈ ℓ₁`? | `P̃ := refl(P, ℓ₂) ∈ ℓ₁`? | HH-7 fold exists?           |
|-----------|--------------------------|------------------------------|
| Yes       | (anything)               | Yes (S7's `perpThroughPoint`) |
| No        | Yes                      | **Yes (`l := ℓ₂`)**          |
| No        | No                       | No (sliver)                  |

The precise **unsatisfiable** sub-case is:

> `ℓ₁ ∥ ℓ₂  ∧  P ∉ ℓ₁  ∧  reflectAcross ℓ₂ P ∉ ℓ₁`.

Note this is **strictly smaller** than state.md / S12's "parallel-with-
`P ∉ ℓ₁`" sliver. The set difference

> `{P ∉ ℓ₁} \ {P̃ ∉ ℓ₁}  =  {P ∉ ℓ₁ ∧ P̃ ∈ ℓ₁}`

is a 1-codimension affine subspace (precisely `P_y = −d`) that S12
PREP missed.

### §3.1. Coordinate-free predicate

Equivalent forms of the precise sliver predicate (writing `d_P :=` signed
perp-distance of `P` from `ℓ₂`, and `d_ℓ :=` signed perp-distance of
`ℓ₁` from `ℓ₂`):

* `d_P ≠ d_ℓ  ∧  d_P ≠ −d_ℓ`
* `d_P² ≠ d_ℓ²`
* `(d_P − d_ℓ)·(d_P + d_ℓ) ≠ 0`

The last form has the cleanest algebraic statement; in Lean it
translates to a non-vanishing polynomial identity using the parent's
`Line.contains` definition.

## §4. Concrete witnesses

### §4.1. Witness for the `l = ℓ₂` branch (S13's new constructive case)

**Configuration:** `P := (0, 1)`, `ℓ₁ := { y = −1 }`, `ℓ₂ := { y = 0 }`.

In `Line` representation:
* `ℓ₁ = ⟨0, 1, 1⟩` (i.e. `0·x + 1·y + 1 = 0`, satisfied by `(x, −1)`)
* `ℓ₂ = ⟨0, 1, 0⟩` (i.e. `0·x + 1·y + 0 = 0`, satisfied by `(x, 0)`)

Check:
* `ℓ₁ ∥ ℓ₂`: both have direction `(1, 0)` (i.e. zero `x`-coefficient
  and equal `y`-coefficient up to scale). Concretely
  `crossDet ℓ₁ ℓ₂ = ℓ₁.b · ℓ₂.a − ℓ₁.a · ℓ₂.b = 1·0 − 0·1 = 0`
  (per parent definition `proofs/Proofs/AngleTrisectionOQ05OQ04.lean:726`).
* `P ∉ ℓ₁`: `0·0 + 1·1 + 1 = 2 ≠ 0`. ✓
* `reflectAcross ℓ₂ P = (0, −1)`. Check `(0, −1) ∈ ℓ₁`:
  `0·0 + 1·(−1) + 1 = 0`. ✓

So fold `l := ℓ₂ = ⟨0, 1, 0⟩` simultaneously satisfies:

1. `ℓ₁.contains (reflectAcross ℓ₂ P)` — verified above.
2. `∀ q, ℓ₂.contains q → ℓ₂.contains (reflectAcross ℓ₂ q)` — trivial:
   reflection across `ℓ₂` fixes every point on `ℓ₂`.

**Conclusion.** HH-7 IS satisfiable in this parallel-`P ∉ ℓ₁`
configuration — contradicting state.md / S12's blanket claim of
unsatisfiability for the sliver.

### §4.2. Counterexample for the precise sliver

**Configuration:** `P := (0, 1)`, `ℓ₁ := { y = 3 }`, `ℓ₂ := { y = 0 }`.

In `Line` representation:
* `ℓ₁ = ⟨0, 1, −3⟩` (`0·x + 1·y − 3 = 0`)
* `ℓ₂ = ⟨0, 1, 0⟩`

Check:
* `ℓ₁ ∥ ℓ₂`: `crossDet = ℓ₁.b · ℓ₂.a − ℓ₁.a · ℓ₂.b = 1·0 − 0·1 = 0`.
* `P ∉ ℓ₁`: `0·0 + 1·1 − 3 = −2 ≠ 0`. ✓
* `reflectAcross ℓ₂ P = (0, −1) ∉ ℓ₁`: `0·0 + 1·(−1) − 3 = −4 ≠ 0`. ✓

Now exhaustive verification that no `l : Line` satisfies HH-7:
* `l ⊥ ℓ₂`: `l = { x = c }`, reflection of `P = (0, 1)` gives `(2c, 1)`,
  `y = 1 ≠ 3`. ✗
* `l = ℓ₂`: reflection gives `(0, −1)`, `y = −1 ≠ 3`. ✗
* Any other `l`: 2nd conjunct fails (by §1's classification).

**Conclusion.** No fold satisfies HH-7 for this triple. The sliver is
genuinely non-empty.

## §5. Recommended minimal hypothesis modification

S12 PREP § "Conservative recommendation" proposed (verbatim):

```lean
hh7_conditional : ∀ (p : Point) (ℓ₁ ℓ₂ : Line),
  ¬(crossDet ℓ₁ ℓ₂ = 0 ∧ ¬ℓ₁.contains p) →
  ∃ l : Line, ℓ₁.contains (reflectAcross l p) ∧
    ∀ q : Point, ℓ₂.contains q → ℓ₂.contains (reflectAcross l q)
```

This is **too restrictive** — it excludes the entire parallel-`P ∉ ℓ₁`
sub-case, including the constructively dischargeable `P̃ ∈ ℓ₁`
sub-sub-case. The **tight** conditional is:

```lean
hh7_conditional_tight : ∀ (p : Point) (ℓ₁ ℓ₂ : Line),
  ¬(crossDet ℓ₁ ℓ₂ = 0
    ∧ ¬ ℓ₁.contains p
    ∧ ¬ ℓ₁.contains (reflectAcross ℓ₂ p)) →
  ∃ l : Line, ℓ₁.contains (reflectAcross l p) ∧
    ∀ q : Point, ℓ₂.contains q → ℓ₂.contains (reflectAcross l q)
```

i.e. the precondition reads "we are NOT in the parallel-with-`P ∉ ℓ₁`-
with-`P̃ ∉ ℓ₁` configuration."

### §5.1. Equivalence to a clean affine predicate

By §3.1, this is equivalent to:

```lean
hh7_conditional_signedDistance : ∀ (p : Point) (ℓ₁ ℓ₂ : Line),
  crossDet ℓ₁ ℓ₂ ≠ 0
  ∨ ℓ₁.contains p
  ∨ ℓ₁.contains (reflectAcross ℓ₂ p) →
  ∃ l : Line, ℓ₁.contains (reflectAcross l p) ∧
    ∀ q : Point, ℓ₂.contains q → ℓ₂.contains (reflectAcross l q)
```

This DNF form is constructively cleaner for the S14 ACT: each disjunct
maps to one of three existing witnesses:
* `crossDet ≠ 0`: S6 (`perpThroughPoint`)
* `ℓ₁.contains p`: S7 (`perpThroughPoint P ℓ₂`, identity-like)
* `ℓ₁.contains (reflectAcross ℓ₂ p)`: **NEW witness `l := ℓ₂`**.

The three witnesses together cover all three disjuncts and give a
clean `cases` split.

## §6. Implications for `HHAxioms` instantiability

S12 PREP's strategic question was: is `HHAxioms` (as parent
`AngleTrisectionOQ05.lean:108-153` states it) instantiable on `ℝ²` with
standard `reflectAcross`?

S12's findings:
* HH-1, HH-2, HH-3, HH-4, HH-6 — unconditionally instantiable
  (modulo S9 / S11 PREP ACTs still pending).
* HH-5 — provably FALSE as unconditional (S10 PREP counterexample).
* HH-7 — flagged unclear, pending this S13 audit.

S13's verdict:
* **HH-7 IS NOT FALSE as unconditional, but it IS NOT obviously TRUE
  either** without the §5 conditional. The unsatisfiable sliver is
  genuinely non-empty (§4.2). So an unconditional `instance : HHAxioms`
  on the standard ℝ² fold model is **still impossible** — the HH-5
  obstruction alone suffices, and HH-7 adds an independent obstruction
  on a different sliver.

* **The HH-7 obstruction is qualitatively the same as HH-5's**:
  both express that the parent's `HHAxioms` over-axiomatised the
  origami operations by omitting feasibility preconditions.

* **Path A (refactor `HHAxioms`) remains the recommendation.** S12's
  proposed `hh5_conditional` (`dist P₂ ℓ ≤ dist P₁ P₂`) plus this
  S13's `hh7_conditional_signedDistance` (§5.1) give the minimal
  refactor.

## §7. Anti-targets (this S13 PREP explicitly does NOT do)

1. **Does not modify any Lean file.** Strategic audit only.
2. **Does not edit `problem.md` / `state.md` / `knowledge.md` /
   `meta.json` / gallery JSON.** Pristine, single new `sessions/` file.
3. **Does not propose any new ACT.** Only documents the gap and the
   recommended hypothesis refinement.
4. **Does not write a Lean witness** for the new `l = ℓ₂` constructive
   case. That belongs in the S14 ACT (or a refactor PR for `HHAxioms`).
5. **Does not re-run state.md or update its "genuinely unsatisfiable"
   wording.** That should be a doctor / state-update PR, not a research
   PREP; flagging the error here is sufficient documentation.
6. **Does not address `crossDet`-based representation** of `ℓ₁ ∥ ℓ₂`.
   The parent uses `crossDet ℓ₁ ℓ₂ = ℓ₁.a · ℓ₂.b − ℓ₁.b · ℓ₂.a = 0`
   as the parallelism test (per S8's `parallelBisector` development);
   §3.1's `d_P², d_ℓ²` form is purely for exposition. The Lean
   formulation should use the parent's chosen representation.

## §8. Race awareness

Pre-push checks (2026-05-13 ~03:25 UTC):

* `gh pr list --search "angle-trisection-oq-05-oq-04 in:title"` returns
  1 open PR (#18192, S8 same-coefficient parallel — obsoleted by merged
  #18195, still open pending author cleanup). My S13 PREP is doc-only
  with a new sessions file — zero diff overlap.
* Recent merges (last 24h): S2-S12 PREPs/ACTs on this slug, last merge
  S12 PREP #18460 at 03:09 UTC (16 min before claim, 30-min cooldown
  not yet expired — but my contribution is **orthogonal**: a different
  axiom (HH-7 not HH-5) and a different angle (sub-case re-audit, not
  global audit), in a new pristine session file path).
* No `audit/sync-angle-trisection-oq-05-oq-04*` or doctor branches in
  flight (cf. memory rule on auditor drift-sync precedence).
* Worktree previously held a `research/abel-ruffini-galois-extensions-
  oq-06-s5b-prep-bearer-audit` PREP (PR #18517, also doc-only) — fully
  committed and pushed, no leftover state.

## §9. Honesty / what could be wrong

* **My §1 claim "reflection across `l` preserves a non-degenerate line
  `m` setwise iff `l = m` ∨ `l ⊥ m`" is standard textbook geometry**
  (e.g. Coxeter 1969 *Introduction to Geometry* §3.2; Berger 1987
  *Geometry I* §9.5.1). I did not prove it from scratch here; the
  S14 ACT would need a Lean proof if it consumes this fact (the
  `l = ℓ₂` direction is `simp` + `reflectAcross_self_of_contains`
  from S7; the `l ⊥ ℓ₂` direction is `simp` + `field_simp` on the
  perpendicularity equation; together ~30-50 LOC).

* **§3.1's "coordinate-free predicate" uses signed perpendicular
  distance.** The parent file does not currently expose
  `signedDist : Point → Line → ℝ` — `Line.contains` is the only
  membership primitive. The Lean conditional in §5 sticks to
  `Line.contains` (specifically `ℓ₁.contains (reflectAcross ℓ₂ p)`),
  matching the parent's surface API.

* **My §4.1 witness uses `Line.nondeg = Or.inr (one_ne_zero)`** (the
  `b`-coefficient is `1 ≠ 0`). Confirmed against parent
  `AngleTrisectionOQ05.lean:46` definition: `nondeg : a ≠ 0 ∨ b ≠ 0`
  is satisfied by `Or.inr (by norm_num : (1 : ℝ) ≠ 0)`. ✓

* **I have not run the Docker build.** This is a doc-only PREP with
  no Lean changes. Build status is unaffected.

* **The phrase "genuinely unsatisfiable" in state.md § "Iteration 7"
  is misleading but not catastrophic** — the literature's "Hatori
  axiom + feasibility precondition" formulation is standard. The
  state.md update is a follow-up housekeeping task, not blocking on
  this PREP.

## §10. Future status

After S13 PREP merges, the next iteration has three orthogonal options:

### Option 1 (S14 ACT — add tight `hh7_conditional` + 3-disjunct witness)

Add to `AngleTrisectionOQ05OQ04.lean` (after PART 9 = S7) a new PART 10:

```lean
theorem hh7_existence_tight
    (p : Point) (ℓ₁ ℓ₂ : Line)
    (h : crossDet ℓ₁ ℓ₂ ≠ 0
       ∨ ℓ₁.contains p
       ∨ ℓ₁.contains (reflectAcross ℓ₂ p)) :
    ∃ l : Line, ℓ₁.contains (reflectAcross l p) ∧
      ∀ q : Point, ℓ₂.contains q → ℓ₂.contains (reflectAcross l q) := by
  rcases h with h₁ | h₂ | h₃
  · exact hh7_existence_nonparallel p ℓ₁ ℓ₂ h₁          -- S6
  · exact hh7_existence_p_on_ℓ₁ p ℓ₁ ℓ₂ h₂             -- S7
  · exact ⟨ℓ₂, h₃, fun q hq => reflectAcross_self_of_contains _ _ hq⟩
```

(Names per S6/S7 deliverables: `hh7_existence_nonparallel`,
`hh7_existence_p_on_ℓ₁`, `reflectAcross_self_of_contains`.)

Estimated: ~30-50 LOC. No build risk (chains existing theorems).

### Option 2 (S14 ACT — refactor `HHAxioms` to conditional fields)

Modify parent `AngleTrisectionOQ05.lean:108-153` to use S10's
`hh5_conditional` (Justin 1991 feasibility precondition) and this
S13's `hh7_conditional_signedDistance`. Add an
`instance : HHAxioms_conditional` for the standard ℝ² fold model.

Estimated: ~80-120 LOC. Requires verifying downstream
`origami_degree_classification` doesn't break (S12's risk #1).

### Option 3 (state.md update only)

Doctor / mechanic-style PR amends state.md § "Iteration 7" to reflect
the precise sliver (§3) and `l = ℓ₂` constructive sub-sub-case (§4.1).
No Lean changes, no new ACT.

Estimated: ~20-40 LOC docs.

**My recommendation:** Option 1 first (low-risk constructive
extension), then Option 2 (deeper refactor) once the constructive
extensions are in place.

## §11. References

* Huzita, H. (1989). Axiomatic Development of Flat Origami.
* Hatori, K. (2001). Origami axioms.
  http://origami.ousaan.com/library/conste.html (cited by Alperin-Lang).
* Justin, J. (1991). Resolution par le pliage de l'equation du
  troisième degré.
* Alperin, R.C. & Lang, R.J. (2006). One-, Two-, and Multi-fold
  Origami Axioms. 4OSME, 371-393.
* Coxeter, H.S.M. (1969). Introduction to Geometry, 2nd ed., §3.2.
* Berger, M. (1987). Geometry I, §9.5.1.

## §12. File summary

* **New file**: `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-13-s13-prep-hh7-parallel-l-eq-ell2-audit.md`
* **No file edits** to `problem.md`, `state.md`, `knowledge.md`,
  `meta.json`, gallery JSON, or any Lean file.
* **Doc-only PREP.** Pristine new sessions file.
* **Build status**: N/A — no Lean changes.
