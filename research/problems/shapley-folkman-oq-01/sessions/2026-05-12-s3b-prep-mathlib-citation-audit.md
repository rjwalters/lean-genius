# 2026-05-12 — S3b PREP: Mathlib v4.26.0 citation audit + Step-4 phantom-lemma correction (doc-only)

**Researcher**: researcher-8
**Slug**: `shapley-folkman-oq-01`
**Phase**: S3b PREP (doc-only)
**Branch**: `research/shapley-folkman-oq-01-s3b-prep-citation-audit-1778644640`
**Mathlib pin**: `v4.26.0` (lean-toolchain `leanprover/lean4:v4.26.0`)
**Audit ref**: leanprover-community/mathlib4 tag `v4.26.0` (NOT `master`)

## §0 Predecessor chain (all merged on `main` at PREP time)

| PR     | Phase      | Contribution                                                                              |
|--------|------------|-------------------------------------------------------------------------------------------|
| #18345 | S1 OBSERVE | Literal `finrank` extension is vacuous; three approaches A/B/C surveyed.                  |
| #18414 | S1b OBSERVE| Aumann/Lyapunov Mathlib prerequisite audit (Approaches A & B deferred).                    |
| #18397 | S2 PREP    | Approach C `ℓ²` counter-example design + `Fin N` formulation chosen.                       |
| #18452 | S2b PREP   | Numeric verification at `N=1..4`, orthogonality uniqueness sketch, truncation refutation. |
| #18491 | S3 PREP    | Pair convex-hull parameter-extraction Lean recipe (verbatim Mathlib chain).                |

This **S3b PREP** audits the Mathlib citations carried forward by #18491 against the
project's pinned Mathlib `v4.26.0` (not `master`, where #18491's audit was done), and
corrects two phantom-lemma references in #18491 §3.1 / §5 step 4 before S3 ACT begins.

**Scope**: doc-only, single file under `sessions/`. No `problem.md` / `state.md` /
`knowledge.md` / gallery JSON / `.lean` edits.

## §1 Why this audit matters before S3 ACT

S3 PREP #18491 §8 disclosure 1 states:

> All Mathlib citations were verified at v4.26.0 via the GitHub Contents
> API on 2026-05-12. Line numbers are pinned to commit
> `23fc2795c350c2c4a5c70e289a545e81273229b3` (`master` HEAD at audit time);
> for the lean-genius `lean-toolchain v4.26.0` Mathlib pin, the line
> numbers may drift by ±3 lines depending on cherry-picks…
> The **lemma names are stable** — `convexHull_pair`, `segment_eq_image'`,
> `segment` (definition), `EuclideanSpace.single_apply` — all present in
> v4.26.0 Mathlib …

This audit finds: **(a)** PiL2.lean line numbers actually drift by ~40-42 lines
between `master` and `v4.26.0` (the deprecation block at lines 297-313 of `master`
did not exist at `v4.26.0`, where the lemmas live at lines 257-271); **(b)** the
informal Lean sketch in #18491 §5 step 4 invokes two phantom lemmas
(`EuclideanSpace.single_ne_zero_iff` and `smul_right_inj`) that have zero hits
org-wide; **(c)** the S2b PREP #18452 §5.1 citation `EuclideanSpace.single_orthonormal`
is reversed — the correct name at `v4.26.0` is `EuclideanSpace.orthonormal_single`.
This affects S3 ACT only if it pulls from S2b PREP §3 (orthonormality route);
S3 PREP §4 already recommends bypassing that route via coordinate evaluation, so
this is a parallel-track issue but still worth flagging.

None of the findings break the S3 ACT plan; this PREP is a **paper correction**,
not a strategic pivot.

## §2 Erratum E1 — PiL2.lean line numbers cite `master`, not `v4.26.0`

### §2.1 What #18491 §10 claims

S3 PREP #18491 §10 lists (with the `master` HEAD audit pin):

```
- Mathlib/Analysis/InnerProductSpace/PiL2.lean:297 — EuclideanSpace.single.
- Mathlib/Analysis/InnerProductSpace/PiL2.lean:308 — EuclideanSpace.single_apply.
- Mathlib/Analysis/InnerProductSpace/PiL2.lean:313 — EuclideanSpace.single_eq_zero_iff.
- Mathlib/Analysis/InnerProductSpace/PiL2.lean:348 — EuclideanSpace.single_orthonormal.
```

### §2.2 What `v4.26.0` actually has (verified via `gh api ... ?ref=v4.26.0`)

```
- Mathlib/Analysis/InnerProductSpace/PiL2.lean:257 — def EuclideanSpace.single (i : ι) (a : 𝕜) ...
- Mathlib/Analysis/InnerProductSpace/PiL2.lean:266 — theorem EuclideanSpace.single_apply
- Mathlib/Analysis/InnerProductSpace/PiL2.lean:271 — theorem EuclideanSpace.single_eq_zero_iff
- Mathlib/Analysis/InnerProductSpace/PiL2.lean:309 — theorem EuclideanSpace.orthonormal_single
                                                     [note: name is _orthonormal_single, not
                                                      _single_orthonormal — see §4]
```

Drift: 40, 42, 42, 39 lines respectively — **far** outside the "±3 lines"
tolerance claimed in #18491 §8 disclosure 1.

### §2.3 Why the drift exists

Between `v4.26.0` (tagged) and `master` HEAD (2026-05-12), Mathlib added a
deprecation block in PiL2.lean (commit landing 2026-03-15 per
`@[deprecated PiLp.single_apply (since := "2026-03-15")]`). The block re-exports
the `EuclideanSpace.single_*` lemmas as deprecated wrappers around their new
`PiLp.single_*` analogs, inserting ~40 lines before the originals.

The `master` audit captured both the deprecation wrapper and the original
definition, but **at `v4.26.0` the deprecation wrappers do not exist** — the
originals are at line 266 (single_apply), 271 (single_eq_zero_iff).

### §2.4 Impact on S3 ACT

**None for correctness.** The lemma names cited (`EuclideanSpace.single_apply`,
`EuclideanSpace.single_eq_zero_iff`) ARE present at `v4.26.0`, with the same
type signatures as on master, and are NOT deprecated at v4.26.0. The `simp`
proof bodies are also the same.

**Minor for future-proofing.** If the project bumps `lean-toolchain` beyond
the 2026-03-15 deprecation, S3 ACT code using `EuclideanSpace.single_apply` will
trip a deprecation warning. The forward-compatible names are
`PiLp.single_apply` and `PiLp.single_eq_zero_iff`. Both exist at v4.26.0
indirectly (since `EuclideanSpace.single` is a `def` over `toLp _ (Pi.single i a)`
in v4.26.0 — see §6) but as named lemmas they only appear in the deprecation
block, which is absent at v4.26.0. So at v4.26.0, `EuclideanSpace.single_apply`
**is** the canonical name; future-proofing is not actionable until the bump.

**Conclusion**: keep `EuclideanSpace.single_apply` and `EuclideanSpace.single_eq_zero_iff`
for S3 ACT. Update line cites to v4.26.0 actual values (§5).

## §3 Erratum E2 — `EuclideanSpace.single_ne_zero_iff` is a phantom

### §3.1 What #18491 §5 step 4 sketch claims

S3 PREP #18491 §5 step 4 provides this skeleton for the non-membership
`(1/2) • e_j ∉ {0, e_j}`:

```lean
have h_not_zero : (1/2 : ℝ) • EuclideanSpace.single j 1 ≠ (0 : E) := by
  rw [smul_ne_zero_iff]
  exact ⟨by norm_num, EuclideanSpace.single_ne_zero_iff.mpr one_ne_zero⟩
```

The cite is `EuclideanSpace.single_ne_zero_iff` (positive form: `single i a ≠ 0 ↔ a ≠ 0`).

### §3.2 What's actually in Mathlib

Org-wide search (`gh api search/code repo:leanprover-community/mathlib4 ...`):

| Query                                            | Total hits |
|--------------------------------------------------|------------|
| `"EuclideanSpace.single_ne_zero"`                | 0          |
| `"PiLp.single_ne_zero"`                          | 0          |
| `"EuclideanSpace.single_ne_zero_iff"`            | 0          |
| `"EuclideanSpace.single_eq_zero_iff"` (defined)  | 1 (def) + uses |

**`EuclideanSpace.single_ne_zero_iff` does not exist** as a named lemma anywhere
in Mathlib (org-wide, all branches/tags accessible via search/code). Only the
`_eq_zero_iff` form exists (PiL2.lean:271 at v4.26.0).

### §3.3 Correct invocation

Two options at v4.26.0:

**Option A — `.not.mpr` on the `_eq_zero_iff` form** (recommended, 1 LOC swap):

```lean
have h_not_zero : (1/2 : ℝ) • EuclideanSpace.single j 1 ≠ (0 : E) := by
  rw [smul_ne_zero_iff]
  refine ⟨by norm_num, ?_⟩
  exact (EuclideanSpace.single_eq_zero_iff (i := j) (a := (1:ℝ))).not.mpr one_ne_zero
```

`Iff.not : (a ↔ b) → (¬a ↔ ¬b)` is in Lean core; `(h : a ↔ b).not.mpr` flips
`a ↔ b` to `¬b → ¬a`. Total replacement: one `.not.mpr` swap.

**Option B — `simp` with `single_eq_zero_iff` and `ne_eq`** (cleaner, no `rw`):

```lean
have h_not_zero : (1/2 : ℝ) • EuclideanSpace.single j 1 ≠ (0 : E) := by
  simp [smul_ne_zero_iff, EuclideanSpace.single_eq_zero_iff]
```

`smul_ne_zero_iff` (NoZeroSMulDivisors/Defs.lean:76 at v4.26.0) gives
`c • x ≠ 0 ↔ c ≠ 0 ∧ x ≠ 0`. `EuclideanSpace.single_eq_zero_iff` is `@[simp]`-tagged
at v4.26.0 line 270, so `simp` will resolve the conjunction's second component to
`(1:ℝ) ≠ 0`, which `simp` closes via `one_ne_zero`. Both halves discharge in one
`simp` call.

**Option B is shorter** but Option A is more pedagogical for the S3 ACT writer
who is following the §5 step 4 sketch literally.

### §3.4 Verification of `smul_ne_zero_iff` at v4.26.0

`Mathlib/Algebra/NoZeroSMulDivisors/Defs.lean:76` at v4.26.0:

```lean
theorem smul_ne_zero_iff : c • x ≠ 0 ↔ c ≠ 0 ∧ x ≠ 0 := by rw [Ne, smul_eq_zero, not_or]
```

Typeclass context: `Zero R`, `Zero M`, `SMul R M`, `NoZeroSMulDivisors R M`.

For `R = ℝ`, `M = EuclideanSpace ℝ (Fin N)`: `NoZeroSMulDivisors ℝ (EuclideanSpace ℝ (Fin N))`
holds via the standard chain `Field ℝ + Module ℝ M → NoZeroSMulDivisors ℝ M` (instance
in `Mathlib/Algebra/NoZeroSMulDivisors/Basic.lean`). No instance-search risk.

## §4 Erratum E3 — `EuclideanSpace.single_orthonormal` is reversed

### §4.1 What S2b PREP #18452 §5.1 claims

S2b PREP #18452 §5.1 (per S3 PREP #18491 §10 reference list):

```
- PiL2.lean:348 — EuclideanSpace.single_orthonormal.
```

### §4.2 What `v4.26.0` actually has

The name is **`EuclideanSpace.orthonormal_single`** (line 309 at v4.26.0):

```lean
/-- `EuclideanSpace.single` forms an orthonormal family. -/
theorem EuclideanSpace.orthonormal_single :
    Orthonormal 𝕜 fun i : ι => EuclideanSpace.single i (1 : 𝕜) := by
  simp_rw [orthonormal_iff_ite, EuclideanSpace.inner_single_left, map_one, one_mul,
    EuclideanSpace.single_apply]
  intros
  trivial
```

`grep` for `EuclideanSpace.single_orthonormal` (with `_single` last):

```
$ gh api search/code -q '"EuclideanSpace.single_orthonormal"'
total_count: 0
```

vs `orthonormal_single` (correct):

```
$ gh api search/code -q '"EuclideanSpace.orthonormal_single"'
# Found at PiL2.lean:309 and downstream uses
```

### §4.3 Impact

**Zero for S3 ACT as planned**. S3 PREP §4 explicitly recommends the
**coordinate-evaluation route** (`EuclideanSpace.single_apply` + `Finset.sum_ite_eq'`)
**over** the orthonormality route. So `EuclideanSpace.orthonormal_single` is not
invoked by the recommended path.

**Non-zero for S3 fallback / S2b reuse.** If S3 ACT hits unexpected issues
with the coordinate route and falls back to the S2b §3 orthonormality argument,
the cite name in S2b PREP §5.1 is wrong and will produce an "unknown identifier"
error. The fix is a one-token swap: `single_orthonormal` → `orthonormal_single`.

## §5 Corrected reference list (v4.26.0)

For carry-forward to S3 ACT / future PREPs, the v4.26.0-correct citations:

### §5.1 Mathlib source citations (v4.26.0 verified)

| Lemma / Definition                         | File                                                              | Line  |
|--------------------------------------------|-------------------------------------------------------------------|-------|
| `convexHull_pair`                          | `Mathlib/Analysis/Convex/Hull.lean`                                | 124   |
| `def segment`                              | `Mathlib/Analysis/Convex/Segment.lean`                             | 50    |
| `segment_eq_image`                         | `Mathlib/Analysis/Convex/Segment.lean`                             | 193   |
| `segment_eq_image'`                        | `Mathlib/Analysis/Convex/Segment.lean`                             | 207   |
| `def EuclideanSpace.single`                | `Mathlib/Analysis/InnerProductSpace/PiL2.lean`                     | 257   |
| `EuclideanSpace.single_apply`              | `Mathlib/Analysis/InnerProductSpace/PiL2.lean`                     | 266   |
| `EuclideanSpace.single_eq_zero_iff`        | `Mathlib/Analysis/InnerProductSpace/PiL2.lean`                     | 271   |
| `EuclideanSpace.orthonormal_single`        | `Mathlib/Analysis/InnerProductSpace/PiL2.lean`                     | 309   |
| `smul_eq_zero` (@[simp])                   | `Mathlib/Algebra/NoZeroSMulDivisors/Defs.lean`                     | 72    |
| `smul_ne_zero_iff`                         | `Mathlib/Algebra/NoZeroSMulDivisors/Defs.lean`                     | 76    |
| `smul_ne_zero_iff_left` / `_right`         | `Mathlib/Algebra/NoZeroSMulDivisors/Defs.lean`                     | 80,81 |

### §5.2 File-path correction

S3 PREP §4 cites:

> the canonical lemma is `Finset.sum_ite_eq'` (or `Finset.sum_ite_eq`) which collapses
> `∑ i, if j = i then f i else 0` to `f j` when `j ∈ Finset.univ`. Both are in
> `Mathlib/Algebra/BigOperators/Basic.lean`.

At v4.26.0, `Mathlib/Algebra/BigOperators/Basic.lean` **does not exist** (returns
HTTP 404). The directory tree at v4.26.0 is:

```
Mathlib/Algebra/BigOperators/
├── Associated.lean   Balance.lean   Expect.lean   Field.lean   Fin.lean
├── Finprod.lean      Finsupp/       Group/        GroupWithZero/
├── Intervals.lean    ModEq.lean     Module.lean   NatAntidiagonal.lean
├── Option.lean       Pi.lean        Ring/         RingEquiv.lean
├── Sym.lean          WithTop.lean
```

The `sum_ite_eq` / `sum_ite_eq'` pair lives in
`Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean` (generated by
`@[to_additive]` on the `prod_ite_eq` / `prod_ite_eq'` theorems at lines 140,
153 of that file).

### §5.3 Non-existent name list (phantom lemmas — do not cite in S3 ACT)

| Name                                            | Org-wide hits | Notes                                                  |
|-------------------------------------------------|---------------|--------------------------------------------------------|
| `EuclideanSpace.single_ne_zero_iff`             | 0             | Use `single_eq_zero_iff.not` instead (§3.3 Option A).  |
| `EuclideanSpace.single_orthonormal`             | 0             | Correct: `orthonormal_single` (S2b PREP §5.1 wrong).   |
| `smul_right_inj`                                | 0             | Use coordinate-eval (§7) for `(1/2)•e_j ≠ e_j`.        |
| `PiLp.single_apply`  (at v4.26.0)               | 0 as named    | Exists at master via deprecation block, not v4.26.0.    |
| `PiLp.single_eq_zero_iff`  (at v4.26.0)         | 0 as named    | Same — appears post-2026-03-15 only.                    |
| `PiLp.sum_apply`                                | 0             | Use `Finset.sum_apply` (function-space defeq).         |

## §6 Why `EuclideanSpace.single` is a `def` at v4.26.0 (not an `abbrev`)

S3 PREP #18491 §2 mentions in passing that `EuclideanSpace.single i a := PiLp.single 2 i a`.
At `master` (post-deprecation block) this is correct — line 297 of `master`
PiL2.lean is:

```lean
abbrev EuclideanSpace.single (i : ι) (a : 𝕜) : EuclideanSpace 𝕜 ι := PiLp.single 2 i a
```

At `v4.26.0` (line 257) it is instead:

```lean
def EuclideanSpace.single (i : ι) (a : 𝕜) : EuclideanSpace 𝕜 ι :=
  toLp _ (Pi.single i a)
```

(`def` not `abbrev`, body via `toLp _ (Pi.single i a)` not via `PiLp.single 2`.)

This means:

1. **Definitional unfolding** of `EuclideanSpace.single` at v4.26.0 reveals
   `toLp _ (Pi.single i a)`, NOT `PiLp.single 2 i a`. Any tactic that tried to
   unfold `EuclideanSpace.single` to `PiLp.single` (which is what `master`-era
   code would do) would fail at v4.26.0.

2. **`PiLp.single` as a named definition does not appear in
   `Mathlib/Analysis/Normed/Lp/PiLp.lean` at v4.26.0** (verified by grepping the
   file's 1,179 lines for `def single|abbrev single` — zero hits).

3. **The `single_apply` proof body at v4.26.0** is:
   ```lean
   theorem EuclideanSpace.single_apply (i : ι) (a : 𝕜) (j : ι) :
       (EuclideanSpace.single i a) j = ite (j = i) a 0 := by
     rw [EuclideanSpace.single, PiLp.toLp_apply, ← Pi.single_apply i a j]
   ```
   It is `@[simp]`-tagged. `simp` will close any goal of the shape
   `(EuclideanSpace.single i a) j = ite (j = i) a 0` automatically.

**Practical consequence for S3 ACT**: do not rely on `unfold EuclideanSpace.single`
to expose `PiLp.single` machinery. Use `simp [EuclideanSpace.single_apply]` or
just `simp` (since the lemma is `@[simp]`).

## §7 Coordinate-evaluation proof of `(1/2) • e_j ≠ e_j` (§5 step 4 fix)

The S3 PREP §5 step 4 cite of `smul_right_inj` is also a phantom (§5.3).
The cleanest substitute is coordinate evaluation at index `j`:

```lean
have h_not_basis : (1/2 : ℝ) • EuclideanSpace.single j 1 ≠ EuclideanSpace.single j 1 := by
  intro h_eq
  -- Apply both sides at coordinate j; LHS = 1/2, RHS = 1.
  have hj : ((1/2 : ℝ) • EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin N)) j =
            (EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin N)) j := congrFun h_eq j
  simp [EuclideanSpace.single_apply, PiLp.smul_apply] at hj
  -- hj : (1/2 : ℝ) = 1
  norm_num at hj
```

**Tactic justification**:

- `congrFun h_eq j` extracts the coordinate-`j` equation from a function-equality
  hypothesis. `EuclideanSpace ℝ (Fin N)` is defeq to a `PiLp` over a function
  space, so `congrFun` applies (alternatively `congr_arg (· j) h_eq`).
- `simp [EuclideanSpace.single_apply, PiLp.smul_apply]` evaluates both sides:
  LHS becomes `(1/2 : ℝ) • ite (j = j) 1 0 = (1/2 : ℝ) • 1 = 1/2`; RHS becomes
  `ite (j = j) 1 0 = 1`. `simp` collapses the `ite (j = j)` via `if_pos rfl`.
- `norm_num at hj` closes the resulting `(1/2 : ℝ) = 1` as false.

**LOC**: 5 lines (header + body). No phantom lemmas; all cited names exist at v4.26.0.

**Alternative (algebraic, no coord-eval)**:

```lean
have h_not_basis : (1/2 : ℝ) • EuclideanSpace.single j 1 ≠ EuclideanSpace.single j 1 := by
  intro h_eq
  have h_sub : ((1/2 : ℝ) - 1) • EuclideanSpace.single j 1 = 0 := by
    rw [sub_smul, h_eq, one_smul, sub_self]
  rw [smul_eq_zero, EuclideanSpace.single_eq_zero_iff] at h_sub
  rcases h_sub with h_half | h_one
  · norm_num at h_half
  · exact one_ne_zero h_one
```

This route uses `smul_eq_zero` (NoZeroSMulDivisors/Defs.lean:72) and
`EuclideanSpace.single_eq_zero_iff`, both verified-present at v4.26.0. Either
route works; coord-eval is preferred (shorter, no `sub_smul` step).

## §8 Tactic-availability summary for §5 Step 4 (S3 ACT pre-flight)

| Goal                                                    | Recommended tactic chain                                          | LOC |
|---------------------------------------------------------|-------------------------------------------------------------------|-----|
| `(1/2 : ℝ) • e_j ≠ 0`                                   | `rw [smul_ne_zero_iff]; refine ⟨by norm_num, ?_⟩; exact (EuclideanSpace.single_eq_zero_iff).not.mpr one_ne_zero` | 3 |
| `(1/2 : ℝ) • e_j ≠ 0` (alt)                             | `simp [smul_ne_zero_iff, EuclideanSpace.single_eq_zero_iff]`      | 1   |
| `(1/2 : ℝ) • e_j ≠ e_j` (coord-eval)                    | §7 first block                                                    | 5   |
| `(1/2 : ℝ) • e_j ≠ e_j` (algebraic)                     | §7 second block                                                   | 6   |
| `(1/2 : ℝ) • e_j ∉ ({0, e_j} : Set _)`                  | `simp [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto` after the two above | 2 |

**Total step-4 LOC budget**: ~6-10 lines (down from S3 PREP §5 step 4 estimate
of "5 LOC for the non-membership check" plus phantom-lemma fix overhead).

## §9 Race-check + diff scope

### §9.1 Race check

- `gh pr list --repo rjwalters/lean-genius --search "shapley-folkman in:title" --state open`
  → 0 open PRs at audit time (post-#18491 merge).
- `git log origin/main -- research/problems/shapley-folkman-oq-01/` recent:
  - #18491 (S3 PREP) merged 02:46 UTC, ~2 hours pre-claim.
  - #18452 (S2b PREP) merged 02:05 UTC.
  - #18397 (S2 PREP) merged 00:14 UTC.
  - #18414 (S1b OBSERVE) merged 22:47 UTC.
  - #18345 (S1 OBSERVE) merged 22:47 UTC.

Most recent merge was ~2 hours before this PREP, comfortably past the
30-min-post-merge cool window. No in-flight competitor.

Filename `2026-05-12-s3b-prep-mathlib-citation-audit.md` is unique under
`sessions/` (existing files: s01-observe, s01b-aumann-lyapunov, s2-prep-approach-c,
s2b-prep-construction, s3-prep-pair-convexhull).

### §9.2 Diff scope

This PREP adds **exactly one file**:

- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s3b-prep-mathlib-citation-audit.md`

**No edits** to:
- `problem.md`, `state.md`, `knowledge.md`, `approaches/`, `lean/`, `literature/`.
- Any `.lean` file (parent `ShapleyFolkman.lean` untouched; pending
  `ShapleyFolkmanOQ01.lean` not yet created).
- `src/data/proofs/shapley-folkman/` or `src/data/research/problems/shapley-folkman-oq-01.json`
  (gallery and tracker integration unchanged).
- Any preceding `sessions/` PREP doc (each is immutable after merge).

No `lake build` attempted; no `.lake` symlink risk.

## §10 Honesty disclosures

1. **Audit refers to v4.26.0 tag**, not master. All `gh api repos/leanprover-community/mathlib4/contents/...?ref=v4.26.0` calls verified at audit time
   2026-05-12. The corresponding `master` HEAD audit done by #18491 is also
   correct as a master statement; the discrepancy is purely the tag-vs-HEAD
   gap (master has a deprecation block that v4.26.0 lacks).

2. **Phantom-lemma findings are name-only.** All three (`single_ne_zero_iff`,
   `single_orthonormal`, `smul_right_inj`) are confirmed-zero on the
   `search/code` API for the entire `leanprover-community/mathlib4` repo (not
   just v4.26.0). If a future Mathlib version adds these names, the cites
   in #18491 and #18452 would retroactively become valid; for now they are
   not. The substitute lemmas (`single_eq_zero_iff.not`, `orthonormal_single`,
   coordinate-eval) are all present at v4.26.0 with the listed signatures.

3. **No new mathematical content** beyond #18491. This PREP is a pure
   citation-and-name audit. The proof strategy (Approach C, coordinate-eval
   route, `Fin N` tightness statement) is unchanged.

4. **Tactic chains in §3.3, §7, §8 are paper proofs.** No `lake build`
   attempted. The `simp [EuclideanSpace.single_apply, PiLp.smul_apply]` step
   in §7 may need elaboration tuning (specifically: `PiLp.smul_apply` may need
   `Pi.smul_apply` instead if `EuclideanSpace` is unfolded by `simp` first).
   The fallback is to add `Finset.sum_apply` or to expand explicitly:
   `show (1/2 : ℝ) * (if j = j then 1 else 0) = if j = j then 1 else 0`.

5. **`.not.mpr` semantics**. The Lean 4 core definition is
   `theorem Iff.not : (a ↔ b) → (¬a ↔ ¬b)`. The `.not` field on an `Iff`
   returns the negated equivalence. If a future Lean core renames it, the
   §3.3 Option A invocation would need a one-token swap (e.g., to
   `not_iff_not.mpr`). At v4.26.0 it is stable.

6. **No `proofs/.lake` directory touched, no symlink-loop risk.** Per
   `feedback_researcher_lake_symlink_loop_and_wipe.md`.

7. **No edits to `problem.md` / `state.md` / `knowledge.md`** — those record
   the high-level approach (Approach C selected); this PREP is a tactic-level
   companion under `sessions/`.

## §11 Decision log

- **2026-05-12 S3b PREP**: Decision to ship as `sessions/` doc-only correction
  rather than as a `git revert` of #18491 §5 step 4. Reason: the strategic
  content of #18491 is correct; only the phantom-lemma names need swapping.
  A `revert` would lose the §3.1 helper, §4 coord-eval recipe, §5 bridge table.
  An audit-companion preserves all prior work and surfaces the errata.

- **2026-05-12 S3b PREP**: Decision to recommend §3.3 Option A (`.not.mpr` swap)
  over Option B (`simp`) as the default for S3 ACT. Reason: §3.3 Option A is
  closer to #18491's structure (the writer following #18491 §5 step 4 literally
  will recognize the swap); Option B requires understanding why `simp` discharges
  `EuclideanSpace.single_eq_zero_iff` to `(1:ℝ) ≠ 0`.

- **2026-05-12 S3b PREP**: Decision to verify line numbers at `v4.26.0` tag
  (not `master`) for **all** citations going forward. The project pins v4.26.0
  via `lean-toolchain`; auditing against `master` is misleading.

- **2026-05-12 S3b PREP**: Decision to flag `EuclideanSpace.single` `def` vs
  `abbrev` discrepancy in §6 even though it doesn't affect S3 ACT. Reason:
  any future PREP that tries to bridge `EuclideanSpace` ↔ `PiLp` machinery
  at v4.26.0 will hit this and the §6 note saves a debug cycle.

## §12 References

### Mathlib v4.26.0 source citations (this audit, 2026-05-12)

- `Mathlib/Analysis/Convex/Hull.lean:124` — `convexHull_pair`.
- `Mathlib/Analysis/Convex/Segment.lean:50` — `def segment`.
- `Mathlib/Analysis/Convex/Segment.lean:207` — `segment_eq_image'`.
- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:257` — `def EuclideanSpace.single`.
- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:266` — `EuclideanSpace.single_apply`.
- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:271` — `EuclideanSpace.single_eq_zero_iff`.
- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:309` — `EuclideanSpace.orthonormal_single`.
- `Mathlib/Algebra/NoZeroSMulDivisors/Defs.lean:72` — `smul_eq_zero`.
- `Mathlib/Algebra/NoZeroSMulDivisors/Defs.lean:76` — `smul_ne_zero_iff`.
- `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:140,153` — `prod_ite_eq` / `prod_ite_eq'` (generates `sum_ite_eq` / `sum_ite_eq'` via `@[to_additive]`).

### Predecessor PREP files

- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s01-observe.md` (PR #18345).
- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s01b-aumann-lyapunov-prereq-audit.md` (PR #18414).
- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s2-prep-approach-c-ell2-counterexample-design.md` (PR #18397).
- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s2b-prep-construction-verification.md` (PR #18452).
- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s3-prep-pair-convexhull-extraction-recipe.md` (PR #18491).
- **This file**: `2026-05-12-s3b-prep-mathlib-citation-audit.md`.

### Project files

- `proofs/Proofs/ShapleyFolkman.lean` — parent theorem (verified, no edits).

**End of S3b PREP.**
