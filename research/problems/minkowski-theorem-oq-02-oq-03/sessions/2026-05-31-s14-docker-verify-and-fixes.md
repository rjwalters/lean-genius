# S14 ACT — Docker verify of OQ-03 graduation candidate + 9 fixes

- **Date**: 2026-05-31 (UTC)
- **Researcher**: researcher-1
- **Mode**: Lean ACT (bug-fix) + STATE-SYNC (build qualifier flip)
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
- **Predecessor**: S13 S6 ACT (PR #21529, merged 2026-05-31 16:31Z, "build pending — G9 lake self-loop")

## §1. Disposition

Per the [[project_lake_self_loop_main_repo]] memory (G9 self-symlink is
INERT for Docker builds; the cached "build pending — G9 lake self-loop"
qualifier shipped by #21239 / #21492 / #21529 is **obsolete**), this
session attempted the deferred Docker verification of the OQ-03
graduation candidate (`MinkowskiTheoremOQ02OQ03.lean`, 569 LOC, 14 thm,
0 sorries, 0 axioms post-S13).

**Outcome.** Docker verify on the as-merged file from #21529 **FAILED**
with **8 distinct compile errors** spanning PARTS 6 / 7 / 8 / 9. The
"build pending" qualifier on #21239, #21492, and #21529 was masking
real, substantive bugs. A 9th error (`lt_div_iff` deprecation at the
pin) surfaced after the first 8 fixes landed.

This S14 ACT discharges all 9 errors. Final Docker build is **CLEAN at
3075 jobs** (Proofs.MinkowskiTheoremOQ02OQ03 built in 9.2s after cache
get; total wall-clock for cold cache + Mathlib clone + build ≈ 3 min).

**File metric delta** (`proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`):

| Metric | Before (post-#21529) | After (this S14 ACT) | Δ |
|---|---|---|---|
| LOC | 569 | 568 | −1 (two `simp only [Pi.zero_apply]` lines removed) |
| Theorems / private | 14 / 0 | 14 / 0 | 0 |
| Definitions | 3 | 3 | 0 |
| Sorries | 0 | 0 | 0 |
| `axiom` declarations | 0 | 0 | 0 |
| Docker build | "pending — G9" | **3075 jobs clean** | qualifier removed |

## §2. The 9 errors and their fixes

All errors localised to four theorems: `dirichletSetN_volume` (#21492
PART 6), `stdLatticeN_coords` (#21239 PART 7),
`dirichletSetN_volume_gt_two_pow` (#21529 PART 8), and
`simultaneous_dirichlet_from_minkowski` (#21529 PART 9).

### Error 1 — L389 (PART 6, #21492): abs/inv ordering

**Symptom.**
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  |(-1) ^ n|⁻¹
in the target expression
  ENNReal.ofReal |((-1) ^ n)⁻¹| • volume = volume
```

**Root cause.** The `show` lemma proved `|(-1)^n|⁻¹ = 1` (abs-then-inv);
the goal needed `|((-1)^n)⁻¹| = 1` (inv-inside-abs). The two are equal
via `abs_inv : |x⁻¹| = |x|⁻¹`, but the rewrite-as-written looked for
the wrong-shape pattern.

**Fix.** Change the show LHS to `|((-1 : ℝ)^n)⁻¹|` and prepend
`abs_inv` to the proof chain. Final form:
```lean
show |((-1 : ℝ)^n)⁻¹| = 1 from by
  rw [abs_inv, abs_pow, abs_neg, abs_one, one_pow, inv_one]
```

### Error 2 — L419 (PART 7, #21239): `Finset.sum_ite_eq` vs `_eq'`, `mul` vs `smul` simp args

**Symptom.**
```
error: unsolved goals
…
⊢ (∑ x, ↑(c x) * if i = x then 1 else 0) = ↑(c i)
warning: unused simp arg: smul_ite
warning: unused simp arg: smul_zero
warning: unused simp arg: mul_one
warning: unused simp arg: Finset.sum_ite_eq'
warning: unused simp arg: Finset.mem_univ
warning: unused simp arg: if_true
```

**Root cause.** Two cascading mismatches in the simp list:
1. After `smul_eq_mul` fires, the goal has `↑(c x) * ite (i = x) 1 0`
   shape. The remaining `smul_ite`, `smul_zero` are for `smul`-shaped
   terms and never fire; the goal needs `mul_ite`, `mul_zero` to push
   the multiplication inside the `ite`.
2. After `mul_ite`/`mul_one`/`mul_zero`, the goal is
   `∑ x, ite (i = x) ↑(c x) 0 = ↑(c i)`. The condition `i = x` has
   target `i` on the left and sum-var `x` on the right, matching
   `Finset.sum_ite_eq` (NOT the primed `_eq'` variant, which has the
   `Eq` arguments swapped). Per `Mathlib/Algebra/BigOperators/Group/Finset.lean:1132/1144`.

**Fix.**
```lean
simp only [Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply,
           Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
           Finset.sum_ite_eq, Finset.mem_univ, if_true]
```
(Replaces `smul_ite`/`smul_zero` with `mul_ite`/`mul_zero`; replaces
`Finset.sum_ite_eq'` with `Finset.sum_ite_eq`.)

### Errors 3 & 4 — L459 / L460 (PART 8, #21529): ENNReal `(2 : ENNReal)` vs `ENNReal.ofReal 2` + bearer name

**Symptom (L459).**
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ENNReal.ofReal 2 ^ ?n
in the target expression
  2 ^ (n + 1) = ENNReal.ofReal (2 ^ (n + 1))
```

**Symptom (L460).**
```
error: Unknown constant `ENNReal.ofReal_lt_ofReal_of_nonneg`
```

**Root cause (L459).** The reverse-rewrite `← ENNReal.ofReal_pow`
expects the goal to contain `ENNReal.ofReal 2 ^ n`, but the goal has
the literal `(2 : ENNReal) ^ (n + 1)`. The first rewrite step needs to
bridge `(2 : ENNReal) = ENNReal.ofReal 2` via the norm_cast lemma
`ENNReal.ofReal_ofNat` (`Mathlib/Data/ENNReal/Basic.lean:464`).

**Root cause (L460).** `ENNReal.ofReal_lt_ofReal_of_nonneg` does not
exist at the pin. The correct name is `ENNReal.ofReal_lt_ofReal_iff_of_nonneg`
(`Mathlib/Data/ENNReal/Real.lean:187`), an iff (not an implication);
calling `.mpr` extracts the implication.

**Fix.**
```lean
rw [show ((2 : ENNReal) ^ (n + 1)) = ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) from by
  rw [show (2 : ENNReal) = ENNReal.ofReal 2 from by norm_num,
      ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]]
apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr
```

### Errors 5 & 6 — L543 / L545 (PART 9, #21529): `Pi.zero_apply` no-op

**Symptom.**
```
error: `simp` made no progress
```

**Root cause.** After `apply Subtype.ext; funext i; refine i.cases ?_ (fun k => ?_)`,
the RHS is `(0 : ↥(stdLattice m)).val i`, not `(0 : Fin m → ℝ) i`.
`Pi.zero_apply` doesn't fire on the `Subtype` coercion. The downstream
`rw [hc 0, hc0]; simp` is robust enough to close the goal without the
no-op pre-simp.

**Fix.** Remove the two `simp only [Pi.zero_apply]` lines; the
subsequent `rw [hc 0, hc0]; simp` (and the `k.succ` analogue) close
both subgoals.

### Errors 7 & 8 — L560 / L563 (PART 9, #21529): spurious `Int.` namespace

**Symptom.**
```
error: Unknown constant `Int.abs_of_pos`
error: Unknown constant `Int.abs_of_neg`
```

**Root cause.** `abs_of_pos` / `abs_of_neg` are top-level lemmas
(LinearOrder-class, applicable to any `α` with `LinearOrder` +
`Neg`). The `Int.`-namespaced variants do not exist; the v4.26 codebase
uses the unqualified names throughout (e.g.
`Mathlib/Algebra/Order/Ring/Abs.lean:38,40`).

**Fix.** Drop the `Int.` prefix in both occurrences:
```lean
rw [abs_of_pos hpos]
rw [abs_of_neg hneg]
```

### Error bonus — L562 (PART 9): `le_of_not_lt` deprecation

**Symptom (warning, not error).**
```
warning: `le_of_not_lt` has been deprecated: Use `le_of_not_gt` instead
```

**Fix.** `le_of_not_lt hpos` → `le_of_not_gt hpos`. (Pre-emptively
flipped to avoid warning noise even though the build would have
succeeded.)

### Error 9 — L465 (PART 8, this iter 2): `lt_div_iff` → `lt_div_iff₀` at pin

**Symptom (surfaced after fixes 1-8 landed).**
```
error: Unknown identifier `lt_div_iff`
```

**Root cause.** The local Mathlib clone at
`/Users/rwalters/Projects/lean-genius-proofs/.lake/packages/mathlib/`
(HEAD `05147a76…`) is **more recent** than the project's pinned
Mathlib (`2df2f0150c…`). Between the pin and HEAD, the zero-class
typeclass refactor merged: at HEAD the lemma is `lt_div_iff` (file
line 70 in v4.26-ish), but at the project pin `git show
2df2f0150c…:Mathlib/Algebra/Order/Field/Basic.lean` shows the
zero-class-decorated name `lt_div_iff₀` (file line 70-ish at the pin).

**Fix.** `lt_div_iff hQn_pos` → `lt_div_iff₀ hQn_pos`.

**Generalised lesson.** When grepping the local clone for bearer
names, prefer `git show <pin>:<path>` (or check both the unqualified
and `₀`-decorated forms) for pin-faithful queries. The
[[reference_mathlib_source_paths_outside_g9_loop]] memory is amended
with this caveat.

## §3. Docker iteration timeline

| Iter | Memory | Outcome | Errors |
|------|--------|---------|--------|
| 1 | 6144 MB | Build failed | 8 errors (L389, L419, L459-461, L543, L545, L560, L563) |
| 2 | 6144 MB | Build failed | 1 error (L465 `lt_div_iff`) — fixes 1-8 verified, surface error 9 |
| 3 | 6144 MB | **Build succeeded** | 0 errors, 3075/3075 jobs |

Each iter cold-clones Mathlib via `lake update` (≈15s) → `lake exe
cache get` (≈3 min, 7727 oleans) → `lake build Proofs.MinkowskiTheoremOQ02OQ03`
(≈10-15s). Total iter wall-clock ≈3-4 min on M2 + Docker desktop
6 GB memory cap + 14 CPU. The `.lake/build` named volume persists
between iters but `.lake/packages/mathlib` (the source clone) does
not; this is per-design and the redundant clone cost is acceptable.

## §4. Honest framing

- **No new mathematics.** All 9 errors are mechanical:
  bearer renames, namespace prefixes, simp-set composition, and
  tactic shape. The S13 ACT's algebraic structure (Cassels 5-step
  Minkowski assembly with `dirichletSetN_volume_gt_two_pow` as the
  volume-threshold lemma) is **correct as designed**. The bugs were
  in how the design was encoded in Lean syntax.

- **The G9 qualifier was masking real bugs.** PRs #21239, #21492, and
  #21529 each shipped with `(build pending — G9 lake self-loop)` in
  their titles; this S14 session is the first time any of them was
  actually Docker-verified. Per
  [[project_lake_self_loop_main_repo]], the G9 qualifier was already
  documented as obsolete (empirically falsified by PRs #21558 and
  #21550 on the same date); this S14 is the third independent
  confirmation, on a research slug specifically.

- **Sorry / axiom counts unchanged.** This session does not add or
  remove any sorries or axioms — it only changes which Mathlib lemma
  names are invoked. The mathematical content of the file is
  identical pre- and post-S14.

- **Scope discipline.** Edits restricted to
  `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (9 fixes),
  `research/problems/minkowski-theorem-oq-02-oq-03/state.md` (one
  Lean-status table block + Merged PRs row + Session 14 block + Next
  Action + Attempt Count flips), the slug's research JSON
  (iter 13 → 14, focus / nextAction / leanFiles.lineCount 569 → 568,
  knowledge.progressSummary + insights for S14), and this new memo.
  No `meta.json`, gallery, parent-file, sibling-slug, or
  `lake-manifest.json` touches.

- **Iter bump**: 13 → 14.

## §5. Verdict — OQ-03 graduation status

**Promoted from "candidate (modulo Docker verify)" → "graduated
(Docker verified at v4.26.0 pin)".**

`simultaneous_dirichlet_from_minkowski` is now a build-verified,
0-sorry, 0-axiom theorem of `MinkowskiTheoremOQ02OQ03.lean` in the
lean-genius repository. The slug's OQ-03 target is achieved.

Subsequent work on this slug should be follow-up open questions
(Khintchine refinement, Schmidt subspace, metric Diophantine — see
Session 13 §7) via Seeker, not further ACT iterations on the OQ-03
statement itself. The champion can promote this slug's status to
`verified` (or `axiomatized`, if upstream `MinkowskiFundamentalTheorem`
turns out to carry structure-encoded assumptions per the
[[axiom_integrity_policy]] — to be audited separately).

## §6. Files touched this session

- `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` — 9 fixes, −1 LOC
- `research/problems/minkowski-theorem-oq-02-oq-03/state.md` — S14 catchup
- `src/data/research/problems/minkowski-theorem-oq-02-oq-03.json` — iter / phase / leanFiles flips
- `research/problems/minkowski-theorem-oq-02-oq-03/sessions/2026-05-31-s14-docker-verify-and-fixes.md` (this memo)

🤖 Generated with [Claude Code](https://claude.com/claude-code)
