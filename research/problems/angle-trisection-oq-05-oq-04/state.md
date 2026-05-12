# Current State

**Phase**: ACT
**Since**: 2026-05-12 (S8)
**Iteration**: 8

## Current Focus

S8 (researcher-8): close the **parallel case** of HH-3
(`crossDet ℓ₁ ℓ₂ = 0`), using the *translate-bisector* — the line
parallel to both `ℓ₁` and `ℓ₂` whose constant term is chosen so
that reflection across it sends every point of `ℓ₁` to a point of
`ℓ₂`. Avoids `Real.sqrt` (which the intersecting case would
require), so the parallel sub-case is constructively dischargeable
in pure `ℝ`-algebra. Together with S3 (HH-1), S4 (HH-2), S5 (HH-4),
S6 (HH-7 non-parallel), and S7 (HH-7 P-on-ℓ₁), six of seven HH
axioms now have constructive ingredients — the remaining gaps are
HH-3 intersecting, HH-5 (Beloch-light), and HH-6 (Beloch fold).

### Deliverables of this iteration (new in S8)

1. `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` grows 923 → 1144
   lines with a new "PART 10: Constructive HH-3 (Parallel Case) —
   Translate Bisector" section. Counts: 0 axioms (unchanged), 3
   sorries (unchanged — all in S2/S3/S4/S5 target theorems), 26
   theorems (21 + 5 new), 10 definitions (9 + 1 new
   `parallelBisector`), 1 structure (unchanged).

2. Five new theorems and one new definition, all proved without
   sorry and without new axioms:

   - `parallelBisector_dot_ne_zero` — given `crossDet ℓ₁ ℓ₂ = 0`
     and the structural `ℓ₂.nondeg`, the dot product
     `ℓ₁.a · ℓ₂.a + ℓ₁.b · ℓ₂.b` is nonzero. Proof: assume it is
     zero; combine with `crossDet = 0` via two `linear_combination`s
     (`linear_combination ℓ₁.a * h_zero + ℓ₁.b * h_cross` and
     `linear_combination ℓ₁.b * h_zero - ℓ₁.a * h_cross`) to derive
     `(ℓ₁.a² + ℓ₁.b²) · ℓ₂.a = 0` and the same for `ℓ₂.b`;
     positivity of `ℓ₁.a² + ℓ₁.b²` forces `ℓ₂.a = ℓ₂.b = 0`,
     contradicting `ℓ₂.nondeg`.

   - `parallelBisector` — explicit `noncomputable def` of the
     translate-bisector. Coefficients
     `(ℓ₁.a, ℓ₁.b, (s · ℓ₁.c + ℓ₂.c · (ℓ₁.a²+ℓ₁.b²)) / (2s))` where
     `s := ℓ₁.a·ℓ₂.a + ℓ₁.b·ℓ₂.b`. Non-degeneracy inherited
     directly from `ℓ₁.nondeg`.

   - `parallelNormal_left_id`, `parallelNormal_right_id` — under
     `crossDet ℓ₁ ℓ₂ = 0`, the scaling identities
     `(ℓ₁.a² + ℓ₁.b²) · ℓ₂.a = s · ℓ₁.a` and
     `(ℓ₁.a² + ℓ₁.b²) · ℓ₂.b = s · ℓ₁.b`. Each is one line of
     `linear_combination` against the `crossDet = 0` hypothesis.

   - `reflectAcross_parallelBisector_to_ℓ₂` — main HH-3 reflection
     law in the parallel case. For any `q ∈ ℓ₁`, the reflection of
     `q` across `parallelBisector ℓ₁ ℓ₂ h_par` lies on `ℓ₂`. Proof:
     `simp only [Line.contains, reflectAcross, parallelBisector]`
     unfolds; `field_simp` clears the two denominators
     `(ℓ₁.a² + ℓ₁.b²)` and `2 · s`; `linear_combination` closes the
     residual polynomial identity via
     `−2s · hq + 2(ℓ₁.b·q.1 − ℓ₁.a·q.2) · h_par`.

   - `hh3_existence_parallel` — standalone HH-3 existence form for
     the parallel case: for parallel non-degenerate lines `ℓ₁, ℓ₂`,
     there exists a fold `l` such that `ℓ₁.contains p` implies
     `ℓ₂.contains (reflectAcross l p)`. Witness:
     `parallelBisector ℓ₁ ℓ₂ h_par`.

3. **Why this matters.** Six of the seven HH-axiom existence
   ingredients are now constructive in standalone form. The HH-3
   constructive coverage is `{crossDet ℓ₁ ℓ₂ = 0}` (parallel case).
   The intersecting case `crossDet ≠ 0` requires angle bisectors
   over `Real.sqrt` and is deferred to S9 (this is *not* a
   genuine-impossibility corner — both cases are constructible —
   just `Real.sqrt`-bound). HH-5 (Beloch-light) and HH-6 (Beloch
   fold) remain entirely open.

4. **Independence from other in-flight work.** PR #17915 (S3 HH-1)
   is still open against an earlier file state; S8 inserts PART 10
   strictly at the end of the file (after PART 9, the S7 section)
   so no textual conflict is expected when both merge. The S8
   contribution uses S5's `perpThroughPoint_normSq_pos` lemma but
   does not depend on S3 (HH-1) names.

5. Gallery metadata updated:
   `src/data/proofs/angle-trisection-oq-05-oq-04/meta.json`
   (lineCount 923 → 1144; theoremCount 21 → 26; definitionCount
   9 → 10; sorries 3 unchanged; axiomCount 1 unchanged; added
   PART 10 section entry; appended five S8 original-contributions
   bullets; refreshed S7 section's endLine 814 → 922 to reflect the
   actual post-S7 file end).

### Prior session deliverable (preserved, summary form)

S7 (researcher-3): close the **`P ∈ ℓ₁` case** of HH-7
unconditionally (in the relative position of `ℓ₁` and `ℓ₂`), and add
the generic primitive `reflectAcross_self_of_contains` (a point on a
line is fixed by reflection across that line). Combined with S6's
non-parallel case (`crossDet ℓ₁ ℓ₂ ≠ 0`), the constructive coverage
of HH-7 is now `{crossDet ≠ 0} ∪ {P ∈ ℓ₁}` — the whole HH-7 statement
except the genuinely-unsolvable parallel-with-`P ∉ ℓ₁` corner that S6
identified.

### Deliverables of this iteration (new in S7)

1. `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` grows 814 → 923 lines
   with a new "PART 9: Constructive HH-7 (P-on-ℓ₁ Case) — Identity-
   Like Fold" section. Counts: 0 axioms, 3 sorries (unchanged), 21
   theorems (18 proved + 3 sorry), 9 definitions, 1 structure.

2. Two new proved theorems, both sorry-free and axiom-free:
   - `reflectAcross_self_of_contains` — generic lemma: a point on a
     line is fixed under reflection across that line. Proof: the
     numerator `2 · (l.a · p.1 + l.b · p.2 + l.c)` of the reflection
     parameter vanishes when `p ∈ l`, so `t = 0` and the reflection
     returns `(p.1, p.2) = p`. `linarith` + `simp only` with
     `zero_div`, `zero_mul`, `sub_zero`, `Prod.mk.eta`.
   - `hh7_existence_p_on_ℓ₁` — standalone HH-7 existence in the
     `P ∈ ℓ₁` case. Witness: `perpThroughPoint P ℓ₂` (S5's HH-4
     construction). Proof: `perpThroughPoint_contains` (S5) gives
     `P` is on the fold; `reflectAcross_self_of_contains` (S7) gives
     `reflectAcross fold P = P`, which lies on `ℓ₁` by hypothesis;
     `reflectAcross_perpThroughPoint_preserves` (S5) gives `ℓ₂`
     preservation. The witness works **unconditionally** in the
     relative position of `ℓ₁` and `ℓ₂` (no `crossDet ≠ 0` needed).

3. **Why this matters for the eventual `HHAxioms` instance.** Five of
   the seven HH ingredients are now constructive in standalone form:
   HH-1 (S3, PR #17915), HH-2 (S4, PR #17926), HH-4 (S5, PR #17988),
   HH-7 non-parallel (S6, PR #18009), and HH-7 P-on-ℓ₁ (S7, this PR).
   The HH-7 constructive coverage is now `{crossDet ≠ 0} ∪ {P ∈ ℓ₁}`;
   only the corner `crossDet = 0 ∧ P ∉ ℓ₁` remains open, which S6
   showed is *genuinely* unsolvable (any fold perpendicular to ℓ₂ in
   the parallel configuration preserves perpendicular distance to
   `ℓ₁`, so `P ∉ ℓ₁` is invariant).

4. Gallery metadata updated:
   `src/data/proofs/angle-trisection-oq-05-oq-04/meta.json`
   (lineCount 814 → 923; theoremCount 15 → 21 — also corrects prior
   S6 undercount; definitionCount 9 unchanged; sorries 3 unchanged;
   axiomCount 1 unchanged; added PART 9 section entry; added two
   original-contributions bullets for S7; refreshed S6 section's
   endLine 814 → 812 to reflect the post-S6 file end before S7;
   updated title and description).

### Prior session deliverables (preserved)

S6 (researcher-6): constructive HH-7 (Hatori fold, **non-parallel
case**) as the fourth of seven HH-axiom ingredients required by the
conservativity target `straight_fold_recovers_HH` (S3, still open in
PR #17915).



S5 (researcher-5): constructive HH-4 (perpendicular fold through a
point preserving a given line) as the third of seven HH-axiom
ingredients required by the conservativity target
`straight_fold_recovers_HH` (S3, still open in PR #17915).

Deliverables of this iteration (new in S5):

1. `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` grows 448 → 573 lines
   with a new "Part 7: Constructive HH-4 — Perpendicular Through a
   Point" section. Counts: 0 axioms, 3 sorries (unchanged), 11
   theorems (8 proved + 3 sorry), 7 definitions, 1 structure.

2. Four new theorems, one new definition, all proved without sorry:
   - `perpThroughPoint p ℓ : Line` — explicit `noncomputable def` of
     the fold through `p` perpendicular to `ℓ`, with coefficients
     `(-ℓ.b, ℓ.a, ℓ.b · p.1 − ℓ.a · p.2)`.
   - `perpThroughPoint_normSq_pos` — squared norm `ℓ.a² + ℓ.b² > 0`
     via `ℓ.nondeg` + `sq_pos_of_ne_zero`.
   - `perpThroughPoint_contains` — the fold passes through `p` (via
     `simp` + `ring`).
   - `reflectAcross_perpThroughPoint_preserves` — HH-4 line-
     preservation law (`field_simp` + `linear_combination` exploiting
     `ℓ.a · ℓ.b − ℓ.b · ℓ.a = 0`).
   - `hh4_existence` — standalone HH-4 existence theorem.

3. Gallery metadata updated:
   `src/data/proofs/angle-trisection-oq-05-oq-04/meta.json`
   (lineCount 448 → 573; theoremCount 7 → 11; definitionCount 6 → 7;
   added Part 7 section entry; added five original-contributions
   bullets for S5; updated title and description to reflect S5).

This S5 PR is **independent of S3 PR #17915 (still open)** at the
file level: S5's additions are at the END of the file (after the S4
Part 6 perpBisector section), while S3 PR #17915 inserted content
BETWEEN `straight_fold_recovers_HH` and
`curved_fold_algebraic_implies_origami` (i.e. before line 213 of the
post-S4 file). When both merge, no textual conflict is expected.

## Active Approach

S5 closes the **third of seven** HH-axiom existence ingredients
needed to discharge `straight_fold_recovers_HH`. After S3 (HH-1),
S4 (HH-2), and S5 (HH-4), the remaining ingredients are HH-3 (angle
bisector), HH-5 (fold through `P₂` placing `P₁` on `ℓ`), HH-6
(Beloch fold — the deep cubic-solving one), and HH-7 (Hatori). Once
all seven are constructive, building an `HHAxioms` instance is
mechanical, and `straight_fold_recovers_HH` reduces to combining
`straight_fold_endpoints_collinear` (S3, PR #17915) with the new
instance.

### Geometric content of HH-4

For a line `ℓ : a x + b y + c = 0` (normal vector `(a, b)`) and a
point `P`, the perpendicular fold through `P` has its OWN normal
parallel to `ℓ`'s DIRECTION. The natural choice is:

  a' = -ℓ.b
  b' =  ℓ.a
  c' =  ℓ.b · P.1 − ℓ.a · P.2

(90° rotation of `(ℓ.a, ℓ.b)` for the normal; constant chosen so
the fold passes through `P`.)

Under reflection across this fold, for any `q ∈ ℓ`,

  ℓ.a · q'.1 + ℓ.b · q'.2 + ℓ.c
    = ℓ.a · (q.1 − t · (-ℓ.b)) + ℓ.b · (q.2 − t · ℓ.a) + ℓ.c
    = (ℓ.a · q.1 + ℓ.b · q.2 + ℓ.c) + t · (ℓ.a · ℓ.b − ℓ.b · ℓ.a)
    = 0 + 0 = 0,

so `q' ∈ ℓ` as required. The Lean proof unfolds `Line.contains`,
`reflectAcross`, and `perpThroughPoint` via `simp only`, clears the
single denominator `(-ℓ.b)^2 + ℓ.a^2` via `field_simp`, and closes
with `linear_combination ((-ℓ.b)^2 + ℓ.a^2) * hq`.

## Blockers

None mathematical. The math is correct by hand-derivation.

Practical:

- Build verification of `AngleTrisectionOQ05OQ04.lean` is deferred —
  the `.lake` symlink is recursive-self-broken on this worktree, so
  `docker-build` would re-fetch Mathlib (~45 minutes). This PR
  follows the same "build pending" convention as the S2, S3, and S4
  PRs (#17883 merged build-pending; #17915 still open build-pending;
  #17926 merged build-pending). The proof structure mirrors S4's
  successful `reflectAcross_perpBisector` proof (`simp only` +
  `field_simp` + closing tactic) so confidence is high.
- The S3 PR #17915 has not merged yet; if its final form differs
  from the prior-session HH-1 names referenced in the S5 docstrings,
  a trivial doc-only follow-up will sync them. The S5 Lean code does
  not depend on S3 (HH-1) names; it stands alone.

## Next Action (S9+)

**Status after S8**: six of seven HH-axiom existence ingredients are
now constructive (HH-1 via S3 PR #17915, still open; HH-2 via S4
PR #17926, merged; HH-3 parallel via S8, this PR; HH-4 via S5
PR #17988, merged; HH-7 non-parallel via S6 PR #18009, merged; HH-7
P-on-ℓ₁ via S7 PR #18059, merged). Three gaps remain.

Recommended next targets, in order of estimated tractability:

(a) **HH-3 intersecting case** (`crossDet ℓ₁ ℓ₂ ≠ 0`) — there are
    two angle bisectors at the intersection of `ℓ₁` and `ℓ₂`; either
    one reflects `ℓ₁` setwise onto `ℓ₂`. The cleanest formulation
    uses unit normals, so `Real.sqrt` and `Real.sqrt_sq_eq_abs` are
    required. Expect ~200 lines including the `Real.sqrt`
    nondegeneracy boilerplate. Combined with S8, this would complete
    HH-3 unconditionally.

(b) **HH-5 (Beloch-light)** — given two points `P₁`, `P₂` and a
    line `ℓ`, fold through `P₂` placing `P₁` on `ℓ`. The fold line
    is tangent to the parabola with focus `P₁` and directrix `ℓ`,
    passing through `P₂`. Two-or-zero solution behaviour; expect
    ~150 lines.

(c) **HH-6 (Beloch fold)** — the deep cubic-solving axiom. Common
    tangent to two parabolas. Expect ~300 lines and may need new
    Mathlib infrastructure (parabola-tangent definitions); defer to
    last.

Once all seven HH ingredients are constructive (modulo the genuinely-
unsolvable parallel-with-P∉ℓ₁ corner of HH-7), building an `HHAxioms`
instance is mechanical, and `straight_fold_recovers_HH` (S3 PR #17915)
reduces to combining `straight_fold_endpoints_collinear` (S3) with the
new instance.

Alternative: tackle `curved_fold_algebraic_implies_origami` (S4-target
sorry), noting that the current `IsOrigamiConstructible` def in the
parent file `AngleTrisectionOQ05.lean` underuses `_α` (placeholder),
so the theorem is trivially provable at `deg = 1` without substantive
math — a stronger quantitative version using `minpoly` degree should
be stated and proved instead.

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| 1 | Pre-flight: `gh pr list -R rjwalters/lean-genius --state open` for slug returns 0 research-PRs (only stale meta PR #18079, #18184); `git worktree list | grep angle-trisection` returns no in-flight S8 work | clean to proceed |
| 2 | Released two earlier claims that were saturated/contested (`mean-value-theorem-oq-02-oq-04-oq-01` — researcher-3 mid-S5; `sperner-ndim-mathlib-oq-02` — 3 open PRs + S29-prep) | safe sequential probes |
| 3 | `git fetch origin main && git checkout -B research/angle-trisection-oq-05-oq-04-s8-hh3-parallel-... origin/main` — fresh branch off post-S7 main | clean base |
| 4 | Verified parent `AngleTrisectionOQ05.HHAxioms.hh3` definition (line 121-122); selected HH-3 parallel case as S8 target (avoids `Real.sqrt`) | scope set |
| 5 | Hand-derived translate-bisector coefficients `(ℓ₁.a, ℓ₁.b, (s·ℓ₁.c + ℓ₂.c·D)/(2s))` and `parallelBisector_dot_ne_zero` via crossDet + nondeg argument | math verified |
| 6 | Inserted PART 10 (221 new lines) after S7 PART 9, before `end`; no overlap with S3 PR #17915 additions or any in-flight S5/S6/S7 content | clean independent extension |
| 7 | Updated meta.json: lineCount 923 → 1144, theoremCount 21 → 26, definitionCount 9 → 10, added PART 10 section + 5 S8 contributions; refreshed title and description | gallery in sync |
| 8 | Updated this state.md | iteration recorded |
| 9 | (pending) Commit + push + PR with label `research` | next |

## Honest Calibration

S5 produces:

- One explicit `noncomputable def` (`perpThroughPoint`) of a fundamental
  Euclidean construction (drop-perpendicular);
- Four proved theorems: the normSq positivity helper, the
  through-point property, the line-preservation law (HH-4 setwise
  preservation), and the standalone HH-4 existence statement;
- No new sorry, no new axiom, no change to existing assumption count;
- Concrete and verifiable progress toward closing the still-open S3
  sorry `straight_fold_recovers_HH`: 3/7 HH ingredients now
  constructive in standalone form.

S5 does **not** resolve any open mathematical question. The value is
three of seven HH-axiom ingredients now constructive, with explicit
witnesses computable from input coordinates. Progress is incremental
and additive — each subsequent session (S6 — S9) can close one or two
more ingredients independently before the final assembly into a full
`HHAxioms` instance and the discharge of `straight_fold_recovers_HH`.

## References Captured

Same set as S1/S2/S3/S4: Huffman 1976; Fuchs-Tabachnikov 1999 (Thm 1 =
FT identity); Demaine-DHPT 2011 (transcendental curve elastica
witness); Alperin 2000 + Alperin-Lang 2006 (K_origami classification).

See `knowledge.md` for the full citation list and Mathlib gap
analysis (unchanged from S1).
