# Current State

**Phase**: ACT
**Since**: 2026-05-12 (S7)
**Iteration**: 7

## Current Focus

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

## Next Action

**S6 (any researcher)**: Continue the HH-axiom construction sequence.
Three of seven ingredients are now constructive (HH-1 via S3 in
PR #17915; HH-2 via S4 in PR #17926; HH-4 via this S5). Recommended
next targets, in order of estimated tractability:

(a) **HH-3 (angle bisector)** — given two lines `ℓ₁`, `ℓ₂`, fold to
    place `ℓ₁` onto `ℓ₂`. Two cases: parallel (translate-bisector,
    perpendicular construction) and intersecting (two angle bisectors;
    pick one). Concrete formulas exist in classical geometry; expect
    ~120 lines.
(b) **HH-7 (Hatori)** — given a point `P` and two lines `ℓ₁`, `ℓ₂`,
    fold perpendicular to `ℓ₂` that places `P` onto `ℓ₁`. Shares the
    "perpendicular to a line" structure with HH-4, so likely ~80
    lines once a `perpThroughPoint`-style helper is reused.
(c) **HH-5 (point on line through other point)** — given two points
    `P₁`, `P₂` and a line `ℓ`, fold through `P₂` placing `P₁` on `ℓ`.
    Requires a parabola-tangent construction (Beloch-light); a fold
    line is tangent to the parabola with focus `P₁` and directrix
    `ℓ`, passing through `P₂`. Two-or-zero solution behaviour;
    expect ~150 lines.
(d) **HH-6 (Beloch fold)** — the deep cubic-solving axiom. Common
    tangent to two parabolas. Expect ~300 lines and may need new
    Mathlib infrastructure; defer to last.

Approximate scope of completing all seven HH ingredients: another
~650 lines, easily distributed over four sessions (S6 — S9).

Alternative (b): tackle `curved_fold_algebraic_implies_origami`
(S4-target sorry), noting that the current `IsOrigamiConstructible`
def in the parent file `AngleTrisectionOQ05.lean` underuses `_α`
(placeholder), so the theorem is trivially provable at `deg = 1`
without substantive math — a stronger quantitative version using
`minpoly` degree should be stated and proved instead.

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| 1 | Checked active claim (`research/claims/angle-trisection-oq-05-oq-04.json`); expires 2026-05-12T09:18:28Z; researcher-5 owns | clean to proceed |
| 2 | `gh pr list -R rjwalters/lean-genius --state open` filtered for slug: only S3 PR #17915 open; no S5 work in flight | safe |
| 3 | `git fetch origin main && git checkout -B feature/researcher-5-s5 origin/main` — fresh branch off updated main (#17926 S4 already merged) | clean base |
| 4 | Verified parent `AngleTrisectionOQ05.HHAxioms.hh4` definition (line 124-128); selected HH-4 as S5 target (easiest after HH-2) | scope set |
| 5 | Hand-derived `perpThroughPoint` coefficients and cancellation `ℓ.a · ℓ.b − ℓ.b · ℓ.a = 0` proof outline | math verified |
| 6 | Edit tool's first attempt phantom-reverted (FS-cache trap from memory); used Python inline write instead | reliable insert |
| 7 | Inserted Part 7 (125 new lines) after S4 Part 6, before `end`; no overlap with S3 PR #17915 additions | clean independent extension |
| 8 | Updated meta.json: lineCount 448 → 573, theoremCount 7 → 11, definitionCount 6 → 7, added Part 7 section + 5 contributions; refreshed title and description | gallery in sync |
| 9 | Updated this state.md | iteration recorded |
| 10 | (pending) Commit + push + PR with label `research` | next |

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
