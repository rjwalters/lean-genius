# Research State: product-of-segments-of-chords-oq-02

## Current State
**Phase**: RESOLVED (all work merged to main; verified 2026-06-15 by researcher-1)
**Path**: full
**Since**: 2026-06-15T14:05:00Z
**Iteration**: 6

## RESOLUTION (researcher-1, 2026-06-15) — supersedes the stale ACT notes below
Everything the older sections list as "pending" is **already on main**:
- `ProductOfSegmentsOfChordsConverse.lean` is **0 sorry / 0 axiom** (the
  `gram_pos` and `circumcenter_signed` gaps were closed by **merged** PR #24462)
  and is **registered** in `proofs/Proofs.lean` (line 2733).
- The parent's FALSE axiom `converse_product_implies_concyclic_axiom` is
  **eliminated**: `ProductOfSegmentsOfChords.lean` has **0 axioms** (the name now
  survives only in docstrings noting it was "previously a false axiom"). PR #24500
  (parent axiom-elimination plan) is merged.

So the corrected **signed** converse is fully machine-checked and the unsigned
converse is documented false (counterexample in Lean). No open work remains for
this slug; the build-gated / Aristotle "Next Action" steps in the older sections
are **done**. The depth-first picker should stop re-selecting this. The sections
below are retained as historical record only.

## S5 (researcher-5) — saturation check, stood down (no PR)
The converse (`ProductOfSegmentsOfChordsConverse.lean`) is fully assembled and its sole remaining
`sorry` (`gram_pos`) is **already discharged in open MERGEABLE PR #24462** (file → 0 sorry/0 axiom).
Re-proving = duplicate, so stood down. The only remaining oq-02 work is eliminating the parent's
FALSE axiom `converse_product_implies_concyclic_axiom` (axiomCount 1→0); verified it is referenced
ONLY by the in-file re-export (no external `.lean` consumer) and named by one gallery annotation.
That cleanup is coupled to #24462 (the corrected converse lives there) and is a registered-flagship
edit — doing it now under blackout would be delete-then-readd churn or a blind multi-file edit, so
deferred. Documented a ready-to-execute post-merge patch in knowledge.md "Session 2026-06-15
(researcher-5)". No code shipped (saturation + dual blackout).

## Current Focus
Reduced the single opaque circumcenter `sorry` to one isolated, reusable geometric
lemma. `signed_converse_implies_concyclic` is now **fully assembled** from a
translation-normalized lemma `circumcenter_signed`; the only remaining `sorry` lives
inside `circumcenter_signed` (the build-gated 2×2 perpendicular-bisector solve). This
turns a bespoke 4-point statement into a clean origin-centered fact that is a much
better Aristotle target. Numerically validated the reduction (signed power ⟹ 4th point
concyclic) over 19987 random configs (`verify_signed_converse.py`).

## Active Approach
Coordinate / circumcenter construction over `EuclideanSpace ℝ (Fin 2)`:
1. Correct the converse statement (signed power `t‖A-P‖² = s‖C-P‖²` +
   linear-independence of `A-P, C-P`).  [DONE — `signed_converse_implies_concyclic`]
2. Translation reduction `O = P + Õ`, `X-(P+Õ)=(X-P)-Õ`; radius `>0` from `A≠C`
   (`u≠v` via `LinearIndependent.injective`).  [DONE — assembly fully written]
3. `circumcenter_signed (u v t s)`: solve 2×2 perp-bisector system in basis `{u,v}`
   (det `= ‖u‖²‖v‖²−⟪u,v⟫² ≠ 0` Cauchy–Schwarz), then `‖s•v−O‖=‖u−O‖` via polarization
   + `t‖u‖²=s‖v‖²`.  [sorry — the lone remaining gap, build-gated / Aristotle target]

## Degeneracy analysis (new this session)
The statement carries **no** `t≠1`/`s≠1` hypotheses, and is still true at those values:
`t=1 ⟹ B=A`, `s=1 ⟹ D=C`, so the corresponding equalities in `circumcenter_signed`
(`‖u-O‖=‖t•u-O‖` etc.) become `rfl`-trivial and no extra non-degeneracy is needed —
the signed hypothesis only does work in the generic `t,s≠1` case. Confirmed in the
numeric sweep (degenerate scalars included, 0 failures).

## Counterexample (now in Lean)
`unsigned_converse_counterexample_general` (any two unit vectors `e₀, e₁`) and the
concrete `unsigned_converse_counterexample` (standard basis): witness
`P=0, A=e₀, B=-4•e₀, C=e₁, D=4•e₁`. Proof works entirely with squared norms /
polarization (`norm_sub_sq_real`, `real_inner_smul_left`, `norm_smul`): the three
perpendicular-bisector equalities force `⟪e₀,O⟫ = -3/2`, `⟪e₁,O⟫ = 5/2`, and
`⟪e₀,O⟫ = ⟪e₁,O⟫` simultaneously → contradiction. No orthogonality of `e₀,e₁` needed.

## Attempt Count
- Total attempts: 3 (ORIENT paper feasibility; ACT Lean counterexample; ACT reduction)
- Current approach attempts: 2 (counterexample lemma + signed-converse assembly)
- Approaches tried: 2

## Blockers
- Docker build + Aristotle MCP unavailable this session (dual blackout — `docker info`
  hangs; Aristotle `prove` returns 404 "Resource not found"). The Lean file is written
  but NOT machine-checked. The lone remaining `sorry` (`circumcenter_signed`) cannot be
  discharged/submitted yet. Mathematics fully resolved + numerically validated.

## Next Action
When Docker is available:
1. Build `ProductOfSegmentsOfChordsConverse.lean`; fix any lemma-name drift. Risk points:
   `norm_sub_sq_real`, `real_inner_smul_left`, `EuclideanSpace.norm_single` (counterexample);
   `LinearIndependent.injective`, `norm_pos_iff`, `abel` on `Vec2` (new assembly).
2. Discharge the single `circumcenter_signed` `sorry` via the 2×2 perp-bisector solve
   (write `O = x•u + y•v`, Cramer with det `‖u‖²‖v‖²−⟪u,v⟫²`), OR submit that one
   isolated lemma to Aristotle (now a clean origin-centered target).
3. Once both compile, fold the counterexample + corrected statement into the parent
   `ProductOfSegmentsOfChords.lean`, delete the false axiom, drive `axiomCount` → 0,
   register the file in `Proofs.lean`.
