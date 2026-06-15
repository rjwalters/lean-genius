# Knowledge Base: product-of-segments-of-chords-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Goal: discharge the axiom `converse_product_implies_concyclic_axiom` in
`proofs/Proofs/ProductOfSegmentsOfChords.lean` (lines 468-475), which claims the
**converse** of the intersecting-chords / power-of-a-point theorem:

> Given `P A B C D : Vec2` (`Vec2 := EuclideanSpace ℝ (Fin 2)`) with
> `B - P = t • (A - P)`, `D - P = s • (C - P)` (P collinear with each pair),
> all four points `≠ P`, `A ≠ B`, `C ≠ D`, and
> `‖P - A‖ * ‖P - B‖ = ‖P - C‖ * ‖P - D‖`,
> then `∃ O r, r > 0 ∧ ‖A-O‖ = ‖B-O‖ = ‖C-O‖ = ‖D-O‖ = r` (A,B,C,D concyclic).

---

## Insights

### CRITICAL: the axiom as currently stated is FALSE (integrity finding)

The hypothesis uses **unsigned** products `‖P-A‖·‖P-B‖ = ‖P-C‖·‖P-D‖`. The true
converse of power-of-a-point requires **signed** products to agree. They differ
exactly when P lies *between* one pair but *outside* the other.

**Explicit counterexample** (all hypotheses of the axiom hold, conclusion fails):
- `P = (0,0)`
- `A = (1,0)`, `B = (-4,0)`  → `B - P = -4 • (A - P)`, so `t = -4`; `‖PA‖·‖PB‖ = 1·4 = 4`
- `C = (0,1)`, `D = (0,4)`  → `D - P = 4 • (C - P)`, so `s = 4`; `‖PC‖·‖PD‖ = 1·4 = 4`

All preconditions satisfied (products equal `4`; none equal `P`; `A≠B`, `C≠D`).
The unique circle through `A,B,C` is `x² + y² + 3x + 3y − 4 = 0`
(center `(-3/2,-3/2)`, `r² = 17/2`). Evaluating at `D=(0,4)`:
`0 + 16 + 0 + 12 − 4 = 24 ≠ 0`, so **D is not on it**. No common circle exists,
because the power of `P` w.r.t. any circle through `A,B` is `−4` (P strictly
inside that chord) while the power w.r.t. any circle through `C,D` is `+4` (P
outside segment `CD`). Opposite signs ⇒ no shared circle.

Consequence: the derived theorem `converse_product_implies_concyclic`
(lines 481-490) is currently "proved" only by invoking a false axiom. It cannot
be discharged as typed — **the statement must be corrected first.**

### Signed-power identity (the correct quantity)

Parametrize line `AB` by `λ ↦ P + λ•(A-P)`: `A` is `λ=1`, `B` is `λ=t`. For a
circle with center `O`, radius `r`, the membership condition `‖P+λ(A-P)-O‖² = r²`
is the quadratic `‖A-P‖²·λ² + 2⟪A-P, P-O⟫·λ + (‖P-O‖² - r²) = 0`. Its product of
roots is `λ_A·λ_B = (‖P-O‖² - r²)/‖A-P‖² = pow(P)/‖A-P‖²`. With `λ_A=1`, `λ_B=t`:

> **`t · ‖A-P‖² = pow(P)`**   (signed power; this is `powerOfPoint P C` in the file)

Likewise `s · ‖C-P‖² = pow(P)`. So the *correct* hypothesis is the **signed**
equality `t · ‖A-P‖² = s · ‖C-P‖²`. Note `‖P-A‖·‖P-B‖ = |t|·‖A-P‖²`, i.e. the
unsigned product is `|signed power|` — discarding the sign is exactly the bug.

### Corrected, provable formulation

Replace the unsigned hypothesis with either form:
- **(a) signed form:** `t * ‖A - P‖^2 = s * ‖C - P‖^2` (drop the unsigned eq), or
- **(b) unsigned + orientation:** keep `‖P-A‖·‖P-B‖ = ‖P-C‖·‖P-D‖` and add
  `(0 < t ∧ 0 < s) ∨ (t < 0 ∧ s < 0)` (P on the same side w.r.t. both pairs).

Both recover signed equality. Form (a) is cleaner for the Lean proof.

Also required: the two chords must be **distinct lines**, otherwise all four
points are collinear and no finite circle contains them. Sufficient hypothesis:
`A - P` and `C - P` are linearly independent (equivalently `¬ ∃ u, C - P = u • (A - P)`).
Without it the conclusion `∃ O r, r>0 ∧ …` is false (a line is not a circle).

### Proof of the corrected converse (coordinate / algebraic, ring-friendly)

1. From non-collinearity of `A-P, C-P`, the triangle `A,B,C` is non-degenerate
   (B is on line `PA`, distinct from line `PC`), so its **circumcenter** `O`
   exists and is unique: solve the 2×2 linear system from the two perpendicular-
   bisector equations `‖X-A‖² = ‖X-B‖²`, `‖X-A‖² = ‖X-C‖²`. The system's
   determinant is `2·(signed area of △ABC) ≠ 0`.
2. Set `r := ‖A - O‖ > 0`. By construction `‖A-O‖ = ‖B-O‖ = ‖C-O‖ = r`.
3. Show `‖D - O‖ = r`. Compute `pow(P) := ‖P-O‖² - r²`. From step-1 circle and the
   signed identity, `pow(P) = t‖A-P‖²` (line `AB`) and the line `CD` meets the
   circle at `C` (`λ=1`) and at `λ' = pow(P)/‖C-P‖²`. Hypothesis (a) gives
   `pow(P)/‖C-P‖² = s`, and `D` is the point at `λ = s` on line `CD`
   (`D-P = s•(C-P)`), hence `D` is the second intersection ⇒ `‖D-O‖ = r`. Close
   with `ring`/`nlinarith` after expanding `⟪·,·⟫` in coordinates.

---

## Infrastructure Assessment

**Needed:** circumcenter of 3 non-collinear points in `ℝ²` as the solution of a
2×2 linear system, plus the quadratic-root / power identity above.
**Size estimate:** ~150-250 lines, fully self-contained coordinate algebra over
`EuclideanSpace ℝ (Fin 2)` (no Mathlib `Cospherical`/`Concyclic` machinery
required; the file already uses bare `Vec2`/`Circle`/`onCircle`).
**Decision:** BUILD (well under the 500-line threshold). Build-gated only by
Docker availability, not by missing mathematics.
**Mathlib gaps:** none fundamental. Uses inner product on `EuclideanSpace ℝ (Fin 2)`,
`norm_sub_sq_real` / `@inner_…`, and `ring`/`nlinarith`/`linarith`. The only mild
friction is solving the 2×2 system explicitly (Cramer-style) and discharging the
non-degeneracy determinant `≠ 0`.

---

## Dead Ends

- Discharging the axiom **as currently typed** (unsigned products, no orientation,
  no distinct-lines hypothesis) is impossible: the statement is false (see
  counterexample). Any attempt must first correct the statement.

---

## Lean realization (S3, build-pending)

`proofs/Proofs/ProductOfSegmentsOfChordsConverse.lean` (UNREGISTERED) now encodes the
finding in Lean for the first time (prior PRs #24105/#24153/#24204 were sympy/symbolic
only):

- `unsigned_converse_counterexample_general (e₀ e₁ : Vec2) (‖e₀‖=1) (‖e₁‖=1)` — proves
  `∃ P A B C D, <all axiom hyps> ∧ ¬ ∃ O r, r>0 ∧ <four points on a circle>`. Witness
  `P=0, A=e₀, B=-4•e₀, C=e₁, D=4•e₁`. **Key simplification discovered:** the
  contradiction needs only `‖e₀‖=‖e₁‖=1` — *no orthogonality*. Working with squared
  norms via `norm_sub_sq_real`, the perpendicular-bisector equalities `‖A-O‖=‖B-O‖`,
  `‖C-O‖=‖D-O‖`, `‖A-O‖=‖C-O‖` reduce (cancelling `‖O‖²`) to the linear system
  `⟪e₀,O⟫=-3/2`, `⟪e₁,O⟫=5/2`, `⟪e₀,O⟫=⟪e₁,O⟫`, closed by `nlinarith`. So the
  obstruction is one-dimensional (the sign of the power), independent of chord direction.
- `unsigned_converse_counterexample` — concrete standard-basis instance (the documented
  `(1,0),(-4,0),(0,1),(0,4)`); only extra dependency is `EuclideanSpace.norm_single`.
- `signed_converse_implies_concyclic` — the corrected statement (signed power equality
  `t‖A-P‖²=s‖C-P‖²` + `LinearIndependent ℝ ![A-P, C-P]`), proof `sorry` (circumcenter,
  build-gated). This is the clean Aristotle target / future ACT goal.

Lemma-name risk points if a future build fails: `norm_sub_sq_real`, `real_inner_smul_left`,
`EuclideanSpace.norm_single`.

---

## Next Steps

1. (build-gated) Correct the axiom statement in `ProductOfSegmentsOfChords.lean`:
   use signed hypothesis `t * ‖A-P‖^2 = s * ‖C-P‖^2` + linear-independence of
   `A-P, C-P`. Update the parent gallery `meta.json` note that the *unsigned*
   converse is false.
2. (build-gated) Prove the corrected converse via the circumcenter construction
   (M1: signed-power identity — largely already in the file's forward lemmas;
   M2: circumcenter exists + D lies on it). Target `axiomCount: 0`.
3. Consider a small **decidable counterexample lemma** capturing the
   `(1,0),(-4,0),(0,1),(0,4)` instance to document, in Lean, why the unsigned
   form fails — cheap, self-contained, and a permanent guardrail.

---

## Session 2026-06-15 (researcher-1) — doc-integrity fix (build-gated ACT still deferred)

Math finding (unsigned converse FALSE; signed correction) was already verified &
merged (PRs #24153, #24204; ORIENT #24105). But the **gallery presentation still
overclaimed the converse as true**:
- `ProductOfSegmentsOfChords.lean:457` — the axiom docstring billed the unsigned
  converse as a real theorem with a "proof sketch". Replaced with a FALSE-as-stated
  WARNING carrying the counterexample (line count held at 541 → no annotation drift;
  axiom statement itself untouched so the downstream re-export still typechecks).
- `meta.json` — corrected the keyInsight, summary, implications (proof-techniques),
  openQuestion, and assumptions fields that presented the unsigned converse as valid.

No Lean proof changed (docstring + JSON only), so build risk is nil even under the
persisting Docker + Aristotle blackout. The build-gated ACT (replace the false axiom
with the signed/linearly-independent corrected converse, target axiomCount 0) remains
the open next step — see "Next Steps" above.

## Session 2026-06-15 (researcher-2) — sorry decomposition + reduction (build-pending)

Dual blackout persists (`docker info` hangs; Aristotle `prove` → 404). Instead of
blind-writing the full ~200-line circumcenter proof, **reduced** the lone opaque
`sorry` to one isolated, reusable lemma and proved the surrounding assembly.

### New structure in `ProductOfSegmentsOfChordsConverse.lean`

- `circumcenter_signed (u v : Vec2) (t s : ℝ)` — translation-normalized heart (`P` at
  origin, `A=u, B=t•u, C=v, D=s•v`): given `LinearIndependent ℝ ![u,v]` and the signed
  power `t‖u‖²=s‖v‖²`, `∃ O, ‖u-O‖=‖t•u-O‖ ∧ ‖u-O‖=‖v-O‖ ∧ ‖u-O‖=‖s•v-O‖`. This is
  the **lone remaining `sorry`** — a clean, classical, origin-centered Aristotle target
  (much better than the bespoke 4-point statement).
- `signed_converse_implies_concyclic` — now **fully assembled** (no `sorry` of its own)
  from `circumcenter_signed` via the translation `O = P + Õ`. Key glue:
  - `X - (P + Õ) = (X - P) - Õ` by `abel`, carrying each of the 4 distance equalities
    to the origin-centered ones; `B-P` / `D-P` rewritten via `hAB` / `hCD`.
  - radius `r := ‖(A-P) - Õ‖ > 0` via `norm_pos_iff.mpr`, using `A-P ≠ C-P` (else
    `r=0 ⟹ A-P=Õ=C-P`). `u≠v` extracted from `hindep.injective.ne (by decide)`.

### Numerical validation (`verify_signed_converse.py`, 19987 configs, 0 failures)

Confirmed the reduction's core claim: with `O` = circumcenter of `A,B,C` (solved from
`2(B-A)·X=|B|²-|A|²`, `2(C-A)·X=|C|²-|A|²`) and `s` chosen so `t‖u‖²=s‖v‖²`, the fourth
point `D=P+s(C-P)` satisfies `‖D-O‖²=‖A-O‖²` exactly. So the signed hypothesis is
precisely the consistency condition that puts `D` on the circumcircle of `A,B,C`.

### Degeneracy analysis (new)

The statement has **no** `t≠1`/`s≠1` hypotheses and needs none: `t=1 ⟹ B=A` makes
`‖u-O‖=‖t•u-O‖` `rfl`-trivial (similarly `s=1 ⟹ D=C`); the signed hypothesis only does
work in the generic `t,s≠1` case (where `A,B,C` are genuinely 3 distinct non-collinear
points). Degenerate scalars were included in the numeric sweep — still 0 failures.

### Remaining gap (`circumcenter_signed` sorry) — blueprint

Solve `O = x•u + y•v` (valid basis since `u,v` indep). With `p=‖u‖², q=‖v‖², w=⟪u,v⟫`:
`‖u-O‖=‖t•u-O‖` and `‖u-O‖=‖v-O‖` give a 2×2 linear system in `(x,y)` with determinant
`pq − w² ≠ 0` (Cauchy–Schwarz strict, since `u,v` indep). The third equality
`‖u-O‖=‖s•v-O‖` then follows from `t·p = s·q` by polarization expansion + `nlinarith`.
~120-180 LOC, or one `prove()` call once Aristotle is back.

---

## Session (researcher-7, 2026-06-15): circumcenter_signed FULLY CONSTRUCTED

Built on the merged #24346 reduction. `circumcenter_signed` was a single
monolithic `sorry`; it is now fully constructed, leaving the whole converse
proved modulo ONE standard sorry (`gram_pos`). Dual blackout LIVE: `docker info`
timed out (20s), Aristotle `prove` returned "Resource not found" (404,
tested live on both `circumcenter_signed` and would-be `gram_pos`).

**Key mathematical insight — `‖O‖²` cancels.** Expanding each squared distance
by polarization `‖x−O‖² = ‖x‖² − 2⟪x,O⟫ + ‖O‖²`, the `‖O‖²` term is common to all
four points `u, t•u, v, s•v` and cancels in every comparison. So the circumcenter
is completely determined by just **two inner-product values**:
`⟪u,O⟫ = (t+1)/2·‖u‖²`, `⟪v,O⟫ = (s+1)/2·‖v‖²`. All three equidistances then
reduce to the signed hypothesis `t‖u‖² = s‖v‖²`. No `t=1`/`s=1` case split is
needed — the construction is uniform.

**New lemmas (in `ProductOfSegmentsOfChordsConverse.lean`):**
- `equidistant_of_inner (u v O t s)` — reusable core: the two inner-product
  values + `hsigned` ⟹ the four equidistances. Proof = `norm_sub_sq_real`
  expansion (confirmed in-file at the counterexample) + `Real.sqrt_sq` to lift
  squared equality to norm equality + `linear_combination -hsigned`. Low risk.
- explicit Cramer center `O = a•u + b•v`,
  `a = ‖v‖²(‖u‖²(t+1) − ⟪u,v⟫(s+1))/(2Δ)`,
  `b = ‖u‖²(‖v‖²(s+1) − ⟪u,v⟫(t+1))/(2Δ)`, `Δ = ‖u‖²‖v‖² − ⟪u,v⟫²`.
  Inner-product values proved via `inner_add_right`/`real_inner_smul_right`/
  `real_inner_self_eq_norm_sq`/`real_inner_comm` + `field_simp [hΔ0]; ring`.
- `gram_pos (u v)` — `0 < ‖u‖²‖v‖² − ⟪u,v⟫²` from `LinearIndependent ℝ ![u,v]`.
  **The sole remaining `sorry`.** Standard strict Cauchy–Schwarz / Gram
  determinant. Clean Aristotle target once 404 clears.

**Verification.** Cramer coefficients re-derived symbolically (sympy: the two
inner-product identities and all three equidistance conditions check out, with
cond1 an identity and cond2/cond3 reducing to `t‖u‖²=s‖v‖²`). The geometric
identity was already numerically validated over 19987 configs
(`verify_signed_converse.py`).

**Residual risk (build-pending, UNREGISTERED — zero gallery-build blast radius):**
`field_simp; ring` in the two inner-product proofs (`hiu`/`hiv`) and the exact
names/directions of `real_inner_self_eq_norm_sq` / `real_inner_smul_right` /
`real_inner_comm` (confirmed to EXIST on mathlib4 master via gh API; directions
unverified). `equidistant_of_inner` uses only lemmas already exercised elsewhere
in this file. Next live Docker session: build, repair any gaps, prove `gram_pos`,
then discharge the parent axiom.

## Session 2026-06-15 (researcher-5) — saturation check + consolidated axiom-elimination plan (no PR)

Dual blackout still LIVE (`docker info` timeout; Aristotle `prove` → 404, re-probed). Claimed the
slug, found it **saturated for this session**:

- `ProductOfSegmentsOfChordsConverse.lean` is fully assembled; the **sole** remaining `sorry`
  (`gram_pos`, strict Cauchy–Schwarz) is **already discharged in open, MERGEABLE PR #24462**
  (witness `z = ‖u‖²•v − ⟪u,v⟫•u`, `⟪z,z⟩ = ‖u‖²·Δ`, `z ≠ 0` by `LinearIndependent.pair_iff`).
  That PR makes the file **0 sorry / 0 axiom**. Re-proving it would duplicate #24462 — stood down.
  (gram_pos was also proved independently in PR #24451 via `inner_lt_norm_mul_iff_real`.)

- **Only remaining oq-02 work = eliminate the parent's FALSE axiom**
  `converse_product_implies_concyclic_axiom` (`ProductOfSegmentsOfChords.lean:468`), driving
  `meta.json` axiomCount `1 → 0`. Dependency map (verified this session):
  * The axiom is referenced **only** by the re-export `converse_product_implies_concyclic`
    (`:481–490`) inside the same file. **No other `.lean` uses it** (other hits are docstrings).
    meta.json itself notes "the axiom is not used by the forward theorem."
  * The re-export `converse_product_implies_concyclic` is named by **one gallery annotation**
    (`src/data/proofs/product-of-segments-of-chords/annotations.source.json:120`) — must be
    repointed/removed if the re-export is deleted, else the auditor flags a dangling annotation.
  * Nothing below `:490` (Part 8 numerical examples) touches either declaration.

  **Why not now:** doing it under blackout means either (a) pure deletion of axiom + re-export now,
  then a LATER PR re-adding a corrected signed re-export once #24462 merges (delete-then-readd
  churn on a registered flagship), or (b) a blind multi-file flagship edit I can't typecheck. Both
  bad. The clean single move belongs in the **post-#24462-merge, Docker-up** session.

  **Ready post-merge patch (execute once #24462 is on main + Docker returns):**
  1. In `ProductOfSegmentsOfChords.lean`: delete `axiom converse_product_implies_concyclic_axiom`
     (`:468`). Replace the re-export `converse_product_implies_concyclic` (`:481`) with the
     **corrected signed** statement, proved by `exact ProductOfSegmentsOfChordsConverse.signed_converse_implies_concyclic …`
     (add `import Proofs.ProductOfSegmentsOfChordsConverse`). Signature gains `(t s : ℝ)`,
     `hAB : B-P = t•(A-P)`, `hCD : D-P = s•(C-P)`, `hindep : LinearIndependent ℝ ![A-P, C-P]`,
     `hsigned : t*‖A-P‖² = s*‖C-P‖²`, `hAneP hCneP`; drop the unsigned `hProduct`.
  2. Update the gallery annotation (`annotations.source.json:120`) to the corrected signature, or
     drop it; regen annotations.
  3. `meta.json`: axiomCount `1 → 0`; keep `status:"axiomatized"`→ may move toward `"verified"`
     ONLY after a clean full build confirms 0 sorries/0 axioms across parent + Converse.
  4. Register `import Proofs.ProductOfSegmentsOfChordsConverse` in `proofs/Proofs.lean` (currently
     unregistered) and build both.

No code shipped this session (saturation + blackout). Forward value = the dependency map + the
consolidated post-merge patch above, so the next session executes in one pass without re-deriving.
