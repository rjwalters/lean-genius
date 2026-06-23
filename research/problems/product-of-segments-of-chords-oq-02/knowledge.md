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

---

## Session 2026-06-15 (researcher-6) — converse file RESTORED to compiling under Mathlib 4.26.0

**Mode**: FRESH (claimed via claim-random) · **Outcome**: progress (verified converse)

### Key discovery
The entire `ProductOfSegmentsOfChords*` family does **not** compile against the
pinned Mathlib (v4.26.0, rev `2df2f0150c`). PR #24462 (which claimed the converse
was `sorry`-free) was merged under the build-gate blackout and **never actually
built**. Root cause: Mathlib 4.26.0 made the inner-product field an **explicit**
first argument — `inner x y` → `inner ℝ x y` (bare `inner u v` now parses `u` as
the field `𝕜`, giving `Application type mismatch: ... expected Type`).

### What I did (all Docker-verified, build `…converse-final.log`, 7743 jobs, exit 0)
Repaired `proofs/Proofs/ProductOfSegmentsOfChordsConverse.lean` (now 0 sorry / 0
axiom, **builds green standalone**):
- `inner X Y` → `inner ℝ X Y` at every call site (gram_pos, equidistant_of_inner,
  circumcenter_signed, signed_converse_implies_concyclic, counterexample).
- `gram_pos.hzeq`: split the single `simp only` into two stages — pull scalars
  (`real_inner_smul_left/right`) BEFORE `real_inner_self_eq_norm_sq`, otherwise
  4.26.0 simp rewrites `⟪‖u‖²•v,‖u‖²•v⟫ → ‖‖u‖²•v‖²` (a norm-of-smul `ring` can't
  touch) instead of pulling the scalar.
- Latent bug: `gram_pos` line 186 used `hpz.symm` (`0 = ‖u‖²`) where
  `ne_of_gt hup` needs `‖u‖² = 0` → changed to `hpz`.
- `circumcenter_signed.hiu/hiv` Cramer steps: `field_simp [hΔ0]; ring` does NOT
  clear the difference-denominator `Δ = ‖u‖²‖v‖²−⟪u,v⟫²` (leaves `Δ⁻¹`). Replaced
  with a deterministic chain: `rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
  div_add_div_same, div_eq_iff hΔ2]; ring` where `hΔ2 : 2*Δ ≠ 0`. For `hiv`,
  simp normalizes the cross term to `⟪v,u⟫` orientation, so it needs a
  `⟪v,u⟫`-form nonzero fact `hΔ2'` (derive via `rw [real_inner_comm u v]` —
  note `real_inner_comm a b` rewrites the `⟪b,a⟫` occurrence).

### Parent file NOT shipped this session (documented next steps)
`ProductOfSegmentsOfChords.lean` (the gallery `leanFile`, still holds the FALSE
axiom `converse_product_implies_concyclic_axiom`) has ~10 further pre-existing
4.26.0 breakages beyond `inner`, requiring a larger Mechanic-scale repair:
- `def powerOfPoint` → must be `noncomputable` (EuclideanSpace norm has no IR).
- `chord_quadratic`: `by rw [hOnCircle]; ring` → drop `; ring` (rw closes it,
  "No goals"); rewrite `expand` with `real_inner_smul_*`+simp (not `inner_smul_*`,
  which now insert `starRingEnd`).
- `power_of_point_product` (~160 lines): uses **vector division**
  `dir := (A'-P') / ‖A'-P'‖` — no `HDiv Vec2 ℝ` instance in 4.26.0
  (`failed to synthesize`). Must become `(‖A'-P'‖)⁻¹ • (A'-P')` and rework
  every `smul_div_assoc`/`div_self` step. Also `ring`/`ring_nf` on vector goals
  (lines 268/270/304/315) → `abel`/`module`; `linarith` deriving `A=P` from
  `A-c=P-c` (278/378/380) → `sub_right_cancel`.
- `center_chord_product` line 454: a `rw` pattern no longer matches.

**Axiom elimination is blocked behind this parent 4.26.0 repair**, not behind any
mathematics (the corrected converse is now machine-checked in the converse file).
Once the parent builds, delete the axiom + its re-export theorem and either point
to `signed_converse_implies_concyclic` or re-export it from a NON-`import Mathlib`
module (importing the converse pulls full Mathlib and collides with the parent's
own `structure Circle`).

## Session 2026-06-15 (researcher-1) — FALSE axiom REMOVED + partial 4.26.0 migration (build-pending)

Acted on the prior session's documented next-steps. Two concrete advances to the
gallery `leanFile` `ProductOfSegmentsOfChords.lean`:

1. **Deleted the FALSE axiom** `converse_product_implies_concyclic_axiom` and its
   re-export theorem `converse_product_implies_concyclic`. They are replaced by a
   plain `/- -/` doc block that states the unsigned converse is false, points at the
   machine-checked `unsigned_converse_counterexample` / `signed_converse_implies_concyclic`
   in the converse file, and explicitly records WHY the corrected theorem is NOT
   re-exported here: `import Proofs.ProductOfSegmentsOfChordsConverse` pulls full
   `import Mathlib`, whose root-namespace `Circle` (`Submonoid.unitSphere ℂ`) shadows
   the local `structure Circle`, breaking every `C.center`/`C.radius` in this file.
   (Confirmed empirically: the import-and-delegate version compiled the converse fine
   but failed with `Invalid field 'center'/'radius'` across the forward lemmas.)
   File `axiomCount` 1 → **0**. Nothing depends on the deleted re-export (only doc
   mentions in OQ03 + the converse file).

2. **Applied the forced mechanical 4.26.0 migrations** (reduce the repair surface):
   - `inner X Y` → `inner ℝ X Y` at all ~24 application sites (forms `inner P dir`,
     `inner P' dir`, `inner P P`, `inner dir dir`, `inner (P+t•dir) (P+t•dir)`).
   - `def powerOfPoint` → `noncomputable def` (EuclideanSpace norm has no IR).

**Still build-pending — the lone remaining blocker is the vector-division rot** in
`power_of_point_product` (~lines 290–410), unchanged this session because it needs a
working build to iterate and the shared `.lake` mathlib cache was wiped mid-session
(re-clone → OOM risk on the 7.65GB Docker VM). Blueprint (still accurate):
`dir := (A'-P') / ‖A'-P'‖` → `(‖A'-P'‖)⁻¹ • (A'-P')`, reworking each
`smul_div_assoc`/`div_self` step into `smul_smul`/`inv_mul_cancel₀`; `ring`/`ring_nf`
on vector goals (268/270/304/315) → `abel`/`module`; the `A=P`-from-`A-c=P-c`
`linarith` steps → `sub_left_injective`/`sub_right_cancel`; and the `rw` at
`center_chord_product` (~line 454). Once green, gallery flips formalized/wip →
verified/original (or mathlib).

Gallery meta updated honestly this session: `status` axiomatized → **formalized**,
`badge` axiom → **wip**, `axiomCount` 1 → **0**, `lineCount` 541 → 530, and the
`assumptions` field rewritten to record the axiom removal + the build-pending rot.
This is the honest state: 0 axioms, 0 sorries, but NOT machine-checked (does not yet
compile). Do NOT mark verified until the vector-div repair lands a green Docker build.

## Session 2026-06-15 (researcher-4) — vector-div rot REPAIRED + FALSE-as-stated theorem fixed (build-pending)

Acted on the prior "lone remaining blocker = vector-division rot" note. Applied ALL
the 4.26.0 mechanical fixes researcher-6 had derived from an actual parent build, PLUS
discovered and fixed a genuine **correctness bug** (missing `A ≠ B` hypothesis). All
lemma names verified against the pinned Mathlib rev `2df2f0150c` via raw.githubusercontent
(could not build: Docker saturated at 3–4 containers all session, ~4.8GB free on the
7.6GB VM — a 4th mathlib build risks OOM-killing active peers).

### Changes to `ProductOfSegmentsOfChords.lean` (the gallery leanFile)

1. **Vector division → scalar-inverse smul** (the documented main blocker). `dir`
   redefined `(A'-P')/‖A'-P'‖` → `(‖A'-P'‖)⁻¹ • (A'-P')`. Proof steps reworked:
   - `hdir`: `norm_div,norm_norm` → `norm_smul,norm_inv,norm_norm; field_simp`.
   - `hA'param`: `smul_div_assoc,div_self` → `smul_smul, mul_inv_cancel₀ hAnorm, one_smul; abel`.
   - `hB'param`: same `smul_smul/mul_assoc/mul_inv_cancel₀/mul_one` chain; the `by ring`
     vector step → `by abel`.
   - `hs1`/`hs2`: collapsed to `rw [← hA'param]; exact hA'` / `rw [← hB'param]; exact hB'`
     (the old `smul_div_assoc` forms are gone).
2. **`chord_quadratic`**: `rw [hOnCircle]; ring` → `rw [hOnCircle]` (rw closes `r^2=r^2`,
   `; ring` errored "no goals"). `expand`: `inner_smul_left/right` (insert `starRingEnd`
   over ℝ, blocking `ring`) → `real_inner_smul_left/right`.
3. **Vector `ring`/`ring_nf` → `abel`** at the `hCollinear'` calc (`B-c-(P-c)=B-P` and the
   smul step via `congr 1; abel`) and the `hPBdist` `‖P'-(P'+X•dir)‖=‖-(X•dir)‖` step
   (`ring_nf` → `congr 1; abel`).
4. **Vector `linarith` cancellations → `sub_left_inj.mp`**: `hAneP'` (`A-c=P-c ⟹ A=P`)
   and the t=1 block.
5. **`center_chord_product`**: `rw [hB']` failed (goal has `‖C.center-B‖`, hB' has
   `‖B-C.center‖`) → `rw [norm_sub_rev, hB']`.

### CORRECTNESS BUG found + fixed: `power_of_point_product` was FALSE for `t=1`

The old t=1 branch of the `hdiff : ‖A'-P'‖ ≠ t*‖A'-P'‖` sub-proof was incoherent
(`exact absurd rfl hdiff` references `hdiff` inside its own proof; vector `linarith`).
Root cause: **the theorem is genuinely false when `t=1` (i.e. `B=A`)** — then
`‖PA‖·‖PB‖ = ‖PA‖²` but `|power|` need not equal `‖PA‖²` (secant ≠ tangent), and
`hdiff` itself is unprovable (both sides equal). The two chord intersection points must
be distinct. **Fix:** added hypothesis `(hABne : A ≠ B)` to `power_of_point_product`,
and threaded `(hABne : A ≠ B) (hCDne : C ≠ D)` through `product_of_segments_of_chords`
(its two call sites pass `hABne`/`hCDne`). The t=1 branch now closes cleanly:
`rw [ht1, one_smul] at hCollinear'` → `B'-P'=A'-P'` → `B'=A'` → `B=A` → `hABne hBA.symm`.
All references are in-file (only `#check`s + gallery annotations/meta mention them).

### Verified (no build): lemma names exist at rev 2df2f0150c
`sub_left_inj`, `mul_inv_cancel₀`, `real_inner_smul_left`, `real_inner_smul_right`,
`one_smul`, `smul_smul`, `norm_smul`, `norm_inv`, `norm_sub_rev` — all confirmed.

### RESIDUAL RISK (build-pending — next Docker-free session must build Proofs.ProductOfSegmentsOfChords)
Lemma names confirmed; only tactic-closure is unverified: the `field_simp` in `hdir`,
the two `congr 1; abel` steps, whether `abel` closes `hA'param`'s residual after the
smul cancel, and `sub_left_inj` direction (a-b=c-b↔a=c; used 3×). If `sub_left_inj`
mismatches, swap for `sub_right_cancel`/`add_right_cancel`. Once green, gallery flips
formalized/wip → verified/original. **Note:** the meta `assumptions` field should also
record the newly-required `A≠B`/`C≠D` distinctness hypotheses (correctness fix, not an
axiom) — update when the build confirms.
