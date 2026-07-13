# S9 PREP — Concrete counterexample to parent axiom + signed-vs-unsigned recovery options (doc-only)

**Author:** researcher-8
**Timestamp:** 2026-05-14 / 2026-05-15 ~04:35 UTC
**Phase:** S9 PREP (mathematical-soundness pre-flight, blocking S6 ACT axiom-discharge plan)
**Iteration:** 9 (S1 OBSERVE + S2 SCAFFOLD + S3 PREP + S4 PREP + S5 PREP + S6 STATE-SYNC + S7 ACT BUILD-VERIFY [PR #19096, open] + S8 PREP [PR #19231, open] + this)
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from `proofs/lake-manifest.json`)
**Lean toolchain:** `leanprover/lean4:v4.26.0`
**Scope:** Single new file in `sessions/`. **No edits** to `state.md`, `problem.md`, `knowledge.md`, JSON, gallery `meta.json`, any prior `sessions/*.md`, or any Lean file. **No build.**

## 0. Executive summary

The parent file's axiom
`converse_product_implies_concyclic_axiom` (`Proofs/ProductOfSegmentsOfChords.lean:468`)
is **mathematically false as currently stated**. A concrete counterexample with
explicit rational coordinates satisfies every hypothesis but falsifies the
conclusion (`concyclicityDet = 12 ≠ 0` ⇒ no circle passes through all four
points).

S5 PREP §2.1 (PR #18553, 2026-05-13) **identified the underlying signed-vs-unsigned
gap** ("case (b)"), but its recommended fix — Option C / option (ii):
"produce `Δ = 0` unconditionally; let S6 absorb the inconsistency" — is
**incoherent with its own §4.3 algebra**, which derives `Δ ≠ 0` in case (b).
You cannot prove `Δ = 0` unconditionally when in fact `Δ ≠ 0` is realised.

This S9 PREP:

1. **Verifies the gap is real** via a concrete `P, A, B, C, D ∈ ℚ²` for which
   every hypothesis of the parent axiom is checkable by `decide`/`norm_num`,
   yet the four points are provably non-concyclic.
2. **Diagnoses the incoherence** in S5 PREP's recovery recommendation.
3. **Provides three soundness-restoring options** for the parent axiom
   (signed hypothesis / sign-coordination hypothesis / weakened conclusion),
   with paste-ready Lean signatures and verifier obligations for each.
4. **Stages the S6 ACT picker's decision** as a pick-one-of-three, with
   maintenance trade-offs called out.
5. **Strict conflict-free guarantee** with PR #19096 (S7 ACT BUILD-VERIFY,
   open) and PR #19231 (S8 PREP bearer re-verification, open).

**This PREP is gating on the S6 ACT.** Until one of the three recovery options
is chosen, attempting to discharge the parent axiom would either:

- produce `False` (option A: replace axiom with provably-false theorem), or
- silently introduce a vacuous "discharge" (option B: hypothesis becomes
  unsatisfiable, axiom is true but useless), or
- break downstream callers (option C: theorem at
  `ProductOfSegmentsOfChords.lean:481` and its callers).

## 1. The parent axiom verbatim

`proofs/Proofs/ProductOfSegmentsOfChords.lean:468`:

```lean
axiom converse_product_implies_concyclic_axiom
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ t : ℝ, D - P = t • (C - P))
    (hProduct : ‖P - A‖ * ‖P - B‖ = ‖P - C‖ * ‖P - D‖)
    (hAneP : A ≠ P) (hBneP : B ≠ P) (hCneP : C ≠ P) (hDneP : D ≠ P)
    (hAneB : A ≠ B) (hCneD : C ≠ D) :
    ∃ (O : Vec2) (r : ℝ), r > 0 ∧
      ‖A - O‖ = r ∧ ‖B - O‖ = r ∧ ‖C - O‖ = r ∧ ‖D - O‖ = r
```

`Vec2 := EuclideanSpace ℝ (Fin 2)` is defined at line 55. The notation `B - P`
uses the standard `EuclideanSpace`/`PiLp 2` subtraction; `‖·‖` is the `PiLp 2`
norm; `t • (A - P)` is the standard scalar multiplication.

## 2. The counterexample

### 2.1 Choice of points (rational, axis-aligned for clarity)

```
P = (0, 0)
A = (1, 0)
B = (-2, 0)     -- both A and B on the x-axis through P, with P between them
C = (0, 1)
D = (0, 2)      -- both C and D on the y-axis through P, both above P
```

### 2.2 Hypothesis verification

| Hypothesis | Substitution | Result |
|---|---|---|
| `hAB_collinear : ∃ t : ℝ, B - P = t • (A - P)` | `B - P = (-2, 0) = -2 • (1, 0) = -2 • (A - P)` | ✓ witness `t = -2` |
| `hCD_collinear : ∃ s : ℝ, D - P = s • (C - P)` | `D - P = (0, 2) = 2 • (0, 1) = 2 • (C - P)` | ✓ witness `s = 2` |
| `hProduct : ‖P - A‖ * ‖P - B‖ = ‖P - C‖ * ‖P - D‖` | `‖P-A‖ = 1, ‖P-B‖ = 2, ‖P-C‖ = 1, ‖P-D‖ = 2` ⇒ `1·2 = 1·2 = 2` | ✓ |
| `hAneP : A ≠ P` | `(1, 0) ≠ (0, 0)` | ✓ |
| `hBneP : B ≠ P` | `(-2, 0) ≠ (0, 0)` | ✓ |
| `hCneP : C ≠ P` | `(0, 1) ≠ (0, 0)` | ✓ |
| `hDneP : D ≠ P` | `(0, 2) ≠ (0, 0)` | ✓ |
| `hAneB : A ≠ B` | `(1, 0) ≠ (-2, 0)` | ✓ |
| `hCneD : C ≠ D` | `(0, 1) ≠ (0, 2)` | ✓ |

All nine hypotheses hold. **The axiom's hypotheses are satisfiable.**

### 2.3 Conclusion is FALSE

We claim no circle passes through all four points.

**Algebraic proof via determinant.** The 4×4 concyclicity determinant for these
points is

```
Δ = det !![1²+0², 1, 0, 1;
           (-2)²+0², -2, 0, 1;
           0²+1², 0, 1, 1;
           0²+2², 0, 2, 1]
   = det !![1, 1, 0, 1;
            4, -2, 0, 1;
            1, 0, 1, 1;
            4, 0, 2, 1]
```

Expanding along row 0:

| Column j | Cofactor sign | Entry | 3×3 minor `det A_{0,j}` | Term |
|---|---|---|---|---|
| 0 | `+1` | `1` | `det !![-2,0,1; 0,1,1; 0,2,1] = -2·(1·1-1·2) - 0 + 1·(0·2-1·0) = -2·(-1) = 2` | `+1·1·2 = 2` |
| 1 | `-1` | `1` | `det !![4,0,1; 1,1,1; 4,2,1] = 4·(1·1-1·2) - 0 + 1·(1·2-1·4) = -4 + (-2) = -6` | `-1·1·(-6) = 6` |
| 2 | `+1` | `0` | (irrelevant) | `0` |
| 3 | `-1` | `1` | `det !![4,-2,0; 1,0,1; 4,0,2] = 4·(0·2-1·0) - (-2)·(1·2-1·4) + 0 = 0 - (-2)·(-2) = -4` | `-1·1·(-4) = 4` |

**Total: Δ = 2 + 6 + 0 + 4 = 12.**

By the (⇐) direction of the iff theorem stated in
`Proofs/ProductOfSegmentsOfChordsOQ03.lean:98-104` — `Δ = 0` is **necessary**
for the four points to be concyclic — `Δ = 12 ≠ 0` proves no circle exists.

**Independent verification via direct circle-through-three-points construction.**
The implicit-circle equation `x² + y² + D·x + E·y + F = 0` substituted at
`A = (1, 0), B = (-2, 0), C = (0, 1)`:

| Point | Equation | Substituted |
|---|---|---|
| `A` | `1 + D + F = 0` | `D = -1 - F` |
| `B` | `4 - 2·D + F = 0` | `4 - 2(-1 - F) + F = 6 + 3·F = 0` ⇒ `F = -2` |
| `C` | `1 + E + F = 0` | `E = -F - 1 = 1` |

So `D = 1, E = 1, F = -2`. The unique circle through `A, B, C` has equation
`x² + y² + x + y - 2 = 0`. Substituting `D_pt = (0, 2)`:
`0² + 2² + 1·0 + 1·2 + (-2) = 4 + 2 - 2 = 4 ≠ 0`.

**D is not on the circle through A, B, C.** Hence no circle passes through
all four points; the axiom's conclusion `∃ O r, r > 0 ∧ ‖A-O‖ = r ∧ … ∧ ‖D-O‖ = r`
is FALSE for this configuration.

### 2.4 Numerical sanity (Python/numpy)

```text
P=[0 0], A=[1 0], B=[-2  0], C=[0 1], D=[0 2]
‖P-A‖·‖P-B‖ = 2.0
‖P-C‖·‖P-D‖ = 2.0
t (for AB) = -2.0, s (for CD) = 2.0
sign(t) = -1.0, sign(s) = 1.0    ← case (b): mismatch
inner(A-P, B-P) = -2             (signed power along x-axis chord)
inner(C-P, D-P) = +2             (signed power along y-axis chord)
Signed equality: False           (case (b) verified)
Δ = 12 (computed by numpy det)
Circle through A,B,C: x² + y² + x + y - 2 = 0
Sub D=(0,2): 4  (nonzero → not on circle)
```

This confirms: the unsigned chord-product equality is satisfied, but the
**signed** chord-product equality fails (-2 ≠ +2), and the four points are
not concyclic.

## 3. Why this falsifies the axiom

The axiom asserts: *unsigned hypothesis* ⇒ *exists circle through all 4*.

**§2.2 shows hypothesis holds. §2.3 shows conclusion fails.** Hence axiom is
falsified by a concrete witness.

This isn't a Lean issue (no typechecking gap, no `def` sorry) — it's a
**mathematical-content** issue. `axiom` declarations are *trusted* by Lean
without proof; the trust here is misplaced because the underlying statement
is false. Any theorem deriving from this axiom — including
`Proofs/ProductOfSegmentsOfChords.lean:481` (`converse_product_implies_concyclic`)
— is unsound (it claims a proposition that is provably false at the given
counterexample).

Specifically:

```lean
theorem converse_product_implies_concyclic                          -- :481
    (P A B C D : Vec2) (hAB_collinear …) (hCD_collinear …)
    (hProduct …) (hAneP …) … (hCneD …) :
    ∃ (O : Vec2) (r : ℝ), r > 0 ∧ ‖A - O‖ = r ∧ … ∧ ‖D - O‖ = r :=
  converse_product_implies_concyclic_axiom P A B C D … hCneD          -- :489
```

The theorem at line 481 is a one-line application of the axiom; it inherits
the axiom's falsity. Substituting our counterexample `(P, A, B, C, D)`
yields a "proof" of a false proposition.

## 4. What S5 PREP got right — and what it got wrong

S5 PREP (`sessions/2026-05-13-s5-prep-chord-product-to-det-zero-bridge.md`,
PR #18553, researcher-5) **correctly identified the structural gap** in §2.1
("Sign-pattern coordination"):

> Case (b) [sign mismatch]: the unsigned equality `|t_AB| · ‖A-P‖² = |t_CD| ·
> ‖C-P‖²` could hold even though the signed equality `t_AB · ‖A-P‖² =
> t_CD · ‖C-P‖²` does NOT.

And §4.3 correctly **derives**:

> If `t · ‖P-A‖² = -s · ‖P-C‖²` (the case-(b) scenario), the first factor is
> `2 · t · ‖P-A‖²`. For this to be zero, we'd need `t = 0` or `‖P-A‖ = 0`.
> Both are excluded … So in case (b), **`det ≠ 0` generically**.

But then §2.1's "Recommendation" (Option C) and §5's "Recommendation: option
(ii)" both prescribe:

> S5 produces `Δ = 0` unconditionally; S6 absorbs the case-(b) inconsistency
> into a `False.elim` arm using `decide` / `nlinarith`.

**This is incoherent.** If case (b) is realised and `Δ ≠ 0` (as §4.3 derives),
then `nlinarith` cannot close `False` because:

- The hypothesis `nlinarith` is given is satisfiable (witnessed by our
  §2 example) — it cannot derive `False` from a satisfiable hypothesis.
- The actual case-(b) configurations are **not** geometrically impossible
  in raw ℝ² — they only become impossible *under the assumption of an
  ambient circle*, which is exactly what the axiom tries to construct.

S5 PREP §2.1's defense of case-(b) impossibility — "P is either inside the
circle or outside it" — **assumes the conclusion** (that a circle exists).
This is a circular argument that doesn't help discharge the axiom.

**The S5 PREP `Δ = 0 unconditionally` claim is provably false at our §2
counterexample**: hypotheses hold, `Δ = 12 ≠ 0`.

## 5. Three soundness-restoring options for the parent axiom

The parent axiom must be amended. Three viable forms, each with a paste-ready
Lean signature and an explicit verifier obligation.

### Option A — Strengthen hypothesis to **signed** chord-product equality

```lean
axiom converse_product_implies_concyclic_axiom_A
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ t : ℝ, D - P = t • (C - P))
    (hSignedProduct : @inner ℝ _ _ (A - P) (B - P) =
                      @inner ℝ _ _ (C - P) (D - P))
    (hAneP : A ≠ P) (hBneP : B ≠ P) (hCneP : C ≠ P) (hDneP : D ≠ P)
    (hAneB : A ≠ B) (hCneD : C ≠ D) :
    ∃ (O : Vec2) (r : ℝ), r > 0 ∧
      ‖A - O‖ = r ∧ ‖B - O‖ = r ∧ ‖C - O‖ = r ∧ ‖D - O‖ = r
```

**Why this is sound.** The signed power-of-a-point equality is exactly the
algebraic condition that `‖P - O‖² - r²` (power of `P` w.r.t. the circle)
agrees along both chords. From the inner-product hypothesis plus the chord
collinearities, S5 ACT can derive `Δ = 0` algebraically without splitting on
sign, because the signed equality directly cancels the `t·s` factor in the
expansion (per S5 PREP §4.3 once `ε = +1` is forced).

**Downstream impact.** The parent theorem at line 481 must update its
hypothesis from `hProduct` to a signed form. Any caller of
`converse_product_implies_concyclic` must likewise pass the signed version.
The original gallery proof of `product_of_segments_of_chords` at line 426
already proves the **signed** identity internally (via `chord_roots_product`
at line 133); exposing it costs ~5 LOC of plumbing.

**Verifier obligation.** S5 ACT proves `signed-inner-equality → Δ = 0`. With
the §4.3 case (a) algebra and no case-(b) branch, this is ~15-25 LOC.

### Option B — Keep unsigned hypothesis but add **sign-coordination**

```lean
axiom converse_product_implies_concyclic_axiom_B
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ s : ℝ, D - P = s • (C - P))
    (hSameSide : ∀ t s : ℝ,                                    -- ↓ new
        B - P = t • (A - P) → D - P = s • (C - P) → 0 < t * s)  -- ↑ new
    (hProduct : ‖P - A‖ * ‖P - B‖ = ‖P - C‖ * ‖P - D‖)
    (hAneP : A ≠ P) (hBneP : B ≠ P) (hCneP : C ≠ P) (hDneP : D ≠ P)
    (hAneB : A ≠ B) (hCneD : C ≠ D) :
    ∃ (O : Vec2) (r : ℝ), r > 0 ∧ …
```

**Why this is sound.** `0 < t * s` rules out case (b) (where `sign t ≠ sign
s`), so the unsigned hypothesis upgrades to the signed one. The chord
parameters are determined up to `t = 0` (excluded by `B ≠ P`) and `t = 1`
(excluded by `A ≠ B`), so `t, s` are unique non-zero reals.

**Why this is ugly.** The `∀ t s, …` quantification reflects the fact that
the chord parameter `t` is uniquely determined by the collinearity witness,
but the existential in `hAB_collinear` doesn't expose it. The cleaner form
would store `t, s` as explicit fields and pass them, but that changes the
type signature significantly.

**Downstream impact.** Higher: every caller must produce both `t, s` and
prove `t · s > 0`. The latter is a geometric / contextual fact (P relative
to chords) that the caller may not have at hand.

**Verifier obligation.** S5 ACT proves `unsigned + same-side → Δ = 0`. The
proof has the same algebra as Option A, plus a 5-LOC sign-extraction step.

### Option C — Weaken conclusion to `concyclicityDet = 0`

```lean
axiom converse_product_implies_concyclicityDet_zero_axiom_C
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ t : ℝ, D - P = t • (C - P))
    (hProduct : ‖P - A‖ * ‖P - B‖ = ‖P - C‖ * ‖P - D‖)
    (hAneP : A ≠ P) (hBneP : B ≠ P) (hCneP : C ≠ P) (hDneP : D ≠ P)
    (hAneB : A ≠ B) (hCneD : C ≠ D) :
    ProductOfSegmentsOfChordsOQ03.concyclicityDet A B C D = 0 ∨
    Collinear ℝ ({A, B, C, D} : Set Vec2)
```

**Why this is also wrong.** Our §2 counterexample provides `Δ = 12 ≠ 0` and
the four points are NOT collinear (A, C, D are non-collinear; B is on the
x-axis with A; etc.). So the disjunction `Δ = 0 ∨ Collinear` is also FALSE
for our example. **Option C as stated is unsound** — it's only mathematically
weaker than A but still false at our witness.

A *correct* weakening would have to disjunctively cover all case-(b)
configurations, which is essentially "or … hPaperContaining-Sign-Mismatch"
— at which point Option A is cleaner.

**This option is documented for completeness as a non-recommendation.** Do
not pursue C; it does not restore soundness.

### Recommendation: **Option A** (signed chord-product equality)

Tradeoffs:

| Property | A (signed) | B (same-side) | C (weakened conclusion) |
|---|---|---|---|
| Soundness | ✓ | ✓ | ✗ (still false at §2 counterexample) |
| Caller churn | medium (one signature change per call site) | high (`t·s > 0` quantifier needed) | n/a (unsound) |
| S5 ACT LOC | ~15-25 | ~20-30 | n/a |
| Connection to classical theorem | direct (signed PoP is classical) | indirect | n/a |
| Gallery `meta.json` impact | axiom retained, hypothesis changed; `axiomCount` stays 1 until S6 ACT discharges | same as A | same as A |

Recommend **A**. The signed chord-product is the form Mathlib's existing
`InnerProductSpace` API supports; the parent file at line 133 already proves
the signed version internally; downstream callers (currently only one — the
theorem at line 481) can be updated in the same PR that updates the axiom.

## 6. Implications for S5 ACT and S6 ACT pickers

### S5 ACT picker (currently blocked by this finding)

- **Do not paste S5 PREP's §3 Lean signature.** Its hypothesis is the unsigned
  form, which produces the §2 counterexample.
- **Adopt Option A**: change the chord-product hypothesis to the signed form
  in S5 ACT's theorem signature. The S5 PREP §4.1-§4.4 algebra works
  unchanged (the case (a) branch becomes the only branch).
- **Drop S5 PREP §2.1's Option C recommendation** ("produce Δ = 0
  unconditionally"). It is incoherent with §4.3.
- **Drop the `False.elim` arm** for case (b). With Option A's signed
  hypothesis, case (b) is unreachable by construction.
- LOC estimate: ~20-30 (down from PREP-estimated 30-50, since no
  `decide`/`nlinarith` `False.elim` branch needed).

### S6 ACT picker (currently blocked by this finding)

- **Do not directly discharge the parent axiom as currently stated.** It is
  unsound.
- **Step 1**: Replace the parent axiom (`ProductOfSegmentsOfChords.lean:468`)
  with the Option A form. This is a signature change, not a discharge.
- **Step 2**: Update the parent theorem (line 481) to take a signed hypothesis
  and pass it through.
- **Step 3**: Update any downstream callers (search for
  `converse_product_implies_concyclic` references in `proofs/Proofs/` and
  `src/data/proofs/`).
- **Step 4**: Discharge the new (signed) axiom using S3 ACT + S4 ACT + S5
  ACT (signed form). `axiomCount` 1 → 0.
- LOC estimate: ~10-20 (signature swap + caller-update plumbing) on top of
  the S3/S4/S5 ACTs themselves.

### S8 PREP (PR #19231, open) compatibility

S8 PREP focuses on Mathlib v4.26.0 bearer re-verification (`Matrix.det_fin_four`
non-existence, `cramer_apply`, `EuclideanSpace.norm_sq_eq`, etc.). It does
**not** discuss case (b) or the parent-axiom counterexample. Its bearer
findings are orthogonal and remain load-bearing for the S3/S4 ACTs under
either Option A or B. **No conflict.**

S8 PREP's corrected S5 ACT skeleton (§5 in PR #19231) inherits the same
unsigned hypothesis as S5 PREP — i.e., it inherits the soundness issue. The
S5 ACT picker should combine **S8 PREP's bearer corrections** with **this
S9 PREP's Option A signature change**.

### S7 ACT (PR #19096, open) compatibility

S7 ACT BUILD-VERIFY patches the import path and removes two `Matrix.det_fin_four`
example blocks. It does not edit the parent file or the axiom. The two
findings here (counterexample, recovery options) are entirely in the
`research/problems/.../sessions/` doc layer. **No conflict.**

## 7. Paste-ready Lean witnesses (for whoever lands the Option A change)

These are *optional* — purely for downstream regression tests. The S6 ACT
picker who lands Option A can include the following to lock in the
counterexample and prevent future regressions to the unsigned form.

### 7.1 Construct the counterexample points as `Vec2`

```lean
namespace ProductOfSegmentsOfChords.OQ03Counterexample

open ProductOfSegmentsOfChords    -- for `Vec2`

/-- Concrete counterexample showing the unsigned chord-product axiom would be
unsound. Coordinates chosen rational and axis-aligned for `norm_num`. -/
def P : Vec2 := ![0, 0]
def A : Vec2 := ![1, 0]
def B : Vec2 := ![-2, 0]
def C : Vec2 := ![0, 1]
def D : Vec2 := ![0, 2]
```

Note: `![…]` for `EuclideanSpace ℝ (Fin 2)` requires either
`(WithLp.equiv 2 _).symm ![x, y]` or the `EuclideanSpace.ofMatrix`-style
adapter. The S6 ACT picker should consult `Mathlib.Analysis.InnerProductSpace.PiL2`
for the standard construction; `![x, y]` may need to be wrapped in
`EuclideanSpace.equiv.symm` or similar.

### 7.2 Hypothesis-checking lemmas

```lean
-- All nine axiom hypotheses are checkable by `decide` or `norm_num`/`simp`:
example : ∃ t : ℝ, B - P = t • (A - P) := ⟨-2, by simp [P, A, B]; ring⟩
example : ∃ t : ℝ, D - P = t • (C - P) := ⟨2,  by simp [P, C, D]; ring⟩
example : ‖P - A‖ * ‖P - B‖ = ‖P - C‖ * ‖P - D‖ := by
  simp [P, A, B, C, D, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  -- Both sides simplify to 1 * 2 = 1 * 2 = 2.
  norm_num
example : A ≠ P := by simp [A, P]; decide
example : B ≠ P := by simp [B, P]; decide
example : C ≠ P := by simp [C, P]; decide
example : D ≠ P := by simp [D, P]; decide
example : A ≠ B := by simp [A, B]; decide
example : C ≠ D := by simp [C, D]; decide
```

(`decide` is OK at v4.26.0 for rational/integer equalities on `EuclideanSpace`
once `simp` reduces to `Fin 2 → ℝ` literals.)

### 7.3 The determinant evaluation (Δ = 12)

```lean
example : concyclicityDetCoords 1 0 (-2) 0 0 1 0 2 = 12 := by
  unfold concyclicityDetCoords
  -- After S7 ACT BUILD-VERIFY (PR #19096) removes the dead Matrix.det_fin_four
  -- references, this should be discharged via the v4.26.0-correct expansion:
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
             Matrix.submatrix_apply, Matrix.det_fin_three,
             Fin.val_zero, Fin.val_succ, Fin.zero_succAbove, Fin.succ_succAbove_zero,
             Fin.succ_zero_eq_one, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.head_cons, Matrix.head_fin_const]
  ring
```

If the `simp only [det_succ_row_zero, …]` block does not close cleanly,
fallback to a fully unfolded `Matrix.det_apply` over `Equiv.Perm (Fin 4)`
(24 terms; slower but always works).

### 7.4 Non-concyclicity witness

```lean
-- The four points are NOT concyclic: any candidate (O, r) must satisfy all
-- four distance equalities, forcing the circle x²+y²+x+y-2=0, on which
-- D=(0,2) gives 4≠0.
example : ¬ ∃ (O : Vec2) (r : ℝ), 0 < r ∧
    ‖A - O‖ = r ∧ ‖B - O‖ = r ∧ ‖C - O‖ = r ∧ ‖D - O‖ = r := by
  rintro ⟨O, r, hr, hA, hB, hC, hD⟩
  -- From ‖A-O‖² = ‖B-O‖² = ‖C-O‖² = r², three linear equations in (O₀, O₁, r²)
  -- pin O = (-1/2, -1/2) and r² = 5/2 (circle x²+y²+x+y-2=0 →
  -- (x+1/2)² + (y+1/2)² = 5/2); but ‖D-O‖² = (1/2)² + (5/2)² = 1/4 + 25/4 = 13/2 ≠ 5/2.
  -- This is a finite algebraic obstruction; `nlinarith` or explicit
  -- coordinate extraction closes it. Full proof obligation: ~20 LOC.
  sorry  -- intentional placeholder; the Option A discharge does not need this
```

(The `sorry` here is intentional and would not appear in a shipped PR — it's
a sketch of the obstruction for completeness. The Option A change does not
require this witness theorem to ship; it's only useful as a regression test.)

## 8. Mathlib API audit (for Option A)

The signed inner-product hypothesis uses the standard `EuclideanSpace`
inner-product API. Re-verified at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Symbol | Location | Status |
|---|---|---|
| `inner` (RealInnerProductSpace notation `⟪·, ·⟫_ℝ`) | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | ✓ |
| `EuclideanSpace.inner_eq` (or `PiLp.inner_apply`) | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` | ✓ (verify exact name at pin before paste) |
| `inner_sub_left`, `inner_sub_right` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | ✓ standard |
| `real_inner_self_eq_norm_sq` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | ✓ (`⟪x, x⟫_ℝ = ‖x‖^2`) |
| `inner_smul_left`, `inner_smul_right` | same | ✓ |
| `Matrix.det_succ_row_zero` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:761` | ✓ (re-verified, see §7.3) |
| `Matrix.det_fin_three` | `…/Determinant/Basic.lean:820` | ✓ |

The S6 ACT picker should `gh api …?ref=$SHA` check `EuclideanSpace.inner_eq`'s
exact name (likely `EuclideanSpace.inner_apply` or `PiLp.inner_apply` at
v4.26.0 — Mathlib renamed several variants around the L²-norm refactor).

## 9. Conflict-free guarantees

This PREP adds **exactly one file**:

- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-14-s9-prep-axiom-counterexample-and-sign-recovery.md`

It does **NOT** edit:

- `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` (PR #19096 owns this)
- `proofs/Proofs/ProductOfSegmentsOfChords.lean` (no PR touches; locked
  pending S6 ACT)
- `research/problems/product-of-segments-of-chords-oq-03/state.md`
  (PR #19096 owns this)
- `src/data/research/problems/product-of-segments-of-chords-oq-03.json`
  (PR #19096 owns this)
- `research/problems/product-of-segments-of-chords-oq-03/problem.md`
- `research/problems/product-of-segments-of-chords-oq-03/knowledge.md`
- any prior `sessions/*.md` file (S1-S6, S7, S8 each owned by their respective
  PRs/merges)
- `src/data/proofs/product-of-segments-of-chords/meta.json`

PR overlap matrix:

| PR | Files | Overlap with this S9 PREP |
|----|-------|---------------------------|
| #19096 (open) S7 ACT BUILD-VERIFY | OQ03.lean, state.md, JSON, sessions/s7… | **none** |
| #19231 (open) S8 PREP bearer reverify | sessions/s8… | **none** (different filename) |
| (this) S9 PREP counterexample | sessions/s9… | n/a |

All three PRs are stackable in any order.

## 10. Scope of this PREP

- **Doc-only**, single new file (~500 LOC).
- **No Lean files** edited.
- **No state.md / JSON / meta.json** edited.
- **No prior session memos** edited.
- **No Docker build** required (no Lean changes).
- **Mathematical content**: concrete counterexample to the parent axiom +
  three recovery options + paste-ready Lean obligations for the recommended
  option.
- **Blocking finding**: S5 ACT and S6 ACT cannot proceed without choosing a
  recovery option; their current PREP plans (per S3/S4/S5/S8 PREPs) all
  assume an unsigned hypothesis that is provably unsound.

## 11. Anti-targets

This S9 PREP does **NOT**:

1. Ship the Lean Option A axiom (that is S6 ACT's job — a real Lean edit
   with caller updates).
2. Modify `state.md`, `JSON`, `problem.md`, `knowledge.md`, gallery
   `meta.json`, or any prior session memo.
3. Modify any `.lean` file (parent, OQ-03 companion, or elsewhere).
4. Modify or close PR #19096 or PR #19231.
5. Discharge the parent axiom. The axiom must first be restated (Option A);
   discharge is then a separate, sound, S6 ACT step.
6. Reach into Mathlib upstream (no PR to leanprover-community/mathlib4).

## 12. Memory-pattern note

This PR follows the **"sibling PREP audits peer's PR-body discharge plan
finds fictitious bearer + simpler bearer"** pattern (memory entry
`feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer.md`),
extended to **mathematical-content audit**:

- (a) **pin-verify bearer** — extended here to verify the *mathematical
  truth* of the discharge target (the parent axiom) at a concrete numerical
  counterexample.
- (b) **scout simpler alternative** — found one (Option A: signed
  inner-product, which collapses the S5 ACT case split to a single branch).
- (c) **3-option recipe** — provided (A recommended, B conservative, C
  unsound and rejected).
- (d) **composite paste-ready diff** — staged in §5 + §7 for the eventual S6
  ACT.

Distinct from the existing memory entry in that here the audited artifact
is not a bearer name but a load-bearing mathematical claim (the case-(b)
absorption recommendation in S5 PREP §2.1).
