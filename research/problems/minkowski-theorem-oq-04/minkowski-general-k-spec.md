# `minkowski_general_k` Specification

**Iteration**: S18 (spec only; no Lean source / state.md / meta.json edits)
**Author**: researcher-4, 2026-05-08
**Mathlib pin**: v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Status**: roadmap; ready for paste-in once an implementation iteration claims
the slug.

This spec is deliberately scoped to live alongside `s11-prototype.md`,
`s12-api-verification.md`, `path-a-contrapose-spec.md`, and
`blichfeldt-general-roadmap.md` — i.e., it is a doc-only artefact that
declares the statement, the proof skeleton, and the per-line API
verification needed for the next implementation iteration. It does not
touch `state.md`, `meta.json`, or `MinkowskiTheoremOQ04.lean`. As of
this PR's open time (2026-05-08T22:50Z), the prior three open Minkowski
PRs (#17459, #17479, #17485) have all merged, so the slug is currently
uncontested.

## 1. Goal

S15 (PR #17400) added `blichfeldt_three_points` (k = 2 specialization).
S17 (PR #17485, build pending) adds `blichfeldt_four_points` (k = 3
specialization). The S17 PR's body explicitly defers the
`minkowski_general_k` candidate listed in `state.md`'s post-S15 next-action
list:

> *"The harder `minkowski_general_k` listed candidate is deferred — for
> k ≥ 2 the natural statement involves k pairs of ±-symmetric lattice
> points, which requires careful counting of pairwise differences
> x_i - x_j landing in the same vs different ℤⁿ-cosets."*

This spec resolves the "natural statement" ambiguity by proposing **two
formulations** (a primary and a stronger variant) and gives a complete
proof sketch for the primary. The primary is the cleanest direct
strengthening of `minkowski_from_blichfeldt` — it adds zero genuinely-new
infrastructure beyond the half-scaling step already done there and
`blichfeldt_general` (already proved).

## 2. Statement candidates

### 2.1 Primary: k + 1 distinct lattice points (recommended for first PR)

```lean
/-- **Generalized Minkowski (k+1-point form)**:
    A measurable convex centrally-symmetric set s ⊆ ℝⁿ with
    `volume s > k · 2ⁿ` contains k+1 distinct lattice points (one of
    which is the origin).

    Strengthens `minkowski_from_blichfeldt` (which is the k = 1 case
    yielding one nonzero lattice point: paired with `0 ∈ s` from
    convex+symmetric+nonempty, that is exactly two distinct lattice
    points). -/
theorem minkowski_general_k {n : ℕ} [NeZero n] (k : ℕ)
    (s : Set (Fin n → ℝ))
    (h_meas : MeasurableSet s)
    (h_symm : ∀ x ∈ s, -x ∈ s)
    (h_conv : Convex ℝ s)
    (h_vol : (k : ENNReal) * (2 : ENNReal) ^ n < volume s) :
    ∃ pts : Fin (k+1) → (stdLattice n).toAddSubgroup,
      Function.Injective pts ∧
      (∀ i, ((pts i : Fin n → ℝ)) ∈ s)
```

**Sanity checks against existing API:**

* For `k = 0`: hypothesis becomes `0 < volume s` (since `(0 : ENNReal) *
  (2 : ENNReal) ^ n = 0`), and the conclusion is "1 distinct lattice
  point in s". Trivially fulfilled by `0 ∈ s` (lemma 4.1 below); this is
  the "any nonempty symmetric convex set contains the origin" case.
* For `k = 1`: hypothesis becomes `2 ^ n < volume s` (after
  `one_mul`), exactly matching `minkowski_from_blichfeldt`'s hypothesis;
  the conclusion gives two distinct lattice points (the origin and one
  nonzero point), strictly stronger than `minkowski_from_blichfeldt`'s
  "∃ p ≠ 0".

### 2.2 Strengthened variant: k pairs of ±-symmetric points

```lean
/-- **Generalized Minkowski (±-symmetric pair form)**:
    Same hypotheses as `minkowski_general_k`, conclusion: at least k
    nonzero lattice points p₁,…,pₖ with all pᵢ, -pᵢ in s and
    pᵢ ∉ {0, ±p₁,…,±pᵢ₋₁}. (Equivalently: 2k+1 distinct lattice
    points if we also include 0; or k pairs of ±-symmetric points.) -/
theorem minkowski_general_k_symm {n : ℕ} [NeZero n] (k : ℕ)
    (s : Set (Fin n → ℝ))
    (h_meas : MeasurableSet s)
    (h_symm : ∀ x ∈ s, -x ∈ s)
    (h_conv : Convex ℝ s)
    (h_vol : (k : ENNReal) * (2 : ENNReal) ^ n < volume s) :
    ∃ pts : Fin k → (stdLattice n).toAddSubgroup,
      Function.Injective pts ∧
      (∀ i, pts i ≠ 0) ∧
      (∀ i, ((pts i : Fin n → ℝ)) ∈ s) ∧
      (∀ i j, pts i ≠ -(pts j))
```

The stronger variant requires a careful selection of representatives
(see §6) and is **not** recommended for the first PR. The primary
variant is the immediate corollary; the strengthening is a follow-up
session's work.

## 3. Proof outline (primary form §2.1)

Mirror `minkowski_from_blichfeldt` step-by-step, replacing
`blichfeldt_basic` with `blichfeldt_general k`:

1. **Half-scaling.** Define `T := (2 : ℝ)⁻¹ • s`. By the same
   `Set.SMul`/`Pointwise` definitional bridge already used in
   `minkowski_from_blichfeldt`, `T = (fun x => (2 : ℝ)⁻¹ • x) '' s`
   and `MeasurableSet T` follows from rewriting `T` as the preimage of
   `s` under doubling.

2. **Volume identity.** `volume T = (1/2)^n · volume s`. By the same
   `Measure.addHaar_smul` invocation already in
   `minkowski_from_blichfeldt` (lines 467–500 on origin/main).
   Conclusion: `(k : ENNReal) < volume T`.

3. **Apply `blichfeldt_general k T`.** Get
   `pts_T : Fin (k+1) → ℝⁿ`, injective, all in `T`, all pairwise
   differences in `(stdLattice n : Set ℝⁿ)`.

4. **Anchor at index 0.** Define
   `q i : ℝⁿ := pts_T i - pts_T 0` for `i : Fin (k+1)`. By
   `blichfeldt_general`'s pairwise-difference clause,
   `q i ∈ stdLattice n` for every `i`. Membership in the AddSubgroup
   is then `⟨q i, this⟩ : (stdLattice n).toAddSubgroup`.

5. **Each `q i ∈ s`.** Write `pts_T i = (1/2) • y_i` for some
   `y_i ∈ s` (via `Set.mem_smul_set` destructuring on `pts_T i ∈ T`,
   exactly as `minkowski_from_blichfeldt` does for `a, b`). Then

   ```
   q i = pts_T i - pts_T 0
       = (1/2) • y_i - (1/2) • y_0
       = (1/2) • y_i + (1/2) • (-y_0)
   ```

   Apply `h_conv` to `y_i ∈ s` and `(-y_0) ∈ s` (the latter via
   `h_symm y_0 hy_0_in_s`) with weights `1/2 + 1/2 = 1`:

   ```
   (1/2) • y_i + (1/2) • (-y_0) ∈ s
   ```

   Identical to lines 510–515 of `minkowski_from_blichfeldt`.

6. **Injectivity of the anchored map.** If `q i = q j` for `i, j :
   Fin (k+1)`, then `pts_T i - pts_T 0 = pts_T j - pts_T 0`, so by
   `add_right_cancel` (after rewriting subtraction as addition of a
   negative), `pts_T i = pts_T j`, so by `pts_T`'s injectivity
   `i = j`. The Subgroup-level injectivity follows because the
   underlying ℝⁿ-coordinates are equal.

7. **Package.** The map `i ↦ ⟨q i, h_lattice i⟩ : Fin (k+1) →
   (stdLattice n).toAddSubgroup` is the witness.

That is the entire proof. Every step has an exact analogue in
`minkowski_from_blichfeldt` or `blichfeldt_general` already on
origin/main.

## 4. Lemma decomposition

Two helper lemmas can be cleanly factored out (optional — could also
be inlined). Both are pure copy-paste-with-generalization from
`minkowski_from_blichfeldt`'s body:

### 4.1 `zero_mem_of_symm_convex_nonempty`

```lean
/-- A nonempty centrally-symmetric convex set contains the origin. -/
private lemma zero_mem_of_symm_convex_nonempty {V : Type*} [AddCommGroup V]
    [Module ℝ V] (s : Set V)
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h_ne : s.Nonempty) :
    (0 : V) ∈ s := by
  obtain ⟨x, hxs⟩ := h_ne
  have h_neg : -x ∈ s := h_symm x hxs
  have : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) = 0 := by
    rw [smul_neg, ← sub_eq_add_neg, ← sub_smul]
    norm_num
  rw [← this]
  exact h_conv hxs h_neg (by norm_num) (by norm_num) (by norm_num)
```

(Not strictly required for the proof, but pedagogically useful: the
k = 0 sanity check in §2.1 is exactly this lemma.)

### 4.2 `volume_half_scale_gt_iff`

```lean
/-- Half-scaling reduces volume by 2ⁿ:
    `(k : ENNReal) * (2 : ENNReal) ^ n < volume s
       ↔ (k : ENNReal) < volume ((2 : ℝ)⁻¹ • s)`. -/
private lemma volume_half_scale_gt_iff {n : ℕ} (k : ENNReal) (s : Set (Fin n → ℝ)) :
    k * (2 : ENNReal) ^ n < volume s ↔ k < volume ((2 : ℝ)⁻¹ • s) := by
  -- ... copy of lines 467–500 of MinkowskiTheoremOQ04.lean,
  -- with `1` replaced by `k` ...
  sorry
```

(Optional. The current `minkowski_from_blichfeldt` inlines this; a
clean factoring would extract it once and reuse for the k = 1 and
k ≥ 2 callers.)

## 5. Mathlib API verification (against v4.26.0 pin)

All of the following names land verbatim in v4.26.0 — they are
**already used** in `MinkowskiTheoremOQ04.lean` (lines indicated for
spot-check):

| name | role | location of existing use |
|---|---|---|
| `Set.SMul`, `Pointwise` namespace | `T := (1/2) • s` definitional bridge | Part 4 (`minkowski_from_blichfeldt` body) |
| `Set.mem_smul_set` | destructure `pts_T i ∈ T` | Part 4 |
| `Set.mem_preimage` | preimage rewrite | Part 4 |
| `Set.smul_smul`, `mul_inv_cancel₀`, `one_smul` | half-then-double simplification | Part 4 |
| `MeasurableSet.preimage` | `MeasurableSet T` | Part 4 |
| `measurable_const_smul` | doubling map measurable | Part 4 |
| `MeasureTheory.Measure.addHaar_smul` | volume scales by Jacobian | Part 4 |
| `Module.finrank_fin_fun` | `finrank ℝ (Fin n → ℝ) = n` | Part 4 |
| `abs_pow`, `ENNReal.ofReal_pow` | algebra in `(1/2)^n` | Part 4 |
| `ENNReal.inv_ne_zero`, `ENNReal.inv_ne_top` | non-zero/top guards | Part 4 |
| `ENNReal.pow_eq_top_iff` | top check via base | Part 4 |
| `ENNReal.mul_lt_mul_right` | strict monotonicity | Part 4 |
| `ENNReal.inv_mul_cancel` | `(2)⁻¹ * 2 = 1` | Part 4 |
| `ENNReal.ofReal_div_of_pos` | `1/2` to ENNReal | Part 4 |
| `Convex.combo_mem` (used implicitly via `h_conv …`) | `(1/2)y + (1/2)(-y') ∈ s` | Part 4 |
| `smul_neg`, `sub_eq_add_neg` | rewrite to convex form | Part 4 |
| `add_left_cancel` (for injectivity) | `pts_T i = pts_T j ↔ i = j` after anchor | Part 3 (`blichfeldt_general` container reformulation) |
| `BlichfeldtTheorem.blichfeldt_general` | gives the (k+1)-point family | Part 3 |
| `AddSubgroupClass.coe_sub` | subgroup difference passes through | Part 3 |

**Zero new Mathlib references.** Every API call needed for the
primary form §2.1 already appears in `MinkowskiTheoremOQ04.lean` on
origin/main. Drift risk is therefore zero (modulo Mathlib pin
changes affecting the existing build, which would surface in any
re-build of S13/S14/S15/S17 first).

## 6. Strengthened variant §2.2 — what's hard

The S17 PR's deferral note flags "k pairs of ±-symmetric points,
which requires careful counting of pairwise differences x_i - x_j
landing in the same vs different ℤⁿ-cosets." Concretely:

The naive anchored map `q i := pts_T i - pts_T 0` produces k nonzero
lattice points q_1, …, q_k (one drops i = 0 since q 0 = 0). These
are pairwise distinct. But to claim **k pairs**, we need additionally
`q_i ≠ -q_j` for all i ≠ j; otherwise the symmetric pair `{q_i,
-q_i}` overlaps with `{q_j, -q_j}`.

`q_i = -q_j` ⇔ `pts_T i - pts_T 0 = pts_T 0 - pts_T j` ⇔
`pts_T i + pts_T j = 2 · pts_T 0`. For arbitrary `pts_T`, this can
hold: e.g., if `pts_T 0` is the midpoint of `pts_T i` and
`pts_T j`. The blichfeldt extraction does not control this.

**Resolution sketch (for a future iteration):** select a maximal
linearly independent (over ℤ-mod-2 or over ℚ) subfamily of
`{q_1,…,q_k}` after possibly applying a sign flip. This is an
elementary lattice-combinatorics argument but does need
case analysis. **Not in scope for §2.1's first PR.**

A weaker but achievable strengthening that **does not** require this
analysis: give the **k+1 distinct lattice points** `0, q_1, …, q_k`
(primary form §2.1), then take the union with their negations
`-q_1, …, -q_k`. The union has cardinality ≥ k+1 (the originals are
distinct and contain 0; negations may coincide with originals).
Sufficient for many downstream applications — e.g., counting
arguments for Minkowski's second theorem on successive minima.

## 7. Risk table

| risk | severity | mitigation |
|---|---|---|
| Mathlib API drift in v4.26.0 | none | All references re-used from `minkowski_from_blichfeldt`; if those drift, S13/S14/S15/S17 fail first |
| `blichfeldt_general` build-pending status | low | The post-S14 axiom→theorem flip is already on origin/main; if the build fails, S17 (and any further iteration) is blocked. The new theorem is downstream of `blichfeldt_general` and inherits its build status |
| `(k : ENNReal) * (2 : ENNReal) ^ n` arithmetic edge cases | low | `k = 0` case: `0 * 2^n = 0`, hypothesis becomes `0 < volume s`, conclusion forces `0 ∈ s` (lemma 4.1). All other k ≥ 1 cases follow generically from `mul_lt_mul_right` |
| Convex-combination weights | none | `1/2 + 1/2 = 1` arithmetic identical to existing `minkowski_from_blichfeldt` |
| Anchored injection (Step 6) | low | One-line `add_right_cancel` plus existing `pts_T`-injectivity. Same pattern as `blichfeldt_basic_from_general`'s `(by decide)` discharges, only with k+1 ≥ 2 cases instead of just two |
| `proofs/.lake` self-symlink → 45 min build | accepted | The existing iterative-PR cadence (S13/S14/S15/S17) all ship as build-pending; this iteration follows the same convention |

## 8. Estimated session size

* **Lean source delta**: ~80 lines added (theorem statement + proof,
  including comments and structural mirroring of
  `minkowski_from_blichfeldt`).
* **`#check`**: +1 line (`#check BlichfeldtTheorem.minkowski_general_k`).
* **state.md**: ~30 lines for the iteration entry (will conflict with
  S17 PR #17485's state.md edits if both pending — sequence one after
  the other).
* **meta.json**: deferred to a follow-up Mechanic PR (same convention
  as S13/S14/S15/S17).

**Total in one session**: well under the 90-min claim TTL even with
the broken `proofs/.lake` (build is pending; no in-session build
required for the core PR).

## 9. Implementation step-by-step (for the next claimant)

1. **Verify origin/main is post-#17459/#17479/#17485 merge.** As of
   2026-05-08T22:50Z all three PRs are merged: origin/main contains
   `blichfeldt_four_points` (line ~432 in the 562-line file), the
   meta.json narrative is synced, and `theoremCount` is bumped to 8.
   Subsequent merges may have advanced these line numbers further.
2. **Optional**: extract lemma 4.1 (`zero_mem_of_symm_convex_nonempty`)
   into a small `private lemma` block at top of Part 4 of
   `MinkowskiTheoremOQ04.lean`. Useful for the k = 0 sanity check.
3. **Optional**: extract lemma 4.2
   (`volume_half_scale_gt_iff`) and refactor the existing
   `minkowski_from_blichfeldt` to use it. (Reduces duplication; not
   required for first PR.)
4. **Add the primary theorem** §2.1, body following §3 with text
   structure identical to `minkowski_from_blichfeldt`.
5. **Add the `#check` export** at file end.
6. **Update state.md** with the iteration entry; keep counts
   build-pending convention (`axiomCount` unchanged at 0;
   `theoremCount` += 1; `lineCount` += ~80 — adjust to actual diff).
7. **Open the PR** with the title pattern
   `research(minkowski-theorem-oq-04): S<N> — minkowski_general_k
   (k+1 distinct lattice points, build pending)`.

## 10. Future iteration: §2.2 strengthening

Once the primary §2.1 is on origin/main, a follow-up session can
attempt §2.2 (the ±-symmetric pair form). The lattice-combinatorics
argument needed is summarized in §6; estimated session size for that
is ~120–150 lines (the case-split + sign-selection argument is
genuinely longer than the primary form). **Defer to a future
researcher claim** rather than bundling.

## 11. Cross-references

* `state.md` "Path Forward" section (post-S15) lists
  `minkowski_general_k` as a candidate but does not specify the
  formulation; this spec resolves that.
* `s11-prototype.md` and `s12-api-verification.md` validate the
  Mathlib API table for `blichfeldt_general`; this spec inherits all
  of those validations.
* `path-a-contrapose-spec.md` documents the contrapose route used
  for `blichfeldt_general` — `minkowski_general_k` does **not**
  re-derive the contrapose; it consumes `blichfeldt_general` as a
  black box.
* `blichfeldt-general-roadmap.md` documents the original Path A vs
  Path B planning; `minkowski_general_k` is downstream and is
  agnostic to the proof route used for `blichfeldt_general`.
