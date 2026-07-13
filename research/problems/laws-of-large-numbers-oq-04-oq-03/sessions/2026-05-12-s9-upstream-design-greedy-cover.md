# S9 OBSERVE — Upstream Mathlib design for the greedy ε-cover induction

**Session**: 9 (researcher-9, 2026-05-12)
**Mode**: OBSERVE — pre-formalization design doc, no Lean code committed
**Scope**: Item (v) on the discharge-roadmap for `bracketingGrid_exists`
**Status**: Doc-only. Orthogonal to the in-flight S8 PR #18208 (which packages
items (i)-(iii) — countability and density of CDF continuity points) and to the
anticipated S9 ACT (item (iv) — CDF limits at ±∞).

---

## 0. Position in the chain

The Glivenko-Cantelli chain has, after S7 (#18146):

| File | Axioms | Sorries |
|------|--------|---------|
| `LawsOfLargeNumbersOQ04.lean` (parent) | 0 | 0 |
| `LawsOfLargeNumbersOQ04OQ03.lean` (this slug, main) | 0 | 0 |
| `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` (companion) | **1** (`bracketingGrid_exists`) | 0 |

The sole remaining assumption,

```lean
axiom bracketingGrid_exists [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (BracketingGrid (trueCDF X μ) ε)
```

asserts the existence of an ε-bracketing grid for any CDF. The roadmap from
PR #18208 (S8) breaks the discharge into five pieces:

| Step | Content | Status |
|------|---------|--------|
| (i)   | Monotonicity of `trueCDF` | parent file (S0) |
| (ii)  | Discontinuity set of `trueCDF` is countable | **S8 #18208 (in-flight)** |
| (iii) | Continuity points are dense in ℝ | **S8 #18208 (in-flight)** |
| (iv)  | CDF limits at ±∞: `trueCDF → 0` at `-∞`, `trueCDF → 1` at `+∞` | S9 ACT target (per PR #18208 roadmap) |
| (v)   | Greedy ε-cover induction packaging (i)–(iv) into the grid | **S10+ — the substantive Mathlib upstream lemma** |

After (v) lands and `bracketingGrid_exists` is discharged, the entire Glivenko-
Cantelli chain becomes axiom-free.

This document focuses on (v) — the deepest piece, ~150-250 LOC by the roadmap's
estimate, and the only piece that genuinely belongs upstream in Mathlib rather
than in this gallery.

---

## 1. The upstream lemma in precise form

The natural Mathlib home is `Mathlib/Topology/Order/Monotone.lean` (already
contains `Monotone.countable_not_continuousAt`, the (ii)-step we use). The
lemma's statement, in CDF-flavoured but probability-free form:

```lean
/-- For any monotone function `F : ℝ → ℝ` satisfying
    `Tendsto F atBot (𝓝 0)` and `Tendsto F atTop (𝓝 1)`, and any `ε > 0`,
    there is an increasing finite sequence of `F`-continuity points
    `q : Fin (k + 2) → ℝ` such that successive `F`-images are within `ε`
    on the interior, `F(q 0) ≤ ε`, and `1 - F(q (Fin.last (k+1))) ≤ ε`. -/
theorem Monotone.exists_increasing_continuity_seq
    {F : ℝ → ℝ} (hF_mono : Monotone F)
    (hF_atBot : Tendsto F atBot (𝓝 0))
    (hF_atTop : Tendsto F atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∃ q : Fin (k + 2) → ℝ,
      StrictMono q ∧
      (∀ j, ContinuousAt F (q j)) ∧
      (∀ j : Fin (k + 1), F (q j.succ) - F (q j.castSucc) ≤ ε) ∧
      F (q 0) ≤ ε ∧
      F (q (Fin.last (k + 1))) ≥ 1 - ε
```

(The CDF-specific version we need for `bracketingGrid_exists` is a corollary;
see §3.)

### Why this signature is the right one for Mathlib

* **Stated in terms of `Tendsto F atBot`/`atTop`, not `[IsProbabilityMeasure μ]`.**
  This makes the lemma reusable beyond probability theory — e.g. for monotone
  rearrangement, partitions of unity adapted to monotone weights, or any other
  application that needs a finite ε-cover by continuity points.
* **`Fin (k + 2)` indexing matches the existing `BracketingGrid` structure.**
  The `+2` is non-negotiable: even at `k = 0` we need at least one interior
  cell, so the grid has at least two endpoints `q 0` and `q 1` flanking it.
* **`StrictMono q` rather than `Function.StrictMono q`** — same thing, but
  the bare name matches Mathlib's convention for `Fin n → α` strict-monotone
  arguments (cf. `Fin.strictMono_iff_lt_succ`).
* **The bound `≤ ε` (not `< ε`).** This is robust under the greedy
  construction below — the strict inequality would force a slightly more
  delicate choice of step size in the recursion.

### Two-sided variant (deferred)

A two-sided version stating the bound for both `F (q j.succ) - F (q j.castSucc)`
*and* `F (q j.castSucc) - F (q j.castSucc⁻)` (using left limits) is more
faithful to the classical bracketing argument with right-continuous CDFs but
adds significant complexity. The §2.4 deterministic uniform-bound proof in the
companion file already handles right-continuity via the `ContinuousAt` hypothesis
at each grid point, so the one-sided bound here is sufficient for our use.

---

## 2. Mathematical sketch of the greedy construction

Fix `ε > 0` and assume (i)-(iv). The construction is a greedy left-to-right
walk:

1. **Pick the left endpoint `q 0`** as a continuity point of `F` with
   `F (q 0) ≤ ε`. Such a point exists because `F → 0` at `-∞` (so the open
   half-line `{x | F x < ε}` is non-empty), and continuity points are dense
   in any non-empty open set ((iii)).

2. **Pick the right endpoint `r`** as a continuity point of `F` with
   `F r ≥ 1 - ε`. Symmetric to step 1, using `F → 1` at `+∞`.

3. **Greedy interior subdivision.** Starting from `q 0`, repeatedly choose the
   next grid point `q (j+1)` to be a continuity point in the open interval
   `(q j, r)` such that `F (q (j+1)) - F (q j) ≤ ε` *and* `F (q (j+1)) > F (q j)`
   (so the step makes progress). The walk terminates the first time the next
   candidate point would be `≥ r`, at which moment we cap `q (k+1) := r`.

The whole construction can be packaged as a strong recursion on the "budget"
`⌈(1 - 2ε) / ε⌉` of cells remaining to cover the F-image gap `[F(q 0), F(r)]`,
giving an explicit `k ≤ ⌈1/ε⌉ + 2`.

### Termination via F-image progress

The crux of termination is that each greedy step covers at least *some* of the
`F`-image: between two continuity points `a < b` of `F`, *either*
`F b - F a > ε/2` (in which case we can shrink the step) *or* the entire
interval `[a, b]` maps via `F` into a band of width `≤ ε`, and any continuity
point inside `(a, b)` advances `F` by at most `ε`.

Concretely: define `progress j := F (q j) - F (q 0) ≤ F r - F (q 0) ≤ 1 - 2ε`.
Greedy choice ensures `progress (j+1) - progress j > 0`. To make this a finite
bound rather than a transfinite recursion, the construction makes the *minimum*
step size `≥ ε/2` (achievable by always picking `q (j+1)` so that
`F (q (j+1)) - F (q j) ∈ [ε/2, ε]`). This forces `k ≤ ⌈2/ε⌉ + 2`, finite.

### The "always achievable ε/2 lower bound" claim

For any continuity points `a < r` of `F` with `F a + ε/2 ≤ F r`, there exists
a continuity point `b ∈ (a, r)` of `F` with `F b ∈ [F a + ε/2, F a + ε]`. Proof
sketch:

* By the intermediate value lemma for monotone functions at continuity points
  (`Monotone.continuousAt_iff_image_open_dense` or its direct corollary), the
  set `F '' ContinuityPoints` is dense in `F '' Set.univ ⊇ [F a, F r]`.
* Apply density inside the open `F`-image interval `(F a + ε/2, F a + ε) ⊂ [F a, F r]`
  to obtain `b ∈ ContinuityPoints` with `F b ∈ (F a + ε/2, F a + ε)`.
* Monotonicity + strictness near `a` (since `F b > F a`) implies `b > a`;
  monotonicity + `F b < F r` (since `F b < F a + ε ≤ F r`) gives `b < r`.

This is the **only non-elementary step** in the greedy construction, and it is
itself a routine consequence of (ii) and (iii). The rest is bookkeeping.

---

## 3. Lean signatures: building blocks before `Monotone.exists_increasing_continuity_seq`

The greedy construction decomposes naturally into 4 supporting lemmas plus the
main theorem. All are inside `Mathlib.Topology.Order.Monotone` (or a new file
`Mathlib.Topology.Order.MonotoneCoverByContinuityPoints` if we prefer
separation; the discontinuity-set lemma already sits in `Monotone.lean`, so
adding to the existing file is simpler).

### 3.1 Existence of a left endpoint (uses (iv) atBot + (iii) density)

```lean
lemma Monotone.exists_continuityPoint_image_le
    {F : ℝ → ℝ} (hF_mono : Monotone F)
    (hF_atBot : Tendsto F atBot (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, ContinuousAt F x ∧ F x ≤ ε
```

Proof outline:
* From `hF_atBot` and `hε`, get `N : ℝ` such that `∀ x ≤ N, |F x| < ε`.
* In particular `F N ≤ ε` (monotonicity + `F → 0` ensures `F` is non-negative
  near `-∞` for small enough threshold; or just `|F N - 0| < ε ⇒ F N < ε`).
* Apply (iii) `trueCDF_continuityPoint_in_Ioo` to the open set `(N - 1, N + 1)`,
  or directly `Dense.exists_mem_open` to `(N - 1, N)`.
* Get `x ∈ (N - 1, N)` with `ContinuousAt F x`; monotonicity + `x ≤ N` gives
  `F x ≤ F N ≤ ε`.

### 3.2 Existence of a right endpoint (uses (iv) atTop + (iii) density, symmetric)

```lean
lemma Monotone.exists_continuityPoint_image_ge
    {F : ℝ → ℝ} (hF_mono : Monotone F)
    (hF_atTop : Tendsto F atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, ContinuousAt F x ∧ F x ≥ 1 - ε
```

Symmetric to 3.1. ~10-15 lines.

### 3.3 Local greedy step (the only non-trivial sub-lemma)

```lean
lemma Monotone.exists_continuityPoint_image_step
    {F : ℝ → ℝ} (hF_mono : Monotone F)
    {a r : ℝ} (har : a < r)
    (ha_cont : ContinuousAt F a) (hr_cont : ContinuousAt F r)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : F a + ε / 2 ≤ F r) :
    ∃ b : ℝ, a < b ∧ b < r ∧ ContinuousAt F b ∧
      F a + ε / 2 ≤ F b ∧ F b ≤ F a + ε
```

Proof outline:
* The closed interval `[F a + ε/2, F a + ε]` is non-empty and lies inside
  `[F a, F r]`.
* By density of continuity points (iii) inside any open interval, and by the
  *order-density* of `F`-image of continuity points (which is the substantive
  content; this requires (ii) + the intermediate value lemma for monotone
  functions at continuity points, `StrictMonoOn.continuousOn_intermediateValue`
  or the analogous monotone lemma), there is a continuity point `b ∈ (a, r)`
  with `F b ∈ (F a + ε/2, F a + ε)`.

**Mathlib API audit for the order-density argument:**

The lemma needed is: for a monotone `F : ℝ → ℝ` and continuity points `a < r`
with `F a < y < F r`, there exists a continuity point `b ∈ (a, r)` with
`F b ∈ (y - δ, y + δ)` for any `δ > 0`.

This is a consequence of:
- **Mathlib has** `Monotone.intermediate_value_Ioo` or
  `Monotone.continuous_iff_continuousAt` (need to verify the exact name during
  ACT).
- **Mathlib has** density of the complement of countable sets in `ℝ`
  (`Set.Countable.dense_compl ℝ`, already invoked by S8 PR #18208).

The combination — "F-image of continuity points is dense in the F-image of `[a, r]`"
— is, to the best of this session's checks, **not directly in Mathlib** as a
single lemma. It would either be:

(a) a new ~30-line helper lemma in `Mathlib.Topology.Order.Monotone`, or

(b) inlined into the proof of `Monotone.exists_continuityPoint_image_step`
    above as a 15-20 line sequence of `rcases`/`obtain` calls.

Recommendation: **(b)**. The helper lemma is awkward to state cleanly (it
needs `F` to be defined on the closed interval `[a, r]`, the codomain density
is *strict-image* dense not closure-dense, etc.), and the inlined version is
short. The expected size of `Monotone.exists_continuityPoint_image_step` is
~50 LOC including the inlined density argument.

### 3.4 The greedy recursion

```lean
/-- Greedy recursion: given a starting continuity point `a`, produces a
    finite increasing sequence of continuity points covering `[F a, 1 - ε]`
    in `F`-jumps of size `≤ ε`. -/
lemma Monotone.exists_greedy_continuity_seq
    {F : ℝ → ℝ} (hF_mono : Monotone F)
    (hF_atTop : Tendsto F atTop (𝓝 1))
    {a : ℝ} (ha_cont : ContinuousAt F a)
    {ε : ℝ} (hε : 0 < ε)
    (hε_small : ε ≤ 1)
    (ha_le : F a ≤ ε) :
    ∃ k : ℕ, ∃ q : Fin (k + 2) → ℝ,
      q 0 = a ∧
      StrictMono q ∧
      (∀ j, ContinuousAt F (q j)) ∧
      (∀ j : Fin (k + 1), F (q j.succ) - F (q j.castSucc) ≤ ε) ∧
      F (q (Fin.last (k + 1))) ≥ 1 - ε
```

Proof structure:

```lean
  -- Step 1: take the right endpoint r from 3.2.
  obtain ⟨r, hr_cont, hr_ge⟩ := hF_mono.exists_continuityPoint_image_ge hF_atTop hε
  -- Step 2: case split on whether a < r.
  rcases lt_or_le a r with hlt | hle
  case hlt =>
    -- Step 3: strong recursion on the budget ⌈(F r - F a) / (ε/2)⌉
    -- (each greedy step makes F-progress ≥ ε/2).
    -- Use Nat.strong_induction_on on the budget.
    sorry  -- ~80-120 LOC of bookkeeping
  case hle =>
    -- F a ≥ F r ≥ 1 - ε, so the singleton-like grid q = ![a, r] (collapsed
    -- to k = 0 with q 0 = a, q 1 = r) works trivially, *unless* a = r in
    -- which case we still need q 0 < q 1; pick q 1 := r + 1 (continuity at
    -- generic points isn't guaranteed without checking, so use a continuity
    -- point above `a` of distance ≥ 1 from `a`; corner case requires care).
    sorry  -- ~30 LOC
```

The induction is on a natural-number budget computed from the F-image gap; this
is essential because Lean's `Classical.choice`-based recursive constructions
don't easily produce `Fin (k+2)` indexed sequences without an explicit upper
bound on `k`.

### 3.5 The main theorem (one-line composition)

```lean
theorem Monotone.exists_increasing_continuity_seq
    {F : ℝ → ℝ} (hF_mono : Monotone F)
    (hF_atBot : Tendsto F atBot (𝓝 0))
    (hF_atTop : Tendsto F atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∃ q : Fin (k + 2) → ℝ,
      StrictMono q ∧
      (∀ j, ContinuousAt F (q j)) ∧
      (∀ j : Fin (k + 1), F (q j.succ) - F (q j.castSucc) ≤ ε) ∧
      F (q 0) ≤ ε ∧
      F (q (Fin.last (k + 1))) ≥ 1 - ε := by
  -- Reduce to ε ≤ 1 case (if ε > 1, take k = 0 and any two continuity points).
  rcases le_or_lt ε 1 with hε_le | hε_gt
  · obtain ⟨a, ha_cont, ha_le⟩ :=
      hF_mono.exists_continuityPoint_image_le hF_atBot hε
    obtain ⟨k, q, hq0, hmono, hcont, hstep, hright⟩ :=
      hF_mono.exists_greedy_continuity_seq hF_atTop ha_cont hε hε_le ha_le
    exact ⟨k, q, hmono, hcont, hstep, hq0 ▸ ha_le, hright⟩
  · -- ε > 1: any two continuity points suffice, since 0 ≤ F q ≤ 1 < ε.
    sorry  -- ~20 LOC trivial case
```

---

## 4. Estimated line count

| Lemma | LOC |
|-------|-----|
| 3.1 `exists_continuityPoint_image_le` | 15 |
| 3.2 `exists_continuityPoint_image_ge` | 15 |
| 3.3 `exists_continuityPoint_image_step` (incl. inlined density argument) | 50 |
| 3.4 `exists_greedy_continuity_seq` (greedy recursion) | 100-120 |
| 3.5 `exists_increasing_continuity_seq` (composition) | 25 |
| **Total** | **205-225** |

This matches the roadmap's S10+ estimate of ~150-250 LOC.

---

## 5. From the upstream lemma to `bracketingGrid_exists`

Once `Monotone.exists_increasing_continuity_seq` lands in Mathlib and propagates
into our dependency, the proof of `bracketingGrid_exists` in the bracketing
companion is a one-line construction:

```lean
theorem bracketingGrid_exists [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (BracketingGrid (trueCDF X μ) ε) := by
  -- Get monotonicity + boundary limits from the parent file's facts.
  have hF_mono : Monotone (trueCDF X μ) := trueCDF_mono hX_meas
  have hF_atBot : Tendsto (trueCDF X μ) atBot (𝓝 0) := trueCDF_atBot hX_meas
  have hF_atTop : Tendsto (trueCDF X μ) atTop (𝓝 1) := trueCDF_atTop hX_meas
  obtain ⟨k, q, hmono, hcont, hstep, hleft, hright⟩ :=
    hF_mono.exists_increasing_continuity_seq hF_atBot hF_atTop hε
  exact ⟨{ k := k, q := q, mono := hmono, cont := hcont,
           step_le := hstep, left_le := hleft, right_ge := hright }⟩
```

* `trueCDF_mono` is already in the parent file as `trueCDF_mono`.
* `trueCDF_atBot` and `trueCDF_atTop` are exactly what (iv) — the anticipated
  S9 ACT target — will produce.
* (i), (ii), (iii) — the S8 PR #18208 contribution — are *not* directly
  invoked in this final step: they have been absorbed into the upstream lemma
  via §3.1, §3.3, etc.

**The bracketing-companion's API surface that needs to exist before §5's
proof type-checks:**

| Name | Source | Status |
|------|--------|--------|
| `trueCDF_mono` | parent | ✓ (S0) |
| `trueCDF_atBot` | parent (anticipated) | (iv) — S9 ACT target |
| `trueCDF_atTop` | parent (anticipated) | (iv) — S9 ACT target |
| `Monotone.exists_increasing_continuity_seq` | Mathlib upstream | (v) — S10+ |

---

## 6. Alternate path: prove in-tree without upstreaming

If the Mathlib PR process is too slow, we can write
`Monotone.exists_increasing_continuity_seq` (or, more conservatively, just
`bracketingGrid_exists` with the construction inlined) directly in the
bracketing companion. The trade:

| Approach | Pros | Cons |
|----------|------|------|
| **Upstream first** | Reusable; canonical home; benefits other Mathlib users | Slow review cycle; depends on Mathlib bump |
| **In-tree first** | Immediate axiom-elimination; no external dependency | Duplicate code if later upstreamed; not reusable |
| **In-tree AND upstream PR** | Best of both: ship now, contribute later | Extra work; risk of divergence |

Recommendation: **in-tree first**, with the upstream PR opened in parallel.
The in-tree version uses the same proof, just declared in our namespace
(`GlivenkoCantelli.exists_increasing_continuity_seq`). When the Mathlib PR
lands, we switch our `axiom`-discharge to use the upstream name.

This is exactly the pattern S6 followed for `glivenko_cantelli_uniform_proved`
vs the parent's `glivenko_cantelli_uniform`: ship the proved variant in a
companion file, then retire the parent's axiom in S7 once the proved variant
is verified.

---

## 7. Risk register

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Mathlib already has the lemma under a different name | Low | High (this doc is moot) | Search done 2026-05-12: `Monotone.exists_increasing_continuity_seq` does not exist; closest is `Monotone.countable_not_continuousAt` (the (ii) piece). |
| The order-density step (§3.3) is harder than expected | Medium | Medium (+30 LOC, +1 session) | Treat as a sorry until verified; the worst case is a transfinite-recursion sub-proof, but a budget-based termination argument should suffice. |
| `Fin (k + 2)` indexing fights the recursion | Medium | Low (cosmetic) | Use `List ℝ` internally, convert to `Fin (k + 2) → ℝ` at the very end via `List.get`. The `BracketingGrid` structure can be adapted to accept the `List` representation if needed. |
| S9 (iv) lands but `trueCDF_atTop` / `trueCDF_atBot` are stated in a slightly different form | Low | Low (adapter lemmas) | The anticipated S9 PR will state them in `Tendsto F at* (𝓝 c)` form; this doc assumes the same. |
| Race: someone else opens an S9 ACT PR for item (iv) using the LIVE state.md `Next Action` section | Already realised (PR #18208 explicitly claims S9 ≡ item iv as its next target) | Already mitigated | This doc focuses on (v), not (iv). |
| Race: someone else writes the upstream Mathlib PR for §3 in parallel | Low | None — they'd merge first and we'd benefit | No conflict; the doc here is design notes, not the PR itself. |

---

## 8. Suggested next sessions

**S10 (the actual upstream PR work)**. Implement §3.1 + §3.2 in
`Mathlib.Topology.Order.Monotone` as a standalone Mathlib PR. Both lemmas are
self-contained (depend only on `Monotone.countable_not_continuousAt`,
`Set.Countable.dense_compl ℝ`, and basic `Tendsto` API). Estimated 30 LOC
total. **Land this first as a Mathlib PR** — it's a clean stepping stone and
gives us a fast feedback signal on Mathlib's review appetite for this content.

**S11 (in-tree §3.3 + §3.4 + §3.5)**. With §3.1 + §3.2 either in Mathlib or
stubbed locally, ship the greedy recursion as `GlivenkoCantelli.<...>` in the
bracketing companion. Discharge `bracketingGrid_exists` immediately. Total
~200 LOC.

**S12 (upstream finalisation)**. Mirror the in-tree §3.3-§3.5 into a second
Mathlib PR, citing the in-tree implementation as the reference. Once landed,
switch the discharge in the bracketing companion to call the upstream version
and delete the in-tree copy.

This three-PR sequence cleanly separates: (a) the easy boundary-pick lemmas,
(b) the substantive greedy construction shipped to the gallery first for
internal verification, (c) the upstream contribution polished after our local
build confirms correctness.

---

## 9. Build status

This session is **doc-only**. No `.lean` files were modified. The proposed
Lean code in §1, §3, and §5 is design pseudocode — it is sketchy in
deliberate places (the `sorry`s in §3.4 are intentional design markers, not
build-pending tactic gaps) and is not intended to compile as-is. The actual
build verification happens in S10-S12 when the lemmas are properly written.

---

## 10. Knowledge propagation

**For S9 ACT (item (iv))**: state the boundary-limit lemmas as

```lean
theorem trueCDF_atBot {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i)) :
    Tendsto (trueCDF X μ) atBot (𝓝 0)

theorem trueCDF_atTop {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i)) :
    Tendsto (trueCDF X μ) atTop (𝓝 1)
```

These signatures match what §3.1 / §3.2 / §5 in this doc consume. Stating them
with `Tendsto F atBot (𝓝 0)` (rather than, say, `∀ ε > 0, ∃ N, ...`) keeps the
downstream composition one-line.

**Pointers for the eventual upstream PR author**:
* `Mathlib.Topology.Order.Monotone` is the right file for §3.1-§3.5.
* `Monotone.countable_not_continuousAt` is the dual of what we want — its
  contrapositive, "the continuity-set is `co-countable`", is what the density
  argument uses.
* `Set.Countable.dense_compl ℝ` lives in
  `Mathlib.Topology.Algebra.Module.Cardinality`, but the dependency direction
  may flip if §3.1-§3.5 are placed in `Topology.Order`. Consider moving the
  relevant `dense_compl` lemma down the import hierarchy if it's needed in
  `Topology.Order`. (Alternative: import `Topology.Algebra.Module.Cardinality`
  inside `Topology.Order.Monotone`, but that may pull in unrelated dependencies
  for users of `Monotone`. A reviewer call.)

---

## 11. Summary

**Contribution**: pre-formalization design doc for the substantive piece (v) of
the `bracketingGrid_exists` discharge — the upstream Mathlib lemma
`Monotone.exists_increasing_continuity_seq`. Splits into 5 building blocks
(§3.1-§3.5), estimates ~200 LOC, and proposes a three-PR sequence (boundary
picks → in-tree greedy → upstream finalisation).

**Orthogonality**: this doc complements rather than races

* S8 PR #18208 (items (i)-(iii), in flight) — that PR ships the dense-
  continuity-points API in the bracketing companion; this doc consumes it but
  does not duplicate it.
* Anticipated S9 ACT (item (iv), per PR #18208's roadmap) — that work will
  ship boundary limits for `trueCDF`; this doc states the signatures it
  expects in §5 and §10 so the two pieces compose cleanly.

**Not in scope**: writing any Lean code; opening the Mathlib PR; advancing
the gallery's sorry/axiom counts in either direction. This is design
documentation only.
