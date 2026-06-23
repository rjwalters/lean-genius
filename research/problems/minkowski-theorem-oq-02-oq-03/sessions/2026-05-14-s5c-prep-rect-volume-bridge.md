# S5-c PREP — `dirichletSetN_volume` via `dirichletBoxN` rectangle volume

**Date.** 2026-05-14
**Researcher.** researcher-3
**Mode.** ANALYSIS-ONLY (no `.lean` edits, no `state.md` edits, no
JSON edits). Doc-only PREP appended as a new sessions/ file.
Conflict-free with the open S5-b ACT PR (#19046) and the open
STATE-SYNC PR (#18991).

**Predecessors.**

- S5-b ACT (PR #19046, OPEN, build verified 3058 jobs, 2026-05-14):
  ships `shearM_toLin'_apply_zero`, `shearM_toLin'_apply_succ`,
  `dirichletBoxN`, and the **preimage identity**
  `dirichletSetN_eq_shearM_preimage` (the Cassels parallelepiped is
  the preimage of `dirichletBoxN n Q` under `(shearM n α).toLin'`).
- S5-a ACT (MERGED): ships `shearM`, `shearM_lowerTriangular`, and
  `shearM_det = (-1)^n`.
- S5 PREP-2 (PR #18622, MERGED): bearer audit at the lake-pinned
  Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` —
  identified `Real.map_matrix_volume_pi_eq_smul_volume_pi` (needs
  `open Real`), `volume_pi_Ioo`, and the `[DecidableEq ι]`
  instance (free for `ι = Fin (n+1)`).

**This PREP.** With PR #19046's preimage identity available, the
remaining S5-c ACT — discharging `dirichletSetN_volume` —
collapses to a straight-line measure-pushforward chain. This PREP
provides the post-#19046-merge proof skeleton with file:line pins at
the pin SHA, accounting for the LOC drift PR #19046 introduces
(line 248 → ~333), and identifies one subtle `abs` plumbing that
S5 PREP-2 §6 / §9 left implicit.

This PREP does NOT discharge `dirichletSetN_volume`. It is a doc-only
audit ready for the S5-c ACT iteration once PR #19046 merges (or
applied via the mechanic-PR overlay pattern).

---

## §1. Mathlib bearer refresh at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All entries verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c27...`
and direct raw-fetch of `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
(669 lines at the pin).

| Lemma | Path | Line | Signature |
|---|---|---|---|
| `Real.volume_pi_Ioo` | `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` | **236** | `{a b : ι → ℝ} : volume (pi univ fun i => Ioo (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i)` |
| `Real.map_matrix_volume_pi_eq_smul_volume_pi` | `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` | **397** | `[DecidableEq ι] {M : Matrix ι ι ℝ} (hM : det M ≠ 0) : Measure.map (toLin' M) volume = ENNReal.ofReal (abs (det M)⁻¹) • volume` |
| `Fin.prod_univ_succ` | `Mathlib/Algebra/BigOperators/Fin.lean` | 76 | `(f : Fin (n+1) → M) : ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ` |
| `Finset.prod_const` | `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean` (re-export) | n/a | `∀ s : Finset α, (∀ x ∈ s, f x = c) → ∏ x ∈ s, f x = c ^ #s` (constant-product specialization) |
| `Fintype.card_fin` | `Mathlib/Data/Fintype/Card.lean` | re-export | `Fintype.card (Fin n) = n` |

**Verdict.** All lemmas needed by S5 PREP-2's §9 LOC table for the
S5-c block (lines 455–457: `h_meas_T`, `h_meas_rect`, `h_map`,
`h_rect_vol`, `dirichletSetN_volume` assembly = ~43 LOC) are present
at the pin with the signatures S5 PREP-2 §6 cited.

**One subtlety beyond S5 PREP-2.** `map_matrix_volume_pi_eq_smul_volume_pi`'s
RHS scalar is `ENNReal.ofReal (abs (det M)⁻¹)`, NOT `ENNReal.ofReal (abs (det M)⁻¹)`
literally with `det = (-1)^n` — we need `abs ((-1)^n) = 1`. Two
sub-cases by parity (`n` even vs odd) collapse via
`abs_neg_one_pow` + `abs_one`. S5 PREP-2 §6 ("`abs (det M)⁻¹` issue"
unmentioned) elided this; the S5-c ACT must close it explicitly.
Two `simp` strategies offered in §3 below.

---

## §2. Post-#19046-merge state of the parent file

PR #19046 adds 83 LOC at end-of-file (lines 251–331). Pre-merge
(`origin/main` HEAD `2afb1b79c0a`):

```
proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean: 248 LOC
- end namespace at line 248
- open APIs available: shearM (Part 5), shearM_lowerTriangular,
  shearM_det
```

Post-merge (per PR #19046's diff):

```
proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean: 331 LOC
- end namespace at line 331
- open APIs available: + shearM_toLin'_apply_zero (line ~258)
                       + shearM_toLin'_apply_succ (line ~273)
                       + dirichletBoxN (def, line ~290)
                       + dirichletSetN_eq_shearM_preimage (line ~302)
```

The S5-c ACT will append at line 331+1 (post-merge), inside the
existing `namespace MinkowskiTheoremOQ02OQ03`. PR #19046 leaves
`open Real` NOT yet opened (per the file's current convention — only
`open` at the top of file). The S5-c ACT must add `open Real` (or
inline `Real.` prefix) at the namespace level to access
`map_matrix_volume_pi_eq_smul_volume_pi`.

**Cross-check** (sanity): the parent OQ-01 file
`proofs/Proofs/MinkowskiTheoremOQ02OQ01.lean` line 32 has
`open MeasureTheory Set Real`. OQ02OQ03 currently does NOT
(searched at HEAD); it has `open Set` only (line ~36 of S2 ACT). The
S5-c ACT can either add `open Real` at the namespace top OR
inline-prefix the single use site.

---

## §3. S5-c ACT proof skeleton (NOT shipped — for S5-c ACT reference)

Building on PR #19046's `dirichletSetN_eq_shearM_preimage` and
`dirichletBoxN` def, plus the merged `shearM_det = (-1)^n` from S5-a.

### Step A — `dirichletBoxN` is a measurable rectangle

```lean
/-- The dirichletBoxN is a Set.pi of open intervals over Fin (n+1).
    Useful as a `MeasurableSet` witness and the base for `volume_pi_Ioo`. -/
theorem dirichletBoxN_measurable (n : ℕ) (Q : ℕ) :
    MeasurableSet (dirichletBoxN n Q) := by
  unfold dirichletBoxN
  exact MeasurableSet.univ_pi (fun j => measurableSet_Ioo)
```

LOC: ~3. Bearer: `MeasurableSet.univ_pi` + `measurableSet_Ioo` (both
in `Mathlib.MeasureTheory.Constructions.Pi`). No risk.

### Step B — closed-form `volume (dirichletBoxN n Q)`

```lean
/-- Closed-form volume of the dirichletBoxN rectangle: `2(Qⁿ+1) · (2/Q)ⁿ`
    in product form. -/
theorem dirichletBoxN_volume (n : ℕ) (Q : ℕ) (hQ : 1 ≤ Q) :
    volume (dirichletBoxN n Q) =
      ENNReal.ofReal (2 * ((Q : ℝ)^n + 1)) *
      ∏ _ : Fin n, ENNReal.ofReal (2 / (Q : ℝ)) := by
  unfold dirichletBoxN
  rw [Real.volume_pi_Ioo]   -- ∏ ENNReal.ofReal (b j - a j)
  rw [Fin.prod_univ_succ]   -- factor off j = 0
  congr 1
  · -- j = 0 case: ENNReal.ofReal ((Qⁿ + 1) - (-(Qⁿ + 1))) = ENNReal.ofReal (2(Qⁿ+1))
    simp [Fin.cases_zero]
    ring_nf  -- close (Qⁿ+1) - (-(Qⁿ+1)) = 2(Qⁿ+1)
  · -- j = succ k case: ENNReal.ofReal ((1/Q) - (-(1/Q))) = ENNReal.ofReal (2/Q)
    refine Finset.prod_congr rfl ?_
    intro k _
    simp [Fin.cases_succ]
    ring_nf
```

LOC: ~15. Bearer: `Real.volume_pi_Ioo` (verified §1 line 236),
`Fin.prod_univ_succ`, `Fin.cases_zero` / `Fin.cases_succ` (all
verified MERGED by S5 PREP-2 §8). The two `ring_nf` steps close
arithmetic over ℝ; risk-free.

**Hazard.** `Fin.cases_zero` / `Fin.cases_succ` in `dirichletBoxN`'s
def are wrapped in `Fin.cases _ (fun _ : Fin n => ...) j` so the simp
unfolding may need `Fin.cases` explicit unfold. If the inline `simp
[Fin.cases_zero]` doesn't reduce, fallback is
`show Set.Ioo (-((Q:ℝ)^n + 1)) ((Q:ℝ)^n + 1) ∋ ...; rfl` for the
zero coordinate and similarly for `succ k`.

### Step C — pushforward chain via `map_matrix_volume_pi_eq_smul_volume_pi`

```lean
/-- **Volume of the Dirichlet parallelepiped** via the shear pushforward:
    `volume (dirichletSetN n α Q) = volume (dirichletBoxN n Q)` because
    `|det (shearM n α)| = 1`. -/
theorem dirichletSetN_volume (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    volume (dirichletSetN n α Q) =
      ENNReal.ofReal (2 * ((Q : ℝ)^n + 1)) *
      ∏ _ : Fin n, ENNReal.ofReal (2 / (Q : ℝ)) := by
  -- Step 1: rewrite the parallelepiped as a preimage (PR #19046).
  rw [dirichletSetN_eq_shearM_preimage]
  -- Step 2: apply the measure-pushforward identity in REVERSE.
  --   Measure.map (toLin' shearM) volume = ENNReal.ofReal (|det shearM|⁻¹) • volume
  --   ⟹ volume (preimage S) = (|det shearM|⁻¹) • volume S, modulo abs/inv plumbing.
  -- Use the identity volume (T ⁻¹' S) = (Measure.map T volume) S after measurability.
  have hshear_meas : Measurable ((shearM n α).toLin') := by
    apply Continuous.measurable
    exact LinearMap.continuous_on_pi _
  have hbox_meas : MeasurableSet (dirichletBoxN n Q) := dirichletBoxN_measurable n Q
  have hdet_ne : Matrix.det (shearM n α) ≠ 0 := by
    rw [shearM_det]
    exact pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)
  -- volume (T ⁻¹' B) = (Measure.map T volume) B
  rw [show (volume : Measure (Fin (n+1) → ℝ)) ((shearM n α).toLin' ⁻¹' dirichletBoxN n Q)
        = (Measure.map ((shearM n α).toLin') volume) (dirichletBoxN n Q) from
      (Measure.map_apply hshear_meas hbox_meas).symm]
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet_ne]
  -- |det shearM|⁻¹ = 1 because det = (-1)^n so |det| = 1
  rw [shearM_det]
  rw [show |((-1 : ℝ))^n|⁻¹ = 1 from by
    rw [abs_pow, abs_neg, abs_one, one_pow]; simp]
  rw [ENNReal.ofReal_one]
  rw [one_smul]
  -- Now goal: volume (dirichletBoxN n Q) = explicit form
  exact dirichletBoxN_volume n Q hQ
```

LOC: ~25 (including the `abs ((-1)^n) = 1` plumbing).

**Bearer audit (Step C):**

- `LinearMap.continuous_on_pi`: at `Mathlib/Topology/Algebra/Module/LinearMap.lean` (re-export). Verify name; might be `LinearMap.continuous_pi`.
- `Continuous.measurable`: standard, in `Mathlib.MeasureTheory.MeasurableSpace.Basic`.
- `Measure.map_apply`: at `Mathlib/MeasureTheory/Measure/MeasureSpace.lean`. Signature: `(hf : Measurable f) (hs : MeasurableSet s) : Measure.map f μ s = μ (f ⁻¹' s)`.
- `Real.map_matrix_volume_pi_eq_smul_volume_pi`: §1 verified at line 397.
- `abs_pow`, `abs_neg`, `abs_one`, `one_pow`: all in `Mathlib.Algebra.Order.AbsoluteValue.Basic` or `Mathlib.Algebra.Order.Ring.Abs`. Standard.
- `ENNReal.ofReal_one`: at `Mathlib/Data/ENNReal/Basic.lean:283` (S2g PREP §10 verified).
- `one_smul`: standard `Mathlib.Algebra.Group.Action.Defs`.

### Estimated total S5-c LOC

| Step | LOC |
|---|---|
| Step A — `dirichletBoxN_measurable` | 3 |
| Step B — `dirichletBoxN_volume` (closed form) | 15 |
| Step C — `dirichletSetN_volume` via pushforward | 25 |
| Imports / opens (`open Real` if not present) | 1 |
| Inline docstrings | ~5 |
| **Total** | **~49 LOC** |

Compared to S5 PREP-2 §9's S5-c block (`h_meas_T`, `h_meas_rect`,
`h_map`, `h_rect_vol`, `dirichletSetN_volume` assembly = 10 + 25 + 8
= ~43 LOC), the slight overshoot (~49 vs ~43) is the `abs ((-1)^n) = 1`
plumbing that S5 PREP-2 §6 left implicit (~6 LOC).

---

## §4. Hazards (S5-c ACT to verify on Docker)

1. **`open Real` placement.** The file currently has `open Set`
   only. The S5-c ACT either prepends `open Real` to the namespace
   header OR inline-prefixes `Real.volume_pi_Ioo` and
   `Real.map_matrix_volume_pi_eq_smul_volume_pi`. Inline prefix is
   the lower-risk choice (no other simp lemmas affected).

2. **`LinearMap.continuous_on_pi` name.** Mathlib v4.26.0 may have
   renamed this. Fallback path: use `LinearMap.continuous_pi`
   (singular `pi`) or rely on `Matrix.toLin'` having a
   `Continuous` instance directly. If neither works, build the
   continuity manually via `Continuous.matvec` (component-wise
   continuity).

3. **`Measure.map_apply` orientation.** The signature is
   `Measure.map f μ s = μ (f ⁻¹' s)`; the skeleton uses it in the
   `.symm` form `volume (f ⁻¹' s) = Measure.map f volume s`. This
   is straightforward but the `rw [show ... from ...]` step may need
   parenthesization tweaks to elaborate cleanly.

4. **`abs ((-1)^n) = 1` for `n` even or odd.** The shipped form
   uses `abs_pow + abs_neg + abs_one + one_pow + simp`. At v4.26.0,
   `abs_pow` may require `abs_pow_eq` or similar variant. Fallback:
   case-split on `n.even` via `Nat.even_or_odd` and close each case
   by `decide`-on-the-parity-bit + `abs_one` + `abs_neg`.

5. **`Fin.cases` in `dirichletBoxN` def.** PR #19046's def uses
   `Fin.cases (-(...)) (fun _ : Fin n => -(1/Q)) j`. The `simp
   [Fin.cases_zero]` / `simp [Fin.cases_succ]` should reduce
   immediately given `Fin.cases_zero` / `Fin.cases_succ` are `@[simp]`
   (S5 PREP-2 §8 verified). If `simp` doesn't close, fallback to
   explicit `show` + `rfl`.

6. **`hQ : 1 ≤ Q` propagation.** The closed-form bound uses `1 ≤ Q`
   indirectly to ensure `2/Q > 0` and `Qⁿ + 1 > 0`. The S5-c proof
   skeleton above does NOT use `hQ` directly; the `pow_ne_zero` for
   `det` is parity-only. `hQ` is needed downstream by
   `dirichletSetN_volume_gt_threshold` (S6 ACT, line 458 of S5
   PREP-2 §9 table). The S5-c statement could omit `hQ` if the
   closed-form is stated in `ENNReal` form (which never goes
   negative). Recommended: keep `hQ` in the statement for caller
   ergonomics.

---

## §5. Cross-PR coordination — open PRs at PREP-time

| PR | Title | Files touched | Conflict with this PR? |
|---|---|---|---|
| #18991 | STATE-SYNC — refresh after #18975 S5-a ACT (doc-only) | `state.md`, JSON tracker | **No** — doesn't touch sessions/ |
| #19046 | S5-b ACT — shearM linear-map components + preimage identity | `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` | **No** — different new sessions/ file |
| (this PR) | S5-c PREP — rect volume bridge (doc-only) | `sessions/2026-05-14-s5c-prep-rect-volume-bridge.md` (NEW) | n/a |

This PR adds ONLY a new sessions/ file with a different filename
than any in-flight session file. Zero conflict surface. Either PR
can merge first.

---

## §6. Sequencing recommendations

**Option A (preferred):** Wait for PR #19046 to merge, then open S5-c
ACT branched from `origin/main`. Reason: PR #19046 introduces 83
LOC of new APIs that S5-c builds directly on. Branching post-merge
gives a clean compile graph without overlay.

**Option B (if S5-c is time-sensitive):** Use the mechanic-PR overlay
pattern (`feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`)
to validate S5-c against PR #19046's API before that PR merges.
Branch from `origin/main`, `gh pr diff 19046 --repo rjwalters/lean-genius
> /tmp/19046.patch`, `git apply /tmp/19046.patch`, append S5-c work,
Docker-build, then `git checkout origin/main -- proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`
to revert the overlay before commit. Final S5-c PR explicitly notes
"depends on PR #19046 merging first."

Recommendation: Option A, since PR #19046 was opened 2026-05-14 and
appears stable (build verified, 3058 jobs). It will likely merge
within a session-day. Option B is the fallback if PR #19046 stalls.

---

## §7. Conflict-free scope statement (this PR)

This PR is doc-only and conflict-free with every open PR:

* **Adds**: 1 new file —
  `research/problems/minkowski-theorem-oq-02-oq-03/sessions/2026-05-14-s5c-prep-rect-volume-bridge.md`
  (this file).
* **Does NOT touch**: `state.md` (PR #18991 owns that), `problem.md`,
  `knowledge.md`, the JSON tracker, the gallery `meta.json`, or any
  `proofs/*.lean` file (PR #19046 owns the parent .lean).
* **Does NOT discharge** `dirichletSetN_volume`. That is queued for
  S5-c ACT in a future iteration, post-#19046-merge per §6 Option A.
* **Does NOT touch** the S5 PREP-2 (PR #18622, MERGED) bearer audit;
  this PREP supplements §6 / §9 with the explicit `abs ((-1)^n) = 1`
  plumbing missing from S5 PREP-2 plus a concrete skeleton built on
  PR #19046's preimage identity.

---

## §8. Decision Log

* **2026-05-14 S5-c PREP (researcher-3)**: Wrote a doc-only PREP
  rather than attempting the S5-c ACT directly. Reason: PR #19046
  (S5-b ACT) is OPEN with the preimage identity that S5-c builds
  on; branching the S5-c ACT now would either require waiting (no
  Docker iteration possible until #19046 merges) or the
  mechanic-overlay pattern (extra orchestration cost). Per the
  cross-PR coordination memory pattern, the doc-only PREP is the
  conflict-free, value-additive option.

* **2026-05-14 S5-c PREP (researcher-3)**: Identified the
  `abs ((-1)^n) = 1` plumbing (~6 LOC) as missing from S5 PREP-2's
  §9 LOC table. Reason: S5 PREP-2 §6 cited
  `Real.map_matrix_volume_pi_eq_smul_volume_pi` but did not unfold
  the `|det|⁻¹ = 1` step that the slug's specific shear-determinant
  `(-1)^n` requires. The S5-c estimate sharpens from S5 PREP-2's
  ~43 LOC to ~49 LOC after this addition.

* **2026-05-14 S5-c PREP (researcher-3)**: Recommend Option A (wait
  for PR #19046 merge) over Option B (mechanic-overlay). Reason:
  PR #19046 is build-verified and recently created; merge wait is
  reasonable. Option B is the fallback if PR #19046 stalls beyond
  a session-day.
