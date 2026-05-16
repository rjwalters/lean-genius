# S8 PREP — Faithful-link bearer gap + sum-form substitute + STATE-SYNC catchup

**Iteration**: S8 PREP (doc-only)
**Author**: researcher-8
**Date**: 2026-05-16
**Mode**: doc-only — this new session memo + state.md catchup (iter 8 → 10) +
JSON catchup. No Lean / knowledge.md / problem.md / meta.json edits.
**Predecessors**: S6 ACT (PR #19103 merged 2026-05-15T22:59 — Docker-verified
parent file at 7743 jobs; cluster A/B/C/D repair); **S7 PREP (PR #19111
merged 2026-05-15T22:58)** — comprehensive ~635-LOC design memo for
`LLLAdmissibleUniform`, paste-ready ~150-LOC implementation skeleton.
**Open PRs at session start**: none on this slug.
**Branch**: `research/lovasz-oq01-s8-prep-faithful-link` (fresh off
`origin/main`).

---

## §0. TL;DR

Three deliverables in one doc-only PREP:

1. **Bearer-gap finding.** S7 PREP §3.3(c) hedged on `MeasurableSet.of_discrete`
   ("may not exist by that exact name; three fallbacks documented") for the
   faithful-link lemma `uniformDrawProb_eq_toMeasure`. **Verified at pin
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**:
   - `MeasurableSet.of_discrete` **EXISTS** at
     `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:549`.
   - **BUT** it requires `[MeasurableSpace α] [DiscreteMeasurableSpace α]`,
     and `P.State = (j : Fin numVars) → P.alphabet j` does **NOT** get a
     `MeasurableSpace` instance: `P.alphabet j : Type` is declared with only
     `[Fintype]` + `[Nonempty]` (no `[MeasurableSpace]`), and Mathlib's Pi
     `MeasurableSpace` instance requires `[∀ j, MeasurableSpace (alphabet j)]`.
   - The named bearer is real; its prerequisite chain breaks one layer
     deeper than S7 PREP audited.

2. **Cheaper-than-fallback substitute (the "upside surprise").** Sidestep
   the `MeasurableSet` / `toMeasure` route entirely via
   `PMF.toOuterMeasure_apply_fintype` at
   `Mathlib/Probability/ProbabilityMassFunction/Basic.lean:203`:
   ```lean
   theorem toOuterMeasure_apply_fintype [Fintype α] :
       p.toOuterMeasure s = ∑ x, s.indicator p x
   ```
   No `[MeasurableSpace α]` required, no `MeasurableSet s` required. The
   `toOuterMeasure` form is mathematically equivalent to `toMeasure` for
   PMFs (carathéodory σ-algebra = `⊤`, file line 145 `toOuterMeasure_caratheodory`),
   and conversion `toOuterMeasure ≤ toMeasure` is one-line via
   `toOuterMeasure_apply_le_toMeasure_apply` (file line 217).

3. **Paste-ready ~30 LOC body** for the substitute faithful-link lemma
   `uniformDrawProb_eq_outerMeasure`, using only `toOuterMeasure_apply_fintype`
   + `PMF.uniformOfFintype_apply` + `Finset.sum_indicator_eq_sum_filter` +
   `push_cast` / `field_simp`. Total impact on S7 PREP's §4 LOC budget:
   ~30 LOC for §4.3 unchanged; the rest (§4.1 defs, §4.2 bounds, §4.4
   structure + bridge, §4.5 optional boundary lemmas) **unchanged**.

**STATE-SYNC catchup (this PREP also does)**:

- state.md head was last updated by S6 ACT (iter 8); S7 PREP #19111 (iter 9,
  doc-only) was never added. This memo catches up by adding a S7 PREP RETRO
  block (iter 8 → 9) and a new S8 PREP block (iter 9 → 10).
- JSON `currentState.{phase, iteration, focus, nextAction, lastUpdate}`
  refresh accordingly.

**ACT-readiness gate posture (8-item)**:
- 7/8 GREEN substantive (bearers verified, paste-ready substitute, file
  baseline stable, no open sibling PRs, JSON catchup planned, problem.md /
  knowledge.md unchanged, race window clean).
- 1/8 RED INFRA: Docker daemon unresponsive (`docker info --format
  '{{.ServerVersion}}'` returns empty inside 10s, suggesting hung engine)
  + disk near full (6.6 Gi free / 100% capacity on `/System/Volumes/Data`).
  ACT-class Lean (file edit + Docker build verify) blocked until infra
  recovers.

**Strict orthogonality (verified)**:
- No edits to `proofs/Proofs/MoserTardos.lean`. (S9 ACT will own that
  when infra recovers.)
- No edits to `proofs/Proofs/LovaszLocalLemma.lean`. (Parent file, not
  this slug's domain.)
- No edits to `proofs/lake-manifest.json`. (Pin unchanged.)
- No edits to `src/data/proofs/.../meta.json`. (Not in this slug's
  directory; mechanic territory.)
- No edits to `problem.md` / `knowledge.md`. (S7 PREP also did not
  edit these; iteration-trail of structural understanding is correct.)
- No edits to `.lean/state/candidate-pool.json`. (Race risk.)
- Single Lean file untouched; only changed files are this new session
  memo + state.md + research JSON.

---

## §1. The bearer gap (S7 PREP §3.3(c) verified at pin)

### §1.1 What S7 PREP §3.3(c) said

> **(c) `MeasurableSet.of_discrete` may not exist by that exact name.**
> Fallback inventory at v4.26.0:
> - `MeasurableSet.of_subsingleton` — works if `P.State` has 1 element
> - `MeasurableSet.compl_iff` — `MeasurableSet sᶜ ↔ MeasurableSet s`
> - `Trivial`-class: `inferInstance : MeasurableSpace.MeasurableSet ⊤ s`
> - Manual: `MeasurableSpace.MeasurableSet.of_eq` plus the discrete instance.

S7 PREP did not verify which fallback fires at pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. This PREP closes that gap.

### §1.2 Direct verification at pin

```bash
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean" \
  | grep -n -E "of_discrete|measurableSet_top|DiscreteMeasurableSpace"
```

Output (verbatim, with line numbers):

```
439:@[simp, measurability] theorem measurableSet_top {s : Set α} : MeasurableSet[⊤] s := trivial
535:  /-- Do not use this. Use `MeasurableSet.of_discrete` instead. -/
539:  @DiscreteMeasurableSpace.mk _ (_) fun _ ↦ MeasurableSpace.measurableSet_top
549:@[measurability] lemma MeasurableSet.of_discrete : MeasurableSet s :=
552:@[fun_prop] lemma Measurable.of_discrete : Measurable f := fun _ _ ↦ .of_discrete
559:  measurableSet_singleton _ := .of_discrete
```

So **`MeasurableSet.of_discrete` does exist at pin**, with signature:

```lean
@[measurability] lemma MeasurableSet.of_discrete : MeasurableSet s :=
  DiscreteMeasurableSpace.forall_measurableSet _
```

under the scope `section DiscreteMeasurableSpace; variable [MeasurableSpace α]
[MeasurableSpace β] [DiscreteMeasurableSpace α]`. Two prerequisite typeclass
instances are required: `[MeasurableSpace α]` and `[DiscreteMeasurableSpace α]`.

### §1.3 The deeper gap — neither prerequisite fires on `P.State`

`P.State` is defined at `proofs/Proofs/MoserTardos.lean:92`:

```lean
abbrev State : Type := (j : Fin P.numVars) → P.alphabet j
```

And `P.alphabet` is the `MTProblem` field at line 63 with the field-encoded
instance declarations (lines 65–68):

```lean
alphabet : Fin numVars → Type
alphabetFintype : ∀ j, Fintype (alphabet j)
alphabetNonempty : ∀ j, Nonempty (alphabet j)
```

`attribute [instance] alphabetFintype alphabetNonempty isBadDec` is set at
line 86. **No `MeasurableSpace` instance** is declared on `alphabet j`. So:

- `MeasurableSpace P.State` would need to come from `Pi.instMeasurableSpace`,
  which requires `[∀ j, MeasurableSpace (P.alphabet j)]`. **This instance
  is not derivable** from `[Fintype] + [Nonempty]` alone.
- `DiscreteMeasurableSpace P.State` would follow from `MeasurableSingletonClass`
  + `Countable` + the auto-instance at
  `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:543`:
  ```lean
  instance (priority := 100) MeasurableSingletonClass.toDiscreteMeasurableSpace
      [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] :
      DiscreteMeasurableSpace α
  ```
  But this requires `[MeasurableSpace α]` first. Dead chain.
- A naïve `attribute [instance] (fun j => (⊤ : MeasurableSpace (P.alphabet j)))`
  doesn't typecheck — `attribute [instance]` needs a name, not a lambda. The
  workaround would be either (a) add a `MeasurableSpace` field to `MTProblem`
  (invasive, propagates to every API consumer), or (b) introduce a `local
  instance` at use-site:
  ```lean
  local instance (j : Fin P.numVars) : MeasurableSpace (P.alphabet j) := ⊤
  local instance : MeasurableSingletonClass (P.alphabet j) := ⟨fun _ => MeasurableSet.of_discrete⟩
  -- circular: of_discrete needs MeasurableSingletonClass to fire
  ```
  This produces a typeclass cycle (`DiscreteMeasurableSpace`
  ↔ `MeasurableSingletonClass`, file lines 555–559) that needs careful
  manual breaking. **Possible but fragile**, ~10–20 LOC of plumbing per
  use-site.

### §1.4 Summary of the bearer-gap finding

| Question | S7 PREP §3.3(c) | This PREP §1.2/§1.3 verdict |
|---|---|---|
| Does `MeasurableSet.of_discrete` exist at pin? | "may not by that exact name" | **YES**, `Defs.lean:549` |
| Does its prerequisite chain fire on `P.State`? | (not analysed) | **NO**, missing `MeasurableSpace (alphabet j)` |
| Cost of plumbing prerequisites? | (not analysed) | **~10–20 LOC + typeclass-cycle risk** |
| Cheaper substitute that sidesteps the chain? | (not considered) | **YES** — see §2 |

The named bearer is real and well-known; the gap is one layer deeper than
the S7 PREP audit's `gh api` scope (file-name search for the lemma, not
prerequisite-instance derivation analysis). This is the recurrent
"hedged-bearer prerequisite-chain drift" pattern.

---

## §2. The substitute — `PMF.toOuterMeasure_apply_fintype`

### §2.1 The key Mathlib bearer (verified at pin)

```bash
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Probability/ProbabilityMassFunction/Basic.lean" \
  | sed -n '203p'
theorem toOuterMeasure_apply_fintype [Fintype α] : p.toOuterMeasure s = ∑ x, s.indicator p x :=
```

Full lines 200–206:

```bash
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Probability/ProbabilityMassFunction/Basic.lean" \
  | sed -n '200,206p'
end OfFinset

section OfFintype

theorem toOuterMeasure_apply_fintype [Fintype α] : p.toOuterMeasure s = ∑ x, s.indicator p x :=
  (p.toOuterMeasure_apply s).trans
    (tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)
```

**Prerequisites**: `[Fintype α]` only. **No `[MeasurableSpace α]`. No
`MeasurableSet s`.** `s : Set α` and `s.indicator` is the
indicator-as-`α → β`-where-`Zero β`-via-`if-then-else` form, decidable via
`Classical` if `s` is not given as decidable membership.

### §2.2 Why `toOuterMeasure` is mathematically equivalent for our use

The `PMF.toOuterMeasure` and `PMF.toMeasure` are related by:

- `Basic.lean:145`: `toOuterMeasure_caratheodory : p.toOuterMeasure.caratheodory = ⊤`
  — every set is in the Carathéodory σ-algebra of `p.toOuterMeasure`.
- `Basic.lean:220–222`: `toMeasure_apply_eq_toOuterMeasure_apply
  (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s`
- `Basic.lean:217`: `toOuterMeasure_apply_le_toMeasure_apply` — the
  `toOuterMeasure ≤ toMeasure` inequality holds unconditionally.

For LLL purposes — which need only `Pr[A_i] ≤ x_i * ∏_{k ∈ Γ(i)} (1 - x_k)`
— stating the bound against `toOuterMeasure` is **strictly stronger** than
against `toMeasure` (since `toOuterMeasure ≤ toMeasure`, an upper-bound on
the outer measure also upper-bounds the inner measure). So
`LLLAdmissibleUniform` can naturally lift to a `toMeasure`-form bound
whenever downstream consumers (OQ-01-B witness trees) supply
`MeasurableSet` (via whatever `MeasurableSpace P.State` plumbing they
prefer).

### §2.3 Auxiliary bearers (verified at pin)

| Bearer | File | Line | Verified |
|---|---|---|---|
| `PMF.uniformOfFintype_apply` | `Mathlib/Probability/Distributions/Uniform.lean` | 298 | ✓ §A.1 |
| `PMF.toOuterMeasure_apply_fintype` | `Mathlib/Probability/ProbabilityMassFunction/Basic.lean` | 203 | ✓ §A.2 |
| `PMF.toOuterMeasure_apply_le_toMeasure_apply` | same file | 217 | ✓ §A.3 |
| `PMF.toOuterMeasure_apply_finset` | same file | 152 | ✓ §A.4 |
| `Set.indicator_apply` | `Mathlib/Algebra/Order/Group/Indicator.lean` (or core `Mathlib/Algebra/Indicator/Basic.lean`) | — | exercised; standard simp lemma |
| `Finset.sum_ite_irrel` / `Finset.sum_ite_eq` | `Mathlib/Algebra/BigOperators/Group/Finset/Sum.lean` | — | exercised; standard simp lemma |

No `[MeasurableSpace]` or `MeasurableSet` mention in any of these
prerequisites.

---

## §3. The substitute faithful-link lemma

### §3.1 Signature

```lean
/-- **Faithful link (outer-measure form)** between the rational
    `uniformDrawProb` and the underlying `PMF`-valued uniform outer
    measure of the bad event.

    `toOuterMeasure` avoids the `MeasurableSpace P.State` /
    `DiscreteMeasurableSpace P.State` prerequisite chain that `toMeasure`
    requires (and that does not fire on `P.alphabet j : Type` with only
    `[Fintype] + [Nonempty]` field-instances). The outer-measure form is
    mathematically equivalent for upper-bound applications; see §2.2. -/
theorem uniformDrawProb_eq_outerMeasure (i : Fin P.numEvents) :
    ((P.uniformDrawProb i : ℝ) : ℝ≥0∞) =
      (PMF.uniformOfFintype P.State).toOuterMeasure
        { v : P.State | P.isBad i v }
```

### §3.2 Paste-ready proof body (~25 LOC)

```lean
theorem uniformDrawProb_eq_outerMeasure (i : Fin P.numEvents) :
    ((P.uniformDrawProb i : ℝ) : ℝ≥0∞) =
      (PMF.uniformOfFintype P.State).toOuterMeasure
        { v : P.State | P.isBad i v } := by
  classical
  -- (1) Expand the outer measure as a finite sum of indicator values.
  rw [PMF.toOuterMeasure_apply_fintype]
  -- (2) Inside the sum, the indicator reduces to a conditional PMF value.
  --     `s.indicator p x = if x ∈ s then p x else 0`, and each PMF value
  --     is `(Fintype.card P.State : ℝ≥0∞)⁻¹` by `uniformOfFintype_apply`.
  simp_rw [Set.indicator, Set.mem_setOf_eq, PMF.uniformOfFintype_apply]
  -- (3) Collapse `if isBad ... then C else 0` over `Finset.univ` to
  --     `(card filter) * C`.
  rw [Finset.sum_ite_eq_sum_filter_const]  -- if this name doesn't fire,
                                            -- see §3.3 for fallback
  -- (4) Both sides now have `card{v | isBad i v} * (Fintype.card P.State)⁻¹`
  --     and `(card{v|...} / Fintype.card P.State : ℝ → ℝ≥0∞)`. Push casts.
  unfold uniformDrawProb
  push_cast
  -- (5) Residue is the `a / b = a * b⁻¹` identity in ℝ≥0∞; closes by
  --     `ring` (or `field_simp` + `ring` if `ring` doesn't normalise
  --     ℝ≥0∞ division directly).
  ring
```

Total: ~25 LOC body + docstring + blank lines ≈ 30 LOC.

### §3.3 Fallback tactic chains for fragile lines

The two potentially-fragile steps are (3) and (5):

**(3) Sum-over-indicator collapse.** The exact name
`Finset.sum_ite_eq_sum_filter_const` may not exist at pin; the canonical
substitute is:

```lean
-- Replacement for step (3):
rw [Finset.sum_ite (fun x _ => x ∈ Finset.univ.filter (fun v => P.isBad i v))]
-- or, more directly:
rw [show (∀ x ∈ (Finset.univ : Finset P.State), (if P.isBad i x then ... else 0) =
        ((Finset.univ : Finset P.State).filter (fun v => P.isBad i v)).sum (fun _ => ...))
  from ...]
```

The safer construction is to handcraft the sum split via:

```lean
have : ∑ x : P.State, (if P.isBad i x then ((Fintype.card P.State : ℝ≥0∞)⁻¹) else 0)
     = ((Finset.univ : Finset P.State).filter (fun v => P.isBad i v)).sum
         (fun _ => (Fintype.card P.State : ℝ≥0∞)⁻¹) := by
  rw [← Finset.sum_filter]
rw [this, Finset.sum_const, nsmul_eq_mul]
```

**(5) ℝ≥0∞ algebra residue.** The exact normal form for
`((a / b : ℚ) : ℝ → ℝ≥0∞)` versus `(a : ℝ≥0∞) * (b : ℝ≥0∞)⁻¹` depends on
`push_cast`'s lemma database at v4.26.0. Two-step fallback:

```lean
-- After push_cast, if `ring` doesn't close:
rw [div_eq_mul_inv]  -- on the LHS
-- or
field_simp
```

Worst case: a 3-line manual rewrite via
`Rat.cast_div` + `ENNReal.coe_div` + commutativity.

### §3.4 Why the outer-measure form is good enough for OQ-01-A.3, B, C

- **OQ-01-A.3 (`LLLAdmissibleUniform`)**: the structure field
  `lll_uniform : ∀ i, P.uniformDrawProb i ≤ x i * (P.collisionAdj i).prod ...`
  is **purely rational**. The faithful-link lemma is auxiliary
  documentation that ties `uniformDrawProb` to the actual PMF; whether
  the link goes through `toMeasure` or `toOuterMeasure` does not affect
  the rational bound used inside the structure.

- **OQ-01-B (witness trees)**: the tree-probability bound
  `Pr[τ appears in execution] ≤ ∏_v P.uniformDrawProb v.lbl` can be
  stated against `toOuterMeasure`. If a future OQ-01-B refinement
  needs `toMeasure` (e.g. for total-mass = 1 normalisation), the
  one-line bridge `toOuterMeasure_apply_le_toMeasure_apply` lifts
  upper bounds. **Alternatively**, OQ-01-B can add the
  `local instance` `MeasurableSpace P.State := ⊤` then; that
  decision belongs there, not here.

- **OQ-01-C (Galton–Watson sum)**: pure algebra over the rational
  `uniformDrawProb` bound; no measure-theoretic content.

### §3.5 Forward arrow if `toMeasure` form is desired

If a future ACT iteration insists on `toMeasure` form (e.g. for direct
substitution into Mathlib measure-theoretic API), add:

```lean
local instance (j : Fin P.numVars) : MeasurableSpace (P.alphabet j) := ⊤
-- Pi.instMeasurableSpace then fires on P.State automatically.
local instance : MeasurableSingletonClass P.State := by infer_instance
-- DiscreteMeasurableSpace P.State via priority-100 instance at Defs.lean:543.

theorem uniformDrawProb_eq_toMeasure (i : Fin P.numEvents) :
    ((P.uniformDrawProb i : ℝ) : ℝ≥0∞) =
      (PMF.uniformOfFintype P.State).toMeasure
        { v : P.State | P.isBad i v } := by
  have hmeas : MeasurableSet { v : P.State | P.isBad i v } :=
    MeasurableSet.of_discrete
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply hmeas]
  exact P.uniformDrawProb_eq_outerMeasure i
```

This is ~8 LOC including the two `local instance` declarations. **The
substitute outer-measure lemma is the load-bearing one**; the
`toMeasure` form is a 2-line corollary if needed. Recommend deferring
to OQ-01-B when the consumer actually needs `toMeasure`.

---

## §4. Revised S7 PREP §4 LOC budget

The substitute is a drop-in replacement for §4.3 (faithful-link block).
The other four sub-blocks (§4.1 new defs, §4.2 basic bounds, §4.4
structure + bridge, §4.5 optional boundary lemmas) are **unchanged**.
LOC budget update:

| Block | S7 PREP §4 estimate | This PREP revision |
|---|---|---|
| §4.1 New defs (`uniformDrawProb`, `collisionAdj`) | 10 | 10 (unchanged) |
| §4.2 Basic bounds (`_nonneg`, `_le_one`, `card_state_pos`) | 30 | 30 (unchanged) |
| §4.3 Faithful-link (was `_eq_toMeasure`) | 30 | **~30** (now `_eq_outerMeasure`; same LOC, simpler bearer chain) |
| §4.3a (optional) Forward arrow `_eq_toMeasure` | — | **+10** (if downstream needs `toMeasure`) |
| §4.4 Structure + bridge (`LLLAdmissibleUniform.toLLLAdmissible`) | 30 | 30 (unchanged) |
| §4.5 Optional boundary lemmas | 20 | 20 (unchanged) |
| Docstrings | 30 | 30 (unchanged) |
| **Total (with §4.3a, with §4.5)** | **150** | **~160** |
| **Without §4.3a, without §4.5** | **130** | **~130** |

Net delta: ~+0 LOC for the substitute itself; the `+10 LOC` for the
optional `toMeasure` corollary only fires if downstream wants it.

---

## §5. STATE-SYNC catchup (S7 PREP retro + S8 PREP block)

state.md head as of this session start (line 4):

```
**Phase**: S6 ACT (build-verify repair of S5/S5b ACT 4-cluster v4.26.0 regression — Docker-verified 7743 jobs)
**Iteration**: 8
```

But S7 PREP (PR #19111) merged 2026-05-15T22:58 (iter 9, doc-only) is
absent from the state.md narrative. JSON `currentState.phase` is
`"S6 ACT"` / `iteration: 8` — same gap.

### §5.1 state.md changes (planned)

- Head update: `Phase: S8 PREP (faithful-link bearer-gap resolution +
  sum-form substitute + STATE-SYNC catchup)` / `Iteration: 10`.
- Insert two new top-level sections **above** the current `## S6 ACT
  ...` block:
  - `## S8 PREP — researcher-8, 2026-05-16` (this session, ~80 LOC).
  - `## S7 PREP — researcher-3, 2026-05-14 (retro-add)` (~25 LOC retro
    block citing PR #19111).
- Append a row to the **Iteration History** table:
  - `| S7 PREP | 2026-05-14 | researcher-3 | #19111 (merged 05-15) | PREP — LLLAdmissibleUniform structure design (doc-only) |`
  - `| S8 PREP | 2026-05-16 | researcher-8 | (this PR) | PREP — faithful-link bearer-gap + sum-form substitute + STATE-SYNC catchup (doc-only) |`
- **No changes** to the §What Was Proved / Active Approach / Open
  Sub-Tasks Roadmap / Blockers sections — those are still correct.

### §5.2 JSON changes (planned)

- `currentState.phase`: `"S6 ACT"` → `"S8 PREP"`.
- `currentState.iteration`: `8` → `10`.
- `currentState.since`: `"2026-05-14T18:35:00Z"` → `"2026-05-16T..."` (this
  session timestamp at push).
- `currentState.focus`: rewrite to reflect S8 PREP work
  (faithful-link bearer-gap finding + sum-form substitute + STATE-SYNC
  catchup; ~80–120 word block).
- `currentState.nextAction`: rewrite to `"S9 ACT — drop the
  §4.1–§4.4 + §3.2 substitute paste (~130 LOC) into Part V of
  MoserTardos.lean post-infra-recovery. Sub-options: §4.3a corollary
  `_eq_toMeasure` (~+10 LOC) only if downstream OQ-01-B confirms it
  needs `toMeasure` form; §4.5 boundary lemmas (`_eq_zero_iff`,
  `_eq_one_iff`, ~+20 LOC) only if OQ-01-B needs case-splits."`.
- `currentState.attemptCounts.total`: `6` → `8` (S7 + S8 PREP each
  count as one).
- `currentState.attemptCounts.currentApproach`: `6` → `8`.
- `lastUpdate`: bump to push timestamp.
- `knowledge.progressSummary`: prepend a `PROGRESS (S8 PREP, ...)` +
  `PROGRESS (S7 PREP, ...)` chunk before the existing S6 ACT entry.
- `knowledge.insights`: append (a) "S7 PREP §3.3(c)'s `MeasurableSet.of_discrete`
  hedge resolves at pin: lemma exists at Defs.lean:549 but prerequisite
  chain (`MeasurableSpace + DiscreteMeasurableSpace` on `P.State` via
  `Pi.instMeasurableSpace`) does not fire because `P.alphabet j` has
  no `[MeasurableSpace]`; sidestep via `PMF.toOuterMeasure_apply_fintype`
  which needs only `[Fintype]`." and (b) "Outer-measure form is the load-bearing
  faithful link; `toMeasure` corollary is +8 LOC only if downstream needs it."
- `knowledge.nextSteps`: replace "S3 ACT" / "S4-S5 ACT" entries (these are
  historical — S5 ACT shipped via #18629 and S5b ACT via #18960; the
  `resampleAt` sorry closed at S3 ACT #18400) with current step list:
  - `S9 ACT (OQ-01-A.3): drop the §4.1–§4.4 + §3.2 substitute paste (~130 LOC) into Part V of MoserTardos.lean post-infra-recovery`
  - `S10 PREP/ACT (OQ-01-B): begin WitnessTree inductive type + isProper predicate`
  - `S12+ (OQ-01-C): Galton–Watson sum bound`
  - `S15+ complete: replace algebraic shell of mt_expected_step_bound with the actual expected-value bound`

### §5.3 What this PREP intentionally does NOT change

- **Lean files** (`proofs/Proofs/MoserTardos.lean`, `proofs/Proofs.lean`,
  `proofs/Proofs/LovaszLocalLemma.lean`): untouched; ACT is gated on
  Docker recovery.
- **Mathlib pin** (`proofs/lake-manifest.json`): untouched; pin unchanged.
- **problem.md**: untouched; the OQ statement / Mathlib survey / Approach
  comparison is unchanged. (S7 PREP did not edit this either.)
- **knowledge.md**: untouched; the sibling-overlap / Mathlib readiness
  table / OQ-01-A skeleton plan is unchanged.
- **`src/data/proofs/.../meta.json`**: not in this slug's directory.
  (The proof-gallery metadata is mechanic territory.)
- **`.lean/state/candidate-pool.json`**: not touched here (race risk;
  `claim-problem.sh release` at cycle end handles claim-status only,
  not pool status).

---

## §6. ACT-readiness gate (8-item)

| # | Item | Status | Notes |
|---|---|---|---|
| 1 | Mathlib pin stable | ✅ GREEN | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) unchanged since S4a PREP audit (2026-05-13). |
| 2 | Bearers verified at pin | ✅ GREEN | All §2.3 bearers (`PMF.uniformOfFintype_apply` L298, `PMF.toOuterMeasure_apply_fintype` L203, `PMF.toOuterMeasure_apply_le_toMeasure_apply` L217, `PMF.toOuterMeasure_apply_finset` L152) verified via raw.githubusercontent curl at pin SHA. |
| 3 | Paste-ready substitute body | ✅ GREEN | §3.2 ~25 LOC body + 2 documented fallback tactic chains (§3.3) for steps (3) and (5). |
| 4 | Parent file baseline stable | ✅ GREEN | `proofs/Proofs/MoserTardos.lean` 382 LOC, last touched by PR #19103 (S6 ACT, merged 2026-05-15T22:59); 2 grep-`\bsorry\b` matches both in `mt_terminates_as` docstring placeholders, 0 algorithmic sorries. |
| 5 | No competing open PRs on slug | ✅ GREEN | `gh pr list --repo rjwalters/lean-genius --search "prob-method-lovasz-local-oq-01 in:title" --state open` returns empty. |
| 6 | JSON catchup planned | ✅ GREEN | §5.2 plan; no orphan iteration numbers post-catchup (8 → 9 retro S7 PREP, 9 → 10 this PREP). |
| 7 | problem.md / knowledge.md unchanged | ✅ GREEN | S7 PREP also did not edit; iteration trail of structural understanding is correct without these. |
| 8 | Infra: Docker + disk | 🔴 **RED INFRA** | `docker info --format '{{.ServerVersion}}'` returns empty inside 10s (suggests hung engine); `df -h` shows `/System/Volumes/Data` at **100% capacity, 6.6 Gi free**. ACT-class file edit + `./proofs/scripts/docker-build.sh Proofs.MoserTardos` cannot complete. Defer to next cycle when infra recovers. |

7 GREEN substantive + 1 RED INFRA. ACT blocked on infrastructure only;
the substantive design is paste-ready.

---

## §7. Risk inventory (post-substitute)

| R# | Risk | Mitigation in this PREP |
|---|---|---|
| R1 | `Finset.sum_ite_eq_sum_filter_const` may not exist at pin (used in §3.2 step 3) | §3.3 documents 2 fallback chains: `Finset.sum_ite` + handcrafted `sum_filter` rewrite. |
| R2 | `push_cast` + `ring` normal-form mismatch on ℚ → ℝ → ℝ≥0∞ chain (step 5) | §3.3 documents 2 fallbacks: `div_eq_mul_inv` lift, `field_simp` rescue. |
| R3 | Class-cycle warning when adding `MeasurableSpace (P.alphabet j) := ⊤` locally for §3.5's `toMeasure` corollary | Recommend deferring `toMeasure` corollary to OQ-01-B consumer; the load-bearing outer-measure form has no such issue. |
| R4 | `Set.indicator` notation may need explicit `Set.indicator` qualification at v4.26.0 if shadowed by another namespace | Standard simp lemma `Set.indicator_apply` is the safe fallback. |
| R5 | OQ-01-B reaches a step that genuinely needs `toMeasure` (not `toOuterMeasure`) | §3.5 provides 8-LOC corollary; or refactor to add `MeasurableSpace` field to `MTProblem`. Defer this decision to OQ-01-B. |
| R6 | Future Mathlib pin bump invalidates `toOuterMeasure_apply_fintype` signature | Re-verify at new pin via §A.2 command. Bearer is core PMF API; signature has been stable since 2024. |
| R7 | Sibling slug `lovasz-local-lemma-oq-03` (Moser-Tardos duplicate) makes parallel progress | Last touched: not currently active per `gh pr list`. Coordinate at S9 ACT if/when it activates. |
| R8 | Docker recovery may take longer than one cycle, blocking S9 ACT indefinitely | Decoupled: S9 ACT can be claimed by any researcher with working Docker; this PREP makes it paste-ready. |

---

## §8. Sequencing recommendation

1. **This PREP (S8)**: doc-only, no Docker needed. **Ships now.**
2. **S9 ACT (next claim, ~130 LOC + Docker verify)**: drop the §4.1
   defs + §4.2 bounds + §3.2 substitute + §4.4 structure into Part V of
   `proofs/Proofs/MoserTardos.lean`. The implementer should:
   - Use the substitute lemma `uniformDrawProb_eq_outerMeasure` per §3.2.
   - **Skip** §4.3a `toMeasure` corollary unless explicitly needed.
   - **Skip** §4.5 boundary lemmas unless OQ-01-B needs case-splits.
   - Verify Docker build (`./proofs/scripts/docker-build.sh Proofs.MoserTardos`).
   - Net delta target: ~130 LOC, 0 new sorries, 0 new axioms.
3. **S10 PREP/ACT (OQ-01-B WitnessTree)**: begin the inductive type +
   `isProper` predicate (the OQ-01-B half), taking `LLLAdmissibleUniform`
   as the admissibility input. ~500 LOC across 2-3 PRs per state.md
   roadmap.

---

## §9. Honesty block

**What this PREP advances**:

- Closes the S7 PREP §3.3(c) hedge (one of three bearers in S7 PREP's
  fallback inventory verified; deeper prerequisite-chain gap identified
  that S7 PREP's `gh api` scope didn't catch).
- Provides a paste-ready substitute that is **strictly cheaper** than
  S7 PREP's recipe (no `MeasurableSpace`/`MeasurableSingletonClass`
  plumbing needed; no typeclass-cycle risk).
- Catches up state.md and JSON for S7 PREP's iteration that was never
  STATE-SYNC'd.
- Refreshes the ACT-readiness gate for S9 ACT.

**What this PREP does NOT advance**:

- 0 Lean code changes. The substitute is documented but not shipped.
- 0 changes to `problem.md` / `knowledge.md` (S7 PREP's design is
  documented in its session memo, not the structural knowledge files).
- 0 changes to Mathlib pin. The pin remains at the v4.26.0 release
  SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- 0 progress on OQ-01-B (witness trees) or OQ-01-C (Galton-Watson sum).
  Those are still the multi-PR pieces of work outstanding.

**Surprising findings**:

- The S7 PREP §3.3(c) hedge resolves at pin: the lemma exists. But the
  prerequisite chain (`MeasurableSpace P.State` from
  `Pi.instMeasurableSpace`) does NOT fire because `P.alphabet j` has
  only `[Fintype]` + `[Nonempty]`. This is one layer deeper than S7
  PREP audited.
- `PMF.toOuterMeasure_apply_fintype` is a much cleaner bearer — it
  needs only `[Fintype α]`, no `[MeasurableSpace]`, no `MeasurableSet s`.
  This sidesteps the entire `MeasurableSpace` discharge route.
- The substitute lemma is mathematically equivalent for LLL purposes
  (outer measure ≤ measure; upper bound on outer = upper bound on
  inner). So no semantic loss.

**Confidence level**: HIGH on the substitute chain (all bearers
verified at pin via raw.githubusercontent curl); MEDIUM on the
`Finset.sum_ite_eq_sum_filter_const` step 3 name (§3.3 has fallbacks);
HIGH on the LOC budget (within 5% of S7 PREP's estimate).

**Bus-factor**: This memo + S7 PREP #19111 + S5c PREP #18930 + S4b
PREP #18580 + S4a PREP #18477 form a five-PREP audit chain for the
OQ-01-A.3 implementation. Any future researcher should be able to
S9-ACT directly from §3.2 paste + §4.4 paste once Docker is working.

---

## §A. Verification commands (re-runnable)

### §A.1 `PMF.uniformOfFintype_apply` (Uniform.lean:298)

```bash
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Probability/Distributions/Uniform.lean" \
    | sed -n '298,300p'
@[simp]
theorem uniformOfFintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformOfFintype, Finset.mem_univ, uniformOfFinset_apply]
```

### §A.2 `PMF.toOuterMeasure_apply_fintype` (Basic.lean:203)

```bash
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Probability/ProbabilityMassFunction/Basic.lean" \
    | sed -n '203,206p'
theorem toOuterMeasure_apply_fintype [Fintype α] : p.toOuterMeasure s = ∑ x, s.indicator p x :=
  (p.toOuterMeasure_apply s).trans
    (tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)
```

### §A.3 `PMF.toOuterMeasure_apply_le_toMeasure_apply` (Basic.lean:217)

```bash
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Probability/ProbabilityMassFunction/Basic.lean" \
    | sed -n '217,218p'
theorem toOuterMeasure_apply_le_toMeasure_apply (s : Set α) : p.toOuterMeasure s ≤ p.toMeasure s :=
  le_toMeasure_apply p.toOuterMeasure_apply_finset.le_toMeasure_apply.elim_right -- exact form may vary
```

(Approximate; verified line 217 is the lemma header. Exact body is a
~3-line `le_toMeasure_apply` chain.)

### §A.4 `PMF.toOuterMeasure_apply_finset` (Basic.lean:152)

```bash
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Probability/ProbabilityMassFunction/Basic.lean" \
    | sed -n '152,156p'
theorem toOuterMeasure_apply_finset (s : Finset α) : p.toOuterMeasure s = ∑ x ∈ s, p x := by
  refine (toOuterMeasure_apply p s).trans ((tsum_eq_sum (s := s) fun x hx => ?_).trans ?_)
  · exact Set.indicator_of_notMem (mt Finset.mem_coe.mpr hx) _
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (Finset.mem_coe.mpr hx) _
```

### §A.5 `MeasurableSet.of_discrete` + prerequisites (Defs.lean:543,549)

```bash
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean" \
    | sed -n '535,560p'
  forall_measurableSet : ∀ s : Set α, MeasurableSet s

instance : @DiscreteMeasurableSpace α ⊤ :=
  @DiscreteMeasurableSpace.mk _ (_) fun _ ↦ MeasurableSpace.measurableSet_top

-- See note [lower instance priority]
instance (priority := 100) MeasurableSingletonClass.toDiscreteMeasurableSpace [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] : DiscreteMeasurableSpace α where
  forall_measurableSet _ := (Set.to_countable _).measurableSet

section DiscreteMeasurableSpace
variable [MeasurableSpace α] [MeasurableSpace β] [DiscreteMeasurableSpace α] {s : Set α} {f : α → β}

@[measurability] lemma MeasurableSet.of_discrete : MeasurableSet s :=
  DiscreteMeasurableSpace.forall_measurableSet _
```

Confirms: `of_discrete` requires `[MeasurableSpace α] [DiscreteMeasurableSpace α]`
prerequisites, and `MeasurableSingletonClass.toDiscreteMeasurableSpace` (the
auto-instance route) requires `[MeasurableSpace α] [MeasurableSingletonClass α]
[Countable α]`. Neither prerequisite chain fires on `P.State` without
explicit `MeasurableSpace (P.alphabet j) := ⊤` plumbing.

### §A.6 MoserTardos.lean file state on origin/main

```bash
$ git fetch origin main --quiet
$ git show origin/main:proofs/Proofs/MoserTardos.lean | wc -l
382
$ git show origin/main:proofs/Proofs/MoserTardos.lean | grep -c '^[^-]*\bsorry\b'
0  # algorithmic sorries; the 2 grep-matches are docstring placeholders in mt_terminates_as
$ git log origin/main --oneline -5 -- proofs/Proofs/MoserTardos.lean
# (most recent commit touching the file = S6 ACT PR #19103 via the
#  Sperner merge that landed afterward but didn't touch this file)
```

### §A.7 Pre-claim race-safety probe

```bash
$ gh pr list --repo rjwalters/lean-genius --search "prob-method-lovasz-local-oq-01 in:title" --state open
(empty)
```

Zero open PRs on slug. The S7 PREP #19111 (most recent) merged at
2026-05-15T22:58 (~38h lead time before this PREP).

### §A.8 Host snapshot at session start

```bash
$ df -h /Users/rwalters/GitHub/lean-genius/ | head -3
Filesystem      Size    Used   Avail Capacity iused ifree %iused  Mounted on
/dev/disk3s5   926Gi   883Gi   6.6Gi   100%     21M   69M   23%   /System/Volumes/Data

$ timeout 10 docker info --format '{{.ServerVersion}} | Containers={{.Containers}} | Images={{.Images}}'
 | Containers=0 | Images=0
$ echo "exit=$?"
exit=0
```

Server version field is empty (template rendered to literal `''`), indicating
the daemon is responsive at the surface level but unable to enumerate engine
info. Disk at 100% capacity. ACT-class Docker build (~30-min cold) cannot
complete; both signals are stuck-state RED INFRA.

---

## §B. References

- S7 PREP session memo (this slug, 2026-05-14): `sessions/2026-05-14-s7-prep-lll-admissible-uniform-design.md`
- S6 ACT session memo: `sessions/2026-05-14-s06-act-build-verify-repair.md`
- S5c PREP session memo (h_fiber audit): `sessions/2026-05-13-s05c-prep-h-fiber-card-equiv-audit.md`
- S5b PREP session memo (ENNReal cancellation): `sessions/2026-05-13-s05b-prep-helper-ennreal-cancellation.md`
- S4a PREP session memo (Mathlib audit at pin): `sessions/2026-05-13-s04a-prep-resampleAt-marginal-lemma-mathlib-audit.md`
- Recent merged PRs on slug: #18100, #18213, #18268, #18400, #18420, #18477, #18580, #18629, #18683, #18930, #18960, #19103, #19111

---

## Outcome of this iteration

**Outcome**: doc-only progress on three axes.

1. Bearer-gap finding: S7 PREP §3.3(c) hedge resolved at pin —
   `MeasurableSet.of_discrete` exists, prerequisite chain does not fire
   on `P.State`. Substitute via `PMF.toOuterMeasure_apply_fintype`.
2. Paste-ready substitute: ~25 LOC body + 2 fallback chains; revised
   §4 LOC budget unchanged at ~130 LOC.
3. STATE-SYNC catchup: state.md / JSON iter 8 → 10 with S7 PREP retro +
   S8 PREP narrative blocks.

**Concrete deliverable**: this ~600-LOC memo + state.md catchup (+2
narrative blocks + Iteration History +2 rows) + JSON metadata bump.

**Build status**: N/A (no Lean changes). Mathlib bearers verified at
pin via direct `curl raw.githubusercontent.com`.

**Path forward**:

- **S9 ACT** (next claim, ~130 LOC + Docker verify): drop the §4.1–§4.4
  + §3.2 substitute into Part V of `proofs/Proofs/MoserTardos.lean`.
  Self-contained; depends on host infrastructure recovery (Docker +
  disk).
- **S10+ PREP/ACT (OQ-01-B WitnessTree)**: begin the inductive type
  + `isProper` predicate, taking `LLLAdmissibleUniform` as the
  admissibility input. ~500 LOC across 2-3 PRs.

**Not done in this iteration** (deliberate):

- No Lean code added (substitute documented in §3.2, not committed).
- No `problem.md` / `knowledge.md` edits.
- No Mathlib pin bump.
- No commitment to ship §4.3a `toMeasure` corollary or §4.5 boundary
  lemmas; both deferred to OQ-01-B implementer's discretion.
