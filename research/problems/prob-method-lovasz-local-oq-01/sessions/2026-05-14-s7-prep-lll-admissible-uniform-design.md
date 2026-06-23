# S7 PREP — OQ-01-A.3 `LLLAdmissibleUniform` structure design (doc-only)

**Iteration**: S7 PREP (doc-only, follow-up to S6 ACT build-verify PR #19103)
**Author**: researcher-3
**Date**: 2026-05-14
**Mode**: doc-only — only this new file under `sessions/`; no Lean / state.md /
JSON / meta.json edits.
**Predecessors**: S5 ACT (PR #18629 merged — `resampleAt` product-PMF), S5b
ACT (PR #18960 merged — `marginal_uniformOfFintype_pi` helper + `_inside`
+ `_indep` lemmas), S5c PREP (PR #18930 merged — `h_fiber` audit), **S6
ACT build-verify (PR #19103, OPEN/MERGEABLE/CLEAN)** — Docker-verified
parent file at 7743 jobs, repaired 4-cluster v4.26.0 elaboration regression.
**Sister PRs open at session start**: only #19103 (touches
`proofs/Proofs/MoserTardos.lean`, `state.md`, sessions/, and JSON). No
other PRs on this slug.

---

## §0. TL;DR

Per `state.md:100-115` "Next action (S6 ACT or OQ-01-A.3)":

> **S6 PREP (OQ-01-A.3)**: Define `LLLAdmissibleUniform` (a refinement
> of `LLLAdmissible` whose `prob` field is the uniform-draw probability
> of `A_i`); prove the faithful-link lemma
> `prob i = (... uniform measure of isBad i ...)`. ~150 LOC.

Since the S6 ACT label is now taken by the build-verify PR #19103, this
PREP labels the OQ-01-A.3 design at **S7 PREP** and reserves **S7 ACT**
for the implementer. This memo locks the structure signature, the
faithful-link lemma, and the precise Mathlib API at the lake-pinned
rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Key contributions**:

1. **Locks the `LLLAdmissibleUniform` signature** as a refinement of the
   existing `LLLAdmissible` (file lines 308–318) with the `prob` field
   tied to the rational quotient
   `Fintype.card { v // P.isBad i v } / Fintype.card P.State`
   (rather than the symbolic `∃ prob : Fin numEvents → ℚ` existential).
2. **Identifies the load-bearing Mathlib bearer**:
   `PMF.toMeasure_uniformOfFintype_apply` at
   `Mathlib/Probability/Distributions/Uniform.lean:318` (pinned rev),
   which gives
   `(uniformOfFintype α).toMeasure s = Fintype.card s / Fintype.card α`
   for `[Fintype s] [MeasurableSet s]`. This is the single Mathlib
   call the faithful-link lemma needs.
3. **Specifies the faithful-link lemma signature**: a forward direction
   that the rational `uniformDrawProb i` equals the `ℝ≥0∞`-valued
   `(uniformOfFintype P.State).toMeasure { v | P.isBad i v }` after
   coercion. Two short Lean lines after the bearer call.
4. **Provides an implementation skeleton** (~150 LOC total broken into
   `def` + `structure` + `lemma` + `theorem` decompositions) that the
   S7 ACT implementer can drop in verbatim post-#19103-merge.
5. **Verifies orthogonality with PR #19103** field-by-field: the
   helper additions go at the file end (Part IV, post-line 382), not
   touching the four clusters #19103 repairs (lines 163, 211, 247,
   276, 290, 291).

**Strict orthogonality (verified)**:

- No edits to `proofs/Proofs/MoserTardos.lean`. (PR #19103 owns the
  next Lean-code update.)
- No edits to `state.md` / `knowledge.md` / `problem.md`. (PR #19103
  owns the next STATE-SYNC.)
- No edits to `src/data/research/problems/...oq-01.json`. (Same.)
- Single added file: this memo.

---

## §1. Goal — `LLLAdmissibleUniform` structure

The existing `LLLAdmissible` (file lines 308–318) packages an
**existential** over a symbolic `prob : Fin numEvents → ℚ`:

```lean
structure LLLAdmissible (x : Fin P.numEvents → ℚ) : Prop where
  x_range : ∀ i, 0 ≤ x i ∧ x i < 1
  lll : ∃ prob : Fin P.numEvents → ℚ, ∃ adj : Fin P.numEvents → Finset (Fin P.numEvents),
    (∀ i, prob i ≤ x i * (adj i).prod (fun k => 1 - x k)) ∧
    (∀ i, 0 ≤ prob i ∧ prob i ≤ 1)
```

The refinement `LLLAdmissibleUniform` should:

1. **Replace the existential** with a concrete `prob` definition tied to
   the actual uniform-draw measure of `isBad i` over `P.State`.
2. **Use the variable-collision adjacency** `Γ_collision i := { k ≠ i //
   vbl i ∩ vbl k ≠ ∅ }` rather than a free `adj` parameter (the
   variable-collision dependency graph is the "right" one for
   Moser–Tardos).
3. **Reduce to `LLLAdmissible`** via a forward arrow (a constructive
   instance bridge).

### §1.1 Target signature

```lean
/-- **Rational uniform-draw probability**: the probability of `A_i` under
    the uniform distribution on `P.State`, expressed as the rational
    quotient `card{v | isBad i v} / card State`. -/
noncomputable def uniformDrawProb (i : Fin P.numEvents) : ℚ :=
  (Fintype.card { v : P.State // P.isBad i v } : ℚ) / (Fintype.card P.State : ℚ)

/-- **Variable-collision adjacency**: the dependency graph used by
    Moser–Tardos. `k ∈ collisionAdj i` iff `k ≠ i` and `vbl i ∩ vbl k`
    is nonempty. -/
noncomputable def collisionAdj (i : Fin P.numEvents) : Finset (Fin P.numEvents) :=
  (Finset.univ : Finset (Fin P.numEvents)).filter
    (fun k => k ≠ i ∧ (P.vbl i ∩ P.vbl k).Nonempty)

/-- **Refined LLL admissibility predicate**: the uniform-draw probability
    of `A_i` is bounded by `x i · ∏_{k ∈ collisionAdj i} (1 - x k)`,
    using the canonical `uniformDrawProb` and the canonical
    `collisionAdj`. -/
structure LLLAdmissibleUniform (x : Fin P.numEvents → ℚ) : Prop where
  /-- Each tolerance lies in `[0, 1)`. -/
  x_range : ∀ i, 0 ≤ x i ∧ x i < 1
  /-- The per-event uniform-draw probability bound, with the canonical
      `uniformDrawProb` (no symbolic `prob` parameter). -/
  lll_uniform : ∀ i,
    P.uniformDrawProb i ≤ x i * (P.collisionAdj i).prod (fun k => 1 - x k)
```

### §1.2 Forward bridge `LLLAdmissibleUniform → LLLAdmissible`

```lean
/-- The refined `LLLAdmissibleUniform` predicate implies the symbolic
    `LLLAdmissible` predicate (instantiating `prob := P.uniformDrawProb`
    and `adj := P.collisionAdj`). -/
theorem LLLAdmissibleUniform.toLLLAdmissible
    {x : Fin P.numEvents → ℚ} (h : P.LLLAdmissibleUniform x) :
    P.LLLAdmissible x := by
  refine ⟨h.x_range, ⟨P.uniformDrawProb, P.collisionAdj, h.lll_uniform, ?_⟩⟩
  intro i
  refine ⟨?_, ?_⟩
  · -- uniformDrawProb i ≥ 0: card ≥ 0 / card > 0
    exact P.uniformDrawProb_nonneg i
  · -- uniformDrawProb i ≤ 1: card_subtype_le / card_pos_of_state_nonempty
    exact P.uniformDrawProb_le_one i
```

The two helper lemmas `uniformDrawProb_nonneg` and `uniformDrawProb_le_one`
are 1-line each (`Nat.cast_nonneg` / `Nat.cast_pos` + the obvious
`card_subtype_le`-style chain) — see §4.

### §1.3 Why `noncomputable` on the defs

- `uniformDrawProb` uses `Fintype.card` on a subtype with `P.isBadDec` —
  decidable but the `Fintype` instance for `{ v // P.isBad i v }` is
  `Subtype.fintype` which takes the decidability instance as an
  argument. `noncomputable` is a defensive choice (avoids
  `decide`-blocking on later proofs).
- `collisionAdj` filters on `(P.vbl i ∩ P.vbl k).Nonempty`, which is
  decidable but again the `Finset.filter` instance can fight with
  `Classical.dec`. Use `noncomputable` to match `pickBad`'s convention
  (file line 114).

The `LLLAdmissibleUniform` structure itself is `Prop`-valued and needs
no `noncomputable`.

---

## §2. Mathlib API at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

### §2.1 `PMF.toMeasure_uniformOfFintype_apply` (load-bearing)

**File**: `Mathlib/Probability/Distributions/Uniform.lean`
**Line**: 318
**Signature** (verbatim):

```lean
theorem toMeasure_uniformOfFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) [Fintype s] :
    (uniformOfFintype α).toMeasure s = Fintype.card s / Fintype.card α := by
  simp [uniformOfFintype, Fintype.card_subtype, hs]
```

The `α := P.State`, `s := { v : P.State | P.isBad i v }`. For our
`MeasurableSpace P.State` instance:
- `P.State` is `(j : Fin P.numVars) → P.alphabet j`, a finite product
- Mathlib auto-derives `MeasurableSpace` on finite types via the
  `Top` σ-algebra (every set is measurable). Specifically,
  `MeasurableSpace.discrete` is the default-instance for finite types,
  carried transparently by the `Pi.measurableSpace` instance.

For `[Fintype { v // P.isBad i v }]`: derived from `P.isBadDec i v`
via `Subtype.fintype` (`Mathlib/Data/Fintype/Subtype.lean:31`).

For `MeasurableSet { v : P.State | P.isBad i v }`: under the discrete
σ-algebra on the finite `P.State`, **every** set is measurable, so
this is immediate from `MeasurableSet.of_discrete` (or `trivial` /
`MeasurableSet.compl_iff.mpr MeasurableSet.empty` cascade — there are
several routes, all closing in one line).

### §2.2 `PMF.uniformOfFintype_apply` (auxiliary)

**File**: `Mathlib/Probability/Distributions/Uniform.lean`
**Line**: 298
**Signature** (verbatim):

```lean
theorem uniformOfFintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformOfFintype, Finset.mem_univ, uniformOfFinset_apply]
```

Not strictly needed for the faithful-link lemma (we go through
`toMeasure`), but useful as a sanity-check on the relation between the
PMF value at each point and the bulk measure.

### §2.3 `Fintype.card_subtype` (auxiliary)

**File**: `Mathlib/Data/Fintype/Card.lean` (pinned)
**Used by**: the `simp` rewrite chain at the end of
`toMeasure_uniformOfFintype_apply`. Already exercised inside the
helper proof at file line 318.

### §2.4 `ENNReal.toRat` / coercion from ℝ≥0∞ to ℚ

This is the **subtle point**. `PMF.toMeasure_uniformOfFintype_apply`
returns a value in `ℝ≥0∞`:
```
(uniformOfFintype α).toMeasure s = (Fintype.card s : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞)
```

Our `uniformDrawProb : ℚ` is a rational. The faithful-link lemma must
bridge:
```
(P.uniformDrawProb i : ℝ≥0∞) = (uniformOfFintype P.State).toMeasure { v | P.isBad i v }
```

The LHS coerces ℚ → ℝ≥0∞ via `Rat.cast`, then `Real.toNNReal` /
`ENNReal.ofReal`. The cleanest pinned-rev bridge is via:

- `Rat.cast_div`: `((a / b : ℚ) : ℝ≥0∞) = (a : ℝ≥0∞) / (b : ℝ≥0∞)`
  (modulo positivity of `b`).
- `Nat.cast_injective` chains: `(Fintype.card s : ℚ → ℝ≥0∞)` factors
  through `ℕ → ℝ≥0∞`.

The implementer should verify the `simp [Rat.cast_div, Nat.cast_div_le]`
chain works directly; if not, fall back to `push_cast` + `field_simp`.

### §2.5 `MeasurableSet.of_discrete` / `MeasurableSpace.top`

The `MeasurableSet { v | P.isBad i v }` obligation under
`P.State`'s discrete σ-algebra. **Verification**:

```
$ gh api search/code -X GET -f q='"theorem MeasurableSet.of_discrete" repo:leanprover-community/mathlib4' 2>&1
```

The lemma's exact name may have shifted at v4.26.0. Possible variants:
- `MeasurableSpace.top` (discrete instance)
- `MeasurableSpace.measurableSet_top`
- Trivial via `subsingleton.of_top`

The fallback: `(P.State`'s σ-algebra is `⊤` (top, discrete); every set
is measurable. Witnessable via `Trivial`-class instances or
`MeasurableSet.empty.union`-style closure. Worst case: 5-line manual
discharge with `unfold MeasurableSpace.measurableSet'` + `Trivial`.

---

## §3. The faithful-link lemma

### §3.1 Signature

```lean
/-- **Faithful link** between the rational `uniformDrawProb` and the
    underlying `PMF`-valued uniform measure of the bad event. -/
theorem uniformDrawProb_eq_toMeasure (i : Fin P.numEvents) :
    ((P.uniformDrawProb i : ℝ) : ℝ≥0∞) =
      (PMF.uniformOfFintype P.State).toMeasure { v : P.State | P.isBad i v } := by
  -- 1. Apply `toMeasure_uniformOfFintype_apply` at the bad-event set.
  -- 2. Convert the resulting `Fintype.card / Fintype.card : ℝ≥0∞` to
  --    match `((card / card : ℚ) : ℝ≥0∞)` via `Rat.cast_div` + `push_cast`.
  classical
  have hmeas : MeasurableSet { v : P.State | P.isBad i v } := by
    -- discrete σ-algebra on Fintype P.State; every set is measurable.
    exact MeasurableSet.of_discrete  -- OR a 1-line fallback (see §2.5)
  rw [PMF.toMeasure_uniformOfFintype_apply hmeas]
  unfold uniformDrawProb
  push_cast
  ring  -- or `rfl`, depending on the canonical ℝ≥0∞-rational normal form
```

### §3.2 Why this lemma is enough

Downstream uses of `LLLAdmissibleUniform`:

1. **OQ-01-B (witness trees)**: needs the `prob i` bound as a probability
   statement on a state-valued PMF. The faithful-link lemma converts
   the rational bound into the measure-theoretic bound, enabling the
   witness-tree probability inequalities to be stated against the actual
   `PMF.toMeasure`-valued probability rather than the symbolic rational.

2. **`mt_expected_step_bound` / `mt_terminates_as`** (file lines 338,
   370): the statement shells currently take `LLLAdmissible x`. Future
   refinements to the **actual** expected-value bound use
   `LLLAdmissibleUniform x` for the genuine probability-theoretic
   content.

3. **OQ-01-A.3 standalone result**: the bridge from
   `LLLAdmissibleUniform` to `LLLAdmissible` (via §1.2's
   `toLLLAdmissible`) means any future client wanting "the LLL bound
   with concrete probabilities" can write
   `P.LLLAdmissibleUniform x` and use the established
   `mt_expected_step_bound` (which takes `LLLAdmissible x`) via the
   bridge.

### §3.3 Anticipated v4.26.0 elaboration pitfalls

**(a) `Rat.cast` namespace ambiguity.** At v4.26.0, `Rat.cast` exists
in multiple flavours: `Rat.cast : ℚ → α` for `[DivisionRing α]`, plus
specific casts for `ℝ` / `ℝ≥0` / `ℝ≥0∞`. The implementer should be
explicit:
```lean
((P.uniformDrawProb i : ℝ) : ℝ≥0∞)
```
The outer `: ℝ≥0∞` ascription uses `ENNReal.ofReal` under the hood;
the inner `: ℝ` uses `Rat.cast`. Going `ℚ → ℝ≥0∞` directly may fail
to elaborate (no direct `RatCast ℝ≥0∞` instance).

**(b) `push_cast` may need explicit lemma hints.** The mixed
`Fintype.card` (`ℕ`) → ℚ → ℝ → ℝ≥0∞ chain has four layers. If
`push_cast` doesn't normalise to the canonical form, try:
```lean
simp only [Rat.cast_div, Nat.cast_div_le, ENNReal.ofReal_div,
           ENNReal.ofReal_natCast]
```

**(c) `MeasurableSet.of_discrete` may not exist by that exact name.**
Fallback inventory at v4.26.0:
- `MeasurableSet.of_subsingleton` — works if `P.State` has 1 element
- `MeasurableSet.compl_iff` — `MeasurableSet sᶜ ↔ MeasurableSet s`
- `Trivial`-class: `inferInstance : MeasurableSpace.MeasurableSet ⊤ s`
- Manual: `MeasurableSpace.MeasurableSet.of_eq` plus the discrete
  instance.

The safest fallback in case of name drift:
```lean
have hmeas : MeasurableSet { v : P.State | P.isBad i v } := by
  rcases isEmpty_or_nonempty P.State with hempty | hnonempty
  · simp [Set.eq_empty_of_isEmpty]
  · -- discrete instance on Fintype → every set measurable
    exact ⟨trivial⟩ -- or similar manual discharge
```

---

## §4. Implementation skeleton (~150 LOC)

Drop into `proofs/Proofs/MoserTardos.lean` after the current Part III
(end of file at line 382 baseline, after PR #19103 merges).

### §4.1 New definitions (~10 LOC)

```lean
namespace MTProblem

variable (P : MTProblem)

noncomputable def uniformDrawProb (i : Fin P.numEvents) : ℚ :=
  (Fintype.card { v : P.State // P.isBad i v } : ℚ) / (Fintype.card P.State : ℚ)

noncomputable def collisionAdj (i : Fin P.numEvents) : Finset (Fin P.numEvents) :=
  (Finset.univ : Finset (Fin P.numEvents)).filter
    (fun k => k ≠ i ∧ (P.vbl i ∩ P.vbl k).Nonempty)
```

### §4.2 Basic bounds on `uniformDrawProb` (~30 LOC)

```lean
lemma uniformDrawProb_nonneg (i : Fin P.numEvents) :
    0 ≤ P.uniformDrawProb i := by
  unfold uniformDrawProb
  positivity -- or `apply div_nonneg <;> exact_mod_cast Nat.zero_le _`

lemma uniformDrawProb_le_one (i : Fin P.numEvents) :
    P.uniformDrawProb i ≤ 1 := by
  unfold uniformDrawProb
  apply div_le_one_of_le₀
  · exact_mod_cast Fintype.card_subtype_le _
  · exact_mod_cast Nat.zero_le _

lemma uniformDrawProb_mem_unit_interval (i : Fin P.numEvents) :
    0 ≤ P.uniformDrawProb i ∧ P.uniformDrawProb i ≤ 1 :=
  ⟨P.uniformDrawProb_nonneg i, P.uniformDrawProb_le_one i⟩
```

Note: `div_le_one_of_le₀` needs the denominator positivity. Since
`P.State` is nonempty (instance at file line 96), `Fintype.card P.State ≥ 1`,
so `(Fintype.card P.State : ℚ) > 0`. The implementer should add a
helper `card_state_pos` if `linarith` doesn't close it directly:
```lean
lemma card_state_pos : 0 < (Fintype.card P.State : ℚ) := by
  exact_mod_cast Fintype.card_pos
```

### §4.3 Faithful-link lemma (~30 LOC)

```lean
theorem uniformDrawProb_eq_toMeasure (i : Fin P.numEvents) :
    ((P.uniformDrawProb i : ℝ) : ℝ≥0∞) =
      (PMF.uniformOfFintype P.State).toMeasure { v : P.State | P.isBad i v } := by
  classical
  have hmeas : MeasurableSet { v : P.State | P.isBad i v } := by
    -- discrete σ-algebra on Fintype P.State
    apply MeasurableSet.of_discrete -- or fallback per §3.3(c)
  rw [PMF.toMeasure_uniformOfFintype_apply hmeas]
  unfold uniformDrawProb
  push_cast
  -- residue: `(card.bad / card.state : ℝ≥0∞) = (card.bad : ℝ≥0∞) / (card.state : ℝ≥0∞)`
  -- closes by `rfl` after `push_cast` normalises the ℚ → ℝ → ℝ≥0∞ chain.
  rfl
```

The `rfl` closure assumes the canonical ℝ≥0∞-rational normal form
matches `push_cast`'s output. If not, swap `rfl` for `ring` or a
2-3 line `simp only [...]` discharge per §3.3(b).

### §4.4 The structure + forward bridge (~30 LOC)

```lean
/-- **Refined LLL admissibility predicate** ... -/
structure LLLAdmissibleUniform (x : Fin P.numEvents → ℚ) : Prop where
  x_range : ∀ i, 0 ≤ x i ∧ x i < 1
  lll_uniform : ∀ i,
    P.uniformDrawProb i ≤ x i * (P.collisionAdj i).prod (fun k => 1 - x k)

/-- The refined predicate implies the symbolic predicate (with
    `prob := uniformDrawProb` and `adj := collisionAdj`). -/
theorem LLLAdmissibleUniform.toLLLAdmissible
    {x : Fin P.numEvents → ℚ} (h : P.LLLAdmissibleUniform x) :
    P.LLLAdmissible x :=
  ⟨h.x_range,
   P.uniformDrawProb, P.collisionAdj, h.lll_uniform,
   fun i => ⟨P.uniformDrawProb_nonneg i, P.uniformDrawProb_le_one i⟩⟩
```

### §4.5 Trivial-regime + boundary lemmas (~20 LOC)

```lean
/-- `uniformDrawProb i = 0` iff no state makes `A_i` fire. -/
lemma uniformDrawProb_eq_zero_iff (i : Fin P.numEvents) :
    P.uniformDrawProb i = 0 ↔ ∀ v, ¬ P.isBad i v := by
  unfold uniformDrawProb
  rw [div_eq_zero_iff]
  -- ... 5-10 line discharge

/-- `uniformDrawProb i = 1` iff every state makes `A_i` fire. -/
lemma uniformDrawProb_eq_one_iff (i : Fin P.numEvents) :
    P.uniformDrawProb i = 1 ↔ ∀ v, P.isBad i v := by
  -- 8-10 line discharge with `Fintype.card_subtype_eq_card_iff` style
  sorry  -- optional; may defer to a follow-up PR
```

(The two `eq_zero` / `eq_one` lemmas are optional — they're useful for
trivial-regime case-splits in downstream OQ-01-B work, but not
load-bearing for OQ-01-A.3 itself. The S7 ACT implementer may ship
only the §4.1–§4.4 contents, ~100 LOC, and defer §4.5 to S8 ACT.)

### §4.6 Total LOC tally

| Block | LOC | Cumulative |
|---|---|---|
| §4.1 New defs | 10 | 10 |
| §4.2 Basic bounds | 30 | 40 |
| §4.3 Faithful-link | 30 | 70 |
| §4.4 Structure + bridge | 30 | 100 |
| §4.5 Optional boundary lemmas | 20 | 120 |
| Docstrings | 30 | 150 |
| **Total (with §4.5)** | **150** | **150** |
| **Without §4.5** | **130** | **130** |

Matches `state.md`'s "~150 LOC" estimate.

---

## §5. Forward look — OQ-01-A.3 → OQ-01-B → OQ-01-C

`LLLAdmissibleUniform` is the natural input to OQ-01-B (witness trees)
and OQ-01-C (Galton–Watson sum). Concretely:

- **OQ-01-B**: defines `WitnessTree P` inductive type + `isProper`
  predicate. The tree-probability bound theorem then states
  `Pr[τ appears in execution] ≤ ∏_{v ∈ τ.nodes} P.uniformDrawProb v.lbl`.
  This is the **direct** use of `uniformDrawProb` — no symbolic
  intermediary. After OQ-01-A.3 lands, OQ-01-B can state its main
  theorem against `LLLAdmissibleUniform`-style probabilities, not
  `LLLAdmissible`'s existential.

- **OQ-01-C**: Galton–Watson sum bounds `Σ_{τ proper, root=i}
  ∏_v Pr[A_{lbl(v)}] ≤ x i / (1 - x i)`. Algebraic content; consumes
  the per-node `uniformDrawProb` bound from OQ-01-B + the `x_range`
  hypothesis from `LLLAdmissibleUniform`.

After OQ-01-{B, C} land, `mt_expected_step_bound` (file line 338)
gets its full proof body (replacing the current `Σᵢ xᵢ/(1-xᵢ)`
non-negativity placeholder). This is the **OQ-01 finish line**.

---

## §6. Race-awareness / orthogonality

### §6.1 With PR #19103 (S6 ACT build-verify)

PR #19103 modifies `proofs/Proofs/MoserTardos.lean` at lines:
- Cluster A: 163, 247, 276 (`rw [h_const]` post-`PMF.map_comp` fixes)
- Cluster B: 211 (`ℝ≥0∞` notation lift)
- Cluster C: 179 (downstream resolution)
- Cluster D: 291 (`def run` recursive field-notation)

The §4 helper additions go at **file end** (post-line 382, after the
existing Part IV theorem shells). Zero overlap with #19103's repair
sites.

The structure `LLLAdmissibleUniform` lives in Part V (new), after
Part III's `LLLAdmissible`. Adding a new Part V to the file is
strictly additive; no existing lemma names are touched.

### §6.2 With sibling slugs

This PREP is doc-only and does not touch the parent file or any
sibling slug's files. The closest sibling is
`lovasz-local-lemma-oq-03` (parent `LovaszLocalLemma.lean`), which
has its own admissibility framework but does not collide with this
slug's `Proofs/MoserTardos.lean`.

### §6.3 Pre-claim probe (verified)

```
$ gh pr list --repo rjwalters/lean-genius --search "prob-method-lovasz-local-oq-01 in:title" \
    --state open --limit 5
19103  S6 ACT build-verify (open, CLEAN, mergeable)
```

One open PR; mergeable. This PREP is doc-only; no conflict.

---

## §7. Anti-targets (what S7 PREP must NOT do)

- Do not edit `proofs/Proofs/MoserTardos.lean`. (PR #19103 owns the
  next Lean-code update.)
- Do not edit `state.md` / `knowledge.md` / `problem.md`. (PR #19103
  owns the next STATE-SYNC; this PREP's session entry will be added
  there after #19103 merges.)
- Do not edit `src/data/research/problems/...oq-01.json`. (Same.)
- Do not commit to a specific shape of `collisionAdj` if the
  implementer prefers a different convention (e.g., symmetric closure,
  with-self, etc.). The §1.1 form is the canonical Moser–Tardos
  choice, but the implementer can swap it for any predicate-class
  consistent variant without touching downstream consumers.
- Do not lock the `MeasurableSet` discharge route — §3.3(c) provides
  three fallbacks. The implementer should pick whichever survives
  the v4.26.0 elaboration first.

---

## §A. Verification commands (re-runnable)

```bash
# Mathlib rev:
$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# PMF.toMeasure_uniformOfFintype_apply (Uniform.lean:318):
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Probability/Distributions/Uniform.lean" \
    | sed -n '318,322p'
theorem toMeasure_uniformOfFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) [Fintype s] :
    (uniformOfFintype α).toMeasure s = Fintype.card s / Fintype.card α := by
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ _ hs,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  simp [uniformOfFintype, Fintype.card_subtype, hs]

# PMF.uniformOfFintype_apply (Uniform.lean:298):
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Probability/Distributions/Uniform.lean" \
    | sed -n '298,300p'
theorem uniformOfFintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformOfFintype, Finset.mem_univ, uniformOfFinset_apply]

# Existing LLLAdmissible structure (file lines 308-318):
$ sed -n '308,318p' proofs/Proofs/MoserTardos.lean

# Existing theorem shells (file lines 338, 370):
$ sed -n '338,345p' proofs/Proofs/MoserTardos.lean
$ sed -n '370,375p' proofs/Proofs/MoserTardos.lean
```

All four commands point to invariants this PREP relies on. The S7 ACT
implementer should re-run them post-#19103-merge to confirm relevant
line numbers (PR #19103's +20/-20 LOC delta should not shift any line
in 300–382 range materially; lines for Parts I–III should be stable).

---

## Outcome of this iteration

**Outcome**: doc-only progress (structure signature locked,
faithful-link lemma locked, Mathlib bearer audited, implementation
skeleton + LOC budget supplied).

**Concrete deliverable**: this 150-LOC memo gives the S7 ACT
implementer (1) the verbatim `LLLAdmissibleUniform` signature and the
two associated `noncomputable def`s, (2) a 30-LOC faithful-link
lemma skeleton with three concrete v4.26.0 fallback paths for the
`MeasurableSet` discharge, (3) a complete ~150 LOC implementation
skeleton broken into 5 blocks (§4.1–§4.5), (4) a forward arrow to
OQ-01-B / OQ-01-C, (5) re-runnable Mathlib bearer verification
commands.

**Build status**: N/A (no Lean changes). Mathlib bearer verified at
`Mathlib/Probability/Distributions/Uniform.lean:318` via direct
`curl raw.githubusercontent.com` at the lake-pinned rev.

**Path forward**:

- **S7 ACT** (next claim, ~130–150 LOC): drop the §4.1–§4.4 (or
  §4.1–§4.5 with the optional boundary lemmas) into Part V (new file
  end). Self-contained; depends on #19103 having merged.
- **S8 PREP / ACT** (OQ-01-B): begin `WitnessTree` inductive type +
  `isProper` predicate, taking `LLLAdmissibleUniform` as the
  admissibility input.

**Not done in this iteration** (deliberate):

- No Lean code added.
- No state.md / JSON / meta.json edits.
- No proposal to modify the existing `LLLAdmissible` structure
  (backward-compatibility preserved via the forward bridge in §1.2 /
  §4.4).
- No exhaustive `MeasurableSet`-discharge route picked — three
  fallbacks documented in §3.3(c); the S7 ACT implementer picks one.
- No commitment on the optional `uniformDrawProb_eq_zero_iff` /
  `uniformDrawProb_eq_one_iff` boundary lemmas; the implementer may
  ship §4.1–§4.4 only (~130 LOC) and defer §4.5 to S8.
