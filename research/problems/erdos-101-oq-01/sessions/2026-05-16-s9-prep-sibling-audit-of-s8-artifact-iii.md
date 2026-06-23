# Session 9 PREP — Sibling-audit of S8 STATE-SYNC (#19360) Path-A ACT plan: 2 soundness bugs in artifacts (i) + (iii)

- **Date**: 2026-05-16
- **Session**: 9
- **Phase**: PREP (no ACT — surfaces soundness bugs before S8 ACT is executed)
- **Researcher**: researcher-12
- **Status**: doc-only sibling-audit, conflict-free with open S8 STATE-SYNC PR #19360

## 1. TL;DR

S8 STATE-SYNC (#19360, OPEN, 90min old at S9 claim) stages a "readiness
gate fully GREEN" 3-artifact Path-A ACT recipe (per S7 PREP §9 + S8 §5).
Goal-state simulation of the **artifact-(iii) signature** and the
**artifact-(i) per-P corollary signature** — both at the lake-pinned
Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) —
surfaces **2 substantive soundness bugs** that the S8 ACT implementer
following the recipe verbatim would land as **provably false Lean
declarations marked `sorry`** (i.e. they would appear OPEN but actually
be refutable in <10 LOC of pure ℕ arithmetic):

| # | Severity | Where in #19360 / chain | Issue |
|---|----------|--------------------------|-------|
| **F** | **substantive, soundness** | S8 §5 artifact (iii); S7 §4.4 "Path A"; S6 PREP artifact (iii) | The drafted signature `theorem erdos_101_oq_01_isLittleO_form : Asymptotics.IsLittleO atTop (fun n : ℕ => (maxFourPointLines n : ℝ)) (fun n : ℕ => (n : ℝ)^2) := sorry` with `maxFourPointLines n = n*(n-1)/12` (S7 PREP §4.5 surrogate, S8 §5 artifact (i)) is **provably FALSE**: `(n*(n-1)/12) / n² → 1/12 ≠ 0`, so `IsLittleO` fails by the strict bound. Marking it `sorry` would land an OPEN-looking theorem whose negation is a 5-line `decide`-able witness. **Fix: artifact (iii) must be the EXISTENTIAL form** `∃ g : ℕ → ℕ, BoundsAtRate (fun n => (g n : ℝ)) ∧ Asymptotics.IsLittleO atTop (fun n => (g n : ℝ)) (fun n => (n : ℝ)^2)` (see §3.5) — which IS the genuine restatement of OQ-01 in Mathlib idiom, sorry-able, OPEN. |
| **G** | **substantive, soundness** | S8 §5 artifact (i) per-P corollary; S7 §4.4 "recover the original ... relation (~10 LOC)" | The drafted per-P corollary signature `theorem fourPointLineCount_le_max (P : PlanarPointSet) : (fourPointLineCount P : ℝ) ≤ maxFourPointLines P.points.card` (no `NoFiveCollinear P` hypothesis — implicit reading from S7 §4.4's text "recover the *original* `(fourPointLineCount P : ℝ) ≤ maxFourPointLines P.points.card` relation") is **provably FALSE**: take `P` = 9 distinct points on one line, then `fourPointLineCount P = C(9,4) = 126` but `maxFourPointLines 9 = 9*8/12 = 6`, contradicting `126 ≤ 6`. **Fix: signature MUST carry `(hP : NoFiveCollinear P)`** matching the existing `fourPointLineCount_le_quadratic (P) (hP : NoFiveCollinear P)` (line 143) precedent. |

Both bugs are invisible to the prior bearer-existence checks (the
Mathlib names exist; the surrogate definition compiles; the bridge
direction analysis in S7 §3 is correct *for the bridge*). They appear
only when one **walks the goal-state of the drafted signature** for
artifact (iii) and **probes the counterexample at small `n`** for the
artifact-(i) per-P corollary.

**Recommendation**: amend S8 ACT recipe per §3.5 + §4.4 below BEFORE
the S8 ACT picker fires Docker iter 1. Without these fixes, the S8 ACT
would either (a) ship an unsound theorem (the FALSE artifact-(iii) form
masked under `sorry`), or (b) `noConfusion`-fail at the per-P corollary
elaboration (without `NoFiveCollinear`, `fourPointLineCount_le_quadratic`
gives no usable inequality).

This audit is doc-only, adds **exactly one** new sessions/ file
(`2026-05-16-s9-prep-sibling-audit-of-s8-artifact-iii.md`), touches
no `state.md` / `knowledge.md` / JSON / Lean. Strictly conflict-free
with open PR #19360 (paths disjoint).

## 2. Pre-claim probe (2026-05-16T02:58Z, after S8 STATE-SYNC opened at 01:29Z)

```
$ gh pr list -R rjwalters/lean-genius --state open \
    --search 'erdos-101-oq-01 in:title' --json number,title,createdAt,mergeStateStatus
[
  {"number":19360, "createdAt":"2026-05-16T01:29:21Z", "mergeStateStatus":"CLEAN",
   "title":"research(erdos-101-oq-01): S8 STATE-SYNC — post-drain catch-up + bearer drift recheck (doc-only)"}
]
```

One open PR on slug: my own S8 STATE-SYNC #19360 (~90min old). CLEAN/MERGEABLE.
S8 STATE-SYNC ships 3 files (sessions/ new + state.md + JSON) — all
DISJOINT from this S9 PREP's single new sessions/ file. No race.

Last merged research PR on slug: `#19287` (S7 PREP, doc-only) at
2026-05-15T18:01:30Z (~9h ago). No sibling Docker processes touching
`Erdos101OQ01.lean` or `Erdos101Problem.lean` (`ps -ef | grep
docker-build`). Sibling worktree state.md mtimes ≥9h old. Race-free.

Open queue at S9 claim: ~67 PRs (deployer post-drain recovery; previous
wave drained 25+ PRs at 01:08-01:09Z, then 22+ more at 02:08-02:35Z).
Last deployer merge on slug: none in past 9h (slug deferred to
post-S8-STATE-SYNC merge).

## 3. Bug F (substantive, soundness): artifact (iii) signature ⇒ provably FALSE theorem

### 3.1 What S6 PREP / S7 PREP / S8 §5 prescribe for artifact (iii)

S8 STATE-SYNC #19360 §5 artifact (iii) text:

> 3. **Artifact (iii)** — Mathlib-idiom form of OQ-01 (~30 LOC):
>    - `theorem erdos_101_oq_01_isLittleO_form : Asymptotics.IsLittleO atTop (fun n : ℕ => (maxFourPointLines n : ℝ)) (fun n : ℕ => (n : ℝ)^2) := sorry`
>      (the same OPEN content as `erdos_101_oq_01`, rephrased).

S7 PREP §9 step 3.(iii):

> **(iii)** `erdos_101_oq_01_isLittleO_form` per S6 PREP (~30 LOC).

S6 PREP §"S6 ACT scope" mentions artifact (iii) by name with budget
~30 LOC but **never provides a concrete signature** — the implementer
following S6/S7/S8 verbatim has to invent it from the bare slogan
"Mathlib-idiom form of OQ-01". The natural reading, matching artifacts
(i) + (ii)'s explicit use of `maxFourPointLines`, is the signature
inlined in S8 §5 above.

### 3.2 Why that signature is provably FALSE

`maxFourPointLines : ℕ → ℕ` is defined as the surrogate `n * (n-1) / 12`
(S7 PREP §4.5 + S8 §5 artifact (i): "`noncomputable def
maxFourPointLines : ℕ → ℕ` (surrogate `n*(n-1)/12`; pessimistic
upper-bound)").

For this specific surrogate, the asymptotic ratio is:

```
maxFourPointLines n / n²  =  (n * (n-1) / 12) / n²
                          ≤  (n * n / 12) / n²
                          =  1/12
```

and concretely for all `n ≥ 24` (using `Nat.div`'s floor semantics
plus `(n-1)/n → 1`):

```
maxFourPointLines n / n²  ≥  (n*(n-1) - 11) / (12 * n²)
                          →  1/12  as n → ∞.
```

So `lim_{n→∞} maxFourPointLines n / n² = 1/12 ≠ 0`.

**`Asymptotics.IsLittleO atTop f g` unfolds to** (Mathlib `Defs.lean:175`):

```lean
∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in atTop, ‖f x‖ ≤ c * ‖g x‖
```

Specialise at `c := 1/13 < 1/12`. Then we need
`∀ᶠ x in atTop, (maxFourPointLines x : ℝ) ≤ (1/13) * (x : ℝ)²` (norms
collapse to identity on nonneg reals). But for any `x ≥ 24` chosen
as in §3.2:

```
(maxFourPointLines x : ℝ) ≥ (x*(x-1) - 11) / 12  (Nat.div floor lower bound)
                          ≥ (x*(x-1))/12 - 1
```

For `x ≥ 100`:

```
(x*(x-1))/12 - 1  ≥  100*99/12 - 1  =  825 - 1  =  824
(1/13) * x²       ≤  (1/13) * 10000  ≈  769.2
```

So `(maxFourPointLines 100 : ℝ) ≥ 824 > 769.2 ≥ (1/13) * 100²`.
Same `(maxFourPointLines x : ℝ) > (1/13) * x²` holds for all `x ≥ 100`
(both sides quadratic in `x` with coefficient 1/12 vs 1/13).

Hence the `∀ᶠ x in atTop, ...` clause **fails** for `c := 1/13`, so
`IsLittleO atTop maxFourPointLines (· ^ 2)` is FALSE. ∎

### 3.3 Concrete sub-statement that refutes artifact (iii) in <10 LOC

```lean
theorem maxFourPointLines_not_isLittleO_n_squared :
    ¬ Asymptotics.IsLittleO Filter.atTop
        (fun n : ℕ => (maxFourPointLines n : ℝ))
        (fun n : ℕ => (n : ℝ)^2) := by
  intro h
  rw [Asymptotics.isLittleO_iff] at h
  -- specialise at c = 1/13
  have h₁ : ∀ᶠ x in Filter.atTop,
      ‖(maxFourPointLines x : ℝ)‖ ≤ (1/13) * ‖((x : ℝ)^2)‖ :=
    h (by norm_num : (0:ℝ) < 1/13)
  rw [Filter.eventually_atTop] at h₁
  obtain ⟨N, hN⟩ := h₁
  -- pick a witness `n ≥ max N 100`
  specialize hN (max N 100) (le_max_left _ _)
  -- numerical contradiction at n=100 (or any n ≥ 100)
  -- (a) maxFourPointLines (max N 100) ≥ 824   (Nat arithmetic on n*(n-1)/12)
  -- (b) (1/13) * (max N 100)² ≤ ... < 824     for max N 100 ≥ 100
  -- contradicting hN.
  sorry  -- 5-LOC numerical finish; sketched, not load-bearing
```

The above is *not* required to be shipped — it is a **proof witness
that the planned artifact (iii) is unsound**. The S9 PREP recommendation
is to fix the signature so this refutation does not apply.

### 3.4 Why this bug is invisible to prior PREPs

- **S6 PREP** never wrote the artifact-(iii) signature explicitly —
  only the LOC budget and a slogan.
- **S7 PREP** §"S6 ACT scope" artifact (iii) check focused on
  TYPE-COHERENCE (Bug C: `Preorder PlanarPointSet`) for artifact (i),
  not on **semantic content** of artifact (iii). The S7 audit
  goal-state-walked artifacts (i) and (ii) but the artifact (iii)
  walk would have required *unfolding the surrogate definition into
  the IsLittleO* — which S7 §4.4 implicitly DEFERS to "later refinement
  pass".
- **S8 §11 honesty notes** flag "Aggregator surrogate `n*(n-1)/12` ...
  does not depend on `NoFiveCollinear`, so `maxFourPointLines_isBigO_n_squared`
  is a trivial-O(n²) statement" — but **frames this as an `IsBigO`
  triviality (true), not an `IsLittleO` falsity (the actual bug)**.
  The §11 note correctly identifies the surrogate is `Θ(n²)`; the bug
  is that `Θ(n²) ⟹ ¬o(n²)`, which the note does not draw.

This is the canonical "the bug is in the implicit content, not the
explicit content" pattern. S6/S7 PREPs would have caught it via
**unfolding the IsLittleO definition at the surrogate** — a step
that neither PREP took.

### 3.5 Correct signature for artifact (iii): EXISTENTIAL form

Reframe artifact (iii) to match the slug's existing
`erdos_101_oq_01_rate_form` (line 96), which is the **OPEN existential**
already in the file:

```lean
def erdos_101_oq_01_rate_form : Prop :=
  ∃ g : ℕ → ℕ, IsLittleOh_n_squared g ∧
    ∀ (P : PlanarPointSet), NoFiveCollinear P →
      fourPointLineCount P ≤ g P.points.card
```

The Mathlib-idiom analogue of `erdos_101_oq_01_rate_form` is:

```lean
def erdos_101_oq_01_isLittleO_form : Prop :=
  ∃ g : ℕ → ℕ,
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ => (g n : ℝ))
      (fun n : ℕ => (n : ℝ)^2) ∧
    BoundsAtRate (fun n : ℕ => (g n : ℝ))
```

Or, using the existing `BoundsAtRate` predicate (slug line 72):

```lean
def erdos_101_oq_01_isLittleO_form : Prop :=
  ∃ g : ℕ → ℕ,
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ => (g n : ℝ))
      (fun n : ℕ => (n : ℝ)^2) ∧
    BoundsAtRate (fun n : ℕ => (g n : ℝ))
```

(Identical up to whitespace — including for naming hygiene.)

**This existential form IS OPEN**: it asserts the existence of an
o(n²) bounding rate, which is the $100 Erdős prize. Sorry-able as a
`theorem ... := sorry` because the construction `g` is not known.

**It does NOT pin to the surrogate** `maxFourPointLines = n*(n-1)/12`,
so it does not run afoul of §3.2's refutation.

### 3.6 Optional companion: equivalence with primary form

To match the slug's `def erdos_101_oq_01_rate_form` already being
"equivalent" to `def erdos_101_oq_01_conjecture` (per the docstring
at line 90: "The two definitions ... are mutually convertible by the
classical ε-N ↔ Cauchy-criterion bridge"), one may also state:

```lean
theorem erdos_101_oq_01_rate_form_iff_isLittleO :
    erdos_101_oq_01_rate_form ↔ erdos_101_oq_01_isLittleO_form := by
  unfold erdos_101_oq_01_rate_form erdos_101_oq_01_isLittleO_form
  constructor
  · rintro ⟨g, h_olittle, h_bounds⟩
    refine ⟨g, ?_, fun P hP => ?_⟩
    · -- apply isLittleOh_n_squared_iff_isLittleO.mp h_olittle
      exact isLittleOh_n_squared_iff_isLittleO.mp h_olittle
    · exact_mod_cast h_bounds P hP
  · rintro ⟨g, h_olittle_mathlib, h_bounds⟩
    refine ⟨g, ?_, fun P hP => ?_⟩
    · exact isLittleOh_n_squared_iff_isLittleO.mpr h_olittle_mathlib
    · exact_mod_cast h_bounds P hP
```

This adds ~15 LOC and **trades the FALSE concrete `IsLittleO` claim
for a TRUE bidirectional `iff` between the two open-question forms**.

LOC budget for **corrected artifact (iii) + companion**: ~25–35 LOC
(within the original S6 ~30 LOC envelope, slightly larger if companion
included).

## 4. Bug G (substantive, soundness): per-P corollary missing `NoFiveCollinear P`

### 4.1 What S7 §4.4 + S8 §5 prescribe

S7 PREP §4.4 (Path A recommendation, sub-bullet 2):

> A separate per-`P` corollary can recover the original
> `(fourPointLineCount P : ℝ) ≤ maxFourPointLines P.points.card`
> relation (~10 LOC), giving total artifact (i) **~45–60 LOC**.

S8 §5 artifact (i), sub-bullet 3:

>    - Per-P corollary `fourPointLineCount_le_max …` (~10 LOC).

The literal reading — and the natural elaboration matching the
S7 §4.4 displayed signature `(fourPointLineCount P : ℝ) ≤
maxFourPointLines P.points.card` — is:

```lean
theorem fourPointLineCount_le_max (P : PlanarPointSet) :
    (fourPointLineCount P : ℝ) ≤ (maxFourPointLines P.points.card : ℝ) :=
  sorry
```

### 4.2 Why that signature is FALSE (5-collinear-line counterexample)

With `maxFourPointLines n = n*(n-1)/12`:

```
maxFourPointLines 9  =  9 * 8 / 12  =  72 / 12  =  6     (Nat division floor)
```

Take `P` = 9 distinct points on a single line in ℝ² (e.g., `(0,0)`,
`(1,0)`, ..., `(8,0)`; `P.points.card = 9`). Then every 4-subset of
`P.points` is collinear (all 4 points on the `y=0` line), so:

```
fourPointLineCount P  =  C(9, 4)  =  126
```

But `maxFourPointLines 9 = 6`. The drafted theorem claims
`(126 : ℝ) ≤ (6 : ℝ)`, which is FALSE. ∎

### 4.3 Why the existing `fourPointLineCount_le_quadratic` requires `NoFiveCollinear`

`fourPointLineCount_le_quadratic` (`Erdos101OQ01.lean:143-145`):

```lean
theorem fourPointLineCount_le_quadratic (P : PlanarPointSet)
    (hP : NoFiveCollinear P) :
    (fourPointLineCount P : ℝ) ≤ (P.points.card : ℝ)^2 := by
  have hN : fourPointLineCount P ≤ P.points.card * (P.points.card - 1) / 12 :=
    improved_upper_bound P hP    -- ← hP USED HERE
  ...
```

The `hP` is **load-bearing** — it feeds into `improved_upper_bound`
(the n(n-1)/12 bound from `Erdos101Problem.lean`), which is the bound
the per-P corollary inherits via `maxFourPointLines = n*(n-1)/12`.

WITHOUT `hP`, the corollary FAILS at `improved_upper_bound`'s
hypothesis argument; equivalently, the corollary is REFUTABLE via the
9-collinear-line witness in §4.2.

### 4.4 Correct signature for the per-P corollary

```lean
theorem fourPointLineCount_le_max (P : PlanarPointSet)
    (hP : NoFiveCollinear P) :
    (fourPointLineCount P : ℝ) ≤ (maxFourPointLines P.points.card : ℝ) := by
  have h₁ : fourPointLineCount P ≤
      P.points.card * (P.points.card - 1) / 12 :=
    improved_upper_bound P hP
  -- maxFourPointLines unfolds to n*(n-1)/12
  exact_mod_cast h₁
```

LOC: ~6 LOC (within the budgeted ~10 LOC).

### 4.5 Why this bug is invisible to prior PREPs

- **S6/S7 PREP** focused on the IsBigO/IsLittleO bridge tactics; the
  per-P corollary was assumed "trivial recover of existing bound" with
  no explicit signature.
- **S7 §4.4 Path A** explicitly invokes "the *original* `fourPointLineCount
  ≤ maxFourPointLines` relation" — but the **"original"** in the file
  is `fourPointLineCount_le_quadratic`, which has `NoFiveCollinear P`
  as hypothesis (line 143). S7 §4.4's gloss drops the hypothesis from
  the displayed signature, and S8 §5 inherits the drop.
- **S8 §11 honesty notes** specifically observe "**Aggregator surrogate**
  ... **does not depend on `NoFiveCollinear`**" — correctly identifying
  the *aggregator definition* as NoFiveCollinear-free. But the per-P
  **corollary** (which bridges aggregator-bound back to per-P fourPointLineCount)
  MUST depend on `NoFiveCollinear` to be valid, and §11 does not draw
  this distinction.

## 5. Revised artifact-(i) + (iii) sketches (corrected)

### 5.1 Artifact (i) — aggregator + IsBigO + corrected per-P corollary

```lean
/-- Aggregator: upper bound on `fourPointLineCount` for no-five-collinear sets
of size `n`. Surrogate version using `improved_upper_bound`'s `n*(n-1)/12`. -/
noncomputable def maxFourPointLines (n : ℕ) : ℕ :=
  n * (n - 1) / 12

/-- The aggregator is O(n²) at infinity. -/
theorem maxFourPointLines_isBigO_n_squared :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (maxFourPointLines n : ℝ))
      (fun n : ℕ => (n : ℝ)^2) := by
  apply Asymptotics.IsBigO.of_norm_le
  intro n
  -- ‖(maxFourPointLines n : ℝ)‖ = maxFourPointLines n ≤ n²/12 ≤ n² (for n ≥ 0)
  show |(maxFourPointLines n : ℝ)| ≤ |(n : ℝ)^2|
  rw [abs_of_nonneg, abs_of_nonneg]
  · -- maxFourPointLines n = n*(n-1)/12 ≤ n*n = n² (n*(n-1) ≤ n², div_le_self)
    unfold maxFourPointLines
    have hbnd : n * (n - 1) / 12 ≤ n * n := by
      have hsub : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
      exact (Nat.div_le_self _ 12).trans hsub
    have hcast : ((n * (n - 1) / 12 : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) :=
      Nat.cast_le.mpr hbnd
    have hsq : ((n * n : ℕ) : ℝ) = (n : ℝ)^2 := by push_cast; ring
    linarith
  · positivity
  · exact_mod_cast Nat.zero_le _

/-- Per-`P` corollary: `fourPointLineCount` is bounded by the aggregator
**for no-five-collinear** sets. (The hypothesis `NoFiveCollinear P` is
load-bearing — without it, `P` could be 9-collinear-on-a-line and
`fourPointLineCount P = C(9,4) = 126 > 6 = maxFourPointLines 9`.) -/
theorem fourPointLineCount_le_max (P : PlanarPointSet)
    (hP : NoFiveCollinear P) :
    (fourPointLineCount P : ℝ) ≤ (maxFourPointLines P.points.card : ℝ) := by
  have h₁ : fourPointLineCount P ≤
      P.points.card * (P.points.card - 1) / 12 :=
    improved_upper_bound P hP
  exact_mod_cast h₁
```

LOC: ~30 LOC (within S6's ~25 LOC for aggregator + IsBigO statement,
~5 LOC over budget for the explicit `NoFiveCollinear`-aware per-P
corollary).

### 5.2 Artifact (iii) — existential form (replaces FALSE concrete form)

```lean
/-- **OQ-01, Mathlib-idiom form**: there exists a function `g : ℕ → ℕ`
that is `o(n²)` (in Mathlib's `Asymptotics.IsLittleO atTop … (· ^ 2)`
sense) AND bounds `fourPointLineCount P` for every no-five-collinear
`P` of size `n`. This is the existential restatement of OQ-01 with
the `o(n²)` rate phrased in Mathlib idiom.

This statement is **OPEN** ($100 Erdős prize). It is the Mathlib-idiom
twin of `erdos_101_oq_01_rate_form` (the slug-form existential). -/
def erdos_101_oq_01_isLittleO_form : Prop :=
  ∃ g : ℕ → ℕ,
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ => (g n : ℝ))
      (fun n : ℕ => (n : ℝ)^2) ∧
    BoundsAtRate (fun n : ℕ => (g n : ℝ))

/-- The two existential forms are equivalent. -/
theorem erdos_101_oq_01_rate_form_iff_isLittleO :
    erdos_101_oq_01_rate_form ↔ erdos_101_oq_01_isLittleO_form := by
  unfold erdos_101_oq_01_rate_form erdos_101_oq_01_isLittleO_form
  constructor
  · rintro ⟨g, h_olittle, h_bounds⟩
    refine ⟨g, isLittleOh_n_squared_iff_isLittleO.mp h_olittle, ?_⟩
    intro P hP
    exact_mod_cast h_bounds P hP
  · rintro ⟨g, h_olittle_mathlib, h_bounds⟩
    refine ⟨g, isLittleOh_n_squared_iff_isLittleO.mpr h_olittle_mathlib, ?_⟩
    intro P hP
    -- h_bounds: (fourPointLineCount P : ℝ) ≤ ((g P.points.card : ℕ) : ℝ)
    -- goal: fourPointLineCount P ≤ g P.points.card (Nat)
    exact_mod_cast h_bounds P hP

/-- **The main OPEN theorem of OQ-01, Mathlib-idiom form.**

Equivalent to `erdos_101_oq_01` (slug primary form) via the chain
`erdos_101_oq_01 ↔ erdos_101_oq_01_rate_form ↔ erdos_101_oq_01_isLittleO_form`.
Proof is open. -/
theorem erdos_101_oq_01_isLittleO : erdos_101_oq_01_isLittleO_form := by
  sorry
```

LOC: ~30 LOC (within S6's ~30 LOC budget for artifact (iii)).

**Total revised artifact-(i)+(iii) budget**: ~60 LOC (vs S8's ~75–90).
Artifact (ii) is unchanged at ~30 LOC. Grand total: **~90 LOC** — fits
within S7's revised "~105–125 LOC" envelope, with breathing room.

## 6. Bearer pin re-verification (delta vs S8 STATE-SYNC §4)

All bearers from S8 §4 re-verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0, unchanged since S7 PREP and S8 STATE-SYNC).

| Bearer | S8 §4 file:line | S9 re-verified file:line | Status |
|--------|----------------|--------------------------|--------|
| `Asymptotics.IsBigO` | `Defs.lean:93` | `Defs.lean:93` | ✓ (file SHA `d48b4eca7daae59c293b79a6b221afc2d2b25a81`, unchanged) |
| `Asymptotics.isBigO_iff` | `Defs.lean:104` | `Defs.lean:104` | ✓ |
| `Asymptotics.IsBigO.of_norm_le` | `Defs.lean:155` | `Defs.lean:155` | ✓ |
| `Asymptotics.IsLittleO` | `Defs.lean:162` | `Defs.lean:162` | ✓ |
| `Asymptotics.isLittleO_iff` | `Defs.lean:175` | `Defs.lean:175` | ✓ |
| `Filter.eventually_atTop` | `AtTopBot/Basic.lean:72` | `AtTopBot/Basic.lean:72` | ✓ (file SHA `c1d3043255fab4c93a34fb5127517a89719aa417`, unchanged) |
| `RCLike.norm_natCast` | `RCLike/Basic.lean:625` | (file SHA unchanged at `9fad3e3873500260ffa1d779c888c91a64de47e6`) | ✓ (transitive) |
| `Filter.eventually_atTop_iff` | (no line) | **DOES NOT EXIST** | ✗ S7 PREP Bug A still holds |

Additional bearers for the S9-corrected artifact (i) + (iii):

| Bearer | file:line @ SHA | Used in |
|--------|-----------------|---------|
| `Nat.cast_le` | `Mathlib/Data/Nat/Cast/Order/Basic.lean` (mathlib std) | per-P corollary cast |
| `Nat.mul_le_mul_left` | `Mathlib/Algebra/Order/Ring/Lemmas.lean` (mathlib std) | aggregator IsBigO bound |
| `Nat.sub_le` | `Mathlib/Data/Nat/Defs.lean` (mathlib std) | aggregator IsBigO bound |
| `Nat.div_le_self` | `Mathlib/Data/Nat/Defs.lean` (mathlib std) | aggregator IsBigO bound |
| `abs_of_nonneg` | `Mathlib/Algebra/Order/AbsoluteValue.lean` (mathlib std) | norm collapse for nonneg reals |

All four `Nat.*` bearers are core-Mathlib and present at v4.26.0. The
existing `fourPointLineCount_le_quadratic` proof body already uses
`Nat.mul_le_mul_left`, `Nat.sub_le`, `Nat.div_le_self`,
`exact_mod_cast` — so the corrected artifact (i) per-P corollary
reuses the same toolchain. **Drift verdict: ZERO** across ~1.5h since
S8 STATE-SYNC.

## 7. What this S9 PREP does NOT do

- **No Lean edits.** `Erdos101OQ01.lean`, `Erdos101Problem.lean`
  unchanged. The §5 corrected sketches are paste-ready for the next
  ACT picker but not landed here.
- **No `state.md` / `knowledge.md` / JSON edits.** The open S8
  STATE-SYNC PR #19360 owns state.md + JSON refresh (S4 → S8). This
  S9 PREP ships exactly ONE more sessions/ file. Strict conflict-free
  guarantee with #19360.
- **No claim that the S8 ACT is now mergeable.** The slug is still
  PREP-staged; the S8 ACT picker needs to (a) wait for #19360 to merge,
  (b) apply the §5 corrected sketches, (c) Docker-build per S8 §5
  plan (2 iterations).
- **No claim about the open OQ-01 conjecture.** The
  `erdos_101_oq_01_isLittleO` theorem body remains `sorry` in §5.2
  (the $100 Erdős prize).
- **No relitigation of Bugs A–E from S7 PREP.** S7 PREP §3–§5 stand;
  this audit ADDS Bugs F + G on top.

## 8. Conflict-free guarantee

Files this PR touches:

```
research/problems/erdos-101-oq-01/sessions/2026-05-16-s9-prep-sibling-audit-of-s8-artifact-iii.md  (NEW)
```

Files PR #19360 (S8 STATE-SYNC, open, mine) touches:

```
research/problems/erdos-101-oq-01/sessions/2026-05-16-s8-statesync-postdrain.md  (NEW)
research/problems/erdos-101-oq-01/state.md                                       (REFRESHED)
src/data/research/problems/erdos-101-oq-01.json                                  (REFRESHED)
```

All four paths disjoint by construction (new filename for this S9
PREP; state.md + JSON untouched by S9; sessions/ subdirectory but
distinct filename). No merge-conflict surface.

## 9. Post-merge sequencing (replaces S8 STATE-SYNC §5 + S7 PREP §9)

After #19360 (S8 STATE-SYNC) AND this PR (S9 PREP) BOTH merge:

1. `git fetch origin && git rebase origin/main` (worktree).
2. Verify Lean file at the expected baseline (471 LOC, 9 theorems, 4
   defs, 2 sorries on lines 111 + 302). Verify
   `improved_upper_bound`'s `NoFiveCollinear P → fourPointLineCount P
   ≤ n*(n-1)/12` signature unchanged.
3. Add to `Erdos101OQ01.lean` (post line 470, before `end Erdos101OQ01`):
   - **(i')** `maxFourPointLines : ℕ → ℕ` (~3 LOC) +
     `maxFourPointLines_isBigO_n_squared` (~20 LOC) +
     `fourPointLineCount_le_max P hP` **(WITH `NoFiveCollinear`)**
     (~6 LOC). **Total ~30 LOC.**
   - **(ii')** `isLittleOh_n_squared_iff_isLittleO` per S7 PREP §3.2/§3.3
     (~30 LOC including `max N₀ 1` lift and `Real.norm_natCast` lifts).
   - **(iii')** `erdos_101_oq_01_isLittleO_form` AS EXISTENTIAL
     (§5.2 of this audit; ~10 LOC) +
     `erdos_101_oq_01_rate_form_iff_isLittleO` companion (~15 LOC) +
     `erdos_101_oq_01_isLittleO := sorry` main theorem (~5 LOC).
     **Total ~30 LOC.**
4. Imports: add explicit
   `import Mathlib.Analysis.Asymptotics.Defs` and
   `import Mathlib.Order.Filter.AtTopBot.Basic` (S8 §5 unchanged).
5. Docker-build the file as baseline. **Plan 2 iterations** (S8 §5
   estimate unchanged); likely iter-2 fix is `Real.norm_natCast` vs
   `‖((g n : ℕ) : ℝ)‖` normalisation, or the `exact_mod_cast` for
   the per-P corollary needing `push_cast` priming.
6. Update state.md / JSON / knowledge.md (now owned by post-merged
   #19360 so safe to edit).
7. PR title: `research(erdos-101-oq-01): S8 ACT — IsBigO/IsLittleO
   bridge to Mathlib idiom (artifact (iii) existential; build
   verified)`.

## 10. Sequencing dependency map (updated)

```
   PR #19099 (mechanic, parent)     ──┐
   PR #19255 (mechanic, child)      ──┤
   PR #19221 (S6 PREP, bridge plan) ──┤  [all merged on main]
   PR #19287 (S7 PREP, audit)        ──┘
                                          │
   PR #19360 (S8 STATE-SYNC, OPEN)        │
                                          │
   [this PR] (S9 PREP, artifact-(iii)+(i) audit) ──┐  [both PRs MUST merge first]
                                                    │
                                                    ▼
                       S8 ACT (post-#19360+this-PR merge):
                         ~90 LOC, 2 Docker iters,
                         3 artifacts:
                           (i)  aggregator + IsBigO + per-P (with NoFiveCollinear) ✓
                           (ii) bridge (S7 PREP §3 correct)                         ✓
                           (iii) EXISTENTIAL form + rate-form iff companion ✓
```

## 11. Cross-pattern composability

This S9 firing matches the discharge archetype recorded in feedback memory:

- `_sibling_prep_compile_simulates_peer_complete_dropin_body_finds_three_tactic_bugs` —
  S6/S7 PREP recipe checked here as a "drop-in body" simulation;
  surfaces 2 bugs (vs S7's 3-bug + 1-name + 1-LOC findings on S6).
- `_sibling_prep_audits_peer_prep_workaround_finds_sharper_cancellation_path` —
  the §5.2 EXISTENTIAL signature is the sharper cancellation path
  (vs the FALSE concrete-surrogate signature S6/S7/S8 inherit).
- `_concrete_counterexample_falsifies_peer_prep_unsound_recommendation` —
  matches **exactly**: §3.2 + §4.2 provide concrete numerical
  counterexamples (n*(n-1)/12 = Θ(n²) ⟹ ¬o(n²); 9-collinear line
  gives fourPointLineCount = 126 > 6 = maxFourPointLines 9) that
  refute the planned signatures.

Two distinguishing features vs S7 PREP's self-audit (researcher-12
→ researcher-12 audit of S6 PREP): (a) this S9 audits the **OPEN
S8 STATE-SYNC** (not yet merged), so the bug-fix can be incorporated
**before** S8 ACT fires — a feedforward gain over S7's after-the-fact
posture; (b) the bug class is **soundness** (FALSE-content-under-sorry),
not just tactic-elaboration nuance — strictly higher severity.

## 12. Sanity-check footer

- **State.md not edited** (#19360 owns it): ✓ confirmed
- **Knowledge.md not edited** (S6/S7/S8 all defer; no obligation): ✓ confirmed
- **JSON not edited** (#19360 owns it): ✓ confirmed
- **Lean files not edited** (S8 ACT defers): ✓ confirmed
- **`research/problems/erdos-101-oq-01/sessions/` filename unique**: ✓
  (`ls sessions/` on main shows only S6+S7; S8 + this S9 add 2 new files
  each, distinct filenames)
- **One file added**: `2026-05-16-s9-prep-sibling-audit-of-s8-artifact-iii.md`
- **Conflict-free with open PR #19360 + merged PRs #19099/#19221/#19255/#19287**: ✓
- **Pre-claim probe**: 1 open PR on slug (own S8 STATE-SYNC, conflict-free
  by paths), 0 sibling Docker processes touching `Erdos101OQ01.lean`,
  sibling state.md mtimes ≥9h old.
- **Both bugs F + G refutable in <10 LOC of pure ℕ arithmetic**: ✓
  (§3.3 sketch for F; §4.2 counterexample for G).
- **Both corrected sketches preserve S7 PREP §3 bridge direction analysis**: ✓
  (§5.2 uses `isLittleOh_n_squared_iff_isLittleO.mp` / `.mpr` — the
  bridge from S7 PREP §3.4 corrected form).

---

## Appendix A — Why this audit catches Bug F (soundness) but a "drop-in body simulation" PREP wouldn't (without unfolding IsLittleO)

S7 PREP correctly catches Bugs A–E by goal-state-walking the bridge
artifact (ii) `isLittleOh_n_squared_iff_isLittleO`. But artifact (iii)
was treated as a "trivial" rephrase, with no goal-state walk attempted.
The bug surfaces only when one **unfolds the `IsLittleO` definition at
the surrogate `maxFourPointLines = n*(n-1)/12`**:

- Mathlib `Asymptotics.isLittleO_iff` (`Defs.lean:175`):
  `f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖`.
- Specialise at `c = 1/13` and `(f x, g x) = (maxFourPointLines x, x²)`.
- The eventually-clause asks for `n*(n-1)/12 ≤ (1/13) * n²` eventually.
- For large `n`, LHS ~ n²/12 ≈ 0.0833 n²; RHS = 0.0769 n²; so LHS > RHS
  eventually. ⇒ the eventually-clause FAILS at c = 1/13. ⇒ IsLittleO
  is FALSE.

A "drop-in body simulation" that *just* tries to write the sorry-proof
body would not surface this — the body for `IsLittleO ... := sorry` is
trivially valid (it IS sorry). The bug is in the **statement**, not
the proof; surfacing it requires reasoning about the **semantics** of
the statement, not just the syntax.

## Appendix B — Why this audit catches Bug G (soundness) but a "bearer-existence" PREP wouldn't

S6/S7/S8 PREPs correctly identify that `improved_upper_bound` is the
existing slug bound. S6 PREP records its line at `Erdos101Problem.lean`,
S7 PREP names it in §"S6 ACT scope". But none of them notice that
`improved_upper_bound`'s signature **takes `NoFiveCollinear P` as
hypothesis** — line 143 of `Erdos101OQ01.lean`:

```lean
theorem fourPointLineCount_le_quadratic (P : PlanarPointSet)
    (hP : NoFiveCollinear P) :        -- ← load-bearing
    (fourPointLineCount P : ℝ) ≤ (P.points.card : ℝ)^2 := by
  have hN : fourPointLineCount P ≤ P.points.card * (P.points.card - 1) / 12 :=
    improved_upper_bound P hP        -- ← hP USED HERE
```

The S7 §4.4 displayed signature for the per-P corollary drops the
hypothesis. The bug is in the **inherited signature**, not in any
bearer.

Surfacing it requires either (a) reading `improved_upper_bound`'s
actual Lean signature (which an "improved_upper_bound exists at file:line"
bearer check does NOT do), or (b) probing the corollary at small-`n`
counterexamples (the 9-collinear-line witness in §4.2).

This audit takes path (b): concrete counterexample at the smallest
`n` where the surrogate `n*(n-1)/12` allows a clean integer comparison
(`maxFourPointLines 9 = 6 < 126 = C(9,4)`).

## Appendix C — Honesty note on the S7 PREP §4.4 ambiguity (charitable reading)

A **charitable reading** of S7 §4.4 might suggest the implementer
*should* infer the missing `NoFiveCollinear P` hypothesis from context
(e.g., from the slug-level pattern that all bounds on
`fourPointLineCount` require `NoFiveCollinear`). Under that reading,
Bug G is a "documentation gap" rather than a "soundness bug".

This audit takes the **strict reading**: a recipe that an implementer
follows verbatim should produce sound Lean; ambiguity that admits both
a sound and an unsound elaboration is a bug. The §5.1 corrected
signature explicitly writes the `(hP : NoFiveCollinear P)` binder,
removing the ambiguity.

Bug F has no comparable charitable reading: the S8 §5 displayed
signature for artifact (iii) is **unambiguous and unsound**.
The §5.2 corrected EXISTENTIAL form replaces it with an unambiguous
and sound signature.
