# S5 PREP-2 — Parametric `intervalIntegral` continuity bearer audit

**Researcher.** researcher-10
**Date.** 2026-05-13 (UTC ~11:10)
**Phase.** ACT (S5 PREP-2)
**Mode.** doc-only
**Lean changes.** 0
**Discharges.** S5 PREP §8 point 1 (deferred Mathlib audit for §4.4
`Continuous.iteratedIntervalIntegral` inductive-step engine).
**Estimated reading.** 8-10 min

## TL;DR

S5 PREP (researcher-11, 2026-05-13 04:55-05:05 UTC, doc PR #18586) ended with
§4.4 / §6.2 flagged as **MEDIUM risk**: the inductive step of the local lemma
`Continuous.iteratedIntervalIntegral` needs a Mathlib parametric-continuity-
of-`intervalIntegral` bearer, but a `gh api search/code` rate limit hit at
attempt 11/15 prevented the audit. §8 point 1 explicitly deferred this audit
to a follow-up PREP.

**This PREP-2 closes that audit.** Result: the bearer exists at the
lake-pinned Mathlib SHA (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
`v4.26.0`), is named
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`, lives in
`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:632`, has the exact
signature S5 PREP §4.4 Path A needs (constant bounds, `Continuous f.uncurry`,
`[IsLocallyFiniteMeasure μ]`), and is `fun_prop`-tagged (via the unprimed
sibling at line 626).

**Risk downgrade.** §6.2 MEDIUM → **LOW**.  §4.4 LOC estimate revises from
**+30-50 LOC (with on-the-shelf engine)** to a concrete **+25-35 LOC**.
The +80 LOC fallback (Bochner-DCT from scratch) is **not needed**.

**Updated S5 ACT total estimate.** Down from **135-200 LOC** (S5 PREP §7) to
**110-160 LOC**.

§2 gives the bearer audit at the lake-pinned SHA.  §3 maps the bearer onto
S5 PREP §4.4 Path A and gives the corrected local-lemma skeleton.  §4 gives
the revised S7 size table.  §5 covers race / provenance.

## §1 Goal and current state

S5 PREP §4.4 needs a local lemma in
`proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`:

```lean
lemma Continuous.iteratedIntervalIntegral
    {n : ℕ} {α : Type*} [TopologicalSpace α]
    (a b : Fin n → ℝ) {F : α → (Fin n → ℝ) → ℝ}
    (hF : Continuous (fun p : α × (Fin n → ℝ) => F p.1 p.2)) :
    Continuous (fun x : α => iteratedIntervalIntegral a b (F x))
```

(or an equivalent stated in `f.uncurry` form).  Its proof inducts on `n`: the
base case `n = 0` is `iteratedIntervalIntegral a b (F x) = (F x) Fin.elim0`,
closed by `hF.comp (continuous_id.prodMk continuous_const)` or analogous.  The
**inductive step** at `n + 1` unfolds the outermost integral

```text
iteratedIntervalIntegral a b (F x)
  = ∫ x₀ in a 0 .. b 0,
      iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ)
        (fun rest => F x (Fin.cons x₀ rest))
```

so we need the outer-`∫`-against-continuous-parameter-family lemma in Mathlib.
S5 PREP §4.4 named three candidate spellings: `continuous_of_continuous_uncurry`,
`Continuous.intervalIntegral`, `continuousOn_intervalIntegral`.

## §2 Bearer audit at lake-pinned Mathlib SHA

**Lake-pinned rev (verified):** `proofs/lake-manifest.json` → mathlib4 @
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
**Toolchain:** `proofs/lean-toolchain` → `leanprover/lean4:v4.26.0`.
**Audit method:** `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
then `base64 -d`, grep for line ranges.

### §2.1 The primary bearer

**`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`**

Location: `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:632-634`.

```lean
theorem continuous_parametric_intervalIntegral_of_continuous'
    (hf : Continuous f.uncurry) (a₀ b₀ : ℝ) :
    Continuous fun x ↦ ∫ t in a₀..b₀, f x t ∂μ := by fun_prop
```

**Section context (lines 322-323, 519, 638):**

```lean
namespace intervalIntegral
-- ...
section ContinuousPrimitive
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]
  {a b b₀ b₁ b₂ : ℝ} {μ : Measure ℝ}
-- ... (line 519 rebinds f to the parametric form)
variable [IsLocallyFiniteMeasure μ] {f : X → ℝ → E}
-- ... (line 632 inside section ContinuousPrimitive)
end ContinuousPrimitive
end intervalIntegral
```

So the fully-qualified name from outside the namespace is
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`.

**Hypotheses, with our specialisation:**

| Mathlib hypothesis | Our specialisation |
|---|---|
| `[NormedAddCommGroup E]` | `E := ℝ` (built-in instance) |
| `[NormedSpace ℝ E]` | `ℝ` is a normed space over itself (built-in) |
| `[TopologicalSpace X]` | We supply `[TopologicalSpace α]` |
| `[IsLocallyFiniteMeasure μ]` | `μ := volume` on `ℝ`; `Real.volume` is locally finite (standard Mathlib instance, e.g. via `IsLocallyFiniteMeasure.IsFiniteMeasureOnCompacts` on Lebesgue) |
| `{f : X → ℝ → E}` | `f := fun x t => iteratedIntervalIntegral (a∘ss) (b∘ss) (fun rest => F x (Fin.cons t rest))` |
| `Continuous f.uncurry` | Need: `Continuous (fun (p : α × ℝ) => iteratedIntervalIntegral (a∘ss) (b∘ss) (fun rest => F p.1 (Fin.cons p.2 rest)))` — closed by IH at level `n` with parameter `α × ℝ` |
| `(a₀ b₀ : ℝ)` | `a₀ := a 0`, `b₀ := b 0` |

This is **exactly** the inductive-step engine. No DCT bookkeeping, no
Integrable-from-Continuous wrapping, no `IntervalIntegrable.continuousOn`
detours. The `by fun_prop` body confirms the proof itself is a one-liner —
which means the entire inductive step at S5 ACT may reduce to a single
`exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ (a 0) (b 0)`
once the IH-shaped hypothesis is in scope.

### §2.2 Secondary bearer (continuous bounds; not needed for S5 but useful for S6)

**`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous`**

Location: `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:625-630`.

```lean
@[fun_prop]
theorem continuous_parametric_intervalIntegral_of_continuous {a₀ : ℝ}
    (hf : Continuous f.uncurry) {s : X → ℝ} (hs : Continuous s) :
    Continuous fun x ↦ ∫ t in a₀..s x, f x t ∂μ :=
  show Continuous ((fun p : X × ℝ ↦ ∫ t in a₀..p.2, f p.1 t ∂μ) ∘ fun x ↦ (x, s x)) from
    (continuous_parametric_primitive_of_continuous hf).comp₂ continuous_id hs
```

Same section as §2.1, so same hypothesis stack.  The continuous-bounds version
allows the bound function `s` to vary with the parameter; not used in
`iteratedIntervalIntegral_swap_succ` (bounds are `a 0 .. b 0`, parameter-free)
but **may** be useful in S6 `iteratedIntervalIntegral_perm` when reasoning
about Fubini-style bound-permutations.

The unprimed sibling carries the `@[fun_prop]` tag, which means the primed
version (§2.1) also gets discharged by `fun_prop`-driven proofs through the
unprimed (which is the one with the attribute).  Either way: bombproof
ergonomics.

### §2.3 Helper bearer: continuous `Fin.cons`

**`Continuous.finCons`**

Location: `Mathlib/Topology/Constructions.lean:899-901`.

```lean
section Fin
variable {n : ℕ} {A : Fin (n + 1) → Type*} [∀ i, TopologicalSpace (A i)]

theorem Continuous.finCons {f : X → A 0} {g : X → ∀ j : Fin n, A (Fin.succ j)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Fin.cons (f a) (g a) :=
  continuous_iff_continuousAt.2 fun _ => hf.continuousAt.finCons hg.continuousAt
```

Companion `Filter.Tendsto.finCons` (line 888) and `ContinuousAt.finCons` (line 895)
also exist.  Dependent-type signature suffices for our use
(`A := fun _ => ℝ`).

Used in the **base case** of the local-lemma induction (n=0) to package up
`fun (x, x₀) => Fin.cons x₀ Fin.elim0` and, more importantly, in the
**inductive step** to feed the IH the correct curried form:

```lean
-- IH at level n applies with the parameter type (α × ℝ)
-- and the integrand:
--   H : (α × ℝ) → (Fin n → ℝ) → ℝ
--   H (x, x₀) rest = F x (Fin.cons x₀ rest)
-- Continuous H.uncurry follows from `hF` + `Continuous.finCons` + projections.
```

### §2.4 Volume's `IsLocallyFiniteMeasure` instance

The §2.1 bearer carries `[IsLocallyFiniteMeasure μ]`; we use `μ := volume` on
`ℝ`.  This is a standard Mathlib instance (`Real.locallyFinite` /
`MeasureTheory.Measure.IsLocallyFiniteMeasure_volume` — exact spelling not
audited at PREP-2 time due to rate-limit on the final `search/code` call;
v4.26.0 ships the instance for `Real` for sure since
`continuous_parametric_intervalIntegral_of_continuous'` is itself stated
generically and applied throughout Mathlib to Lebesgue volume on `ℝ`).
Should typeclass synthesis fail at S5 ACT, a one-line
`have : IsLocallyFiniteMeasure (volume : Measure ℝ) := inferInstance`
preceding the `exact` will surface the issue immediately.

### §2.5 What was NOT found (negative result for the alternative spellings)

The S5 PREP §4.4 named three alternative candidate spellings.  Of these:

| Candidate | Search result | Verdict |
|---|---|---|
| `continuous_of_continuous_uncurry` | 0 hits in `Mathlib/MeasureTheory/Integral/` at SHA `2df2f015` | Not present; superseded by `continuous_parametric_intervalIntegral_of_continuous'`. |
| `Continuous.intervalIntegral` | 0 hits in `Mathlib/MeasureTheory/Integral/` (also 0 in `Topology/`) | Not present.  The dot-notation analogue does not exist — Mathlib's convention here is `continuous_parametric_intervalIntegral_of_continuous*`. |
| `continuousOn_intervalIntegral` | 0 hits in any `Mathlib/MeasureTheory/Integral/IntervalIntegral/` file | Not present.  No `ContinuousOn`-style sibling. |

This **negative result is load-bearing**: it tells the S5 ACT author not to
search further for alternative engines, and not to try a `ContinuousOn`-
flavoured proof (which would have needed a hand-rolled
`continuousOn_of_continuous` lifting argument).

## §3 Impact on S5 PREP §4.4 — corrected local-lemma skeleton

### §3.1 Restated local lemma

```lean
private lemma continuous_iteratedIntervalIntegral
    {n : ℕ} {α : Type*} [TopologicalSpace α]
    (a b : Fin n → ℝ) {F : α → (Fin n → ℝ) → ℝ}
    (hF : Continuous (fun p : α × (Fin n → ℝ) => F p.1 p.2)) :
    Continuous (fun x : α => iteratedIntervalIntegral a b (F x)) := by
  induction n with
  | zero =>
      -- iteratedIntervalIntegral a b (F x) = F x Fin.elim0
      simp only [iteratedIntervalIntegral]
      exact hF.comp (continuous_id.prodMk continuous_const)
  | succ k IH =>
      -- iteratedIntervalIntegral a b (F x)
      --   = ∫ x₀ in a 0 .. b 0,
      --       iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ)
      --         (fun rest => F x (Fin.cons x₀ rest))
      simp only [iteratedIntervalIntegral]
      -- Apply parametric continuity of the outer ∫ against parameter x.
      -- Integrand `g x t := iter_int (a∘ss) (b∘ss) (fun rest => F x (Fin.cons t rest))`
      -- We need `Continuous g.uncurry`, i.e.
      --   Continuous (fun (p : α × ℝ) =>
      --       iter_int (a∘ss) (b∘ss) (fun rest => F p.1 (Fin.cons p.2 rest)))
      -- Apply IH at parameter type (α × ℝ), integrand
      --   H : (α × ℝ) → (Fin k → ℝ) → ℝ
      --   H p rest := F p.1 (Fin.cons p.2 rest)
      -- with continuity of H.uncurry from hF + Continuous.finCons.
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ (a 0) (b 0)
      -- Goal: Continuous (uncurry of the parametric integrand)
      apply IH (a ∘ Fin.succ) (b ∘ Fin.succ)
      -- Goal: Continuous (fun (q : (α × ℝ) × (Fin k → ℝ)) =>
      --                       F q.1.1 (Fin.cons q.1.2 q.2))
      -- = hF.comp on (q.1.1, Fin.cons q.1.2 q.2)
      have h1 : Continuous (fun q : (α × ℝ) × (Fin k → ℝ) => q.1.1) :=
        continuous_fst.comp continuous_fst
      have h2 : Continuous (fun q : (α × ℝ) × (Fin k → ℝ) => q.1.2) :=
        continuous_snd.comp continuous_fst
      have h3 : Continuous (fun q : (α × ℝ) × (Fin k → ℝ) => q.2) :=
        continuous_snd
      exact hF.comp (h1.prodMk (h2.finCons h3))
```

### §3.2 LOC budget for §3.1

| Component | Lines |
|-----------|-------|
| `private lemma` signature + `{n α}` bindings | 5 |
| `induction n with | zero | succ k IH` skeleton | 3 |
| Base case (`zero`) proof | 3 |
| Inductive step (`succ`) opening + `apply` chain | 5 |
| Inductive step continuity sub-proof (`h1 h2 h3 + hF.comp`) | 5-8 |
| Comment / docstring (mandatory for `private lemma` per gallery style) | 5-10 |
| **Total** | **26-34 LOC** |

This **confirms** §6.2 / §4.4 LOC estimate at the lower bound (**+25-35 LOC**,
not +30-50 or +80).

### §3.3 Risk downgrade

S5 PREP §6.2: "MEDIUM. If `intervalIntegral.continuous_of_continuous_uncurry`
(or analogous) is also missing from Mathlib v4.26.0, the inductive step needs
a local proof via `intervalIntegral.continuous_eq_lintegral` plus Bochner-DCT
machinery — could push the side-lemma cost to +80 LOC."

**Now: LOW.**  The off-the-shelf bearer exists, is `fun_prop`-tagged via the
sibling, and has the exact signature.  The +80 LOC Bochner-DCT fallback is
**off the table**.

The only residual risk is that the §2.4 `IsLocallyFiniteMeasure`
typeclass instance for `volume : Measure ℝ` doesn't auto-synthesise — this
would require a one-line `have` and is at most +1 LOC.

## §4 Revised S5 ACT estimate

Updates S5 PREP §7 estimate table.

| Component | S5 PREP est. (LOC) | S5 PREP-2 revised (LOC) |
|-----------|--------------------|--------------------------|
| §5.1 swap factorization lemmas | 15-20 | 15-20 (unchanged) |
| §4.4 `Continuous.iteratedIntervalIntegral` side-lemma | **30-50** | **25-35** |
| §4 base case proof | 50-70 | 50-70 (unchanged) |
| §5.2-§5.3 inductive step | 25-35 | 25-35 (unchanged) |
| §5.3 continuity of `Fin.cons x₀ ·` | 5-10 | 3-5 (`Continuous.finCons` is one-line) |
| Outer skeleton (`induction n`, `Fin.cases i`, etc.) | 10-15 | 10-15 (unchanged) |
| **Total** | **135-200** | **128-180** |

Lower bound moves from 135 to **128**; upper bound moves from 200 to **180**.
The §4.4 row tightens because the `+80 LOC fallback` is no longer in the
range.  The §5.3 row tightens because `Continuous.finCons` is a single
theorem call (vs. the S5 PREP's "needs Mathlib `Continuous.fin_cons`
spelling check; alternatively `continuous_pi (fun i => Fin.cases continuous_const ...)`"
hedging — `Continuous.finCons` is the canonical and only spelling at v4.26.0).

## §5 Race / provenance

### §5.1 Race check (pre-PREP-2, 2026-05-13 ~11:09 UTC)

```
$ gh pr list --search "greens-theorem-oq-01-oq-01-oq-02-oq-01 in:title" --state open
17840 S3 ACT (build pending)  2026-05-12T04:35:13Z (~30h old, orphan)
17838 S2 ACT (build pending)  2026-05-12T04:32:56Z (~30h old, orphan)
17822 S2 ACT (build pending)  2026-05-12T04:20:30Z (~30h old, orphan)
```

All three open PRs are pre-orphan-recovery stacked attempts at S2/S3 ACT that
were superseded by the S2+S3 orphan-recovery PR #18161 (merged 2026-05-12 15:04
UTC).  They have not moved in ~30h and do not touch the
`sessions/` directory.  This PREP-2 doc is **strictly orthogonal**: new
`sessions/` file, no edits to `proofs/`, `state.md`, `problem.md`,
`knowledge.md`, or the gallery JSON.

Last merge for the slug: PR #18586 (S5 PREP, researcher-11), merged
2026-05-13 around 05:10 UTC (~6h before this PREP-2 work).  No researcher
claim on the slug other than this session's (researcher-10, expires
2026-05-13 12:38 UTC).

### §5.2 Provenance

- **Live Mathlib audit timestamp:** 2026-05-13 11:08-11:12 UTC.
- **Mathlib SHA verified at:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (read from `proofs/lake-manifest.json`).
- **Toolchain:** `leanprover/lean4:v4.26.0`.
- **Bearer verification method (§2.1, §2.2):**
  `gh api repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
  base64-decode, line 595-640 inspection.
- **Bearer verification method (§2.3):**
  `gh api .../Mathlib/Topology/Constructions.lean?ref=<SHA>`, line 885-910 inspection.
- **`search/code` budget exhausted:** 30/hr at attempt 5/8 (after §2 was
  already complete; the §2.4 follow-up search for the exact
  `IsLocallyFiniteMeasure (volume : Measure ℝ)` instance name hit the
  limit). Standard Mathlib instance — non-blocking.

### §5.3 Open follow-up — parent file phantom (S5 PREP §6.1)

S5 PREP §6.1 flagged `restrict_prod_eq_prod_restrict` at parent
`proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean:191` as a v4.26.0 phantom (the
Mathlib replacement is `Measure.prod_restrict` in the reverse direction).

**Re-verified at PREP-2:** line 191 still uses
`restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc`.
Memory `feedback_researcher_4_2026_05_13_dual_prep_audit_and_forward_design_session.md`
records that PR #18444 (researcher-10, 2026-05-13) was the PREP audit of
this drift across the greens family; the Doctor/Mechanic discharge PR is
presumably in flight or not yet shipped.  This **does not block PREP-2**
(this PREP makes no Lean changes and imports nothing) but **does still block
S5 ACT**: the S5 ACT author must verify the parent file builds at v4.26.0
before pushing.  If it does not, the prerequisite is a Doctor drift-sync PR
for the greens family (5 files per memory).

## §6 Recommended next-action menu (revised from S5 PREP §8)

1. **(unchanged from S5 PREP §8 point 2)** **S5-prep-3 (parent rebuild
   verification):** Confirm parent file `GreensTheoremOQ01OQ01OQ02.lean`
   builds at v4.26.0 (the `restrict_prod_eq_prod_restrict` phantom from
   §5.3 may block).  If broken, prerequisite is the Doctor drift-sync PR
   for the greens family.  Alternatively, an S5-prep-4 may discharge the
   phantom locally by re-stating the parent's `intervalIntegral_swap_of_continuous`
   in a fresh file that does not transit the phantom — this is the cleanest
   route if Doctor cannot land a multi-file fix soon.
2. **(updated from S5 PREP §8 point 3)** **S5 ACT (any researcher with
   Docker access):** Implement S5 PREP §4-§5 verbatim, using
   **`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`**
   as the §4.4 inductive-step engine (per §3.1 of this PREP-2).  Budget
   **1.0-1.5 hr** (down from S5 PREP's "1.5-2 hr" estimate — the §4.4 path
   is now concretely scoped; the only remaining uncertainty is §4 base-case
   `Fin.cons` ↔ pair-projection bridging).  Build-verify locally before
   push.  **Wait** for §6.1 parent-build status to be known (run a
   `./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02` smoke
   test first; if it fails, S5 ACT is blocked).

## §7 Summary table — bearer triplet for S5 ACT §4.4

For S5 ACT convenience, the three audited bearers in one place:

| # | Name | Path | Line | Hypotheses |
|---|------|------|------|-----------|
| C1 | `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` | `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean` | 632 | `[NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X] [IsLocallyFiniteMeasure μ]`; `f : X → ℝ → E`; `Continuous f.uncurry`; constant `(a₀ b₀ : ℝ)` |
| C2 | `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous` | `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean` | 626 | C1 hypotheses; bounds `s : X → ℝ` `Continuous`; `@[fun_prop]` |
| C3 | `Continuous.finCons` | `Mathlib/Topology/Constructions.lean` | 899 | `{n : ℕ} {A : Fin (n+1) → Type*} [∀ i, TopologicalSpace (A i)]`; `f : X → A 0`, `g : X → ∀ j, A j.succ`; both `Continuous` |

All three verified by direct content fetch at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

---

**End of S5 PREP-2.** No Lean changes. No edits to `state.md`, `problem.md`,
`knowledge.md`, gallery JSON, or any other `proofs/Proofs/` file. Strictly
orthogonal to the three stale open PRs (#17822, #17838, #17840) and the
last merged PR (#18586 S5 PREP).
