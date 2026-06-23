# S1 OBSERVE — Mathlib bearer audit for `variance_sampleMean` axiom (researcher-5, 2026-05-13)

**Slug**: `laws-of-large-numbers-oq-02`
**Phase**: S1 OBSERVE (doc-only audit + Lean recipe; no Lean changes in this PR)
**Mathlib SHA (pinned)**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
**Lean file**: `proofs/Proofs/LawsOfLargeNumbersOQ02.lean` (338 LOC, 0 sorries, 3 axioms)

## Goal of this OBSERVE

Document that the `variance_sampleMean` axiom at line 114 of
`LawsOfLargeNumbersOQ02.lean` is **not Mathlib-blocked** and can be discharged in ~25 LOC
using two existing Mathlib bearers. Distinguish this from the other two axioms in the same
file (`standardNormalCDF`, `berryEsseenConstant`) which **are** genuinely beyond Mathlib
v4.26.0 (the CLT and Berry–Esseen theorems have no Mathlib formalization).

## Audit findings (per-axiom)

| Axiom | Line | Status | Mathlib bearer |
|---|---|---|---|
| `variance_sampleMean` | 114 | **Derivable** | `IndepFun.variance_sum` + `variance_smul` |
| `standardNormalCDF : ℝ → ℝ` | 217 | Genuinely beyond | Gaussian *density* exists; no named CDF map |
| `berryEsseenConstant : ℝ` | 240 | Genuinely beyond | No Berry–Esseen statement in Mathlib |

## The `variance_sampleMean` recipe

### Mathlib bearers (verified at SHA `2df2f01...`)

Both in `Mathlib/Probability/Moments/Variance.lean`:

```lean
-- Line ~403 of Variance.lean
nonrec theorem IndepFun.variance_sum {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι}
    (hs : ∀ i ∈ s, MemLp (X i) 2 μ)
    (h : Set.Pairwise ↑s fun i j => X i ⟂ᵢ[μ] X j) :
    variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ

-- Line ~194 of Variance.lean
theorem variance_smul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    Var[c • X; μ] = c^2 * Var[X; μ]
```

`Var[·; μ]` is notation for `variance · μ`; `⟂ᵢ[μ]` is notation for `IndepFun · · μ`.

### The slug's axiom (verbatim, line 114)

```lean
axiom variance_sampleMean
    (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 0 < n)
    (σ_sq : ℝ) (hσ : σ_sq ≥ 0)
    (h_var : ∀ i, variance (X i) volume = σ_sq)
    (hℒp : ∀ i, MemLp (X i) 2 volume)
    (h_indep : Pairwise fun i j => IndepFun (X i) (X j) volume) :
    variance (sampleMean X n) volume = σ_sq / n
```

And `sampleMean` is defined earlier as `sampleMean X n ω = (1 / (n : ℝ)) · ∑ i ∈ Finset.range n, X i ω`.

### Derivation (informal)

```
Var(X̄ₙ)
  = Var((1/n) · ∑ᵢ ∈ range n, Xᵢ)                     [defn of sampleMean]
  = (1/n)² · Var(∑ᵢ ∈ range n, Xᵢ)                    [variance_smul]
  = (1/n)² · ∑ᵢ ∈ range n, Var(Xᵢ)                     [IndepFun.variance_sum]
  = (1/n)² · ∑ᵢ ∈ range n, σ²                          [h_var]
  = (1/n)² · n · σ²                                    [Finset.sum_const + card_range]
  = σ² / n                                             [arithmetic]
```

### Lean recipe (~25 LOC, target for S2 ACT)

```lean
/-- **Variance of the sample mean** (proved from Mathlib v4.26 bearers).
    Was previously `variance_sampleMean : axiom`; discharged via
    `IndepFun.variance_sum` + `variance_smul`. -/
theorem variance_sampleMean
    (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 0 < n)
    (σ_sq : ℝ) (hσ : σ_sq ≥ 0)
    (h_var : ∀ i, variance (X i) volume = σ_sq)
    (hℒp : ∀ i, MemLp (X i) 2 volume)
    (h_indep : Pairwise fun i j => IndepFun (X i) (X j) volume) :
    variance (sampleMean X n) volume = σ_sq / n := by
  -- 1. Unfold sampleMean = (1/n) · ∑
  unfold sampleMean
  -- 2. Pull (1/n) out via variance_smul; result has factor (1/n)²
  have hsmul : variance (fun ω => (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, X i ω) volume
      = (1 / (n : ℝ))^2 * variance (fun ω => ∑ i ∈ Finset.range n, X i ω) volume := by
    -- variance_smul, after rewriting `c * f` as `c • f`
    simpa [smul_eq_mul] using variance_smul (1 / (n : ℝ))
      (fun ω => ∑ i ∈ Finset.range n, X i ω) volume
  -- 3. Apply IndepFun.variance_sum on Finset.range n
  have hpair :
      Set.Pairwise ↑(Finset.range n) fun i j => IndepFun (X i) (X j) volume := by
    intro i hi j hj hij
    exact h_indep hij
  have hLp_set : ∀ i ∈ Finset.range n, MemLp (X i) 2 volume :=
      fun i _ => hℒp i
  have hvar_sum :
      variance (fun ω => ∑ i ∈ Finset.range n, X i ω) volume
      = ∑ i ∈ Finset.range n, variance (X i) volume := by
    -- Note: ∑ᵢ X i = (∑ᵢ X i) as functions; Mathlib's variance_sum may need
    -- a `Finset.sum_apply`-style rewrite first.
    simpa [Finset.sum_apply] using IndepFun.variance_sum hLp_set hpair
  -- 4. Substitute h_var to get ∑ σ_sq = n · σ_sq
  rw [hsmul, hvar_sum]
  simp_rw [h_var]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- 5. Algebra: (1/n)² · n · σ² = σ² / n
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring
```

### Subtleties for the S2 ACT author

1. **`Pairwise` (ℕ-indexed) vs `Set.Pairwise` (on `Finset.range n`)**: the slug's
   `h_indep : Pairwise fun i j => IndepFun (X i) (X j) volume` is over all of `ℕ × ℕ`,
   which is *strictly stronger* than `Set.Pairwise ↑(Finset.range n) …`. So the converson
   `hpair` is one direction only: just unpack and apply. The `simpa` in `hvar_sum` will
   take care of unwrapping `∑ᵢ X i ω` to `(∑ᵢ X i) ω` via `Finset.sum_apply`.

2. **`smul_eq_mul` rewrite**: `variance_smul` is stated with `•`; the slug's `sampleMean`
   uses `*`. A single `simpa [smul_eq_mul]` bridges them.

3. **`field_simp` + `ring`** are sufficient for the final algebra given `hn0`.

4. **No new imports**: `Mathlib.Probability.Moments.Variance` is already imported via
   `Mathlib.Probability.Moments.Variance` (the slug already uses
   `variance (X i) volume`, so the file is transitively in scope).

### Build risk

- **LOC**: ~25 lines.
- **Tactics**: `unfold`, `simpa`, `simp_rw`, `rw`, `field_simp`, `ring`, `Nat.cast_ne_zero`,
  `Finset.sum_const`, `Finset.card_range`, `nsmul_eq_mul`. All cheap.
- **No new typeclasses, no new instances.**
- **Sorries delta**: 0 → 0.
- **Axiom delta**: 3 → 2 if S2 ACT succeeds (the axiom becomes a theorem).
- **Worktree `.lake` symlink loop**: build from main repo cwd via
  `./proofs/scripts/docker-build.sh Proofs.LawsOfLargeNumbersOQ02`. Expected ~5–10 min
  (heavier dependency footprint than `BinaryGcdOQ01`).

## CLT / Berry–Esseen status (confirmed beyond Mathlib v4.26)

Mathlib's `Mathlib/Probability/` directory at SHA `2df2f01...` contains:

```
Probability/
├── Decision/   Distributions/   Independence/   Kernel/
├── Martingale/   Moments/   ProbabilityMassFunction/   Process/
├── BorelCantelli.lean   CDF.lean   CondVar.lean   ConditionalExpectation.lean
├── ConditionalProbability.lean   Density.lean   HasLaw.lean   HasLawExists.lean
├── IdentDistrib.lean   IdentDistribIndep.lean   Integration.lean
├── Notation.lean   ProductMeasure.lean   StrongLaw.lean   UniformOn.lean
```

Notably absent: any file named `CentralLimit*`, `Berry*`, `Esseen*`. The
`Probability/Independence/CharacteristicFunction.lean` file proves the *equivalence*
`IndepFun ↔ joint χ = product of χᵢ` but does not extend this to a CLT statement. The
`Probability/Distributions/Gaussian/` directory exposes the Gaussian *measure* and density,
not a `standardNormalCDF : ℝ → ℝ` function.

**Conclusion**: the slug's `standardNormalCDF` and `berryEsseenConstant` axioms are
genuinely beyond Mathlib v4.26 and would require new upstream infrastructure (or a local
multi-hundred-LOC port) to discharge. They are *legitimately* axiomatized, in contrast to
`variance_sampleMean`.

## Files this OBSERVE adds

- `research/problems/laws-of-large-numbers-oq-02/problem.md` (NEW; was missing)
- `research/problems/laws-of-large-numbers-oq-02/state.md` (NEW; was missing)
- `research/problems/laws-of-large-numbers-oq-02/knowledge.md` (NEW; was missing)
- `research/problems/laws-of-large-numbers-oq-02/s1-observe-variance-sampleMean-bearer-audit.md`
  (NEW; this note)
- `research/problems/laws-of-large-numbers-oq-02/literature/` (NEW empty dir scaffold)

The `research/problems/laws-of-large-numbers-oq-02/` directory **did not exist** before
this PR — both the Lean file (`LawsOfLargeNumbersOQ02.lean`) and the gallery entry
(`src/data/proofs/laws-of-large-numbers-oq-02/`, still missing) were managed without the
usual seeker-init scaffold.

## Out of scope for this OBSERVE

- The actual S2 ACT (replacing the `variance_sampleMean` axiom with a theorem). Recipe
  given but not implemented — would require Docker build verification.
- Gallery entry creation (`src/data/proofs/laws-of-large-numbers-oq-02/meta.json` etc.).
  This is the enricher's domain.
- The CLT / Berry–Esseen axioms (genuinely beyond Mathlib v4.26).

## Audit-trail notes

- Memory trap `feedback_researcher_mathlib_head_vs_lockfile_sha_drift.md` followed:
  Mathlib decls verified at lake-pinned SHA `2df2f01...`, not Mathlib HEAD.
- `gh api search/code` rate limit (30/hr per memory trap
  `feedback_researcher_4_2026_05_13_dual_prep_audit_and_forward_design_session.md`): NOT
  invoked in this audit — file structure used `git/trees ?recursive=1` (one request,
  navigates to all paths) and direct `contents/.../*.lean?ref=` (already known paths).
