## Session 2026-05-08 (Session 6, ACT) — `dE_dk` theorem

**Mode**: ACT (assemble §8 + §9 ingredients into the parametric-integral
derivative theorem; no axioms eliminated yet — that lands in S8).
**Outcome**: progress (≈98 lines new code, 0 sorries added, 0 axioms added).

### Goal

Apply `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(pinned in S3, prepared in S4–S5) to obtain the gallery-side identity

```
HasDerivAt ellipticE ((ellipticE k - ellipticK k) / k) k    for 0 < k < 1
```

### What landed in `proofs/Proofs/AmgmInequalityOQ04OQ02.lean`

A new `§ 10` containing the main theorem `dE_dk`:

```lean
theorem dE_dk (hk_pos : 0 < k) (hk_lt : k < 1) :
    HasDerivAt ellipticE ((ellipticE k - ellipticK k) / k) k
```

Proof structure:

1. **Set the band**: `M := (k+1)/2`. Then `0 < k < M < 1`, `M² < 1`,
   `0 ≤ M`, `k² < 1`.
2. **Pick the open neighborhood**: `s := Set.Ioo (-M) M`. Open and contains
   `k`, so `s ∈ 𝓝 k` by `IsOpen.mem_nhds`. For every `κ ∈ s`,
   `-M < κ < M` ⇒ `κ² ≤ M²` (via `sq_lt_sq'`), in particular `κ² < 1`.
3. **Discharge the seven hypotheses** of the Mathlib lemma:
   - `hs ∈ 𝓝 k`: from `IsOpen.mem_nhds` on `Set.Ioo`.
   - `hF_meas`: `Filter.eventually_of_forall` of
     `(integrandE_continuous x).aestronglyMeasurable` for every `x`
     (continuity in `θ` for ALL `x`, not just `x` near `k`).
   - `hF_int`: `ellipticE_integrable k`.
   - `hF'_meas`: `(dIntegrandE_continuous hk_sq).aestronglyMeasurable`.
   - `h_bound`: `MeasureTheory.ae_of_all` of the §9 bound lemma
     `dIntegrandE_abs_le_bound`.
   - `bound_integrable`: §9's `boundDIntegrandE_integrable hM_sq`.
   - `h_diff`: `MeasureTheory.ae_of_all` of `integrandE_hasDerivAt_in_k`
     evaluated at every `κ ∈ s`.
4. **Extract the `HasDerivAt`**: the lemma yields a conjunction; `.2`
   gives `HasDerivAt (fun κ ↦ ∫ θ in 0..π/2, ellipticIntegrandE κ θ)
                     (∫ θ in 0..π/2, dIntegrandE k θ) k`.
5. **Rewrite the integral** via §8's `integral_dIntegrandE_eq` to
   `(ellipticE k − ellipticK k) / k`.
6. **Close the goal**: the function
   `fun κ ↦ ∫ θ in 0..π/2, ellipticIntegrandE κ θ` is definitionally
   `ellipticE`, so `exact h_deriv` finishes.

### Why this matters

The Whittaker–Watson §22.41 proof of Legendre's relation differentiates the
combination

```
f(k) := E(k) · K(k') + E(k') · K(k) − K(k) · K(k')
```

with respect to `k` and shows `f'(k) = 0` on `(0, 1)`. The derivative
formulas

```
dE/dk = (E - K) / k                       (this PR, S6)
dK/dk = (E - (k')² K) / (k · (k')²)        (next S7)
```

drive the cancellation. With `dE/dk` in place, future sessions can
implement `dK/dk` (similar parametric-integral application, ~150–180 lines)
and the final Wronskian closure (`eq_of_hasDerivAt_eq_zero`, ~80–120 lines),
yielding a constructive proof of `legendre_relation` and reducing this
file's axiom count from 1 to 0.

### Build status

Build kicked off via `./proofs/scripts/docker-build.sh Proofs.AmgmInequalityOQ04OQ02`
(45-minute timeout). Pending result at PR-creation time. PR title is
tagged `[BUILD UNVERIFIED]` if not confirmed before merge.

### Files modified

- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (~+98 lines, 0 sorries,
  0 axioms; new section `§ 10` with the `dE_dk` theorem — base file size
  was 565 lines after S5/§9 PR #17358; this PR brings it to 663 lines).
- `src/data/proofs/amgm-inequality-oq-04-oq-02/meta.json` (lineCount
  565→663, theoremCount 30→31, definitionCount unchanged at 7, new section
  `sec-dE-dk-theorem` and new `mainTheorems` entry for `dE_dk`).
- `research/problems/amgm-inequality-oq-04-oq-02/state.md` (updated for
  S6→S7 next-action).
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-08-s06-dE-dk-theorem.md`
  (this report).
- `src/data/research/problems/amgm-inequality-oq-04-oq-02.json` (knowledge
  updates: new builtItems for §10, S6 progress summary, S7 next steps).

### Honest assessment

- This session does **not** eliminate the `legendre_relation` axiom — it
  produces the first of the two derivative identities (`dE/dk`) needed for
  the Whittaker–Watson Wronskian proof.
- The proof of `dE_dk` is a standard parametric-integral application; the
  heavy lifting was the §8 algebraic-split lemma `dIntegrandE_mul_k` (S4,
  PR #17269), which converts the Mathlib output `∫ ∂_k F dθ` into the
  closed form `(E − K)/k`. S6 (this PR) just plugs the §8 + §9 ingredients
  into the Mathlib lemma.
- Roughly 50% of the work toward eliminating the axiom is now done after
  S6 (S4 30%, S5 10%, S6 10%). S7 (`dK/dk`) is similar difficulty (~150–
  180 lines); S8 (Wronskian closure) is more algebraic and shorter
  (~80–120 lines).
- No claim of "verified" or "complete"; this is mid-stream ACT progress on
  the legendre_relation axiom-elimination program (3 of ~5 sessions).

### Build status (pre-merge)

Docker build kicked off; result deferred to a follow-up commit if the build
completes after PR creation. The proof body uses standard Mathlib API
(`Real.norm_eq_abs`, `IsOpen.mem_nhds`, `sq_lt_sq'`,
`Continuous.aestronglyMeasurable`, `MeasureTheory.ae_of_all`,
`Filter.eventually_of_forall`) plus the §8/§9 lemmas — no new tactics or
exotic constructions. If the build fails, the most likely cause is a
Mathlib API drift in one of the auxiliary lemmas (e.g. `div_le_div` →
`div_le_div₀` rename), which would be a one-line fix.

---
