# Knowledge Base: erdos-1039-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Erdős Problem #1039 (Erdős–Herzog–Piranian) asks for the optimal lower
bound on `ρ(f)`, the inscribed-disc radius of the open sublevel set
`{z ∈ ℂ : |f(z)| < 1}`, over monic polynomials with all roots in the
closed unit disc. Known: `1/(2en²) ≤ ρ ≤ π/(2n)`; KLR (2025) gives
`ρ ≫ 1/(n√log n)`. Conjecture (open): `ρ ≫ 1/n`.

`erdos-1039-oq-02` is the gallery extension: identify the extremal
polynomial configuration. Three sorries remain (`area_implies_disc_bound`,
`degree_one_optimal`, `clustered_implies_large_disc`).

---

## Insights

### Session 2026-05-08 (researcher-5) — DESIGN, BUILD NOT VERIFIED

**Outcome**: Proof of `clustered_implies_large_disc` was designed and
written, but local Docker build verification was blocked by a Mathlib
cache-miss requiring a fresh `git clone` of `mathlib4` (estimated
15+ minutes). Lean file changes were reverted to keep main repo in
the known-good state. Proof draft saved to `attempts/clustered.lean`
for the next researcher to pick up and verify.

**Mathematical structure of the design** (recorded for reuse):

1. **Sublevel-set boundedness lemma** (new infra, name `sublevelSet_subset_ball`).
   For `f : UnitDiscPolynomial` with `f.degree > 0`,
   `sublevelSet f ⊆ Metric.ball (0 : ℂ) 2`. Proof: when `|z| ≥ 2`,
   each `|z - rᵢ| ≥ |z| - |rᵢ| ≥ 1` by reverse triangle inequality
   (derived from `Complex.abs.add_le (z - rᵢ) rᵢ`); product over `Fin f.degree`
   gives `1 ≤ |f(z)|` (via `Finset.prod_le_prod` against constant 1),
   contradicting `|f(z)| < 1`.

2. **`BddAbove` of inscribed-radii** (new infra, name `bddAbove_inscribed_radii`).
   For `f.degree > 0`, the set `{r : ℝ | ∃ c, isInscribedDisc (sublevelSet f) c r}`
   is bounded above by 4. Proof: pick `z₁ = c + (r/2 : ℂ)`,
   `z₂ = c - (r/2 : ℂ)`; both lie in `Metric.ball 0 2` via the lemma above,
   so `|z₁| + |z₂| < 4`; but `|z₁ - z₂| = r` and triangle inequality gives
   `|z₁ - z₂| ≤ |z₁| + |z₂|`, so `r < 4`.

3. **`clustered_implies_large_disc` proof**. Given `∀ i, |rᵢ - c| < ε`,
   `Metric.ball c (1 - ε)` is inscribed in `sublevelSet f`: for any
   `z` with `|z - c| < 1 - ε`, each factor `|z - rᵢ| ≤ |z - c| + |rᵢ - c|
   < (1 - ε) + ε = 1`, so `|f(z)| < 1` (via `Finset.prod_lt_one` plus
   the nonempty-witness `i = ⟨0, hdeg⟩`). Then `1 - ε ∈ {r : ∃ c, ...}`
   and `le_csSup` (with `bddAbove_inscribed_radii`) gives `rho f ≥ 1 - ε`.

**Mathlib API used**: `Complex.abs.add_le`, `Complex.abs.nonneg`,
`Complex.abs_neg`, `Complex.abs_ofReal`, `Complex.dist_eq`,
`Complex.ofReal_div`, `Finset.prod_le_prod`, `Finset.prod_lt_one`,
`Finset.prod_const_one`, `Metric.mem_ball`, `le_csSup`. All
standard. The proof draft at `attempts/clustered.lean` was 100+ lines.

### Carryover from prior session (2026-03-30)

* `klr_better_than_pommerenke` proved (filter-eventually bound).
* `bounds_gap` proved (KLR < benchmark for n ≥ 3, c < π/2).
* `sublevelArea` correctly typed as `(volume).toReal`.

---

## Dead Ends / Open Sub-goals

### Remaining sorries

1. **`degree_one_optimal`**: with the (designed-but-unverified)
   infrastructure (`bddAbove_inscribed_radii`, `sublevelSet_subset_ball`),
   the upper-bound half (`ρ ≤ 1`) reduces to a
   `Metric.ball_subset_ball_iff`-style argument; the lower-bound
   half (`ρ ≥ 1`) follows from `c = root, r = 1` being inscribed
   in `Metric.ball root 1`. Use companion file's
   `sublevelSet_degree_one` and `isInscribedDisc_self`.

2. **`area_implies_disc_bound`**: needs
   * `Complex.volume_ball` (or equivalent) for
     `vol(Metric.ball c r) = π r²`
   * monotonicity `B(c,r) ⊆ S → vol B ≤ vol S` via
     `MeasureTheory.measure_mono`
   * a sSup-limit step: for every `r' < ρ`,
     `π · r'² ≤ vol S`, taking sup gives `π · ρ² ≤ vol S`.

3. **`clustered_implies_large_disc`** (designed, build not verified):
   pick up `attempts/clustered.lean`, copy into `Erdos1039Problem.lean`,
   run `./proofs/scripts/docker-build.sh Proofs.Erdos1039Problem`
   when Mathlib cache is warm.
