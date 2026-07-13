# Knowledge Base: Bloom–Sisask `r₃(N) = O(N / (log N)^{1+c})`

## Slug

`roth-theorem-oq-02` — Mathlib-bridge target: prove (or scaffold towards a
proof of) the Bloom–Sisask quantitative bound for `rothNumberNat`.

## Problem Summary

Prove `∃ c > 0, ∀ N sufficiently large, rothNumberNat N ≤ N / (log N)^{1+c}`.
The Mathlib v4.26.0 file
`Mathlib/Combinatorics/Additive/AP/Three/Defs.lean` already names this as the
expected upper bound in its module docstring, but no Lean proof (or even
formal statement) currently exists.

## Status: S1 OBSERVE (scaffold-only, no Lean changes yet)

Created: 2026-05-12. Phase: OBSERVE. Iteration: 1. Researcher: researcher-11.

## Historical Chronology of `r₃(N)` Bounds

| Year | Author(s) | Upper bound on `r₃(N) / N` |
|------|-----------|----------------------------|
| 1946 | Behrend | (lower bound) `≥ exp(-c·√log N)` |
| 1953 | Roth | `O(1/log log N)` |
| 1987 | Heath-Brown | `O((log N)^{-c})` for tiny `c > 0` |
| 1990 | Szemerédi | `O((log N)^{-c})`, larger `c` |
| 1999 | Bourgain | `O((log log N)^{1/2} (log N)^{-2/3})` |
| 2008 | Bourgain | `O((log N)^{-3/4 + o(1)})` |
| 2011 | Sanders | `O((log log N)^5 / log N)` |
| 2012 | Bloom | `O((log log N)^4 / log N)` |
| **2020** | **Bloom–Sisask** | `O((log N)^{-1-c})` ← **this slug** |
| 2023 | Kelley–Meka | `O(exp(-c (log N)^{1/12}))` |

(See `src/data/proofs/roth-theorem-k3-oq-01/meta.json` and
`annotations.json` for the curated historical context already in the gallery.)

## Mathlib v4.26.0 State (pinned rev `2df2f0150c275ad`)

**What exists:**

- `Mathlib/Combinatorics/Additive/AP/Three/Defs.lean`
  - `ThreeAPFree : Set α → Prop` and `ThreeGPFree` (multiplicative twin)
  - `addRothNumber : Finset α →o ℕ`
  - `rothNumberNat : ℕ →o ℕ` (defined as `addRothNumber (Finset.range n)`)
  - Module docstring **explicitly names Bloom–Sisask** as the target:
    > `rothNumberNat N = O(N / (log N)^(1+c))` for an absolute constant `c`.
  - `rothNumberNat_le : rothNumberNat N ≤ N` (trivial)
  - `rothNumberNat_add_le` (subadditivity)
  - `ThreeAPFree.le_rothNumberNat` (canonical injection)

- `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean`
  - Construction of large AP-free sets via lattice points on a sphere
  - `Behrend.box`, `Behrend.sphere`, `Behrend.map` injectivity
  - Lower bound `rothNumberNat n ≥ n · exp(-c · √log n)`
  - **Explicit theorem (verified at pin `2df2f0150c275ad`)**:
    `Behrend.roth_lower_bound : (N : ℝ) * exp (-4 * √(log N)) ≤ rothNumberNat N`
    (unconditional, file line 482; constant `c = 4` hardcoded; small-`N`
    case handled by `rothNumberNat.monotone` from `rothNumberNat 1 ≥ 1`).
    The `4096 ≤ N` case is the substantive content via
    `Behrend.roth_lower_bound_explicit` at line 420. **Note**: the prior
    S2 state.md erroneously claimed "no explicit `rothNumberNat ≥ N · exp(-c · √log N)`
    theorem is yet packaged in Mathlib"; this is corrected in the S3
    state.md (audit verified by direct `git show 2df2f0150c275ad:…`).

- `Mathlib/Combinatorics/Additive/Energy.lean`
  - `mulEnergy : Finset α → Finset α → ℕ` (additive/multiplicative energy)
  - Basic energy ↔ doubling inequalities

- `Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean`
  - Plünnecke–Ruzsa inequalities for iterated sumsets

- `Mathlib/Combinatorics/Additive/RuzsaCovering.lean`
  - Ruzsa covering lemma

- `Mathlib/Combinatorics/Additive/Dissociation.lean`
  - Dissociated sets (precursor to Rudin–Chang)

- `Mathlib/Combinatorics/Additive/ApproximateSubgroup.lean`
  - K-approximate subgroup definition; Sanders-style structural lemmas

- `Mathlib/Combinatorics/Additive/FreimanHom.lean`
  - Freiman homomorphisms

**What is MISSING (the Bloom–Sisask gap):**

1. **Quantitative upper bound on `rothNumberNat`.** No theorem stating
   `rothNumberNat N ≤ f(N)` for any `f(N) = o(N)`. Even the Roth bound
   `O(N/log log N)` is not formalized in Mathlib.
2. **Bohr sets.** No `BohrSet` definition, no Bohr-set Bogolyubov lemma, no
   regularity / nesting infrastructure.
3. **Quantitative Bogolyubov–Ruzsa.** Mathlib has Plünnecke–Ruzsa and Ruzsa
   covering, but not the Bohr-set Bogolyubov form needed for Sanders / Bloom–
   Sisask: `|A| ≥ δN ⇒ A + A − A − A ⊇ Bohr set of dimension/radius ≥ f(δ)`.
4. **Density increment iteration framework.** No `densityIncrement` lemma
   producing `δ' ≥ δ + g(δ)` on a structured sub-progression / Bohr set.
5. **Discrete Fourier transform on `ZMod N`** with the analytic estimates
   (Hausdorff–Young, Parseval-via-energy) that Bloom–Sisask uses extensively.
   Mathlib has `Mathlib.Analysis.Fourier.AddCircle` and `ZMod` characters but
   no organized package for additive-combinatorics Fourier.

## Mathematical Skeleton of the Bloom–Sisask Argument

(Following Bloom & Sisask, arXiv:2007.03528, §1.2 "Sketch.")

1. **Assume** `A ⊆ ZMod N`, `|A| = δN`, `A` is 3-AP-free.
2. **Show** `|A| ≥ δN ⇒ |Â| has large `ℓ^p` mass for some `p > 2`** (Bateman–
   Katz / Heath-Brown style spectral estimate).
3. **Apply quantitative Bogolyubov–Ruzsa on a Bohr set:** the level set
   `Spec_ρ(1_A) = {ξ : |Â(ξ)| ≥ ρ|A|}` is contained in a Bohr set `B(T, ρ)`
   with `|T| ≤ poly(1/δ)` and dimension small.
4. **Density increment:** restrict `A` to a regular Bohr sub-set `B(S, η)`;
   the density of `A` on this sub-set exceeds `δ + δ^{1+ε}` (compared to
   Sanders' `δ + δ²/(log 1/δ)^k`).
5. **Iterate** the density increment: after `≲ (log 1/δ)^{1−c'}` steps,
   density exceeds 1 — contradiction unless `δ ≤ (log N)^{−1−c}`.

The **innovation** is in step 4: a more careful averaging over a *family* of
Bohr sets, using Hölder-type interpolation, gives the `δ^{1+ε}` increment
(versus Sanders' `δ²/polylog`) — and the doubly-logarithmic loss collapses to
a power saving.

## Mathlib Gaps Ranked by Effort

| Rank | Gap | Estimated PR effort | Blocks |
|------|-----|--------------------|--------|
| 1 | Define `BohrSet T ρ` (over `ZMod N`) | ~200 lines | (3), (4), (5) below |
| 2 | Regularity of Bohr sets (Bourgain) | ~400 lines | (3), (4) |
| 3 | Quantitative Bogolyubov on Bohr sets | ~600 lines | (4) |
| 4 | Density increment framework | ~300 lines | full proof |
| 5 | `r₃` Fourier transform interface (level sets, energy) | ~400 lines | (3) |
| 6 | Bloom–Sisask iteration + final bound | ~500 lines | this slug |

Total realistic Lean budget: ~2,400 lines across ~5–8 PRs. Compare:
`SzemerediCounting.lean` (Mathlib's k≥4 piece) is ~1,200 lines and was
written over multiple months. This places Bloom–Sisask at "ambitious but
feasible" — likely a multi-quarter effort tracked as an *epic*, not a
single-iteration session.

## Realistic Single-Iteration Targets

Per `feedback_researcher_s1_deferred_can_be_false.md`: don't commit a flashy
formal statement in S1 OBSERVE that the next session can't actually plug.
Concrete S2 candidates (in increasing scope):

- **S2-A.** Add a *companion file*
  `proofs/Proofs/RothTheoremOQ02BloomSisaskStatement.lean` containing:
  ```
  axiom rothNumberNat_bloom_sisask :
      ∃ c > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        (rothNumberNat N : ℝ) ≤ (N : ℝ) / Real.log N ^ (1 + c)
  ```
  with a docstring linking to the paper. Status `axiomatized`. Closes the
  "missing formal statement" gap with a 1-axiom landmark entry.
- **S2-B.** Add the statement *and* a proven trivial reduction
  `BSImpliesRoth_qualitative`: Bloom–Sisask ⇒ Roth's qualitative theorem
  (`AP-free ⇒ density → 0`). About +50 lines.
- **S2-C.** Define `BohrSet T ρ` in a *new file*
  `proofs/Proofs/RothTheoremOQ02BohrSets.lean`, prove basic
  closure-under-translation and `0 ∈ B(T, ρ)`. About +150 lines. Lays
  groundwork without claiming the headline bound.

S2-A is the lowest-risk, lowest-bullshit option: it gives the gallery a real
Lean-typed *statement* of Bloom–Sisask matching Mathlib's docstring goal, and
lets a future session add proven reductions.

## Race / Saturation Status

Pre-claim checks (2026-05-12 ~09:25 UTC):

- `gh pr list -R rjwalters/lean-genius --search "roth-theorem-oq-02"` → `[]`
- `git branch -r | grep "roth-theorem-oq-02"` → none (only
  `roth-theorem-k3-*` branches)
- `git log --all --oneline | grep "roth-theorem-oq-02"` → none
- Candidate pool: `status = "available"`, `knowledge_score = null`

Fresh slug, no prior work. Per
`feedback_researcher_fresh_slug_simultaneous_scaffold.md`, re-check `gh pr
list --search` immediately before push.

## S5-b / S6-b Constant Audit (2026-06-13, researcher-2) — RESULT: INFEASIBLE

The documented next-step "strengthen the K–M / B–S axioms to bounded-existential
form `∃ c ≤ K, …` to make the conditional analytic envelopes unconditional" was
audited against the primary literature and found **infeasible as scoped**:

- **No published source gives a numeral for the constant `c`.** Kelley–Meka
  (arXiv:2302.05537), the Bloom–Sisask exposition (arXiv:2302.07211 = *Essential
  Number Theory* 2(1), 2023), and the Bloom–Sisask improvement
  (arXiv:2309.02353) all state the bound only as `exp(-c (log N)^{1/12}) N` (resp.
  `^{1/9}`, `^{5/41}`) "for some constant `c > 0`". The almost-periodicity /
  spectral Bohr-set machinery never tracks or optimises `c`.
- Consequently the shipped hypothesis `kelleyMekaConst ≤ 4·(log 3)^{5/12} (≈ 4.165)`
  **cannot be discharged** from literature; asserting a specific `K` in Lean would
  fabricate an unsupported numerical claim. The conditional envelopes are the
  strongest *honest* analytic statements obtainable from abstract-`c` axioms.
- **The only path to a non-axiomatic result is formalisation, not a constant
  audit.** External anchor: `YaelDillies/LeanAPAP` (Lean 4 formalisation of the
  K–M Roth-number bound; abstract `c`, in-progress, not yet upstreamed). Its
  discrete-convolution / Lᵖ / Fourier / almost-periodicity material is the
  intended Mathlib upstream and the realistic prerequisite for the S4-b Bohr-set
  track. Future S4-b sessions should track/reuse LeanAPAP rather than rebuild.

See `sessions/2026-06-13-s5b-prep-km-bs-constant-literature-audit.md` for the
full audit with sources. This closes S5-b/S6-b; do not re-attempt the audit.

## Key References

- Bloom, T. F. & Sisask, O. *Breaking the logarithmic barrier in Roth's
  theorem on arithmetic progressions.* arXiv:2007.03528 (2020).
- Bloom, T. F. & Sisask, O. *An improvement to the Kelley–Meka bounds on
  three-term arithmetic progressions.* arXiv:2309.02353 (2023). Survey of
  the post-Kelley–Meka picture.
- Roth, K. F. *On certain sets of integers.* J. London Math. Soc. **28**
  (1953), 104–109.
- Sanders, T. *On Roth's theorem on progressions.* Annals of Math. **174**
  (2011), 619–636.
- Bourgain, J. *Roth's theorem on progressions revisited.* J. Anal. Math.
  **104** (2008), 155–192.
- Kelley, Z. & Meka, R. *Strong bounds for 3-progressions.* arXiv:2302.05537
  (2023).
- Tao, T. & Vu, V. *Additive Combinatorics.* Cambridge University Press
  (2006), Chapter 10 (Roth's theorem and the density increment).
- Bloom, T. F. & Sisask, O. *The Kelley–Meka bounds for sets free of
  three-term arithmetic progressions.* arXiv:2302.07211; *Essential Number
  Theory* **2** (2023), no. 1 (self-contained exposition with Bohr-set
  simplifications).
- Dillies, Y. et al. *LeanAPAP* — Lean 4 formalisation of the Kelley–Meka
  bound on Roth numbers. https://github.com/YaelDillies/LeanAPAP
  (non-axiomatic counterpart to this slug's `rothNumberNat_kelley_meka`
  axiom; Fourier/Lᵖ/almost-periodicity material intended for Mathlib upstream).

## Gallery cross-references (existing)

- `src/data/proofs/roth-theorem-k3-oq-01/annotations.json` (line 335) —
  curated paragraph on Bloom–Sisask "Breaking the Logarithmic Barrier".
- `src/data/proofs/roth-theorem-k3-oq-01/meta.json` (line 62) — already
  states Bloom–Sisask as one of four landmark `r₃` bounds (the proof is
  a sorry there).
- `src/data/research/problems/roth-theorem-k3-oq-01.json` — sibling open
  question targeting all four bounds simultaneously; this slug refines to
  the Bloom–Sisask bound alone.
