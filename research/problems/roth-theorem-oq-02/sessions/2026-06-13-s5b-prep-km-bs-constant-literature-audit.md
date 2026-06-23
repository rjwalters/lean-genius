# S5-b / S6-b PREP — Kelley–Meka / Bloom–Sisask constant literature audit

**Date:** 2026-06-13
**Author:** researcher-2
**Mode:** PREP (doc-only literature audit; no Lean, no build)
**Slug:** roth-theorem-oq-02 (Bloom–Sisask `r₃(N) = O(N / (log N)^{1+c})`)

## Why this session exists

As of this session the entire previously-documented Lean frontier for this
slug is **already shipped or in-flight**:

- S5-a ACT (`analytic_envelope_conditional`, K–M) — merged (PR #22769).
- S6-a ACT (`bloom_sisask_analytic_envelope_conditional`, B–S),
  S6-d ACT (`kelley_meka_envelope_le_bloom_sisask_envelope_conditional`
  + `min_blasi_kelley_meka_eq_kelley_meka_eventually`),
  S4-b ACT (`RothTheoremOQ02BohrSets.lean`, 151 LOC, Docker-verified
  7743 jobs) — all bundled in **OPEN PR #22850** (`feature/researcher-1`,
  opened 2026-06-10). The deployer merges math PRs directly.

After #22850 merges, the only next-step the canonical `state.md` / gallery
JSON still list as open is:

> **S5-b / S6-b** — literature audits of arXiv:2302.05537 (K–M) and
> arXiv:2007.03528 (B–S) constant tracking, to strengthen the axioms to
> *bounded-existential* form `∃ c, 0 < c ∧ c ≤ K ∧ …`, which would convert
> the three **conditional** analytic envelopes into **unconditional**
> theorems.

This session executes that audit. It is doc-only because (a) Docker is down
on the host (`docker info` hangs → no Lean build can be verified this
session) and (b) the Lean frontier is owned by the open PR; touching the
shared `RothTheoremOQ02.lean`, `state.md`, or the gallery JSON would
conflict with #22850.

## The precise question

The shipped conditional theorem `analytic_envelope_conditional` carries the
hypothesis

```
kelleyMekaConst ≤ 4 * (Real.log 3) ^ (5/12)        -- ≈ 4.165
```

and `kelleyMekaConst := rothNumberNat_kelley_meka.choose` is the
`Exists.choose` witness of the axiom

```
axiom rothNumberNat_kelley_meka :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumberNat N : ℝ) ≤ (N : ℝ) * Real.exp (-c * Real.log N ^ ((1:ℝ)/12))
```

To make the envelope **unconditional**, one must replace the bare
existential `∃ c > 0` with a *bounded* existential `∃ c, 0 < c ∧ c ≤ K ∧ …`
for some **literature-justified** numeral `K ≤ 4·(log 3)^{5/12} ≈ 4.165`.
That is only honest if some published source actually pins (or upper-bounds)
the Kelley–Meka constant by such a `K`.

## Audit findings (with sources)

| Source | Bound stated | Constant `c` |
|--------|--------------|--------------|
| Kelley–Meka 2023, *Strong Bounds for 3-Progressions*, arXiv:2302.05537 | `|A| ≤ exp(-c (log N)^{1/12}) N` | **"for some constant c > 0"** — no numeral |
| Bloom–Sisask 2023, *The Kelley–Meka bounds …* (exposition), arXiv:2302.07211 = *Essential Number Theory* **2** (2023) no. 1 | same, with Bohr-set simplifications | **"for some constant c > 0"** — no numeral |
| Bloom–Sisask 2023, *An improvement to the Kelley–Meka bounds …*, arXiv:2309.02353 | exponent improved `1/12 → 1/9` (and `→ 5/41` with more work) | **"for some c > 0"** — no numeral |
| `YaelDillies/LeanAPAP` (Lean 4 formalisation of the K–M bound on Roth numbers) | `|A| ≤ N / exp(c · (log N)^{1/12})` | abstract `c`; project **incomplete**, **not** upstreamed to Mathlib |

**Conclusion: the Kelley–Meka constant is not numerically pinned anywhere in
the literature.** The proof routes through almost-periodicity and a spectral
/ Bohr-set density increment in which `c` is never tracked; no exposition
optimises or even states a numeral, and the constant is widely understood to
be small but unspecified. The Bloom–Sisask refinements move the *exponent*
(`1/12 → 1/9 → 5/41`), not the constant, and likewise leave `c` abstract.

The same holds for the Bloom–Sisask `r₃(N) = O(N/(log N)^{1+c})` constant
(arXiv:2007.03528): the "+c" power saving is qualitative; no numeral for the
power saving is given.

## Verdict on S5-b / S6-b

**S5-b / S6-b is INFEASIBLE as scoped.** There is no published numeral `K`
with which to honestly replace `∃ c > 0` by `∃ c ≤ K`, so the three
conditional analytic envelopes **cannot be made unconditional by a
literature audit**. The hypothesis `kelleyMekaConst ≤ 4·(log 3)^{5/12}`
cannot be discharged against any source; asserting a specific `K` in Lean
would be fabricating a numerical claim the literature does not support.

This **closes** the S5-b / S6-b next-step that `state.md` has carried as
"open" since S5 (2026-05-13). Future sessions should **not** re-attempt the
constant audit.

## Redirect — what the genuine remaining paths actually are

1. **The non-axiomatic path is a formalisation effort, not a constant
   audit.** The only way to remove the `rothNumberNat_kelley_meka` /
   `rothNumberNat_bloom_sisask` axioms is to *prove* the bound. That is the
   multi-quarter Bohr-set epic already begun in S4-b
   (`RothTheoremOQ02BohrSets.lean`). The realistic external anchor is
   **`YaelDillies/LeanAPAP`**, which is formalising exactly the K–M bound
   and explicitly intends to upstream its discrete-convolution / Lᵖ-norm /
   Fourier-transform / almost-periodicity material into Mathlib. A future
   session on the S4-b track should *track and reuse* LeanAPAP rather than
   rebuild the Fourier/almost-periodicity infrastructure from scratch.

2. **Conditional-but-honest is the ceiling for the axiom approach.** With
   abstract-`c` axioms, the conditional envelopes already shipped
   (`analytic_envelope_conditional` et al.) are the *strongest honest*
   analytic statements obtainable; they correctly quarantine the
   unverifiable numeral into an explicit hypothesis. This is the right
   design and should not be "upgraded" to unconditional by inventing a
   constant.

## Anti-targets (NO)

- **No Lean edits.** Docker daemon is down (`docker info` hangs); no build
  could be verified, and the file is owned by open PR #22850.
- **No `state.md` / gallery-JSON edits.** Open PR #22850 rewrites both
  (iteration → 13, nextAction → S5-b/S6-b). Editing them here would
  conflict. The canonical sync of *this* finding into `state.md` + JSON is
  **deferred to a post-#22850-merge STATE-SYNC** that can absorb both at
  once. (`knowledge.md` is NOT touched by #22850, so the audit summary is
  appended there safely.)
- **No new axioms / sorries.** Net Lean delta: 0.

## Net impact

- Lean: unchanged (2 axioms + 0 sorries on `RothTheoremOQ02.lean`; that file
  not touched this session).
- Knowledge: `knowledge.md` gains an "S5-b/S6-b constant audit" subsection;
  this session log added.
- Forward value: removes a dead next-step from the roadmap and points the
  non-axiomatic track at the correct external anchor (LeanAPAP).

## Sources

- Kelley, Z. & Meka, R. *Strong Bounds for 3-Progressions.* arXiv:2302.05537.
- Bloom, T. F. & Sisask, O. *The Kelley–Meka bounds for sets free of
  three-term arithmetic progressions.* arXiv:2302.07211; *Essential Number
  Theory* 2 (2023), no. 1.
- Bloom, T. F. & Sisask, O. *An improvement to the Kelley–Meka bounds on
  three-term arithmetic progressions.* arXiv:2309.02353.
- Bloom, T. F. & Sisask, O. *Breaking the logarithmic barrier in Roth's
  theorem on arithmetic progressions.* arXiv:2007.03528.
- Dillies, Y. et al. *LeanAPAP* — Lean 4 formalisation of the Kelley–Meka
  bound on Roth numbers. https://github.com/YaelDillies/LeanAPAP
