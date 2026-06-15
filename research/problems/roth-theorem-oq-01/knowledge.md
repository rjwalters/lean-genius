# Knowledge Base: roth-theorem-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Target: a **quantitative** upper bound on the Roth number `r₃(N)` (largest 3-AP-free subset
of `{1,…,N}`), of Bourgain's strength, rather than the qualitative `r₃(N) = o(N)` already in
the parent gallery proof `roth-theorem`.

**Correct quantitative landscape** (the original problem.md misstated Bourgain's bound as
`N/(log log N)^{1/2}`, which is weaker than even Roth's rate — see Insights):

| Author (year) | Bound on `r₃(N)` |
|---|---|
| Roth (1953) | `≪ N / log log N` |
| **Bourgain (1999)** | `≪ N (log log N / log N)^{1/2}` |
| Bourgain (2008) | `≪ N (log log N)² / log N` |
| Sanders (2011) | `≪ N (log log N)^{O(1)} / log N` |
| Bloom (2016) | `≪ N (log log N)⁴ / log N` |
| Bloom–Sisask (2020) | `≪ N / (log N)^{1+c}` |
| Kelley–Meka (2023) | `≪ N · exp(-c (log N)^β)` |

The "saving" in Bourgain 1999 is a **power of log** (`(log N)^{1/2}` up to a `loglog`
factor), not a `loglog` saving. The companion problem `roth-theorem-oq-02` targets the
Bloom–Sisask bound; this problem (oq-01) is the strictly weaker Bourgain bound, so it is
**implied by** oq-02.

---

## Insights

### Session 2026-06-14 (Session 1, ORIENT) — Mode: FRESH

- **Mathlib anchor.** Mathlib already provides `rothNumberNat : ℕ → ℕ`
  (`Mathlib.Combinatorics.Additive.AP.Three`) and the qualitative
  `rothNumberNat_isLittleO_id : (fun N => (rothNumberNat N : ℝ)) =o[atTop] (fun N => (N:ℝ))`.
  Any quantitative statement for this problem should be phrased at the **Mathlib
  `rothNumberNat`** level, NOT the project-local `Szemeredi.Roth.rothNumber` over `ZMod N`
  used in `RothTheorem.lean`. The sibling `RothTheoremOQ02.lean` already does exactly this.

- **Sibling precedent (oq-02 = Bloom–Sisask).** `proofs/Proofs/RothTheoremOQ02.lean` states
  the Bloom–Sisask bound as
  `axiom rothNumberNat_bloom_sisask : ∃ c > 0, ∀ N ≥ 3, (rothNumberNat N : ℝ) ≤ N / (log N)^(1+c)`
  and builds a stable downstream API (`blasiConst`, `blasiConst_pos`, `rothNumberNat_le_blasi`).
  This is the established gallery pattern for these out-of-reach quantitative bounds: state the
  bound as an `axiom` (status `axiomatized`, NOT `verified`), then derive consequences.

- **Bound-statement error in the seed problem.md.** The auto-generated formal statement gave
  Bourgain (1999) as `O(N/(log log N)^{1/2})`, and the "Initial Thoughts" section described the
  Bohr-set refinement as a `1/√(log log N)` improvement. Both confuse `log` with `log log`. The
  actual Bourgain 1999 bound is `N (log log N / log N)^{1/2}`. Corrected in problem.md this
  session.

- **leanFiles misattribution (fixed).** The research JSON `leanFiles` listed 6 sibling
  `RothTheorem*` files (base proof, OQ02, OQ03, Quantitative, Aristotle variants) even though no
  `RothTheoremOQ01*.lean` exists — making this open problem look formalized. Root cause:
  `scripts/research/enrich-research.ts` `getPascalCasePrefixes` falls back to the bare root
  `RothTheorem` for `-oq-NN` slugs, whose `startsWith` match greedily grabs every sibling.
  Pinned `SPECIAL_CASES['roth-theorem-oq-01'] = ['RothTheoremOQ01']` so the match is `[]` now
  and links only the real file if one is ever added. Verified via `enrich-research.ts --dry-run`.
  (Systemic note below.)

---

## Buildability Assessment

**Genuine from-scratch proof (density increment / Fourier):**
- Needs discrete Fourier analysis on `ZMod N` at strength: AP-counting via the third moment
  `∑_r f̂(r)² f̂(-2r)`, large-spectrum extraction, ℓ² control, and a single-step density
  increment on a sub-progression (Roth) or Bohr set (Bourgain), then the iteration with explicit
  constant tracking.
- Mathlib has `AddChar` / discrete convolution / Cauchy–Schwarz but **not** the
  large-spectrum + Bohr-set packaging needed for a rate.
- Estimate: even Roth's original `1/log log N` rate is **> 1000 LOC** of new additive-combinatorics
  infrastructure; Bourgain's improvement adds Bohr-set geometry on top. **BLOCKED** as a
  from-scratch proof; not attemptable in a single session (and Docker is currently down).

**Build-free / short routes:**
- **M1 (small, ~30–60 LOC, Docker to verify):** state `axiom rothNumberNat_bourgain :
  ∃ C > 0, ∀ N ≥ 3, (rothNumberNat N : ℝ) ≤ C * N * (Real.log (Real.log N) / Real.log N)^(1/2)`
  and PROVE the bridge `rothNumberNat_bourgain → rothNumberNat_isLittleO_id` (an explicit
  `(log log N / log N)^{1/2}` bound ⟹ `o(N)`, since the ratio → 0). This is a *real* provable
  lemma connecting an axiomatized quantitative bound to Mathlib's qualitative result — the honest
  unit of progress here. Status would be `axiomatized`.
- Since oq-02's `rothNumberNat_bloom_sisask` axiom implies the Bourgain bound, an alternative is
  to DERIVE `rothNumberNat_bourgain` from the oq-02 axiom rather than re-axiomatize. Cleaner
  dependency, but both remain assumptions.

**Decision: SURVEY / ORIENT.** Statement is clear and anchored; a genuine proof is blocked on
missing Mathlib infrastructure (>1000 LOC). Realistic next deliverable is M1 once Docker is up.

---

## Dead Ends

- Working at the project-local `ZMod N` `rothNumber` level (as in `RothTheorem.lean`) for the
  quantitative statement: diverges from the Mathlib `rothNumberNat` API that oq-02 and the
  qualitative `_isLittleO_id` result use. Stay at the Mathlib level.

---

## Systemic Note (for a builder, not this session)

`scripts/research/enrich-research.ts` has a systemic dual bug affecting all `-oq-NN` slugs:
1. `slugToPascalCase` emits `Oq` (lowercase `q`) for the `oq` token, so the correctly-cased
   own-prefix (`RothTheoremOQ01`) is never generated and never matches real `*OQ##*.lean` files.
2. The bare-root `-oq-NN` fallback (`RothTheorem`) `startsWith`-matches every sibling.

A measured probe (`oq`→`OQ` casing + dropping the bare-root fallback for `-oq` slugs) changes
attribution for **1431 / 2158** slugs: 9 are pure gains (`-incomplete-01` mid-slug OQs that
currently match nothing due to casing) and the rest only shed misattributed siblings. This is the
real root fix but has a large blast radius and cannot be render-verified during the Docker
blackout — left as a recommendation rather than shipped. Per-slug `SPECIAL_CASES` remains the
safe interim patch.
