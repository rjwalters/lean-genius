# Knowledge Base: roth-theorem-oq-01

Insights accumulated during research on this problem.

---

## Session 2026-07-07 (researcher-2) — ACT: explicit bound ⟹ o(N), derived not re-exported

**Mode**: REVISIT (add verified content). The from-scratch Bourgain/Bloom–Sisask proof stays
BLOCKED (>1000 LOC Bohr-set/Fourier infra not in Mathlib v4.26), and the axiom count is already
minimal (0 own axioms; rests on the single imported OQ-02 Bloom–Sisask axiom). The realistic
deliverable was to upgrade the weakest link: `bourgain_consistent_with_isLittleO` merely
**re-exported** Mathlib's independent `rothNumberNat_isLittleO_id` — it did NOT show the
*explicit* Bourgain rate actually yields `o(N)`.

**Outcome**: COMPLETED this deliverable (machine-verified, `docker-build.sh Proofs.RothTheoremOQ01`
→ `=== Build succeeded ===`, first try). Added **2 theorems** (7→9), file 264→325 L, still
0 own axioms / 0 sorries:
- **`bourgain_factor_tendsto_zero`** (axiom-free): `(log log N/log N)^(1/2) → 0`. Proof chain:
  `Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero` gives `log u/u → 0` (real atTop); compose
  with `Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop` (`log N → ∞` over ℕ) to get
  `log(log N)/log N → 0`; then push through `·^(1/2)` via `Real.sqrt` (`Real.continuous_sqrt.tendsto 0`,
  `Real.sqrt_zero`) and convert back with `hsqrt.congr (fun N => Real.sqrt_eq_rpow _)`.
- **`rothNumberNat_isLittleO_of_bourgain`**: `rothNumberNat N = o(N)` DERIVED from the Bourgain
  bound. `Asymptotics.isLittleO_iff`; for ε>0, `bourgainConst · factor → 0` so eventually `< ε`
  (`hfac.eventually (Iio_mem_nhds hε)`); `filter_upwards` with `eventually_ge_atTop 3`; clear
  norms with `Real.norm_eq_abs` + `Nat.abs_cast`; `calc` through `rothNumberNat_le_bourgain` then
  `mul_le_mul_of_nonneg_right`.

### Lean gotchas (v4.26)
- **`Real.continuousAt_rpow_const` does NOT exist** (Unknown constant). Route `y^(1/2)` through
  `Real.sqrt` instead: `Real.sqrt_eq_rpow x : √x = x^(1/2:ℝ)` (unconditional) + `Real.continuous_sqrt`.
- `Filter.Tendsto.eventually_lt_const` is unreliable; use `hfac.eventually (Iio_mem_nhds hε)` +
  `simpa [Set.mem_Iio]` to get eventual `< ε` from a `nhds 0` limit.
- `Real.norm_eq_abs` then `Nat.abs_cast` clears `‖(n:ℝ)‖` for a ℕ-cast (both `rothNumberNat N`
  and `N`); `mul_le_mul_of_nonneg_right ... (Nat.cast_nonneg N)`.
- Build-host note: same corrupt-cache/OOM-under-contention flakiness as elsewhere — plain retries
  self-heal (each auto-purges + re-fetches the bad `.ltar`/`.ir`); this session built first try.

### Honest status
Still **axiomatized** — the presented Bourgain bound rests on the imported Bloom–Sisask axiom;
`rothNumberNat_isLittleO_of_bourgain` inherits that single assumption (via `rothNumberNat_le_bourgain`),
while `bourgain_factor_tendsto_zero` is fully axiom-free. No new axioms. The genuine remaining
open work (a from-scratch quantitative proof) is unchanged and BLOCKED.

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

---

## Session 2026-06-28 (researcher-1) — ACT: eliminated the redundant Bourgain axiom

**Mode**: REVISIT (axiom elimination) · **Outcome**: progress (1 axiom removed from the gallery).

### Stale-knowledge correction
This KB previously recorded "no `RothTheoremOQ01*.lean` exists" and `leanFiles = []`. That was
**out of date**: `proofs/Proofs/RothTheoremOQ01.lean` exists (researcher-10, 2026-06-25) and
carried a **separate `axiom rothNumberNat_bourgain`** — the exact thing the M1 plan flagged as
avoidable, since its own docstring noted "OQ-01 is implied by OQ-02".

### What I did
Replaced `axiom rothNumberNat_bourgain` with a **theorem** of the same statement, **derived from
the Bloom–Sisask axiom** of OQ-02. Bloom–Sisask (`N/(log N)^{1+c}`) decays strictly faster than
Bourgain (`N(loglog N/log N)^{1/2}`), so it implies it. The whole quantitative landscape now
rests on the *single* gallery assumption `RothTheoremOQ02.rothNumberNat_bloom_sisask` instead of
two redundant axioms.
- Registered the file in `proofs/Proofs.lean` (its sibling OQ02 was already registered; OQ01 was
  orphaned from the aggregate build).
- Host-verified: `lake env lean Proofs/RothTheoremOQ01.lean` exit 0 (built OQ02 olean dep via
  `lake env lean -o` first; Docker host down). `#print axioms rothNumberNat_bourgain` =
  `[propext, Classical.choice, Quot.sound, RothTheoremOQ02.rothNumberNat_bloom_sisask]` — **no
  Bourgain axiom**, no `sorryAx`, no `Lean.ofReduceBool`.

### The analytic core (Bloom–Sisask ⟹ Bourgain) — what worked
After cancelling `N>0` and writing `L=log N`, `LL=loglog N`:
- `Real.rpow_add h_logN_pos`: `L^(1+c) = L^(1/2)·L^(1/2+c)` (close exponent equality with
  `congr 1; ring`, NOT `norm_num` — norm_num won't combine `1/2+(1/2+c)` under rpow).
- `Real.div_rpow LL.le L.le`: `(LL/L)^(1/2) = LL^(1/2)/L^(1/2)` (apply via `rw`, the lemma is
  `∀ z`-quantified).
- Reduce to `1 ≤ (LL^(1/2)·L^(1/2+c))/(B·E)` with `B=(loglog 3)^(1/2)`, `E=(log 3)^(1/2+c)`,
  `C := 1/(B·E)`. Both `LL^(1/2)≥B`, `L^(1/2+c)≥E` by `Real.rpow_le_rpow` (base monotone:
  `log 3 ≤ log N`, `loglog 3 ≤ loglog N`).
- GOTCHAS: `div_le_iff₀` (not `div_le_iff`, deprecated in 4.26); `Real.log_le_log (0<x) (x≤y)`
  takes the *inner* positivity `0 < log 3` for `log(log 3) ≤ log(log N)` (NOT `0 < log log 3`);
  `field_simp` closed the algebra identity alone, so guard the trailing `ring` with `try`.
- Constant ≥1 step via `le_mul_of_one_le_left hNpos.le (one_le_div ...).mpr hat`.

### Honest status
Still **axiomatized** — rests on the BS axiom (the full Bloom–Sisask/Bourgain proofs are
thousands of lines of Bohr-set/Fourier infrastructure not in Mathlib). But the file now declares
**0 axioms of its own**: net gallery axiom count for the Roth quantitative landscape drops by 1.

### Files modified
- proofs/Proofs/RothTheoremOQ01.lean (axiom → derived theorem; docstring updated)
- proofs/Proofs.lean (registered RothTheoremOQ01)
- research/problems/roth-theorem-oq-01/knowledge.md (this entry; corrected stale leanFiles claim)
- src/data/research/problems/roth-theorem-oq-01.json (leanFiles, lastUpdate)

### Next steps
- Same `≤` derivation could eliminate the Kelley–Meka or other "weaker-than-BS" quantitative
  axioms if any are added (KM is actually *stronger* than BS in a different regime — not derivable
  this way). The remaining genuine open work is the from-scratch Bourgain/BS proof (BLOCKED on
  Mathlib Bohr-set infrastructure, >1000 LOC).
