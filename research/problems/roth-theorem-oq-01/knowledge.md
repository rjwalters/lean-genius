# Knowledge Base: roth-theorem-oq-01

Insights accumulated during research on this problem.

---

## Session 2026-07-08 (researcher-8) — ACT: Erdős reciprocal-sum consequence (3-AP-free ⟹ Σ1/a < ∞)

**Mode**: REVISIT. The axiomatized landmark route was exhausted; the genuine remaining unit
(flagged in `state.md` "Next Action") was the **Erdős reciprocal-sum theorem for `k = 3`**:
every 3-AP-free `A ⊆ ℕ` has a *convergent* reciprocal sum. This is the true headline
consequence of Bloom–Sisask (2020) and is strictly stronger than the qualitative `o(N)` — it
needs a full power-of-log density saving.

**Outcome**: COMPLETED, machine-verified (`docker-build.sh Proofs.RothTheoremOQ01Reciprocal`
→ `Build succeeded`). New companion file **`Proofs/RothTheoremOQ01Reciprocal.lean`** (215 L,
8 declarations, 0 sorries). Rests on exactly the single imported axiom
`RothTheoremOQ02.rothNumberNat_bloom_sisask` (via `threeAPFree_card_le_blasi`) — **no new
axiom**, no `sorryAx`, no `Lean.ofReduceBool`.

### What I built
- **`threeAPFree_summable_reciprocal`** `{A : Set ℕ} (hA : ThreeAPFree A) (hA0 : 0 ∉ A) :
  Summable (fun a : A => 1 / a)`. The main result.
- **`recipMajorant k = 2 / ((k+1)·log 2)^{1+blasiConst}`** — dyadic block majorant.
- **`summable_recipMajorant`** — `p`-series convergence (`p = 1 + blasiConst > 1`).
- **`fiber_sum_le`** — per-block reciprocal bound `Σ_{a∈T, ⌊log₂ a⌋=k} 1/a ≤ recipMajorant k`.
- **`finite_recip_sum_le`** — uniform bound on finite partial sums by `Σ' recipMajorant`.

### Method
Dyadic partial summation. Partition by `k = ⌊log₂ a⌋`, so `a ∈ [2^k, 2^{k+1})`. The block
`A ∩ [2^k, 2^{k+1})` is 3-AP-free with all elements `< 2^{k+1}`, so
`threeAPFree_card_le_blasi` (at `N = 2^{k+1}`, `log N = (k+1)·log 2`) bounds its card by
`2^{k+1}/((k+1)log 2)^{1+c}`; each term is `≤ 2^{-k}`, giving block sum `≤ recipMajorant k`.
Uniform boundedness of the partial sums (`summable_of_sum_range_le` on the indicator) then
yields summability.

### Lean gotchas (v4.26)
- `summable_of_sum_range_le`, `Real.summable_one_div_nat_add_rpow`, and
  `Real.summable_one_div_nat_rpow` live in `Mathlib.Analysis.PSeries` /
  `Mathlib.Topology.Algebra.InfiniteSum.Real` — **not** pulled in by `Corner.Roth`; import
  explicitly.
- `summable_subtype_iff_indicator` matches the pattern `Summable (f ∘ Subtype.val)`, **not**
  `Summable (fun a : A => …)` — first `rw [show (fun a : A => 1/↑a) = (fun n => 1/↑n) ∘
  Subtype.val from rfl]`.
- The density lemma's RHS carries a ℕ-cast numerator `↑(2^{k+1})` and `Real.log ↑(2^{k+1})`;
  a two-step `rw [hNcast, hlogN]` fails to match — use
  `simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_add, Nat.cast_one] at hdens`.
- `Set.indicator_nonneg` is not in scope from these imports; prove nonneg inline via
  `rw [Set.indicator_apply]; split_ifs <;> positivity`.
- `log 2 ≤ 1` cleanly from `Real.log_le_sub_one_of_pos` (avoids the decimal `log_two_lt_d9`).
- Assemble the fiber decomposition with `Finset.sum_fiberwise_of_maps_to` (`t := T.image
  (Nat.log 2)`) then `Summable.sum_le_tsum`.
- After `field_simp`, the residual `ring` was "no goals" — `field_simp` closed the block
  arithmetic `(2^{k+1}/D)·(1/2^k) = 2/D` on its own.

### Honest status
Still **axiomatized** overall — the reciprocal-sum theorem inherits the one Bloom–Sisask
assumption. But it is genuinely new mathematical content (the actual Erdős-conjecture payoff),
not a rate re-comparison. Axiom count unchanged at 2 for the entry.

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

---

## Session 2026-07-08 (researcher-9) — REVISIT: universal 3-AP-free interface bounds

**Mode**: REVISIT. On claim, the file was already axiomatized-complete (13 theorems, 0 sorries,
0 own axioms; rests only on the single imported `RothTheoremOQ02.rothNumberNat_bloom_sisask`
axiom). Four prior PRs (#30176, #31182, #35228, #35501) extracted the reasonable axiomatized
deliverables: the Bourgain bound (now DERIVED from Bloom–Sisask, not axiomatized), the
`o(N)` derivation, the Behrend-consistency, and the Bourgain-vs-Roth-1953 rate comparison.
The genuine from-scratch quantitative proof stays BLOCKED (>1000 LOC Bohr-set/large-spectrum
Fourier infra absent from Mathlib v4.26).

**Gap identified**: every quantitative bound in the file constrained only the *extremal* Roth
number `rothNumberNat N` (the size of a **largest** 3-AP-free subset of `range N`). Nothing
stated the bound for an **arbitrary** 3-AP-free set — the universally-quantified form that
applications (e.g. the Erdős reciprocal-sum problem) actually consume.

**Outcome**: added 2 theorems (13→15), lifting both extremal bounds to arbitrary 3-AP-free
finite sets via Mathlib's `ThreeAPFree.le_rothNumberNat`. Still 0 sorries / 0 own axioms
(Docker `docker-build.sh Proofs.RothTheoremOQ01` → `=== Build succeeded ===`; `#print axioms`
confirms both depend on `[propext, RothTheoremOQ02.rothNumberNat_bloom_sisask]` — no new axiom,
no sorryAx/ofReduceBool):
- **`threeAPFree_card_le_blasi`**: `ThreeAPFree ↑s → 3≤N → (∀ x∈s, x<N) → #s ≤ N/(log N)^{1+c}`.
- **`threeAPFree_card_le_bourgain`**: same hypotheses → `#s ≤ bourgainConst·N·(loglog N/log N)^{1/2}`.
Both are 3-line composition proofs: `ThreeAPFree.le_rothNumberNat s hs hsub rfl : #s ≤ rothNumberNat N`,
cast `#s ≤ rothNumberNat N` to ℝ via `exact_mod_cast`, then chain the extremal bound
(`rothNumberNat_le_blasi` / `rothNumberNat_le_bourgain`).

### Lean gotchas (v4.26)
- `ThreeAPFree.le_rothNumberNat (s : Finset ℕ) (hs : ThreeAPFree ↑s) (hsn : ∀ x∈s, x<n) (hsk : #s=k) : k ≤ rothNumberNat n`
  — despite the dotted name, `s` is the FIRST explicit arg; call it fully applied
  `ThreeAPFree.le_rothNumberNat s hs hsub rfl` (the `rfl` instantiates `k := #s`, and `n` is
  inferred from `hsub`). `rothNumberNat : ℕ →o ℕ`, applied as `rothNumberNat N`.
- Host-verify (`lake env lean -o`) FAILS on this chain: "missing IR data file for module
  Mathlib.Logic.OpClass" at the import line — `cache get` oleans lack the IR the frontend wants.
  Use `docker-build.sh` for the OQ01/OQ02 chain (Corner.Roth + Behrend imports).
- Line-less exit-135 on the FIRST docker build of a byte-identical file = volume corruption under
  concurrent fleet load; a plain retry replayed OQ02 and built OQ01 green (4.0s).
- **`.loom/worktrees/researcher-9` was DELETED mid-session** (again). Rebuilt into durable
  `/Users/rwalters/lg-r9-wt2` off origin/main; the two Roth `.lean` files were byte-identical
  between the stale base and origin/main so the build carried over. Re-applied all edits.

### Honest status
Still **axiomatized** (single imported Bloom–Sisask assumption). The new theorems are a modest
but genuinely-distinct *interface* addition — they change the subject from the extremal Roth
number to arbitrary 3-AP-free sets, the form needed downstream. NOT a rate-cosmetic variant.

### Remaining open direction (NOT attempted — too heavy for one session)
The headline Bloom–Sisask consequence — the **Erdős reciprocal-sum theorem for 3-APs**: any
3-AP-free `A ⊆ ℕ` has `∑_{a∈A} 1/a < ∞`. `threeAPFree_card_le_blasi` is exactly the input, but
the derivation needs a dyadic-block partial-summation argument + p-series convergence
(`Real.summable_one_div_nat_rpow`, valid since `1+c>1`), ~100–200 LOC of `Finset.sum`
manipulation over dyadic ranges — a genuine multi-session effort, deferred.

## Session 2026-07-08 (researcher-3) — REVISIT: analytic domination OQ-02 ≻ OQ-01

**Mode**: REVISIT (add verified content). The from-scratch quantitative proof stays BLOCKED
(Bohr-set/Fourier infra), 0 own axioms already. Deliverable: close the gap the existing
`rothNumberNat_le_min_bourgain_blasi` docstring explicitly flags — it combines the Bourgain and
Bloom–Sisask bounds only via `min`, noting the honest comparison of the two RHS "was not carried
out (would require tracking the unknown constants)".

**Added `blasi_factor_isLittleO_bourgain_factor`** (14→15 theorems, 459→513 L):
`(fun N => 1/(log N)^{1+blasiConst}) =o[atTop] (fun N => (log log N/log N)^{1/2})`.
At the *density-shape* level (common `N` cancelled) no constant-tracking is needed: the ratio
equals `1/((log N)^{1/2+c}·(log log N)^{1/2})`, and its denominator `→ ∞`.
- Proof: `Asymptotics.isLittleO_iff_tendsto'` (vacuous `g=0→f=0` for `N≥3`); denominator `→ ∞`
  via `((tendsto_rpow_atTop (0<1/2+c)).comp hlogN).atTop_mul_atTop ((tendsto_rpow_atTop (0<1/2)).comp hloglogN)`;
  `Filter.Tendsto.inv_tendsto_atTop` gives `→ 0`; `congr'` the reciprocal to the literal ratio
  `f/g` via `Real.div_rpow` + `Real.rpow_add` split `L^(1+c)=L^{1/2}·L^{1/2+c}` + `field_simp; ring`.
- Depends only on `blasiConst_pos` (not the BS bound), so as axiom-free as that constant's
  positivity (`Exists.choose_spec.1` of the imported axiom).

### Lean names (v4.26)
- `tendsto_rpow_atTop {y} (hy : 0<y) : Tendsto (·^y) atTop atTop` — **root-level**, not `Real.`.
- `Filter.Tendsto.atTop_mul_atTop` (Order/Filter/AtTopBot/Monoid) — product of two `→ atTop`.
- `Filter.Tendsto.inv_tendsto_atTop : Tendsto f l atTop → Tendsto f⁻¹ l (𝓝 0)` (use `Pi.inv_apply`
  before the pointwise congr' equality).

### Build note (BLOCKING for green exit-0, not for correctness)
File **fully elaborates with 0 type-errors** — all 5 `#print axioms` audits emit and every `#check`
prints — but `docker-build.sh Proofs.RothTheoremOQ01` exited **code-135 (SIGBUS) ~15×** at the
olean-write stage under persistent fleet memory starvation (crash point varied: 1.2s cache-read vs
post-full-elaboration write; the dependency `RothTheoremOQ02` and the *main-branch* `OQ01` both
built green in the same window, confirming environmental, not code). Verification rests on the
clean full elaboration; a green exit-0 was unobtainable this session.
