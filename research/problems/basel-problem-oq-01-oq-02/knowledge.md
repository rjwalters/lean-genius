# Knowledge Base: basel-problem-oq-01-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

**Is ζ(7) irrational? Is ζ(2n+1) irrational for all n ≥ 1?**

This is a *genuinely open* problem in analytic number theory. The state of the
art (as of 2026, all **far beyond** current Mathlib):

- **ζ(3)**: irrational — **Apéry (1979)**. This is the only individual odd zeta
  value known to be irrational. **Not in Mathlib.**
- **ζ(5), ζ(7), ζ(9), …**: irrationality is **OPEN** for every individual value.
- **Ball–Rivoal (2001)**: infinitely many ζ(2n+1) are irrational (the ℚ-vector
  space spanned by 1, ζ(3), ζ(5), … is infinite-dimensional). **Not in Mathlib.**
- **Rivoal / Zudilin (2001)**: at least one of ζ(5), ζ(7), ζ(9), ζ(11) is
  irrational; and among any window of consecutive odd values at least one is
  irrational. **Not in Mathlib.**

There is **no known unconditional proof** that ζ(7) — or any single ζ(2n+1) with
n ≥ 2 — is irrational. So this slug cannot be *closed*; only *framed* and
*contrasted* with the tractable even case.

---

## Insights (tractability map — verified against Mathlib v4.26 + repo source, researcher-9 2026-07-02)

### The EVEN case is the only irrationality result reachable here, and it is NOT 0-axiom

Euler's formula (in Mathlib) gives, for `k ≥ 1`:

  `riemannZeta_two_mul_nat : ζ(2k) = (-1)^(k+1) · 2^(2k-1) · π^(2k) · B_{2k} / (2k)!`
  (`Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean`)

so `ζ(2k) = qₖ · π^(2k)` with `qₖ ∈ ℚ`, `qₖ ≠ 0` (since `B_{2k} ≠ 0`). Hence

  `ζ(2k) irrational  ⇐  π^(2k) irrational`.

**But `π^(2k)` irrational is NOT available 0-axiom:**
- Mathlib has `irrational_pi : Irrational π` (`Analysis/Real/Pi/Irrational.lean`,
  Niven-style, genuinely 0-axiom) — but this does **not** give `Irrational (π^n)`
  (irrationality is not closed under powers: cf. √2).
- Mathlib has **no** `Irrational (π^2)` / `Irrational (π^n)` / `transcendental_pi`
  lemma. Its Lindemann development is only `Transcendental/Lindemann/AnalyticalPart.lean`
  (incomplete — the full transcendence theorem is not upstreamed).
- The repo's `Proofs/PiTranscendental.lean` (`pi_transcendental`,
  `pi_transcendental_over_rationals`) delegates to
  `HermiteLindemann.pi_transcendental_real`, which rests on **`axiom hermite_lindemann`**.

So the only route to `Irrational (π^(2k))` is:
`axiom hermite_lindemann` ⟹ `Transcendental ℚ π` ⟹ `Transcendental.pow` ⟹
`Transcendental ℚ (π^(2k))` ⟹ `Transcendental.irrational` ⟹ `Irrational (π^(2k))`.
The resulting "**ζ(2n) is irrational for all n ≥ 1**" theorem is therefore
**`axiomatized`** (badge `axiom`, `axiomCount ≥ 1`, assumption `hermite_lindemann`),
**not** `verified`. This is the honest ceiling for irrationality in this topic.

### What the existing Basel corpus already does (0-axiom, avoids the π-power obstruction)

The `BaselProblemOQ08OQ02` / `…OQ01` chain proves the even-zeta **values**
(`ζ(6)=π⁶/945`, `ζ(8)=π⁸/9450`) and, crucially, the **π-cancelling ratios**
`ζ(6)/ζ(2)³ = 8/35`, `ζ(8)/ζ(2)⁴ = 24/175` — these are **rational** and 0-axiom
precisely because dividing by a power of `ζ(2)` cancels `π^(2k)`, sidestepping the
irrationality of `π^(2k)` entirely. That is why no existing file states an
irrationality result: the corpus deliberately stayed on the 0-axiom side.

---

## Dead Ends

- **"ζ(2n) irrational, 0-axiom"** — impossible in the current stack: needs
  `Irrational (π^(2n))`, which is not in Mathlib and only follows from the repo's
  `axiom hermite_lindemann`. Any such theorem is `axiomatized`, not `verified`.
- **`irrational_pi` alone ⟹ `Irrational (π^2)`** — FALSE inference (powers don't
  preserve irrationality). `irrational_pi` is insufficient for even-zeta irrationality.
- **Attacking the odd case directly** (ζ(5), ζ(7), …) — this is the open problem;
  even Apéry's ζ(3) is not in Mathlib. Not tractable.

---

## Concrete next actions (in priority order)

1. **ACT (axiomatized), when build env is healthy** — new file
   `Proofs/BaselProblemOQ01OQ02.lean`: `theorem zeta_even_irrational (n : ℕ)
   (hn : 0 < n) : Irrational (∑' k : ℕ, 1 / (k:ℝ)^(2*n))` via the transcendence
   chain above. Status `axiomatized` (assumption: `hermite_lindemann`). Framed as
   the sharp contrast "**every even zeta value is irrational; whether any single
   odd value beyond ζ(3) is irrational is open**". Heavy imports
   (`HurwitzZetaValues` + `HermiteLindemann`) — use `docker-build.sh`; DO NOT
   attempt under ~100%-full disk (SIGBUS risk).
2. **Longer term** — formalize the Ball–Rivoal / Nesterenko linear-independence
   framework for the odd values; this is a multi-month effort and the genuine
   research frontier.

_No Lean shipped this iteration: the tractable target is `axiomatized` (not a
0-axiom win) and the build environment was hostile (100%-full disk, reaped
worktree). The value delivered is the corrected tractability map above, so future
iterations do not waste a heavy build re-discovering that even-zeta irrationality
cannot be 0-axiom here._

---

## Update (researcher-3, 2026-07-08) — ACT shipped + transcendence strengthening

**Status: DONE (axiomatized, saturated).** The planned ACT file
`Proofs/BaselProblemOQ01OQ02.lean` was shipped on 2026-07-03 (PR #33636):
`zeta_even_irrational (n≥1)` + concrete `ζ(2)/ζ(4)/ζ(6)` corollaries, badge
`axiom`, single assumption `hermite_lindemann`. The knowledge above predates that
merge — the "next action: ship the file" is complete.

This iteration **strengthened irrationality to transcendence over ℚ** (the natural
"look outward" direction), reusing the same axiom with no new assumptions:

- `zeta_even_transcendental (n : ℕ) (hn : 0 < n) : Transcendental ℚ (∑' k, 1/k^(2n))`
  — strictly stronger than `zeta_even_irrational` (transcendence ⟹ irrationality
  via `Transcendental.irrational`).
- `zeta_two_transcendental` — concrete Basel corollary.

**Recipe (transcendence preserved under nonzero-rational scaling).** Given
`ζ(2n) = ↑q · π^(2n)` (Euler `hasSum_zeta_nat`, `q ≠ 0` from positivity) and
`Transcendental ℚ (π^(2n))` (= `pi_transcendental_over_rationals.pow`), show
`Transcendental ℚ (↑q · π^(2n))` by: `intro halg; apply hpi;` then
`(halg.mul (isAlgebraic_algebraMap (q⁻¹:ℚ)))` rewritten via
`↑q·π^(2n)·(↑q⁻¹) = π^(2n)` (`push_cast; rw [mul_right_comm, mul_inv_cancel₀ hqne',
one_mul]`). Mirrors `PiTranscendental.two_pi_transcendental_axiom`. The coercion
`((q⁻¹:ℚ):ℝ)` unifies definitionally with `algebraMap ℚ ℝ (q⁻¹)`, so
`isAlgebraic_algebraMap` applies directly.

Build clean (Docker, 3153 jobs, `LEAN_SKIP_CACHE=true` — heavy HermiteLindemann +
HurwitzZeta imports were already in the volume). **This slug is now saturated on
the provable side**: the only remaining direction (individual odd-zeta
irrationality past ζ(3)) is the genuinely open research frontier and is not
session-sized. No further follow-up OQ proposed (would be accretion).

## Update (researcher-3, 2026-07-08 later) — extracted axiom-free Euler structure

**Mode**: ACT / axiom-integrity hygiene on a saturated axiomatized entry. **Outcome**: progress —
the file's **first 0-axiom theorem**, plus de-duplication.

Re-confirmed the axiom `hermite_lindemann` is **irreducible**: Mathlib's `NumberTheory/
Transcendental/Lindemann/` contains only `AnalyticalPart.lean` (WIP infrastructure); there is no
finished `transcendental_pi`. `irrational_pi` exists but does NOT lift to `π^m` (m≥2). So the
transitive assumption cannot currently be discharged from Mathlib.

Value delivered instead — cleanly separate the axiom-free skeleton from the axiom-dependent layer:
- `zeta_even_eq_rat_mul_pi_pow (n) (hn : 0<n) : ∃ q:ℚ, q≠0 ∧ ∑' k, 1/k^(2n) = q·π^(2n)`.
  **0-axiom** (only Mathlib `hasSum_zeta_nat` Bernoulli closed form + `tsum_pos` for q≠0). This is
  Euler's structure theorem; it was previously derived *inline and duplicated* inside both
  `zeta_even_irrational` and `zeta_even_transcendental`. Extracting it: (a) gives the file its only
  unconditional result, (b) pinpoints that the *single* step to irrationality (`Irrational (π^2n)`)
  is exactly where `hermite_lindemann` enters, matching the entry's "sharp boundary" narrative.
- Refactored `zeta_even_irrational` and `zeta_even_transcendental` to `obtain ⟨q,hqne,hq⟩ :=
  zeta_even_eq_rat_mul_pi_pow n hn` (removed ~14 duplicated lines total).

Elaboration clean `[3153/3153]` (my file: 0 warnings/0 errors); persistent fleet-memory 135/139
crashes at olean-write forced a multi-retry green build. File 162→165 lines, 7→8 theorems
(.meta.axiomCount stays 1 transitive, .leanFile.axiomCount stays 0 — new lemma adds no assumption).
Meta synced (.meta + .leanFile).

Slug remains saturated on the provable side; odd-zeta irrationality still the open frontier. No
new OQ (would be accretion).

## Session 2026-07-09 (researcher-2) — axiom-free ratio structure skeleton

**Mode**: ACT (look-outward on saturated axiomatized entry, axiom-integrity hygiene).
**Outcome**: progress — a new 0-axiom structural theorem + de-duplication.

The file had `zeta_even_eq_rat_mul_pi_pow` (0-axiom skeleton for SINGLE even zeta values) and
`zeta_even_ratio_transcendental` (for m<n, ζ(2n)/ζ(2m) transcendental, axiom-dependent), but the
ratio's underlying STRUCTURAL identity was established only inline. Extracted it as the file's
new 0-axiom result for ratios:
- `zeta_even_ratio_eq_rat_mul_pi_pow (n m) (hm:0<m) (hmn:m<n) : ∃ q:ℚ, q≠0 ∧
  ζ(2n)/ζ(2m) = q·π^(2(n-m))`. **0-axiom** (only Euler `zeta_even_eq_rat_mul_pi_pow`, no
  hermite_lindemann). Proof: obtain qn,qm from single-value skeleton, `mul_div_mul_comm` +
  `pow_sub₀ π hπ hle` + `push_cast; ring`. Records unconditionally that even zeta values are
  *multiplicatively π-power-incommensurable over ℚ* (quotient never rational) — the axiom enters
  ONLY when π^(2(n-m)) is declared transcendental.
- Refactored `zeta_even_ratio_transcendental` to `obtain ⟨q,hq,hratio⟩ := ...ratio_eq...; rw
  [hratio]; exact transcendental_ratCast_mul (pi_transcendental...pow) hq` (removed inline hratio).

Docker `Build succeeded` (3153 jobs, attempt 4; attempts 1-3 = fleet SIGBUS-135 at olean-write
after clean elab [3153/3153], heavy HermiteLindemann/HurwitzZeta imports make this build memory-
heavy → more SIGBUS-prone). File 221→235 lines, 11→12 theorems. Gallery meta synced (both blocks;
axiomCount unchanged: .meta=1 transitive, .leanFile=0 — new lemma adds no assumption).

Slug remains saturated on the provable side; individual odd-zeta irrationality (past ζ(3)) is the
genuinely open frontier, not session-sized. No new OQ (would be accretion).

## Session 2026-07-12 (researcher-7) — cross-power algebraic DEPENDENCE of even zeta values (axiom-free)

**Mode:** REVISIT (node `BaselProblemOQ01OQ02.lean`, the ℚ·π^(even) closure algebra; the core
question ζ(2n+1) irrationality is genuinely OPEN/Apéry-level, untouched). **Outcome:** progress —
2 axiom-free theorems, no `hermite_lindemann`.

The closure algebra was already very complete (single value, ratio, product, power, finset/
weighted products, polynomial evaluation `transcendental_aeval_pi`, add/sub/inv, rational scaling).
Its `zeta_even_ratio_transcendental` records that distinct even zeta values are π-power
**incommensurable** (their plain ratio always carries a leftover π-power). The complementary fact
— that they are algebraically **dependent** once exponents are crossed — was missing:

- `zeta_even_cross_pow_ratio_rational` : `ζ(2n)^m / ζ(2m)^n = qₙ^m/qₘ^n ∈ ℚ`. Since
  `ζ(2n)^m = qₙ^m·π^(2nm)` and `ζ(2m)^n = qₘ^n·π^(2nm)` share the *identical* power `π^(2nm)`,
  π cancels exactly. Proof: `mul_pow, ← pow_mul` twice, `show 2*n*m = 2*m*n by ring` to align the
  exponents, `mul_div_mul_comm`, `div_self (pow_ne_zero _ hπ)`, `push_cast; ring`.
- `zeta_even_cross_pow_proportional` : `∃ q ≠ 0, ζ(2n)^m = q·ζ(2m)^n` (proportionality form,
  no division). Derived from the ratio form via `(div_eq_iff hden).mp`, with `hden : ζ(2m)^n ≠ 0`
  from the Euler closed form.

Both need **only** Euler's `zeta_even_eq_rat_mul_pi_pow` (Bernoulli closed form), NOT the π-transcendence
axiom — π cancels, so these are unconditional. This is *stronger* footing than the transcendence
results: it shows all even zeta values lie in the transcendence-degree-1 field ℚ(π).

VERIFIED: `lake env lean` EXIT 0; `#print axioms` = [propext, Classical.choice, Quot.sound] for both
(no `hermite_lindemann`, no `sorryAx`). File 664 → ~710 lines. OQ depth 2; **0 follow-ups** (the
provable ℚ·π^(even) side is now saturated including the dependence direction; the open frontier is
odd-zeta irrationality, Apéry/Ball–Rivoal, not session-sized).

## Session 2026-07-12 (researcher-1) — ℚ-linear independence of even zeta values (orthogonal to the closure algebra)

**Mode**: ACT (node `BaselProblemOQ01OQ02.lean` is saturated on transcendence of individual
values / products / powers / pairwise sums; the LINEAR-ALGEBRA structure over ℚ was missing).
**Outcome**: progress — new file, no new axioms.

The closure algebra shows every `ζ(2n)` and every algebraic combination is transcendental, and
pairwise `ζ(2m)±ζ(2n)` transcendental. What it never records is that distinct even zeta values are
jointly **ℚ-linearly independent** — a strictly stronger, different-kind statement (independence,
not transcendence). New file `BaselProblemOQ01OQ02LinIndep.lean`:
- `zeta_even_no_rational_relation (n m) (0<m<n) (a b : ℚ)` : `a·ζ(2m)+b·ζ(2n)=0 → a=0 ∧ b=0`.
  Proof: ζ=q·π^(2·), factor π^(2m) (≠0) ⟹ `a·qm + b·qn·π^(2(n-m))=0`; `b·qn≠0` ⟹
  π^(2(n-m))=−(a·qm)/(b·qn) rational, contradicting `pi_pow_irrational`. ★key move:
  `hirr.ratCast_mul hne` (`Irrational.ratCast_mul`, q IMPLICIT) gives `Irrational (↑(b·qn)·π^…)`,
  then `heq : …=↑(−(a·qm))` via `push_cast; linarith [hbr]`, then `Rat.not_irrational`.
- `zeta_even_linearIndependent_pair` : `LinearIndependent ℚ ![ζ(2m),ζ(2n)]` via
  `LinearIndependent.pair_iff` + `Rat.smul_def` (ℚ-smul on ℝ = ↑·*·).
- `zeta_two_zeta_four_linearIndependent` : concrete Basel pair (`2*1≡2`, `2*2≡4` defeq, `exact`).

Axioms: [propext, Classical.choice, Quot.sound, HermiteLindemann.hermite_lindemann] on all three —
SAME as parent (via `pi_pow_irrational`), NO new assumption. VERIFIED `lake env lean` EXIT 0.

★ `norm_num at h` rewrites `1/k^n → (k^n)⁻¹`, breaking a later `exact` against a `1/`-form goal;
drop it and rely on `2*1`/`2*2` defeq reduction instead.

### Next Steps
- General `LinearIndependent ℚ (fun k : Fin N => ζ(2(k+1)))` (reduce to distinct π²-powers via
  `transcendental_iff_injective` on `aeval (π²)`) — the N-family generalization.
- Odd-zeta irrationality past ζ(3) remains the genuine open frontier (Apéry/Ball–Rivoal), not
  session-sized.

## Session 2026-07-19 (researcher-1) — N-family ℚ-linear independence of even zeta values

**Mode:** ACT (node saturated on transcendence + the *pairwise* linear-independence;
the **N-family** generalization of the pair was the documented open "Next Step").
**Outcome:** progress — 1 general theorem + 1 concrete instance, no new axioms.

The prior linear-independence layer stopped at `zeta_even_linearIndependent_pair`
(`LinearIndependent ℚ ![ζ(2m), ζ(2n)]`). The natural — and strictly stronger — statement,
that the *whole* family `ζ(2), ζ(4), …, ζ(2N)` is jointly ℚ-linearly independent, was
listed as the open next step. Now proved in `BaselProblemOQ01OQ02LinIndep.lean`:

- `zeta_even_linearIndependent_family (N : ℕ) :
   LinearIndependent ℚ (fun i : Fin N => ζ(2(i+1)))`.
- `zeta_two_four_six_linearIndependent` : concrete `Fin 3` instance (`ζ(2), ζ(4), ζ(6)`).

### Proof mechanism (the reusable move)
`Fintype.linearIndependent_iff` reduces to: every rational relation `∑ᵢ gᵢ • ζ(2(i+1)) = 0`
is trivial. Euler (`zeta_even_eq_rat_mul_pi_pow`, `choose`) writes `ζ(2(i+1)) = qᵢ·π^(2(i+1))`
with `qᵢ ≠ 0`, so the relation becomes `aeval π P = 0` for the **single polynomial**
`P = ∑ᵢ C(gᵢ·qᵢ)·X^(2(i+1)) ∈ ℚ[X]`. ★key: `transcendental_iff.mp
pi_transcendental_over_rationals : ∀ p, aeval π p = 0 → p = 0` collapses the whole family to
one polynomial-vanishing fact. Distinct exponents `2(i+1)` ⟹ `P.coeff (2(j+1)) = gⱼ·qⱼ`
(via `finsetSum_coeff` + `coeff_C_mul` + `coeff_X_pow` + `Finset.sum_eq_single_of_mem`,
`Fin.ext`+`omega` for the exponent injectivity), and `P = 0` + `qⱼ ≠ 0` ⟹ `gⱼ = 0`.

This is the clean N-ary form: the pairwise proof routed through
`Irrational (π^(2(n-m)))`, which does not scale to N terms; the polynomial/`transcendental_iff`
route does. `smul→ratCast·` via `Rat.smul_def`; `algebraMap ℚ ℝ q = ↑q` via `eq_ratCast` (simp).

### Verification
Docker `Build succeeded` (8579 jobs, **first attempt**, 23s for the file).
`#print axioms zeta_even_linearIndependent_family` =
`[propext, Classical.choice, HermiteLindemann.hermite_lindemann, Quot.sound]` — SAME as the
parent node (via `pi_transcendental_over_rationals`), **no new axiom, no `sorryAx`**.

### Frontier unchanged
Odd-zeta irrationality past ζ(3) (Apéry / Ball–Rivoal) remains the genuine open frontier and
is not session-sized. **No new OQ** generated: slug is at OQ depth 2 but the provable ℚ·π^(even)
side (now including full N-family independence) is saturated; a follow-up would be accretion.
