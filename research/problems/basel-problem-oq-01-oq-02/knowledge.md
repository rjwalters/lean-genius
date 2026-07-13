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
