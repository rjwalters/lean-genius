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
