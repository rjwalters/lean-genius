
## Session 2026-07-09 (researcher-3) — higher-mode strict damping |n|≥2 (VERIFIED)

`AreaOfCircleOQ01OQ02OQ02OQ02.lean` (IsoperimetricFourier, second-derivative Fourier
identity ĉₙ(f'') = −n²·ĉₙ(f)) already had the magnitude identity
`norm_fourierCoeffOn_deriv2_eq` (‖ĉₙ(f'')‖ = n²‖ĉₙ(f)‖) and the Wirtinger equality case
`norm_fourierCoeffOn_deriv2_eq_of_natAbs_one` (|n|=1 ⟹ equality). Its docstrings promised
the *strict* higher-mode gap in prose but never stated it.

Added **`four_mul_norm_fourierCoeffOn_le_deriv2`**: for |n| ≥ 2,
`4·‖ĉₙ(f)‖ ≤ ‖ĉₙ(f'')‖` (eigenvalue magnitude n² ≥ 4), completing the Wirtinger dichotomy
(equality on the first harmonic vs damping-by-≥4 on every higher mode — why Hurwitz's
equality analysis forces all but n=±1 to vanish, leaving the circle). Proof: rewrite via the
magnitude identity, then `(4:ℝ) ≤ (n:ℝ)²` from `2 ≤ |n|` (`Int.abs_eq_natAbs` + `Int.cast_abs`
+ `sq_abs` + nlinarith), close by nlinarith with `norm_nonneg`.

VERIFIED green via direct lean-elab vs pinned Mathlib v4.26.0 (docker containerd blob I/O down):
built the `Proofs.AreaOfCircleOQ01OQ02OQ02` dep olean into /tmp (Mathlib-only parent), elaborated
target with it on LEAN_PATH — exit 0, no errors, `#print axioms` = `[propext, Classical.choice,
Quot.sound]`. Depth-4 slug → 0 follow-ups per OQ-chain depth guard. No gallery meta references this
file (pure research-layer). File now 177→202 lines, 7→8 theorems.

## Session 2026-07-12 (researcher-9) — FIRST-ORDER Wirtinger ladder (VERIFIED 0-axiom, PR #38567)

The file's narrative is Wirtinger's inequality but it skipped the base **first-order**
ladder (jumped straight to `‖ĉₙ(f'')‖=n²‖ĉₙ(f)‖`). Added the genuine classical content
for the C¹ first derivative from the parent IBP identity `ĉₙ(f')=i·n·ĉₙ(f)`:
- `norm_fourierCoeffOn_deriv_eq` : ‖ĉₙ(f')‖ = |n|·‖ĉₙ(f)‖ (exact per-mode magnitude)
- `norm_fourierCoeffOn_le_deriv` : ‖ĉₙ(f)‖ ≤ ‖ĉₙ(f')‖ (Wirtinger's inequality, mode-wise)
- `norm_fourierCoeffOn_deriv_eq_of_natAbs_one` : equality on first harmonic |n|=1
- `norm_fourierCoeffOn_lt_deriv_of_natAbs_ge_two` : strict |n|≥2
- `norm_fourierCoeffOn_deriv2_eq_abs_mul_deriv` : n²=|n|·|n| composition law d²=d∘d
- `fourierCoeffOn_deriv_eq_zero_iff` : first-order kernel iff
Placed as SECTION IV, complementary to (not superseding) Section III's general
(i·n)ᵐ complex-eigenvalue identity (#38380). Proof kit: `simp only [norm_mul,
Complex.norm_I, Complex.norm_intCast, one_mul]` collapses ‖i·n·ĉ‖→|n|·‖ĉ‖; `Int.one_le_abs hn`.

### Infra gotchas (this session)
- **origin/main advanced past worktree base** (532→659-line file via #38380 iterated-deriv
  section). First "successful" compile was accidentally against the MAIN-repo copy (evolved,
  different file). Fix: `git reset --hard origin/main` in worktree, re-apply to CURRENT file,
  renumber section III→IV. ALWAYS diff worktree vs origin/main before editing shared files.
- **docker-build.sh SIGBUS (exit 135)** on corrupt cache blob `Mathlib/Algebra/Group/Hom/
  Instances.trace` — infra, reproducible 3x. Verified via direct single-file `lean` elaboration
  (LEAN_PATH=main-repo packages+Proofs oleans, `#print axioms` on /tmp copy of WORKTREE file).

## Session 2026-07-19 (researcher-1) — Wirtinger's inequality in INTEGRAL form (VERIFIED, 0-axiom)

The file had 34 per-mode `fourierCoeffOn` inequalities but no INTEGRAL statement — every prior
session added another mode-wise variant while the actual analytic core of Hurwitz (the `∫`-level
inequality the geometric assembly consumes) was still missing. Closed that gap with SECTION V
(2 new theorems, 0 axioms):

- `memLp_two_ofReal_comp_continuous (g) (hg : Continuous g) : MemLp (ofReal ∘ g) 2
  (volume.restrict (Ioc 0 (2π)))` — the square-integrability hypothesis Parseval's identity needs.
  Continuous ⟹ bounded on compact `[0,2π]` (`IsCompact.exists_bound_of_continuousOn`) ⟹ `MemLp`
  on the finite measure (`MemLp.of_bound`, instance `isFiniteMeasure_restrict_Ioc`).
- `integral_sq_le_integral_sq_deriv (f) (hf : ContDiff ℝ 1 f) (hperiod) (hmean : ∫₀^{2π} f = 0)
  : ∫₀^{2π} f² ≤ ∫₀^{2π} (f')²` — **Wirtinger's inequality, integral form.** Proof: sum the
  existing per-mode `norm_fourierCoeffOn_le_deriv` (‖ĉₙ(f)‖ ≤ ‖ĉₙ(f')‖) against Mathlib's Parseval
  `hasSum_sq_fourierCoeffOn` via `hasSum_le`; the zero mode is killed by `hmean`
  (`ĉ₀(f) = (2π)⁻¹∫f = 0`, computed from `fourierCoeffOn_eq_integral` + `fourier_zero` +
  `intervalIntegral.integral_ofReal`); cancel the positive `(2π)⁻¹` scalar (`le_of_mul_le_mul_left`).

Key Mathlib API: `hasSum_sq_fourierCoeffOn` / `tsum_sq_fourierCoeffOn` (Parseval for `fourierCoeffOn`,
`Analysis/Fourier/AddCircle.lean`), `MemLp.of_bound`, `IsCompact.exists_bound_of_continuousOn`,
`pow_le_pow_left₀`, `Complex.norm_real`, `sq_abs`.

VERIFICATION: Docker `docker-build.sh Proofs.AreaOfCircleOQ01OQ02OQ02OQ02` — Build completed
successfully (8577 jobs), v4.31.0. `#print axioms` on BOTH new theorems =
`[propext, Classical.choice, Quot.sound]` (0 extra axioms, no sorryAx/ofReduceBool). File 786→850
lines, 34→36 theorems, still 0 sorries / 0 axioms.

REMAINING WORK (genuine, not filler): the geometric assembly into `C² ≥ 4πA` still needs (a) the
AREA formula `A = (1/2)∮(x dy − y dx)` expressed in Fourier coefficients (needs Green's theorem
glue) and (b) matching the perimeter constraint. The integral-form Wirtinger inequality is the
analytic input those steps consume; the missing piece is now GEOMETRIC, not analytic. Depth-4
slug → 0 follow-ups per OQ-chain depth guard.
