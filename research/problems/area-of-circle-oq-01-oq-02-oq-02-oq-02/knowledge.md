
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
