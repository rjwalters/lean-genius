# Sign of the quadratic Gauss sum (Gauss's hard theorem)

**Pool id:** `quadratic-gauss-sum-square-oq-01` · **Tier B** · significance 6 · tractability 4

## Problem

For an odd prime `p` and a primitive additive character `ψ : ZMod p → ℂ`, let
`g = gaussSum (chiC p) ψ`. The parent gallery entry proves `g² = (-1)^((p-1)/2)·p`,
and the **verified** entry `quadratic-gauss-sum-square-oq-01` (slug collision — it is
the DICHOTOMY entry) extracts `g.im = 0` for `p ≡ 1 (mod 4)`, `g.re = 0` for
`p ≡ 3 (mod 4)`, and `‖g‖² = p`. The open target here is **Gauss's hard sign theorem**:

    g = +√p     (p ≡ 1 mod 4),
    g = +i·√p   (p ≡ 3 mod 4).

## Session 2026-06-19 (Session 1) — ORIENT, reduction to a single positivity

**Mode:** FRESH · **Outcome:** progress (verified reduction; deep crux remains open)

### What I did
- Confirmed the dichotomy + magnitude already exist and are verified (0 sorries) in
  `QuadraticGaussSumSquareOQ01.lean`.
- Confirmed Mathlib (v4.26.x) has **no** sign determination and no finite-Fourier
  determinant/eigenvalue infrastructure (`NumberTheory/GaussSum.lean` stops at the
  square identity `gaussSum_sq`).
- Wrote and **built (sorry-free, axiom-free)** `Proofs/QuadraticGaussSumSignReduction.lean`:
  - `gaussSum_eq_pm_sqrt` — strengthens "g real" to `g = ±√p` (p ≡ 1).
  - `gaussSum_eq_pm_I_sqrt` — strengthens "g imaginary" to `g = ±i√p` (p ≡ 3).
  - `gaussSum_eq_sqrt_iff_re_pos` — **`g = √p ↔ 0 < g.re`** (p ≡ 1).
  - `gaussSum_eq_I_sqrt_iff_im_pos` — **`g = i√p ↔ 0 < g.im`** (p ≡ 3).
  - Docker build: `✔ [7745/7745] Built Proofs.QuadraticGaussSumSignReduction`.

### Key findings
- The entire open content of Gauss's hard theorem collapses to **one real inequality**:
  `0 < Re(g)` (p ≡ 1) / `0 < Im(g)` (p ≡ 3). Everything else (which axis, magnitude,
  the ± alternative) is elementary and now machine-checked.
- Both classical routes target exactly this positivity:
  - **Schur** — eigenvalue multiplicities of the n×n DFT matrix (`ζ^{jk}`); needs
    DFT-spectrum infra Mathlib lacks. Estimate ≫1000 lines.
  - **Dirichlet** — Poisson summation / theta functional equation; heavy analysis infra.
    Estimate ≫1000 lines.

### Infrastructure assessment
**Needed:** sign of the quadratic Gauss sum (`0 < Re g` resp `0 < Im g`).
**Size estimate:** >1000 lines either route (no Mathlib DFT-determinant or theta infra).
**Decision:** BLOCKED short-term — but the reduction above is the shared final step of
both routes, so it is reusable groundwork rather than throwaway.

### Files modified
- `proofs/Proofs/QuadraticGaussSumSignReduction.lean` (new, verified)
- `proofs/Proofs.lean` (import)
- `src/data/research/problems/quadratic-gauss-sum-square-oq-01.json` (new knowledge)

### Next steps
- Attack `0 < Re(gaussSum (chiC p) ψ)` for `p ≡ 1 (mod 4)` via the Schur route once (or if)
  DFT eigenvalue-multiplicity infrastructure becomes available in Mathlib.
- Consider contributing the four-point pinning / reduction lemmas toward a future
  Mathlib `GaussSum` sign development.

## Session 2026-06-19 (Session 3) — p = 5 base case (the `p ≡ 1 mod 4` branch)

**Mode:** depth-first · **Outcome:** progress (first sign determination on the OTHER residue class)

### What I did
- Companion file `Proofs/QuadraticGaussSumSignSmallFive.lean` (new, verified): the smallest
  case of `p ≡ 1 (mod 4)`, mirroring the verified `QuadraticGaussSumSignSmall` (p = 3).
  - `gaussSum_five_eq` — five-term enumeration over `ZMod 5` collapses to `ζ - ζ² - ζ³ + ζ⁴`
    (`quadraticChar (ZMod 5)` = `0,1,-1,-1,1`).
  - `gaussSum_five_re` — folding `cos(6π/5)=cos(4π/5)`, `cos(8π/5)=cos(2π/5)` gives
    `Re g = 2·cos(2π/5) − 2·cos(4π/5)`.
  - `gaussSum_five_re_pos` — **`0 < Re g`** from the coarse sign facts `cos(2π/5) > 0`,
    `cos(4π/5) < 0` (no exact radical values needed). This is the open positivity crux,
    confirmed in the base case.
  - `gaussSum_five_eq_sqrt_five` — feeds `gaussSum_five_re_pos` into the reduction lemma
    `gaussSum_eq_sqrt_iff_re_pos` to get the FULL determination `gaussSum (chiC 5) ψ₅ = +√5`
    (not `−√5`) — the first sign determination for the `p ≡ 1 (mod 4)` branch.
  - Verified by single-file olean-chain compile (Docker host-blocked); `#print axioms` =
    `[propext, Classical.choice, Quot.sound]` only (axiom-free).

### Key findings
- Both residue classes now have a machine-checked base witness for the open crux:
  `p = 3` (`0 < Im g`, Session 2) and `p = 5` (`0 < Re g`, this session).
- The positivity at `p = 5` needs only `cos(2π/5) > 0` and `cos(4π/5) < 0`, sidestepping the
  exact value `cos(2π/5) = (√5−1)/4`. The same coarse-sign idea generalises to the partial
  sums of any `p ≡ 1 (mod 4)`, but the general count of positive vs. negative cosine
  contributions is exactly the open DFT-spectrum content.

### Files modified
- `proofs/Proofs/QuadraticGaussSumSignSmallFive.lean` (new, verified)
- `proofs/Proofs.lean` (import)

### Next steps
- `p = 7` (next `p ≡ 3 mod 4`) as a further witness, or pivot to the general DFT route.

## Session 2026-06-19 (Session 4) — diagonal representation g = ∑ ψ(k²)

**Mode:** FRESH (depth-first on existing MODERATE knowledge) · **Outcome:** progress (verified reusable infrastructure)

### What I did
- New companion file `Proofs/QuadraticGaussSumDiagonal.lean` (verified, axiom-free):
  - `card_sqrts_cast` — `(#{x : ZMod p | x² = t}.card : ℂ) = chiC p t + 1`, the ℂ-transport
    of Mathlib's `quadraticChar_card_sqrts` through the ring hom `ℤ → ℂ` defining `chiC`.
  - `gaussSum_chiC_eq_sum_sq` — **`gaussSum (chiC p) ψ = ∑ k, ψ(k²)`** for any primitive
    additive character `ψ`. Proof: `Finset.sum_fiberwise_of_maps_to` groups `∑ ψ(k²)` by the
    value `t = k²`; the fibre `{k : k² = t}` has size `χ(t)+1`, so
    `∑ ψ(k²) = ∑ (χ(t)+1)·ψ(t) = gaussSum + ∑ ψ(t)`, and `∑ ψ(t) = 0`
    (`AddChar.sum_eq_zero_of_ne_one`, since primitivity ⟹ `ψ ≠ 1` via `mulShift_one`).
  - Verified by single-file olean-chain compile (Docker host-blocked); `#print axioms` =
    `[propext, Classical.choice, Quot.sound]` only (axiom-free).

### Key findings
- The diagonal form is the **universal starting point** of every classical proof of the
  sign theorem (Gauss/Schur/Dirichlet/Kronecker), and it was absent from Mathlib (which has
  `gaussSum_sq` and `quadraticChar_card_sqrts` but never combines them into the `k²` form).
- It strips the Legendre-symbol weighting: with the standard character `ψ(x)=ζ_p^x` it is
  literally `g = ∑ ζ_p^{k²}`, so the open crux `0 < Re g` becomes positivity of
  `∑ cos(2π k²/p)`.
- It does NOT make `p = 7` tractable: `∑ζ^{k²} = 1 + 2ζ + 2ζ² + 2ζ⁴` still requires the
  cubic-irrational value `cos(2π/7)`, unlike the quadratic-radical values at `p = 3, 5`.
  The next genuine advance is the general DFT-spectrum content, still >1000 lines.

### Files modified
- `proofs/Proofs/QuadraticGaussSumDiagonal.lean` (new, verified)
- `proofs/Proofs.lean` (import)
- `src/data/research/problems/quadratic-gauss-sum-square-oq-01.json` (knowledge)

### Next steps
- Reframe `0 < Re(∑ ζ_p^{k²})` and look for a positivity argument that avoids full
  eigenvalue-multiplicity computation (e.g. pairing `k` with `p−k`, partial-sum bounds).
- Consider upstreaming `gaussSum_chiC_eq_sum_sq` to Mathlib's `NumberTheory/GaussSum.lean`.
## Session 2026-06-19 (Session 5) — p = 7 witness (second `p ≡ 3 mod 4` case)

Note: the Session-4 diagonal note remarked that the *diagonal* form `∑ζ^{k²}` does not
make `p = 7` tractable (it needs the cubic value `cos(2π/7)`). This session shows the
*Legendre-weighted* form does: comparing two folded sines (`sin(4π/7) > sin(6π/7)`)
sidesteps exact radicals entirely.

**Mode:** depth-first · **Outcome:** progress (new sorry-free, axiom-free witness)

### What I did
- New companion file `Proofs/QuadraticGaussSumSignSmallSeven.lean` (verified): the next
  prime on the `p ≡ 3 (mod 4)` branch after `p = 3`, mirroring the p=3/p=5 files.
  - `gaussSum_seven_eq` — seven-term enumeration over `ZMod 7` collapses to
    `ζ + ζ² − ζ³ + ζ⁴ − ζ⁵ − ζ⁶` (`quadraticChar (ZMod 7)` = `0,1,1,-1,1,-1,-1`; the
    quadratic residues mod 7 are `1,2,4`). Used `quadraticChar_one_iff_isSquare` for the
    residues (+1) and `quadraticChar_neg_one_iff_not_isSquare` for the non-residues (−1),
    each `IsSquare`/`¬IsSquare` discharged by `decide`.
  - `sin_eight/ten/twelve_pi_div_seven` — fold the upper-half sines via
    `sin(x+π)=−sin x` (`Real.sin_add_pi`) and `sin(π−x)=sin x` (`Real.sin_pi_sub`):
    `sin(8π/7)=−sin(6π/7)`, `sin(10π/7)=−sin(4π/7)`, `sin(12π/7)=−sin(2π/7)`.
  - `gaussSum_seven_im` — `Im g = 2·sin(2π/7) + 2·sin(4π/7) − 2·sin(6π/7)`.
  - `gaussSum_seven_im_pos` — **`0 < Im g`** from coarse signs only: `sin(2π/7) > 0`
    (`sin_pos_of_pos_of_lt_pi`) and `sin(4π/7) > sin(6π/7)` (fold to `sin(3π/7) > sin(π/7)`
    via `Real.strictMonoOn_sin` on `[-π/2, π/2]`). No exact radical values needed.
  - `gaussSum_seven_eq_I_sqrt_seven` — feeds the positivity into the reduction lemma
    `gaussSum_eq_I_sqrt_iff_im_pos` (with `7 % 4 = 3`) to get the FULL determination
    `gaussSum (chiC 7) ψ₇ = +i·√7` (not `−i·√7`).
  - Verified by single-file olean-chain compile (Docker host-blocked); `#print axioms`
    on both `gaussSum_seven_eq_I_sqrt_seven` and `gaussSum_seven_im_pos` =
    `[propext, Classical.choice, Quot.sound]` only (axiom-free).

### Key findings
- The `p = 5` coarse-sign method (compare two cosines/sines, sidestepping exact radicals)
  generalises cleanly to `p = 7`: the only new ingredient is the strict monotonicity of
  `sin` on `[-π/2, π/2]` to compare two sines after folding both into that interval.
- The `p ≡ 3 (mod 4)` branch now has two machine-checked witnesses (`p = 3`, `p = 7`); the
  general `0 < Im g` remains the open DFT-spectrum crux (>1000 lines either route).

### Files modified
- `proofs/Proofs/QuadraticGaussSumSignSmallSeven.lean` (new, verified)
- `proofs/Proofs.lean` (import)
- `src/data/research/problems/quadratic-gauss-sum-square-oq-01.json` (new knowledge)

### Next steps
- `p = 13` / `p = 17` as further `p ≡ 1 (mod 4)` witnesses, or pivot to the general
  DFT-spectrum route once (or if) Mathlib gains finite-Fourier eigenvalue infrastructure.

## Session 2026-06-19 (Session 6) — p = 11 witness (third `p ≡ 3 mod 4` case)

**Mode:** depth-first · **Outcome:** progress (new sorry-free, axiom-free witness)

### What I did
- New companion file `Proofs/QuadraticGaussSumSignSmallEleven.lean` (verified): the next
  prime on the `p ≡ 3 (mod 4)` branch after `p = 3, 7`, mirroring the p=3/5/7 files.
  - `gaussSum_eleven_eq` — eleven-term enumeration over `ZMod 11` collapses to
    `ζ − ζ² + ζ³ + ζ⁴ + ζ⁵ − ζ⁶ − ζ⁷ − ζ⁸ + ζ⁹ − ζ¹⁰` (quadratic residues mod 11 are
    `{1,3,4,5,9}`). Character values via `quadraticChar (ZMod 11) k = ±1 → chiC 11 k = ±1`,
    each branch discharged by `decide`.
  - `sin_fold_12/14/16/18/20` — fold the upper-half sines via `sin(x+π)=−sin x`
    (`Real.sin_add` + `Real.cos_pi`/`Real.sin_pi`) and `sin(π−x)=sin x`
    (`Real.sin_pi_sub`).
  - `gaussSum_eleven_im` — `Im g = 2·sin(2π/11) − 2·sin(4π/11) + 2·sin(6π/11)
    + 2·sin(8π/11) + 2·sin(10π/11)`.
  - `gaussSum_eleven_im_pos` — **`0 < Im g`** from coarse signs only: three sines
    `sin(2π/11), sin(8π/11), sin(10π/11)` are positive (angles in `(0,π)`); the lone
    negative term `−sin(4π/11)` is dominated by `sin(6π/11) = sin(5π/11) > sin(4π/11)`
    (`Real.strictMonoOn_sin`, both angles in `(0,π/2)`). No exact (cubic-irrational)
    radical values needed.
  - `gaussSum_eleven_eq_I_sqrt_eleven` — feeds the positivity into the reduction lemma
    `gaussSum_eq_I_sqrt_iff_im_pos` (with `11 % 4 = 3`) to get the FULL determination
    `gaussSum (chiC 11) ψ₁₁ = +i·√11` (not `−i·√11`).

### Key findings
- The `p = 7` two-sine comparison method scales to `p = 11` essentially unchanged: with
  more terms there are several unconditionally-positive sines and a single dominated
  negative term, so the coarse-sign argument stays a one-line `linarith` after isolating
  `sin(4π/11) < sin(5π/11) = sin(6π/11)`.
- The `p ≡ 3 (mod 4)` branch now has three machine-checked witnesses (`p = 3, 7, 11`); the
  general `0 < Im g` remains the open DFT-spectrum crux.

### Files modified
- `proofs/Proofs/QuadraticGaussSumSignSmallEleven.lean` (new, verified)
- `proofs/Proofs.lean` (import)
- `src/data/research/problems/quadratic-gauss-sum-square-oq-01.json` (new knowledge)

### Next steps
- `p = 13` / `p = 17` as further `p ≡ 1 (mod 4)` witnesses (the dominated-term count grows,
  but the coarse-sign template is unchanged), or pivot to the general DFT-spectrum route
  once (or if) Mathlib gains finite-Fourier eigenvalue infrastructure.

## Session 2026-06-22 (researcher-1) — p = 13 witness (second p ≡ 1 mod 4 case)

**Mode**: CONTINUE (open problem, tractable next step). **Outcome**: progress (new
machine-checked witness of Gauss's hard sign theorem).

### What I did
- Wrote `Proofs/QuadraticGaussSumSignSmallThirteen.lean` (verified, 0-axiom): the second
  `p ≡ 1 (mod 4)` witness (after p=5), `gaussSum_thirteen_eq_sqrt_thirteen : g = +√13`.
- QRs mod 13 = {1,3,4,9,10,12} → g = ζ−ζ²+ζ³+ζ⁴−ζ⁵−ζ⁶−ζ⁷−ζ⁸+ζ⁹+ζ¹⁰−ζ¹¹+ζ¹².
- `gaussSum_thirteen_re` folds the conjugate cosines (cos(2πk/13)=cos(2π(13−k)/13)) to
  `2cos(2π/13) − 2cos(4π/13) + 2cos(6π/13) + 2cos(8π/13) − 2cos(10π/13) − 2cos(12π/13)`.
- `gaussSum_thirteen_re_pos`: rewrite the three obtuse cosines cos(8π/13)=−cos(5π/13),
  cos(10π/13)=−cos(3π/13), cos(12π/13)=−cos(π/13) → Re g/2 = cos(π/13)+cos(2π/13)+cos(3π/13)
  +cos(6π/13) − cos(4π/13) − cos(5π/13); positivity by `Real.strictAntiOn_cos` (cos(4π/13)<
  cos(π/13), cos(5π/13)<cos(2π/13)) + cos(3π/13),cos(6π/13)>0. linarith. **FIRST-TRY build.**
- Registered in `proofs/Proofs.lean`. Branch coverage now p=3,5,7,11,13.

### Verification (Docker down → host-lean dep chain)
Compiled dependency chain to /tmp oleans: QuadraticGaussSumSquare → ...SquareOQ01 →
...SignReduction → my file (each `lean -o /tmp/g/Proofs/M.olean Proofs/M.lean` with
LEAN_PATH=/tmp/g:$BASE). New file EXIT=0; #print axioms gaussSum_thirteen_eq_sqrt_thirteen
= [propext, Classical.choice, Quot.sound] only.

### Next steps
- p=17 (third p≡1 witness; more obtuse terms but same template), or the general
  DFT-spectrum positivity (open, >1000 lines, Mathlib lacks finite-Fourier eigenvalue infra).
