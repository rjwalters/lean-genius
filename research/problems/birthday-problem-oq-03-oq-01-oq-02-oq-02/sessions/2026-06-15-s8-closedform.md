# Session 2026-06-15 (S8, researcher-8) — closed-form attempt for g1; independent confirmation + sharper negative result

**Mode:** REVISIT (RICH; Docker blackout — `docker info` rc=124; pure mpmath/sympy).
**Outcome:** progress — the open thread (closed form of `g1`) is **not closed**, but it is
**sharpened**: g1 (and the `d^{-2/3}` coefficient `c`) are confirmed by an independent method,
pinned to ~4 more digits, and shown to have **no low-height closed form** in the natural constants.

This is a standalone session note. **I deliberately did NOT edit `knowledge.md` / `state.md` /
the problem JSON** — R9's PR #24670 (which settles the functional form and the numeric `g1`) is
OPEN and edits exactly those files; a second edit would collide on merge. New files only.

## Context (what S7 / #24670 left open)
S7 settled: `gap(d) = n_med - n_W = g_inf + g1·d^{-1/3} + c·d^{-2/3} + O(d^{-1})`, clean power
series, **no log d**, `g_inf = -(3/2)ln2 = -c₀³/4`, numeric `g1 = 0.2322254(1)`. PSLQ over
`{1, ln2, c₀, c₀², c₀·ln2, 1/c₀}` (7 digits, maxcoeff 5000) found **no** closed form — left as a
"next steps" target for analytic de-Poissonization. `c₀ = (6 ln2)^{1/3}`.

## What I did
1. **Independent verification harness** (`verify_birthday_oq03_g1_closedform.py`), a *different*
   method from R9's:
   - `n_med` and `n_W` as **continuous (gamma-interpolated) roots** solved by `mpmath.findroot`
     (secant), not R9's integer-grid + power-fit. `n_med` solves `P(W=0) = 1/2` via the exact
     peak-truncated occupancy sum `P = Σ_j C(d,j)C(d-j,n-2j) n! 2^{-j}/d^n`; `n_W` solves the
     exact binomial `E[W] = ln2`.
   - exact gap at `d = 10^5 … 10^{10}` (dps 60), then LSQ fit `gap-g_inf = g1·u + c·u² + …`
     (`u = d^{-1/3}`), 4/5/6-term, deepest-window.
2. **Symbolic saddle scaffolding** (sympy): `φ(ρ)=ρf'/f`, `φ'(ρ)`, `H''(ρ)/d` for
   `f = 1+x+x²/2`. Confirmed the **(1/3)log d from Stirling's ½log(2πn) cancels the −(1/3)log d
   from the saddle prefactor −½log(2π·d·ρ·φ'(ρ))** — the structural reason for S7's "no log d".
3. **Corrected PSLQ basis degeneracy.** Since `c₀³ = 6 ln2`, a basis containing BOTH `ln2` and
   `c₀³` carries the exact relation `c₀³ − 6 ln2 = 0`; PSLQ locks onto that trivial basis relation
   and never tests `g1` (this silently weakened R9's nb≥5 search). The clean, ℚ-independent basis
   is **powers of c₀ alone** (it subsumes every ln2-combination).

## Key findings
- **Independent confirmation:** `g_inf → -(3/2)ln2` and `g1 = 0.2322254…` reproduced exactly by
  the continuous-root method — corroborates #24670 by a fully independent route.
- **Sharper constants** (deepest-window, 5/6-term fits agree):
  - `g1 = 0.2322254399` (≈10–11 digits; R9 had `0.2322254(1)`, 7 digits)
  - `c  = 1.0283769327` (≈10–11 digits; R9 had "≈ 1.03")
- **Stronger negative result on the closed form:** over clean powers-of-c₀ bases (from `c₀^{-2}`
  up to `c₀^5`) PSLQ finds **no relation** at maxcoeff 1e5, full precision (dps 60). (At lower
  precision, dps≈40, a few 6-element "relations" appear with norm ~10⁵ — **spurious**; they vanish
  at full precision, confirming there is no real low-height relation.) So **g1 and c have no
  low-height closed form in powers of c₀** at ~11 digits. (`g1/c₀ = 0.1444057`,
  `g1/c₀² = 0.0897963`, `c/c₀² = 0.3976502` — none simple.) This upgrades R9's "no closed form at
  7 digits" to "no low-height closed form at 11 digits over a degeneracy-free basis" — strong
  evidence `g1` is genuinely **not elementary** in `{c₀, ln2}`.

## Honest assessment
The open thread is the *closed form* of `g1`; I did not produce one. But the evidence now points
the other way: `g1` is very likely a **non-elementary de-Poissonization constant** (not a rational
combination of `c₀` powers / `ln2`). The full saddle-point de-Poissonization to one more order
would *identify* that constant (e.g. as an explicit integral or series), rather than match it to
elementary constants. No Lean changed; the parent file's lone axiom (`p_no_triple_tendsto`) is
untouched and remains the correct Mathlib-gap axiomatization.

## Files
- `research/scripts/verify_birthday_oq03_g1_closedform.py` (NEW; the harness above)
- this session note (NEW)
- (intentionally NOT edited: `knowledge.md`, `state.md`, `...json` — owned by open PR #24670)

## Next steps
- **Analytic de-Poissonization to one more order of R(d) = log P(W=0) + E[W]** using the saddle
  ingredients here (φ, φ', H'' + the next saddle correction + Stirling). Target: express `g1`
  (and `c`) as an explicit — likely non-elementary — constant; the numeric `g1 = 0.2322254399`,
  `c = 1.0283769327` are the checks. Expect NO elementary closed form (PSLQ negative at 11 digits).
- If a future session confirms non-elementarity analytically, record `g1` as a named
  de-Poissonization constant rather than continuing to chase an elementary form.
