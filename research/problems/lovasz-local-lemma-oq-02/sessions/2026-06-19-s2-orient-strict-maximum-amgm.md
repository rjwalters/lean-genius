# S2 ORIENT — Closing the sole sorry: `lllThreshold_strict_maximum`

**Agent:** researcher-3 · **Date:** 2026-06-19 · **Phase:** OBSERVE → ORIENT · **Build:** none (doc + comment-only)

## Target

`proofs/Proofs/LovaszLocalLemmaOQ02.lean` is **0 axioms, 1 sorry**. The lone sorry
(line ~207) is the strict-maximum / uniqueness lemma:

```lean
theorem lllThreshold_strict_maximum (d : ℕ) (hd : 0 < d) (x : ℚ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hne : x ≠ 1 / (↑d + 1)) :
    x * (1 - x)^d < lllThreshold d
```

i.e. `x·(1-x)^d` attains its maximum `T(d) = d^d/(d+1)^{d+1}` on `[0,1]` **uniquely**
at `x = 1/(d+1)`; every other point is *strictly* below.

The non-strict companion `lllThreshold_is_maximum` (`x·(1-x)^d ≤ T(d)`) is **already
proved** in the same file (Part III, lines 105–162) via the 2-weighted AM-GM
`Real.geom_mean_le_arith_mean2_weighted`. The strict lemma is the last gap.

## Key API finding (verified against the pinned Mathlib tree)

Mathlib already carries the **equality characterization** of weighted AM-GM — no new
infrastructure needed:

| Lemma | File | Statement |
|---|---|---|
| `geom_mean_lt_arith_mean_weighted_iff_of_pos` | `Mathlib/Analysis/MeanInequalities.lean:254` | `∏ z i ^ w i < ∑ w i * z i  ↔  ∃ j∈s, ∃ k∈s, z j ≠ z k` (for `0 < w i`, `∑ w = 1`, `0 ≤ z`) |
| `geom_mean_eq_arith_mean_weighted_iff'` | `Mathlib/Analysis/MeanInequalities.lean:200` | `∏ z i ^ w i = ∑ w i * z i  ↔  ∀ j∈s, z j = ∑ w i * z i` |
| `Real.rpow_lt_rpow` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` | `0 ≤ x → x < y → 0 < z → x^z < y^z` (strict monotone of `·^z`) |

These are the **strict** siblings of exactly the tools the non-strict proof already uses.

**The crucial observation:** with the two-element index the AM-GM *equality* case
`z₀ = z₁` reads `xr = (1-xr)/dr`, which is equivalent to `(dr+1)·xr = 1`, i.e.
`xr = 1/(dr+1)` — **precisely the optimal point**. So `x ≠ 1/(d+1)` ⟺ `z₀ ≠ z₁` ⟺
strict AM-GM. The strict lemma therefore mirrors the non-strict proof line-for-line,
swapping `≤`→`<` and `geom_mean_le_arith_mean2_weighted`→the Finset strict-iff form.

## Recommended route (FORWARD strict, preferred)

Drop the current `rcases lt_or_eq_of_le hmax` scaffold; prove `<` directly, reusing the
structure of `lllThreshold_is_maximum`:

1. **Reduce to ℝ.** `suffices ((x*(1-x)^d : ℚ) : ℝ) < ((lllThreshold d : ℚ):ℝ)` then
   `exact_mod_cast`. Reuse the `simp only [...]; push_cast; set xr; set dr` preamble
   verbatim from lines 108–117 (gives `hxr, hx1r, hdr, hd1r, hp2_nn`).
2. **Distinctness `z₀ ≠ z₁`.** From `hne : x ≠ 1/(d+1)` get `xr ≠ 1/(dr+1)` by cast
   injectivity (`Rat.cast_injective` / `exact_mod_cast`). Then
   `xr ≠ (1-xr)/dr` because `xr = (1-xr)/dr ↔ dr*xr = 1-xr ↔ (dr+1)*xr = 1 ↔
   xr = 1/(dr+1)` (use `div_eq_iff hdr.ne'`, `field_simp [hd1r.ne']`).
3. **Strict AM-GM (Finset form).** Set
   `s := (Finset.univ : Finset (Fin 2))`,
   `w := ![1/(dr+1), dr/(dr+1)]`, `z := ![xr, (1-xr)/dr]`.
   Discharge `hw` (both weights `> 0`: `1/(dr+1)>0`, `dr/(dr+1)>0`), `hw'`
   (`∑ w = 1` via `Fin.sum_univ_two`; `field_simp [hd1r.ne']; ring`), `hz`
   (`hxr`, `hp2_nn`). Apply
   `(geom_mean_lt_arith_mean_weighted_iff_of_pos s w z hw hw' hz).mpr ⟨0, _, 1, _, hz01⟩`.
   Simplify `∏`/`∑` with `Fin.prod_univ_two` / `Fin.sum_univ_two` and `Matrix.cons_val_*`
   to obtain
   `xr^(1/(dr+1)) * ((1-xr)/dr)^(dr/(dr+1)) < 1/(dr+1)`   — call it `h_amgm_strict`.
4. **rpow identity.** Reuse `h_eq` from lines 130–135 verbatim:
   `(xr * ((1-xr)/dr)^d)^(1/(dr+1)) = xr^(1/(dr+1)) * ((1-xr)/dr)^(dr/(dr+1))`.
5. **Strict power-up.** `h_eq ▸ h_amgm_strict` gives
   `(xr*((1-xr)/dr)^d)^(1/(dr+1)) < 1/(dr+1)`. Apply
   `Real.rpow_lt_rpow (rpow_nonneg ...) h_le hd1r` to the exponent `dr+1`, then
   collapse `((·)^(1/(dr+1)))^(dr+1)` with `← Real.rpow_mul`, `div_mul_cancel₀`,
   `Real.rpow_one` (exactly the calc at lines 145–149 but with `_ < _`). Result:
   `xr*((1-xr)/dr)^d < (1/(dr+1))^(d+1)`.
6. **Multiply by `dr^d > 0`.** `mul_lt_mul_of_pos_right _ (pow_pos hdr d)` and the
   `hrewrite`/`hcancel` algebra from lines 150–161 give
   `xr*(1-xr)^d < dr^d/(dr+1)^(d+1)`. `exact_mod_cast`.

Everything except the swapped lemma + strict steps is copy-from-`lllThreshold_is_maximum`.

## Fallback route (BACKWARD equality, if the forward calc is fiddly)

Keep the `rcases lt_or_eq_of_le hmax with h | h`; in the `h : x*(1-x)^d = T(d)` branch
use `geom_mean_eq_arith_mean_weighted_iff'` to force `z₀ = z₁` ⟹ `xr = 1/(dr+1)` ⟹
`x = 1/(d+1)`, contradicting `hne` (`exfalso`). Costs an extra back-propagation of the
equality through the `rpow`/`pow` chain (injectivity of `·^(dr+1)` and `·^(1/(dr+1))`
on nonneg reals via `Real.rpow_left_injective` / `Real.rpow_natCast`), so the forward
route is preferred.

## Why this is now a one-cycle ACT

- No new imports (`Mathlib` already imported wholesale).
- No new axioms (pure analysis glue; file stays **0 axioms**).
- The hard analytic content (weighted AM-GM, rpow algebra) is *already in the file* for
  the non-strict bound; the strict version reuses it with the strict-iff lemma.
- Closing it takes the file to **0 sorry / 0 axiom** ⟹ flip gallery meta to
  `verified`/`original`, `leanFile.sorries 1→0`.

## Risk register

- `![...]`/`Fin.prod_univ_two`/`Matrix.cons_val_*` simp bookkeeping is the only finicky
  part; if it fights, define `w`/`z` by `fun i => if i = 0 then _ else _` and use
  `Finset.prod_fin_eq_prod_range` or just `Fin.cases`.
- Verify the *exact* argument order of `geom_mean_lt_arith_mean_weighted_iff_of_pos`
  (`s` is the implicit Finset; `w z` then the three hypotheses) at elaboration time.
- **Build discipline:** the 7.65 GB Docker VM OOM-kills concurrent `mathlib` builds.
  ACT must build solo (`docker ps --filter name=lean-build-` empty) — do not race other
  fleet builds.

## State delta

OBSERVE (iter 1, 0 attempts) → ORIENT. Active approach fixed: **strict weighted AM-GM
equality case**, primary tool `geom_mean_lt_arith_mean_weighted_iff_of_pos`. The
`state.md` "dead end" note (full measure-theoretic tightness needs `ProbabilityTheory`)
is **not** relevant to this lemma — `lllThreshold_strict_maximum` is purely the algebraic
uniqueness of the maximizer and is fully formalizable with existing real-analysis API.
