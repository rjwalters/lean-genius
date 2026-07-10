# Knowledge Base: brouwer-fixed-point-oq-02-oq-02-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The parent OQ-02/OQ-02 states an *information-theoretic* lower bound only as the
arithmetic inequality `2^n < 1/ε → 1/2^n > ε` (theorem `info_theoretic_bound`),
with the actual adversary argument left in prose: "some pair of fixed point
locations at distance > ε produces identical query outcomes." No witnessing
functions are ever constructed. This child asks whether that adversary lower
bound can be **fully formalized with explicit function constructions** — i.e.
exhibit the indistinguishable pair, not just count scenarios.

Answer: YES (see `BrouwerFixedPointOQ02OQ02OQ01Adversary.lean`, verified).

---

## Insights

1. **Explicit one-query witness.** `f x = x/2 + 1/8` and `g x = (5/6)x + 1/8`
   are both contractions of [0,1] (rates 1/2, 5/6) and both self-maps of [0,1].
   They AGREE at the probe point x = 0 (`f 0 = g 0 = 1/8`) yet have unique fixed
   points 1/4 and 3/4 — separation 1/2. An algorithm querying only x = 0 gets the
   same observation from both, so any single answer is ≥ 1/4 from one of them.

2. **Adversary principle = triangle inequality.** The abstract core is
   `|p - q|/2 ≤ max(|a - p|, |a - q|)` for any answer `a` (`adversary_error_bound`).
   Combined with an indistinguishable witness pair whose solutions are `p`, `q`,
   this gives an unconditional error lower bound of `|p - q|/2`.

3. **Contractions are NOT exempt.** Striking: even for the best-behaved class
   (contractions), one *value* query cannot resolve the fixed point below 1/4.
   The rate advantage that gives contractions `O(log(D/ε)/|log L|)` query
   complexity only kicks in over MULTIPLE queries; a single query is essentially
   useless. Symmetric contractions about the probe point cannot even agree there
   (forces slopes summing to 2 > 2·max slope), so the witness must be asymmetric —
   we query at x = 0 with fixed points 1/4, 3/4 and slopes 1/2, 5/6.

4. **Arbitrary separation is achievable.** Querying at x = 0 with fixed points
   p = δ, q = 1−δ and slopes L_f = 1/2, L_g = 1 − δ/(2(1−δ)) keeps both < 1 and
   makes the separation 1 − 2δ → 1. So one query gives essentially NO resolution.
   (Only the concrete separation-1/2 instance is formalized; this is the extension.)

---

## Dead Ends

- **Symmetric same-slope witnesses.** Two contractions with equal slope agreeing
  at a query point are forced equal (`p(1−L) = q(1−L) ⇒ p = q`). Symmetric
  (mirror-about-probe) contractions agreeing at the probe force `L_f + L_g = 2`,
  impossible for two contractions. The witness must use *distinct slopes* and an
  *asymmetric* probe placement.

---

## Extension (researcher-3, 2026-07-08): parametrized family, sup = 1/2

Insight #4 above ("arbitrary separation is achievable") is now formalized in
`proofs/Proofs/BrouwerFixedPointOQ02OQ02OQ01AdversaryFamily.lean` (VERIFIED,
0 sorries, 0 axioms, Mathlib v4.26).

- One-parameter family `fδ δ x = x/2 + δ/2`, `gδ δ x = Lg δ · x + δ/2` with
  `Lg δ = 1 − δ/(2(1−δ))`, for `δ ∈ (0, 1/2)`.
- Both are contractions of [0,1] and self-maps; they AGREE at the probe x = 0
  (common value `δ/2`), with unique fixed points `δ` and `1 − δ`, separation
  `1 − 2δ`.
- `one_query_lower_bound_family`: no one-query algorithm resolves the fixed point
  below `(1 − 2δ)/2` for the pair at parameter δ.
- `sup_lower_bound_is_half`: for every ε < 1/2 there is a δ whose pair forces
  error > ε — the one-query error lower bound has supremum exactly 1/2. A single
  value query gives NO worst-case resolution of the fixed point.
- The concrete base instance (`f`, `g`; fixed points 1/4, 3/4) is recovered at
  δ = 1/4 (then `Lg (1/4) = 5/6`).

Lean gotcha (v4.26): `div_le_div_iff` was REMOVED. Replaced the two-fraction
comparison in `Lg_le` with a denominator-cleared identity
`(δ/(2(1−δ)) − δ/2)·(2(1−δ)) = δ²` + `positivity` + `nlinarith`.

## Multi-step iteration bounds (researcher-2, 2026-07-08, PR pending)
Closed the base entry's next steps ("iterating m maps"; "explicit query count";
"convergence/existence") in new companion
`proofs/Proofs/BrouwerFixedPointOQ02OQ02OQ01Iteration.lean` (imports the base entry,
VERIFIED 0 axioms / 0 sorries, Docker green, first-try build).

- `iterate_contraction (m x y) : |f^[m] x − f^[m] y| ≤ Lᵐ·|x−y|` — the m-fold iterate
  of an L-contraction is an Lᵐ-contraction. Induction on m via `Function.iterate_succ'`
  (f^[m+1] = f ∘ f^[m]), then hf + `mul_le_mul_of_nonneg_left`. Generalises the base
  `contraction_comp` (2 maps) to m repeated maps.
- `iterate_dist_tendsto` : for 0≤L<1, |f^[m] x − f^[m] y| → 0. `squeeze_zero` between
  0 (abs_nonneg) and the vanishing Lᵐ·|x−y| (`tendsto_pow_atTop_nhds_zero_of_lt_one`
  `.mul_const`).
- `apriori_iteration_count` : ∀ε>0 ∃N ∀n≥N, |xₙ−x*|≤ε — finite iteration count reaches
  any accuracy = the parent's O(log 1/ε) guarantee, from the a priori bound. The a priori
  sequence Lⁿ/(1−L)·|x₁−x₀| → 0 (mul_const + `Tendsto.congr` reshape), eventually < ε via
  `htend.eventually (Iio_mem_nhds hε)`, then `eventually_atTop.mp`, dominated by
  `apriori_estimate`.
- `iteration_converges` : xₙ → x* in ℝ. `tendsto_iff_dist_tendsto_zero` + `squeeze_zero`
  with `Real.dist_eq` reducing dist to |·|, upper bound = apriori_estimate.

Lean notes (v4.26): `Function.iterate_succ'` gives the OUTER-application form f∘f^[m]
(needed so the contraction hf applies to the last f); `Tendsto.mul_const` yields
`𝓝 (0*c)` — `rw [zero_mul]` then `Tendsto.congr (fun n => by ring)` to reshape the
constant into the a-priori form. `squeeze_zero (hf) (hft) (g0)` infers g from hft, so
provide the vanishing-bound Tendsto as a `have` first rather than a named `(g := …)` arg.

This child is now fully closed on the elementary/asymptotic side: single-query lower
bound (Adversary/Family/Tightness) + iteration convergence with computable stopping.

## Session 2026-07-09 (researcher-2) — SURVEY: slug saturated; ★BITROT finding in sibling OQ02OQ03

**Mode**: REVISIT (RICH, depth-3 slug → 0 follow-ups). **Outcome**: no code change (my slug's
files are fully closed on the elementary/asymptotic side per prior sessions:
Adversary/AdversaryFamily/Tightness single-query lower bound + Iteration convergence). Per the
anti-scaffolding rule I added nothing to the saturated primary.

★**Actionable finding for mechanic / a dedicated repair session:**
`proofs/Proofs/BrouwerFixedPointOQ02OQ03.lean` (Newton quadratic convergence, slug
`brouwer-fixed-point-oq-02-oq-03`) is **BITROTTED — it does NOT build on Mathlib v4.26.0**. Direct
`lean` elaboration (docker down) reports 5 real errors plus 1 sorry:
- L91–92: `pow_le_one` positivity + a `rw` pattern miss.
- L121, L125: `rewrite failed: did not find pattern` (API drift).
- L156: `ContDiffOn.differentiableOn_iteratedDerivWithin` no longer unifies (Taylor/iterated-deriv
  API changed).
- L187: real `sorry` in `newton_convergence_rate` succ case.

Additionally, **`newton_convergence_rate` is FALSE as stated**: hypothesis `hε1 : C * ε < 1` is too
weak — the induction needs the precondition `|eₙ| ≤ 1/(C+1)` for `hstep`, which requires
`(C+1)·ε ≤ 1` (the standard Newton basin condition), not merely `C·ε < 1` (counterexample
`C=1/2, ε=3/2`: `Cε=3/4<1` but `(C+1)ε=9/4>1`). With the strengthened hypothesis the succ step
closes cleanly: `|e_{n+1}| ≤ C|eₙ|² ≤ C(ε(Cε)^{2ⁿ−1})² = ε(Cε)^{2^{n+1}−1}` (needs
`(Cε)^{2ⁿ−1} ≤ 1` via `pow_le_one₀`, `ε ≤ 1/(C+1)` via `le_div_iff`, and exponent identity
`2^{n+1}−1 = (2ⁿ−1)·2 + 1` via `pow_succ` + `Nat.one_le_two_pow` + `omega`). Deferred here because
the file's 5 bitrot errors (fragile `iteratedDerivWithin`/`ContDiffOn` Taylor API) are a
docker-down repair hazard and off this claim's slug.

Docker down all session (containerd meta.db/blob I/O, NOT disk — 157Gi free); verification via
[[reference-docker-down-lean-elab-verification-path]].
