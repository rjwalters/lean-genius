# Knowledge Base: erdos-1039-oq-04

Open question (Seeker-selected, generalization, tier B): *"What is the analogous
problem in higher dimensions — for polynomials in ℂᵈ or for systems of
polynomials?"* Parent: `erdos-1039` (Erdős–Herzog–Piranian polynomial lemniscate
**inradius** problem: for monic `f(z)=∏(z−zᵢ)`, `|zᵢ|≤1`, is the largest disc
inside `{|f|<1}` of radius `ρ(f) ≫ 1/n`? OPEN; best lower bound
`ρ(f) ≥ c/(n√log n)`, KLR 2025; upper bound `ρ(zⁿ−1) ≤ π/(2n)`).

---

## Session 1 — OBSERVE survey (2026-06-28, researcher-4)

**Outcome: SURVEY (no Lean delivered, by design).** The question asks one to
*formulate* a higher-dimensional analogue of an already-OPEN problem; it has no
theorem to prove yet. The parent gallery entry is `axiomatized` (the 1-D
conjecture and its bounds are axioms), so adding a Lean file for an even-harder
generalization would be pure definitional scaffolding on top of an unprovable
conjecture — exactly the "fake formalization" the researcher role forbids. The
honest first-session deliverable is to pin down the precise formulation(s),
record the literature state, and assess the Mathlib gap.

### The generalization is not unique — it bifurcates

Unlike the 1-D problem, "the higher-dimensional analogue" is genuinely
**ambiguous**, and the ambiguity is mathematically essential rather than
cosmetic. At least three inequivalent readings:

1. **Single polynomial in ℂᵈ, sublevel set, inscribed ball.**
   `f : ℂᵈ → ℂ` a polynomial; study `Ω_f = {z ∈ ℂᵈ : |f(z)| < 1}` and the
   radius of the largest inscribed **ball** vs. largest inscribed **polydisc**.
   Crucial subtlety from SCV: for `d ≥ 2` the ball `Bᵈ` and polydisc `Dᵈ` are
   **not biholomorphic** (Poincaré), so "inradius" splits into two genuinely
   different extremal quantities. The 1-D notion `ρ(f)` therefore has *two*
   natural lifts, and they need not agree even up to constants.

2. **System of polynomials / common zero set.**
   `f = (f₁,…,f_k)`, `|f|² = ∑|fⱼ|²`, sublevel set `{|f| < 1}` around the common
   variety `V(f)`. This is the reading closest to "for systems of polynomials"
   in the question text. Here "roots in the unit disc" becomes "the common zero
   variety lies in the unit polydisc/ball," and degree `n` becomes a tuple of
   degrees (or the Bézout number).

3. **Product-of-linear-forms model.**
   `f(z) = ∏ᵢ ℓᵢ(z)` with each `ℓᵢ` a linear form vanishing on a hyperplane
   meeting the unit ball — the literal lift of `∏(z−zᵢ)`. The lemniscate is then
   a union of hyperplane neighbourhoods; the inradius asks how large a ball
   avoids none-too-closely all `n` hyperplanes.

A correct formalization would have to **choose and justify** one reading;
readings (1-ball) and (1-polydisc) are the most faithful to the parent, with the
ball/polydisc dichotomy being the first genuinely new phenomenon (absent in 1-D).

### Literature state — essentially unstudied as a direct generalization

A focused search (2026-06-28) found **no** direct higher-dimensional EHP-inradius
result. The active EHP literature is entirely 1-D:

* KLR 2025 — `ρ(f) ≥ c/(n√log n)` (area method, 1-D). (parent)
* "On the area of polynomial lemniscates," arXiv:2503.18270 (1-D area bounds).
* "The maximal length of the EHP lemniscate in high degree," arXiv:2512.12455 /
  Tao's blog (2025) — settles the *length* conjecture (`zⁿ−1` extremal) for
  large `n`; still 1-D.
* "Inradius of random lemniscates," ScienceDirect S0021904524000042 — 1-D,
  random model (`E[ρ] ~ 1/√n`).

Adjacent higher-dimensional machinery exists but does **not** answer the
question: pluripotential theory and logarithmic **capacity in ℂⁿ**
(Bedford–Taylor, Siciak extremal function), and "Variations on the capacitary
inradius" (arXiv:2503.07868) — a capacitary inradius notion, but for general
compact sets, not the polynomial-lemniscate extremal problem. So oq-04 sits in a
genuine gap: the tools (pluripotential capacity, Lelong numbers) exist, but the
specific extremal inradius conjecture has not been posed or attacked in `d ≥ 2`.

### What is even conjecturable

Heuristic for reading (1): with `n` "roots" (or a degree-`n` variety) in the unit
polydisc of `ℂᵈ`, the lemniscate `{|f|<1}` near a smooth piece of `V(f)` is a
tube of complex-codimension 1, so it has real codimension 2 regardless of `d`.
The inscribed *ball* radius is governed by how the `n` sheets cluster — plausibly
still `≍ 1/n` for the polydisc-inradius along the "thin" complex-normal
direction, while the *ball*-inradius could behave differently because a ball must
simultaneously fit the thin normal direction. **No rate is established;** even the
benchmark `∏(zⱼ-style)` extremal configuration is unclear. This is why the
deliverable is a survey, not a bound.

### Mathlib infrastructure gap

* `MvPolynomial ℂ` exists, but there is **no** multivariate complex-analytic
  lemniscate / sublevel-set geometry, no inscribed-ball-radius API, and no
  pluripotential capacity (Bedford–Taylor `(ddᶜ)ᵈ`, Siciak extremal function) in
  Mathlib 4.26.0. The parent's 1-D file already axiomatizes its analytic bounds;
  a `d ≥ 2` file would axiomatize strictly more with strictly less Mathlib
  support — net-negative formalization value at this stage.

### Insights

* **The interesting new content is the ball/polydisc dichotomy**, not the degree
  asymptotics. Any future Lean work should foreground `Bᵈ ≇ Dᵈ` (`d ≥ 2`) as the
  reason the 1-D `ρ(f)` does not lift uniquely.
* **Reading (2) "systems of polynomials" is the cleanest to *state*** (common
  zero variety in the unit polydisc, `|f|²=∑|fⱼ|²`) but the hardest to *bound*;
  reading (1-polydisc) is the most faithful lift of the parent.
* This is a "formulate, don't prove" OQ: its value is a precise problem
  statement plus the observation that `d ≥ 2` is open even at the conjectural
  level.

### Recommendation / Next steps

1. **Do not open a Lean file yet.** Net formalization value is negative until
   either (a) Mathlib gains pluripotential capacity, or (b) a concrete, defensible
   conjecture (rate + extremal configuration) is fixed for one chosen reading.
2. If a future session insists on Lean, the *only* honest scope is a
   **statement-only** formalization of reading (1-polydisc): define
   `MvUnitPolydiscPolynomial`, the sublevel set, and `inscribedPolydiscRadius`,
   and state the conjecture as an explicit `axiom` (mirroring the parent's
   honesty), with the d=1 specialization proved to recover the parent's
   `inscribedDiscRadius` — that reduction is the one genuinely provable nugget.
3. **OQ-chain depth guard:** slug `erdos-1039-oq-04` has depth 1; a follow-up
   would be depth 2 (permitted). But no strong follow-up exists — the question is
   itself the open frontier — so **0** follow-ups generated.

### Honesty note

No theorem was proved this session and none was claimed. This is a documentation
/ problem-formulation contribution only. Status set to `in-progress` (surveyed),
not `completed`: the generalization remains open and unformalized.
