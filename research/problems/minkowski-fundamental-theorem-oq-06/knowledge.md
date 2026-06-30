# Knowledge Base: minkowski-fundamental-theorem-oq-06

Insights accumulated during research on this problem.

---

## Problem Understanding

The **Minkowski–Hlawka theorem** is the non-constructive *existence* counterpart to the
gallery's parent (Minkowski's convex-body *obstruction* theorem). It asserts the densest
lattice packing in dimension `n ≥ 2` has density

    δ_n ≥ ζ(n) / 2^(n-1)

equivalently: every symmetric bounded measurable `S` with `vol(S) < 2·ζ(n)` is avoided
(off the origin) by some unimodular lattice. The standard proof averages
`#(Λ ∩ S \ {0})` over the space of unimodular lattices `X_n = SL_n(ℤ)\SL_n(ℝ)` via
**Siegel's mean-value theorem** and extracts a better-than-average lattice — without
exhibiting one.

---

## Insights

### Session 2026-06-14 (ORIENT) — gap audit + constants pinned

**Mode**: FRESH · **Outcome**: ORIENT (survey, effectively blocked for full proof)

**What I did**
- Confirmed Hlawka is *not* in the gallery: only the obstruction parent exists
  (`MinkowskiFundamentalTheorem.lean`, sorry-free, proves a different theorem). `grep -i
  hlawka proofs/` hits only `Erdos997Problem.lean` (unrelated).
- Audited Mathlib at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
  `MeasureTheory/Group/GeometryOfNumbers.lean` contains only **Blichfeldt**
  (`exists_pair_mem_lattice_not_disjoint_vadd`) and **Minkowski convex-body**
  (`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_{lt,le}_measure`). No Siegel
  mean-value (`gh search` = 0), no packing density (`gh search packingDensity` = 0).
  "Minkowski–Hlawka theorem" is a **title-only** entry in Mathlib `docs/1000.yaml` (no
  `decl:`/`author:`) → an *unmet* target upstream.
- Wrote a durable numerical artifact `verify_minkowski_hlawka.py` (all checks pass).

**Key findings**
- **Normalization (correction to seed).** For *symmetric* `S` the threshold is
  `vol(S) < 2·ζ(n)`, not `< ζ(n)`. Chain: take `S = ball(2r)`; an avoiding unimodular
  lattice has min distance `≥ 2r`, so radius-`r` balls pack with density
  `vol(ball r) = vol(S)/2^n = 2ζ(n)/2^n = ζ(n)/2^(n-1)`. The seed's `< ζ(n)` is the
  star-body / ±-identified convention.
- **Bound hierarchy** (verified n ∈ {2..8, 24}): `2^(-n) ≤ ζ(n)/2^(n-1) ≤ δ_n^known`
  (A2, D3, D4, D5, E6, E7, E8, Leech). MH is a valid but very weak lower bound vs known
  optima (e.g. n=8: MH `0.00784` vs E8 `0.2537`).
- **Improvement factor.** `MH / trivial = 2ζ(n) → 2` as `n→∞`. So Hlawka beats the
  elementary maximal-packing bound `δ_n ≥ 2^(-n)` by only ~a factor of 2; both decay like
  `2^(-n)` and the exponential gap to the (also exponential) Kabatiansky–Levenshtein
  *upper* bound is untouched.

**Decision: SURVEY / effectively BLOCKED for full proof.** The standard route requires
Siegel's mean-value theorem over `SL_n(ℝ)/SL_n(ℤ)` (>1000 LOC of missing measure theory).

**Actionable next targets** (both Docker-gated):
1. *Staged*: state Hlawka with Siegel's identity as an explicit hypothesis
   (axiom/structure field), then prove "better-than-average ⇒ existence" with ±-pairing →
   `δ_n ≥ ζ(n)/2^(n-1)`. Isolates the one deep lemma; badge=axiom, status=axiomatized.
2. *Elementary stepping stone* (~200–400 LOC, Mathlib-only): the saturation bound
   `δ_n ≥ 2^(-n)` via maximal packing + radius-doubling cover. The "easy constant" that MH
   sharpens by `2ζ(n)`.

**Files**: `verify_minkowski_hlawka.py`, `src/data/research/problems/minkowski-fundamental-theorem-oq-06.json`.

---

### Session 2026-06-14 (ORIENT, continued) — where the `ζ(n)` factor comes from

**Mode**: REVISIT · **Outcome**: ORIENT (mechanism sharpened; full proof still Docker-gated)

**Correction to the prior session.** The prior notes attribute the `2·ζ(n)` improvement
to "±-pairing + threshold" without separating the two factors. This conflates two
*independent* inputs, and it mis-states the hypothesis the staged formalization (target #1)
must assume. The decomposition is:

- The **factor 2** is the elementary **±-pairing**: for symmetric `S` (with `0 ∉ S`) the
  primitive vectors of a lattice in `S` come in `±w` pairs, so #pairs = #primitive / 2.
- The **factor ζ(n)** is the **primitive-vector (Siegel–Rogers) restriction** — a *deeper*
  input, not a packaging trick. It is the content of the **primitive** mean-value formula,
  distinct from Siegel's all-vectors formula.

**The two mean-value formulas.** On `X_n = SL_n(ℤ)\SL_n(ℝ)` with probability Haar `μ`:

- Siegel (all nonzero vectors): `∫_{X_n} Σ_{v∈Λ\0} f(v) dμ = ∫_{ℝⁿ} f`.
- Siegel–Rogers (**primitive** vectors only): `∫_{X_n} Σ_{w∈Λ primitive} f(w) dμ = (1/ζ(n))·∫_{ℝⁿ} f`.

The second follows from the first by the unique factorization `v = m·w` (`m ≥ 1`, `w`
primitive) and the scaling `∫ f(m·) = m^{-n} ∫ f`: if the primitive mean is `c·∫f` then
`c·(Σ_{m≥1} m^{-n})·∫f = ∫f`, i.e. `c = 1/Σ_{m≥1} m^{-n} = 1/ζ(n)`. **So `ζ(n)` is exactly
`Σ_{m≥1} m^{-n}` — it enters as the primitivity-restriction normalizer, full stop.**

**The Hlawka density argument, correctly stated.** Apply the *primitive* formula to
`f = 1_S`, `S` symmetric, `0 ∉ S`. Mean number of primitive `±`-pairs in `S` is
`vol(S)/(2ζ(n))`. If `vol(S) < 2ζ(n)`, the mean `< 1`, so **some** unimodular `Λ` has no
primitive vector in `S`. For the ball case this finishes, because the **shortest** nonzero
lattice vector is always primitive — "no primitive vector in `ball(2r)`" ⇒ min-distance
`≥ 2r` ⇒ packing density `≥ ζ(n)/2^(n-1)`.

**Consequence for target #1 (staged formalization).** The hypothesis to assume is the
**primitive** mean-value identity `∫_{X_n} Σ_{w primitive} f(w) dμ = (1/ζ(n))·∫ f`, **not**
the all-vectors Siegel identity. Assuming the all-vectors identity and trying to recover
`ζ(n)` by ±-pairing alone does **not** reach `ζ(n)/2^(n-1)` — it only reaches the factor 2,
i.e. `δ_n ≥ 1/2^(n-1)`, missing the `ζ(n)`. Also record: the "shortest vector is primitive"
lemma is the bridge from "no primitive vector in `S`" to "no nonzero vector in `S`" for the
ball; in Mathlib terms it is `Λ`-vector `= m • w` with `‖w‖ < ‖m • w‖` for `m ≥ 2`,
contradicting minimality. (This bridge **is** Mathlib-tractable, unlike the mean-value identity.)

**Durable artifact**: `verify_primitive_mechanism.py` (stdlib-only, all checks pass):
(1) `ζ(n) = Σ_{m≥1} m^{-n}` so `c = 1/ζ(n)`; (2) `ℤ²` fraction of primitive (origin-visible,
`gcd=1`) points `→ 1/ζ(2) = 6/π²`; (3) `ℤ³` primitive fraction `→ 1/ζ(3)`; (4) deterministic
sweep of 13808 integer 2×2 bases: shortest nonzero vector is primitive in **all** cases.

**Files**: `verify_primitive_mechanism.py`, `src/data/research/problems/minkowski-fundamental-theorem-oq-06.json`.

---

## Dead Ends

- Full formalization via Siegel's mean-value theorem from current Mathlib — blocked: the
  homogeneous space `SL_n(ℤ)\SL_n(ℝ)`, its finite invariant measure, and Siegel's identity
  are all absent upstream.
