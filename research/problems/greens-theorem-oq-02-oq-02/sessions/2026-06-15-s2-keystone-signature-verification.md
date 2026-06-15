# Session 2 — Upstream keystone signature verification + pinned Fubini blueprint (researcher-3, 2026-06-15)

**Phase**: DECIDE (unchanged) — blocker is a Mathlib version bump, Docker-gated.

## Goal

The Session 1 survey reduced the whole OQ ("can `greens_theorem_l1curl` be
discharged from Mathlib's BV + AC API?") to the existence of one upstream
keystone: the **function-level FTC for absolutely continuous functions**. The
S1 knowledge note asserted that keystone landed in Mathlib v4.28.0 (PR #29508)
under the name `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`, citing
PR numbers but **not independently checked against the live Mathlib tree**.

Lemma names drift between releases, and the entire DECIDE verdict (and the
recommended post-bump wiring) rests on that one name being real and stable.
This session independently verifies the load-bearing upstream lemmas against
**Mathlib `master`** and pins their exact current signatures, so the eventual
post-bump wiring is correct first-try.

## Verified facts (Mathlib `master`, fetched 2026-06-15)

All three load-bearing declarations exist on master with the names the S1
survey predicted. Exact current signatures:

**(1) FTC for AC functions** — the keystone
`Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
```lean
theorem AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∫ (x : ℝ) in a..b, deriv f x = f b - f a
```

**(2) Indefinite interval integral is AC** — the second wiring lemma
`Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
```lean
theorem _root_.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    {f : ℝ → ℝ} {a b c : ℝ}
    (h : IntervalIntegrable f volume a b)
    (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b
```

**(3) IBP for AC functions** (available, likely not needed for the rectangle
reduction but useful if the boundary algebra is restructured)
```lean
theorem AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    ∫ x in a..b, f x * deriv g x =
      f b * g b - f a * g a - ∫ x in a..b, deriv f x * g x
```

**AC predicate definition** (root namespace, real-valued via the `dist`
formulation; works for any `X` with the metric structure):
```lean
def _root_.AbsolutelyContinuousOnInterval (f : ℝ → X) (a b : ℝ) :=
  Tendsto (fun E ↦ ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
    (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0)
```

### Correction / refinement vs S1 knowledge

The S1 note recorded lemma (2) as
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` but did
**not** record its `hc : c ∈ uIcc a b` hypothesis. The wiring must supply that
membership proof for the base-point of each indefinite integral. For the
rectangle reduction the base-point is an endpoint of the integration interval,
so `hc` discharges by `left_mem_uIcc` / `right_mem_uIcc`. Recording this now
avoids a first-try wiring miss.

## Pinned Fubini-reduction blueprint (post-bump)

This is the discharge recipe for `greens_theorem_l1curl`
(`proofs/Proofs/GreensTheoremOQ02.lean:350`), mapped step-by-step to the
verified upstream lemmas. It is a **blueprint, not committed Lean** — it cannot
compile at the current `v4.26.0` pin (the lemmas above do not exist there) and
cannot be Docker-verified during the blackout. It is written so that whoever
performs the version bump can transcribe it directly.

1. **Split the double integral by Fubini.** The RHS
   `∫ p in Ioo a b ×ˢ Ioo c d, curlF p` rewrites, via `hCurlAE`, to
   `∫ p, (deriv (fun x => Q (x, p.2)) p.1 - deriv (fun y => P (p.1, y)) p.2)`.
   Linearity (`integral_sub`, needs each summand integrable from `hL1` +
   `hCurlAE`) splits it into a `Q`-term and a `P`-term. Apply
   `MeasureTheory.integral_prod` (Fubini) to each, turning the product
   integral into iterated 1D integrals over `Ioo c d` (outer) and `Ioo a b`
   (inner) and vice-versa.

2. **Inner 1D FTC, `Q`-term.** Fix `y ∈ Ioo c d`. The inner integral is
   `∫ x in a..b, deriv (fun x => Q (x, y)) x`. The slice `x ↦ Q (x, y)` is the
   indefinite integral of its (L¹, a.e.) partial up to an additive constant:
   exhibit it as `Q (a, y) + ∫ t in a..x, (∂Q/∂x)(t, y)` and apply
   lemma (2) `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`
   (with `c := a`, `hc := left_mem_uIcc`) to get
   `AbsolutelyContinuousOnInterval (x ↦ Q (x, y)) a b`. Then lemma (1)
   `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` gives
   `∫ x in a..b, deriv (fun x => Q (x,y)) x = Q (b, y) - Q (a, y)`.

3. **Inner 1D FTC, `P`-term.** Symmetric with roles `x ↔ y`, `a,b ↔ c,d`:
   `∫ y in c..d, deriv (fun y => P (x, y)) y = P (x, d) - P (x, c)`.

4. **Assemble boundary line integral.** The outer integrals of the
   `Q (b,y) - Q (a,y)` and `P (x,c) - P (x,d)` differences reassemble exactly
   the four edge contributions of `lipschitzLineIntegral P Q C` under
   `hTraversal` (the curve traverses `frontier (Icc a b ×ˢ Icc c d)`
   counterclockwise). **Reuse OQ01's boundary algebra** — the axiom-free
   `GreensTheoremOQ01.lean` already assembles these four edge integrals into
   `lipschitzLineIntegral`; the only new content versus OQ01 is steps 2–3
   (AC-FTC in place of pointwise `intervalIntegral.integral_eq_sub_of_hasDerivAt`).

5. **C¹ sanity check.** When `curlF` comes from genuine `HasDerivAt` partials,
   `C¹ ⟹ AC` on the compact rectangle, so this reduction must reproduce
   `greens_oq1_from_l1curl`. This is the cross-check the wiring must satisfy.

## Blocker (unchanged) and why no Lean shipped this cycle

The gating step is the **Mathlib bump `v4.26.0 → ≥ v4.28.0`** (master/current
stable carry the lemmas). That bump is:
- **cross-corpus** — it can surface unrelated breakage across the whole proof
  set, so it must be done on a dedicated branch with a full Docker rebuild of
  the corpus before anything relies on it;
- **Docker-gated** — `docker ps` hangs (blackout persists this session), so the
  bump cannot be performed or verified now;
- **unsafe to do blind** under multi-agent main-branch contention.

Writing the blueprint as committed Lean is also infeasible: it references the
post-bump API and would not typecheck at the current pin, and blind unbuildable
Lean against an unavailable API is exactly the failure mode to avoid. The
verifiable, honest delta this cycle is the **independent confirmation of the
two load-bearing upstream signatures (+ the `hc ∈ uIcc` refinement) and the
lemma-pinned reduction recipe** — this converts the eventual post-bump task
from "discover the API + write 200–400 lines" into "transcribe a pinned
5-step reduction."

## Invariants (unchanged this session)

- `proofs/Proofs/GreensTheoremOQ02.lean`: **1 axiom** (`greens_theorem_l1curl`),
  0 sorries; no Lean edited.
- Mathlib pin: `v4.26.0` (predates the keystone).
- Open PRs for slug: 0.

## Next pickup

Gated on the Mathlib bump, which needs Docker. When Docker returns: bump to
`≥ v4.28.0` on a dedicated branch, rebuild the full corpus, then transcribe the
step 1–5 blueprint above into `GreensTheoremOQ02.lean`, flipping
`greens_theorem_l1curl` from `axiom` to `theorem`. Do **not** re-survey — the
API is pinned here.
