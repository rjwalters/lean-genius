# Knowledge Base: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The open question asks to discharge the `exists_nice_reparam` **axiom** in the parent
proof `proofs/Proofs/AreaOfCircleOQ01OQ02OQ02OQ01.lean`
(`namespace IsoperimetricFromFourier`) "from the inverse function theorem in Mathlib".

The axiom (parent file, lines 315–322):

```lean
axiom exists_nice_reparam (γ : SmoothClosedCurve) (hL : 0 < γ.circumference) :
    ∃ γ' : SmoothClosedCurve,
      γ'.circumference = γ.circumference ∧
      γ'.area = γ.area ∧
      (∀ t, deriv γ'.x t ^ 2 + deriv γ'.y t ^ 2 = (γ.circumference / (2 * π)) ^ 2) ∧
      (∫ t in (0:ℝ)..(2*π), γ'.x t = 0) ∧
      (∫ t in (0:ℝ)..(2*π), γ'.y t = 0)
```

with the relevant definitions (parent file, lines 198–216):

```lean
structure SmoothClosedCurve where
  x : ℝ → ℝ
  y : ℝ → ℝ
  smooth_x : ContDiff ℝ 1 x
  smooth_y : ContDiff ℝ 1 y
  periodic_x : ∀ t, x (t + 2 * π) = x t
  periodic_y : ∀ t, y (t + 2 * π) = y t

noncomputable def SmoothClosedCurve.circumference (γ) : ℝ :=
  ∫ t in (0:ℝ)..(2*π), sqrt (deriv γ.x t ^ 2 + deriv γ.y t ^ 2)
noncomputable def SmoothClosedCurve.area (γ) : ℝ :=
  (1/2) * |∫ t in (0:ℝ)..(2*π), (γ.x t * deriv γ.y t - γ.y t * deriv γ.x t)|
```

---

## Insights

### Session 2026-06-13 (s01, ORIENT) — feasibility blocked by two specification gaps

**Outcome: surveyed.** The OQ is *not* a tractable "wire up a Mathlib lemma" extension
(pool rated tractability 8/10). Two structural gaps make the stated route — proving the
axiom via the inverse function theorem (IFT) — infeasible without first amending the
parent proof's definitions.

**Gap 1 — `SmoothClosedCurve` has no regularity (immersion) field.**
Arc-length reparametrization defines `s(t) = ∫₀ᵗ √(x'² + y'²)` and inverts it. The IFT
applies only where `s'(t) = √(x'(t)² + y'(t)²) > 0` for *every* `t`, i.e. the curve must be
**regular** (`|γ'(t)| > 0` ∀t). The structure assumes only `ContDiff ℝ 1` + periodicity;
it admits curves with stationary points (`γ'(t) = 0`), for which `s` is not strictly
monotone and the IFT does not give a `C¹` inverse. So the axiom **cannot** be proved "from
the inverse function theorem" for `SmoothClosedCurve` as currently defined.

**Gap 2 — the conclusion does not tie `γ'` to `γ`, and as written already implies the goal.**
The axiom only requires the witness `γ'` to share `γ`'s *circumference* and *area*; it does
**not** require `γ'` to be a reparametrization of `γ` (same trace, `γ' = γ ∘ φ`). A genuine
reparametrization preserves both invariants automatically (arc length and signed area are
reparametrization-invariant), so the stated conclusion is strictly weaker than "a
reparametrization exists". Worse, any constant-speed witness `γ'` with speed `c = L/(2π)`
has circumference `L` and therefore satisfies the isoperimetric bound
`γ'.area ≤ π c² = L²/(4π)`. Since the axiom forces `γ'.area = γ.area`, it can hold only if
`4π·γ.area ≤ γ.circumference²` — which is **exactly** `isoperimetric_inequality`, the theorem
the axiom is invoked to prove. Read literally, `exists_nice_reparam` already contains the full
strength of the target theorem (it is not a benign analytic lemma feeding Wirtinger /
Cauchy–Schwarz).

**Consequence.** To make this OQ provable as intended, the parent proof must first be amended:
1. add a regularity field to `SmoothClosedCurve`, e.g.
   `regular : ∀ t, 0 < deriv x t ^ 2 + deriv y t ^ 2`, enabling the IFT; and
2. restate `exists_nice_reparam` so `γ'` is literally a reparametrization of `γ`
   (`γ'.x = γ.x ∘ φ`, `γ'.y = γ.y ∘ φ` for a `C¹` increasing `φ` with `φ(2π)−φ(0) = 2π`),
   making circumference/area preservation a *change-of-variables theorem* rather than an
   assumption — and removing the circularity in Gap 2.

Even after (1)+(2) the build is substantial — define the (rescaled) arc-length map, prove it
is a `C¹` diffeomorphism via Mathlib's IFT, and prove reparametrization-invariance of arc
length and signed area (Mathlib `intervalIntegral` change-of-variables / FTC). Rough estimate
**400–800 lines**; not the low-effort extension the pool metadata suggests.

**Verification status this session:** Docker build harness down and Aristotle backend
returning 404 (both confirmed live this session), so no Lean ACT could be compiled/checked.
This is an OBSERVE/ORIENT survey only — no proof was attempted or claimed.

---

## Dead Ends

- **Direct IFT on `SmoothClosedCurve` as defined** — fails: no regularity hypothesis, so
  `s' = |γ'|` may vanish and the inverse function theorem does not apply (Gap 1).
- **Treating the axiom as a routine Mathlib-wiring extension** — fails: as stated it is
  logically at least as strong as the isoperimetric inequality itself (Gap 2).

---

### Session 2026-06-20 (s02, ORIENT, researcher-12) — harness up; change-of-variables API pinned

**Outcome: surveyed (held).** Re-confirmed S1's analysis against the live pin and parent file,
and de-risked the eventual build by locating the exact Mathlib lemmas.

- **Parent re-verified:** `AreaOfCircleOQ01OQ02OQ02OQ01.lean` is registered and proves
  `isoperimetric_inequality` (line 368) from **5 disclosed axioms** — `fourier_decomp_exists`,
  `exists_nice_reparam`, `wirtinger_sum_bound`, `area_cauchy_schwarz_bound`,
  `integral_cauchy_schwarz_sq`. This is a properly-`axiomatized` entry (not an integrity
  violation); the OQ targets discharging just `exists_nice_reparam`. The Lean proof routes
  through the reparam axiom **plus** the Wirtinger/Cauchy–Schwarz axioms (line 372 onward), so
  the Gap-2 circularity is a statement about the axiom's *logical strength*, not a literal
  one-line collapse inside the file — but S1's point stands: as written, the witness is only
  required to *share* `γ`'s area/circumference, not to *be* a reparametrization of `γ`.
- **Harness now UP:** Docker build verified working this session (used it on a sibling entry),
  lifting S1's "build blackout" caveat. The build is now *attemptable*, just large.
- **Change-of-variables API located (was an S1 assumption):** Mathlib provides
  `intervalIntegral.integral_comp_mul_deriv` / `integral_comp_smul_deriv` (and primed variants)
  in `Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean:317–387`. These
  are exactly the substitution lemmas needed to prove reparametrization-invariance of arc length
  and signed area once the structure is amended — confirming the ~400–800 LOC estimate is
  API-supported, not blocked on a missing change-of-variables theorem.

## Next Steps

1. Propose amending the parent proof: add `regular` field to `SmoothClosedCurve` and restate
   `exists_nice_reparam` as a genuine reparametrization (`γ' = γ ∘ φ`). **(Touches a verified
   gallery entry — do via a separate companion + a deliberate parent-edit PR, not in-place
   blindly.)**
2. Build the reparametrization-invariance lemmas FIRST as a standalone companion using
   `intervalIntegral.integral_comp_mul_deriv` (located this session): for a `C¹` increasing
   `φ` with `φ(2π)−φ(0)=2π`, both `circumference` and signed `area` are invariant. This is the
   mathematical heart of Gap 2 and is verifiable in isolation without risking the parent.
3. Then attempt the IFT-based arc-length construction (Mathlib FTC + inverse-function-theorem;
   the regular-curve hypothesis from step 1 makes `s'(t)=|γ'(t)|>0`, enabling the `C¹` inverse).
   ~400–800 lines total; harness is up, so it is now attemptable.
