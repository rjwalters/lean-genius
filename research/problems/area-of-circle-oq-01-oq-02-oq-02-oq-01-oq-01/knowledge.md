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

---

### Session 2026-06-20 (s03, ACT, researcher-8) — invariance core PROVED (0-axiom)

**Outcome: progress (ACT).** Built and verified the change-of-variables heart of Gap 2 that
S1/S2 identified as the prerequisite for any honest discharge of `exists_nice_reparam`. New
file `proofs/Proofs/AreaOfCircleOQ01OQ02OQ02OQ01OQ01.lean` (196 lines, 6 theorems, 2 defs,
**0 axioms, 0 sorries**, docker build GREEN). Gallery entry created under
`src/data/proofs/area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01/` (status `verified`, badge
`original`).

Proved, for `C¹` 2π-periodic coordinates `x, y` and a `C¹` reparametrization `φ` with
`φ(2π) = φ(0) + 2π`:
- `arclength_reparam_invariant` (assuming `φ' ≥ 0`):
  `∫₀²π √((x∘φ)'²+(y∘φ)'²) = ∫₀²π √(x'²+y'²)`.
- `signed_area_reparam_invariant` (no monotonicity needed):
  `∫₀²π ((x∘φ)(y∘φ)' − (y∘φ)(x∘φ)') = ∫₀²π (x·y' − y·x')`.
Plus helpers `periodic_deriv`, `speedFn_periodic`, `areaFn_periodic`, `deriv_coord_comp`.

**Technique (3-step, both proofs):**
1. chain rule `deriv_comp` factors the γ∘φ integrand pointwise as `(integrand∘φ)·φ'`
   (arc length: `√(φ'²·A) = φ'·√A` via `Real.sqrt_mul`+`Real.sqrt_sq`, needs `φ'≥0`;
   signed area: `φ'` factor is linear ⇒ no sign hypothesis);
2. `intervalIntegral.integral_comp_mul_deriv` substitutes `u = φ t` →
   `∫_{φ0}^{φ(2π)} integrand`;
3. `hshift : φ(2π)=φ0+2π` + integrand periodicity ⇒
   `Function.Periodic.intervalIntegral_add_eq` collapses to `∫₀²π`.

**Mathlib gotchas pinned (v4.26.0):**
- no `Function.Periodic.deriv` lemma exists; derive it from `deriv_comp_add_const` +
  `funext hf` (period identity), **no differentiability hypothesis required**.
- continuity of the speed integrand: `(((hx.continuous_deriv le_rfl).pow 2).add
  ((hy.continuous_deriv le_rfl).pow 2)).sqrt` (use `Continuous.sqrt`, not `continuous_sqrt`
  which is ambiguous with the NNReal one under `open Real`).
- `integral_comp_mul_deriv` wants `Continuous g` (g = the period integrand as a function of
  the *new* variable), `ContinuousOn (deriv φ)` on `uIcc`, and `∀ t ∈ uIcc, HasDerivAt φ
  (deriv φ t) t` via `.differentiableAt.hasDerivAt`.

**What remains to fully discharge the axiom (unchanged from S2's plan):**
1. add a `regular : ∀ t, 0 < deriv x t ^2 + deriv y t ^2` field to `SmoothClosedCurve` so the
   arc-length map `s(t)=∫₀ᵗ|γ'|` is strictly increasing and the IFT gives a `C¹` inverse;
2. restate `exists_nice_reparam` so the witness is literally `γ' = γ ∘ φ` (then these two
   invariance theorems supply the circumference/area-preservation clauses directly, killing
   the Gap-2 circularity);
3. construct the rescaled arc-length `φ` via Mathlib's IFT and prove it is increasing,
   `C¹`, and period-commuting. Steps 1–2 touch a verified gallery entry → do via a deliberate
   parent-edit PR, not in place.

---

### Session 2026-06-20 (s04, ACT, researcher-9) — verified self-contained arc-length + mean-subtraction infrastructure; both sibling and parent found bit-rotted

**Outcome: ACT (0-axiom file shipped) + integrity finding.** Two results this session.

**(A) INTEGRITY FINDING — sibling and parent are bit-rotted on Mathlib v4.26.0.**
The hard analytic core (the IFT arc-length reparametrization estimated at 400–800 LOC) was
*already written* `0`-axiom in the sibling `AreaOfCircleOQ01OQ03OQ01.lean`
(`ArcLengthReparam.exists_arclength_reparam'`: `arcLengthInv` via `Equiv.ofBijective`,
`arcLengthInv_hasDerivAt` via `HasStrictDerivAt.to_local_left_inverse`, plus
`circumference_reparam_preserved`/`area_reparam_preserved`). **However, both that sibling and
the parent `AreaOfCircleOQ01OQ02OQ02OQ01.lean` fail to `lake build` on the current Mathlib
pin** — verified directly via docker this session:
- Parent: `Real.contDiff_cos`/`Real.contDiff_sin`/`pi_lt_four` unknown, several rewrite
  failures, a type mismatch (≈6 errors).
- Sibling: `Filter.eventually_of_forall`, `HasFDerivAtFilter.congr`, `Function.continuous`
  removed/renamed; many rewrite failures and "No goals"/type-mismatch (≈25 errors).
These are gallery entries marked **"verified"** that have silently rotted — audits use a
cheap grep check, not `lake build`. **Flag for the mechanic/auditor.** (This matches the
prior note that the OQ03 area-of-circle parent bit-rotted on v4.26.0.)

**(B) Shipped a SELF-CONTAINED 0-axiom file** `AreaOfCircleOQ01OQ02OQ02OQ01OQ01Reparam.lean`
(`namespace RegularCurveArcLength`, Mathlib-only imports — deliberately depends on *neither*
broken file so it compiles and survives the rot). 302 LOC, 22 theorems / 7 defs / 1
structure, docker-verified GREEN. Content:
1. `structure RegularClosedCurve` — C¹ + 2π-periodic + a **`regular` field**
   (`∀ t, 0 < |γ'(t)|²`). This bakes in the Gap-1 hypothesis the survey proved necessary.
2. **Arc-length map = the IFT object.** `speed` continuous & strictly positive;
   `arcLength s = ∫₀ˢ speed` has `HasDerivAt (arcLength) (speed s) s` (FTC,
   `integral_hasDerivAt_right`), so `deriv arcLength = speed`, hence **`StrictMono` and
   `Injective`** (`strictMono_of_deriv_pos`) and continuous. This is exactly the strictly-
   monotone differentiable map the inverse function theorem inverts.
3. **Mean subtraction = Gap 2.** `centered γ` subtracts each coordinate's period-mean
   `(1/2π)∫`. Proven: `centered γ` is again a `RegularClosedCurve` (deriv unchanged via
   `deriv_sub_const`, so regularity/periodicity/`C¹` all survive); `centered_circumference`
   and `centered_area` (the signed-area correction `meanX·y' − meanY·x'` integrates to zero
   because `∫ x' = ∫ y' = 0` over a period, via `integral_deriv_eq_sub` + periodicity);
   `speed_centered` (speed unchanged); `integral_centered_x/y_eq_zero` (**zero mean**).
4. `centered_preserves_all` — capstone: from a constant-speed curve, `centered` yields all
   **five** clauses of `exists_nice_reparam` (circumference, area, constant speed, two
   zero-mean) at once.

**Honest status.** This file does NOT, by itself, fully prove `exists_nice_reparam` even for
regular curves: it supplies the two *ends* (the strictly-monotone differentiable arc-length
map, and the zero-mean centering with all preservation lemmas), but the IFT-inverse +
change-of-variables *middle* that joins them lives in the bit-rotted sibling. Once the
sibling is repaired (or that middle re-derived ~300 LOC on the current API), composing it
with `centered_preserves_all` gives the full `0`-axiom `exists_nice_reparam` for regular
curves immediately. Parent's `axiom exists_nice_reparam` is NOT removed (its
`isoperimetric_inequality` is stated for all curves, and the axiom is genuinely false for
non-regular curves — Gap 1).

## Dead Ends (updated)

- **Import-and-compose against the sibling `exists_arclength_reparam'`** — blocked: the
  sibling does not build on Mathlib v4.26.0. Hence the self-contained route. Always
  `lake build` (not grep) a dependency before importing it; "verified" gallery badges can be
  stale under Mathlib drift.

### Session 2026-06-21 (s05, ACT, researcher-9) — IFT middle re-derived; full `exists_nice_reparam` for regular curves PROVED (0-axiom)

**Outcome: ACT — the open question's core is now discharged on the regular locus.** New file
`proofs/Proofs/AreaOfCircleOQ01OQ02OQ02OQ01OQ01IFT.lean` (`namespace RegularCurveArcLength`,
imports Mathlib + the verified s04 `…Reparam` companion only; **0 axioms, 0 sorries, 35
theorems/3 defs, docker GREEN**, `#print axioms` = `[propext, Classical.choice, Quot.sound]`
i.e. no `ofReduceBool`/`sorryAx`). This re-derives the **IFT-inverse + change-of-variables
middle** that the bit-rotted sibling held, on the current pin, against the `RegularClosedCurve`
structure, and composes it with the s04 ends to give:

**`exists_nice_reparam_for_regular`** — every regular closed curve `γ` with `0 < L` admits a
regular closed curve `ρ` with `ρ.circumference = L`, `ρ.area = γ.area`, constant speed
`(L/2π)²`, and **zero mean** (`∫₀²π ρ.x = ∫₀²π ρ.y = 0`). This is exactly the parent axiom's
conclusion, discharged where the IFT route is valid (Gap-1 regular curves).

**Construction (all 0-axiom on v4.26.0):**
1. Arc-length `s` is bijective ℝ→ℝ: surjective by IVT (`intermediate_value_uIcc` over
   `s(±n·2π)=±nL` bounds, `div_lt_iff₀`), injective from the s04 `StrictMono`.
2. `σ = s⁻¹` via `Equiv.ofBijective … |>.symm`; `C¹` with `σ'(y)=1/speed(σ(y))` by the IFT
   (`hasStrictDerivAt_of_hasDerivAt_of_continuousAt` + `HasStrictDerivAt.to_local_left_inverse`),
   continuity via `Monotone.continuous_of_surjective` + `contDiff_one_iff_deriv`.
3. `τ(t)=σ(c·t)`, `c=L/2π`: `C¹`, quasi-periodic `τ(t+2π)=τ(t)+2π`, and the reparam
   `ρ = γ∘τ` has **constant speed `c`** (chain rule + `speed(σ(ct))·(1/speed·c)=c`), so `ρ` is
   built directly as a `RegularClosedCurve` (the `regular` field = `c²>0`).
4. Circumference preserved trivially (`∫₀²π c = 2πc = L`, no change-of-variables needed —
   the structure gives constant speed). Area preserved by genuine change-of-variables
   (`integral_comp_mul_deriv'`) + signed-area-integrand periodicity collapsing `[τ0,τ0+2π]`→
   `[0,2π]` (`Function.Periodic.intervalIntegral_add_eq`).
5. Compose with s04 `centered` → zero mean while preserving the other four clauses.

**Mathlib v4.26.0 pin notes (the sibling's actual bit-rot):** the only true API renames the
sibling needed were `Filter.eventually_of_forall`→`Eventually.of_forall` and
`lt_div_iff`/`div_lt_iff`→`…₀`. Other gotchas hit this session: `deriv_comp_add_const` needs
explicit `(f) (a) (x)` args; `integral_comp_add_left` changed arity (use
`Function.Periodic.intervalIntegral_add_eq` for the periodic shift instead); `simp_rw [hderiv]`
cannot rewrite under an *unapplied* `Continuous (deriv σ)` — `funext` to `deriv σ = fun y => …`
first; `area`'s `(1/2)*|·|` needs **two** `congr 1` to strip the constant *and* the abs before
the integral identity; `integral_comp_mul_deriv'` rw-matches only if the integrand is literally
`(g ∘ τ) x * f' x` (write the `∘` explicitly in the `integral_congr` target). Verified all key
lemma names against the unpacked Mathlib source in a sibling worktree before writing — much
faster than build-failure iteration.

**Honest scope.** Parent `axiom exists_nice_reparam` is NOT removed: it is stated for *all*
`SmoothClosedCurve` and is genuinely false for non-regular curves (Gap 1). This file is the
maximal honest target — the regular-curve version, which is where "prove the reparam axiom from
the IFT" can succeed. A parent edit restating the axiom for regular curves + importing this
would drop `axiomCount` 5→4, but touches a verified gallery entry (sensitive).

## Next Steps (updated)

1. **(optional, sensitive) Parent edit:** restate parent `exists_nice_reparam` with a `regular`
   field on `SmoothClosedCurve` and discharge it via `exists_nice_reparam_for_regular`
   (a `SmoothClosedCurve`↔`RegularClosedCurve` bridge is needed). Drops parent `axiomCount` 5→4.
   Touches a verified entry → deliberate parent-edit PR, not in place.
2. **Mechanic task (still open):** repair the bit-rotted `AreaOfCircleOQ01OQ03OQ01.lean` (sibling)
   and `AreaOfCircleOQ01OQ02OQ02OQ01.lean` (parent) for v4.26.0 — the renames are now pinned
   above. These are "verified" gallery entries that fail `lake build`.
3. Remaining four parent axioms (`fourier_decomp_exists`, `wirtinger_sum_bound`,
   `area_cauchy_schwarz_bound`, `integral_cauchy_schwarz_sq`) — separate analytic targets.

### Session 2026-06-21 (s06, ACT, researcher-9) — both Cauchy–Schwarz parent axioms discharged 0-axiom

**Outcome: ACT — two of the four remaining analytic parent axioms are now proved.** New
self-contained file `proofs/Proofs/AreaOfCircleOQ01OQ02OQ02OQ01OQ01CauchySchwarz.lean`
(`namespace IsoperimetricCauchySchwarz`, imports `Mathlib` only; **0 axioms, 0 sorries, 4
theorems, docker GREEN on v4.26.0**, `#print axioms` = `[propext, Classical.choice, Quot.sound]`
for all three headline results — no `ofReduceBool`/`sorryAx`). This discharges the two
Cauchy–Schwarz axioms of the parent `IsoperimetricFromFourier` proof:

* **`integral_cauchy_schwarz_sq`** (parent axiom verbatim) — for continuous `x, y`,
  `(∫₀²π √(x²+y²))² ≤ 2π · ∫₀²π (x²+y²)`. Proof = discriminant of the nonnegative quadratic
  `λ ↦ ∫₀²π (√(x²+y²) − λ)² = ∫g² − 2λ∫g + 2π·λ²`, evaluated at `λ = (∫g)/(2π)`. The parent
  axiom carries *no* hypotheses because `SmoothClosedCurve` is `C¹` hence continuous; my
  statement makes that continuity explicit (strictly more general — no periodicity/`C¹` needed).

* **`area_cauchy_schwarz_bound`** + **`…_contDiff`** corollary (parent axiom shape) — for
  continuous coords `x,y` and continuous velocity `dx,dy` with constant speed `dx²+dy²=c²`
  (`0≤c`), `|∫₀²π (x·dy − y·dx)| ≤ c·∫₀²π √(x²+y²)`. Since signed area `A = ½|∫(x·dy−y·dx)|`,
  the LHS is exactly `2A`, so this is the parent's `2A ≤ c·∫√(x²+y²)`. The `…_contDiff` version
  instantiates `dx,dy := deriv x, deriv y` for `C¹` coords (literally the axiom signature).
  Proof = pointwise 2D CS `|x·dy − y·dx| ≤ √(x²+y²)·√(dx²+dy²) = c·√(x²+y²)`, then
  `|∫| ≤ ∫|·| ≤ ∫ c√(x²+y²) = c·∫√(x²+y²)`.

**Mathlib v4.26.0 pin notes / gotchas:**
- `integral_const_mul` and `integral_const` are **ambiguous** (`intervalIntegral.*` vs
  `MeasureTheory.*`) — must fully qualify as `intervalIntegral.integral_const_mul` /
  `intervalIntegral.integral_const` inside an `open MeasureTheory intervalIntegral` file.
- Bare `rw [mul_comm]` rewrites the *first* product it finds (here the `|x·dy − y·dx|` inside
  the abs) — give explicit args `rw [mul_comm (√(x t^2+y t^2)) c]` to flip the intended factor.
- Discriminant assembly: avoid `set S`/`Sxy` before the `integral_add/sub` rewrites — those
  rewrites *produce* fresh `∫ g` terms that won't fold to the `set` name, so `ring` then sees
  two distinct atoms. Prove the `expand` equation purely between integral expressions first,
  derive `hquad`, and only then `set A := ∫g²`, `set B := ∫g` (no further rewriting after).
- Finish the discriminant division-safely: `B² = B²/(2π)·(2π) ≤ A·(2π) = 2π·A`
  (`field_simp` for the first `=`, `mul_le_mul_of_nonneg_right` for the `≤`) — feeding the
  raw `B/(2π)` substitution to `nlinarith` fails on the divisions.
- Key lemmas: `intervalIntegral.integral_nonneg`, `IntervalIntegrable.const_mul`/`.sub`/`.add`,
  `abs_integral_le_integral_abs`, `integral_mono_on hab hf hg h`, `Real.sqrt_sq_eq_abs`,
  `Real.sqrt_mul (0≤·)`, `Real.sqrt_sq (0≤·)`, `Real.sq_sqrt (0≤·)`, `ContDiff.continuous_deriv_one`.

**Honest scope.** These theorems are stated for raw continuous functions, not the parent's
`SmoothClosedCurve` structure, so they are not yet *wired into* the parent (that is a separate,
sensitive parent edit that would drop `axiomCount` 5→4→…→2). Mathematically the two
Cauchy–Schwarz axioms are now fully discharged 0-axiom; only the two genuinely Fourier-analytic
axioms (`fourier_decomp_exists`, `wirtinger_sum_bound`) remain.
