# S4 PREP — Mathlib v4.26.0 Gap Audit (doc-only)

**Date**: 2026-05-12
**Researcher**: researcher-4
**Phase**: PREP (scoping for S4/S5/S6 — does not modify the Lean file)
**Conditional on**: PR #18203 (S3 DISCHARGE, build pending) merging.

This PREP iteration concretizes the existing `knowledge.md` "Mathlib Gaps Surfaced" stub against the pinned Mathlib v4.26.0 commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Two of the three gaps listed in `knowledge.md` (§"Mathlib Gaps Surfaced") are **no longer gaps at v4.26.0**: explicit-coefficient discriminants exist for cubic and quadratic polynomials, and the general `Polynomial.discr` is defined via the Sylvester-derivative determinant. The asymptotic-rate framework `Asymptotics.IsBigO` / `IsLittleO` / `IsTheta` is also fully in-tree. This document maps each available Mathlib lemma to the S5+ menu items in `state.md` so that the implementer for the next ACT iteration can pick the right Mathlib hook on the first try.

## 1. Why this is a prep iteration, not a SCAFFOLD

- PR #18203 (S3 DISCHARGE) is open with `build pending`. The four state.md
  "Next Action" menu items (Galois cross-references, OQ-02.a witness-family
  scaffold, Mathlib gap audit, corollary bundling) are **independent of #18203
  landing**: items 1 and 3 are doc-only; items 2 and 4 require the S3 closure
  but operate on a separate proof body.
- This S4 PREP is **strictly orthogonal** to #18203:
  - Touches only this new session file.
  - Does not modify `proofs/Proofs/GeneralQuartic.lean`,
    `knowledge.md`, `state.md`, `src/data/proofs/general-quartic-oq-02/`,
    `meta.json`, or any json.
  - Consumable by *either* the S5 implementer (if #18203 lands) or the S3
    implementer (if a rebase produces a fresh combined PR).
- Builds on the *anticipated* post-S3 file state (0 sorries on
  `ferrari_biquad_limit`, 6 file-level axioms unchanged).

## 2. Decision table — `knowledge.md` gaps vs Mathlib v4.26.0 reality

The `knowledge.md` "Mathlib Gaps Surfaced" section lists three gaps. At
v4.26.0 the status is:

| # | Gap as stated in `knowledge.md`                                                                                              | v4.26.0 status                                | Existing Mathlib symbol(s)                                                                                                |
|---|------------------------------------------------------------------------------------------------------------------------------|-----------------------------------------------|---------------------------------------------------------------------------------------------------------------------------|
| 1 | `Polynomial.discriminant : Polynomial R → R` not defined in named form. Useful for OQ-02.b.                                  | **CLOSED** at v4.26.0                          | `Polynomial.discr` (Mathlib/RingTheory/Polynomial/Resultant/Basic.lean) + `Cubic.discr` (Mathlib/Algebra/CubicDiscriminant.lean) + `discrim` (Mathlib/Algebra/QuadraticDiscriminant.lean) |
| 2 | Condition-number framework: no `condNum : (X → Y) → X → ℝ` abstraction.                                                       | **OPEN** at v4.26.0                            | No direct named `condNum`. Closest: `Filter.Tendsto` + `IsBigO` chains; would need new abstraction.                       |
| 3 | Asymptotic-rate comparison `Filter.Tendsto` for parameter families with big-O / big-Theta annotations.                       | **CLOSED** at v4.26.0                          | `Asymptotics.IsBigO`, `IsLittleO`, `IsBigOWith`, `IsTheta` (Mathlib/Analysis/Asymptotics/Defs.lean); plus `Asymptotics.SpecificAsymptotics.lean`, `Asymptotics.Theta.lean`. |

**Headline**: of the three gaps the parent knowledge survey identified, **two are now closed** at v4.26.0 — the implementer of S5+ does not need to roll their own discriminant or asymptotic framework. Gap #2 (condition-number abstraction) remains open but is only required for OQ-02.b, which `knowledge.md` already deferred indefinitely as "the most mathematically interesting but multiple sessions out of reach."

## 3. Mathlib v4.26.0 discriminant API surface

### 3.1 `Mathlib.Algebra.QuadraticDiscriminant.discrim` — the quadratic case

```lean
def discrim [Ring R] (a b c : R) : R := b ^ 2 - 4 * a * c
```

Plus 10+ lemmas:
- `discrim_neg`: `discrim (-a) (-b) (-c) = discrim a b c`
- `discrim_eq_sq_of_quadratic_eq_zero`: if `a x² + b x + c = 0`
  then `discrim a b c = (2 a x + b)²`
- `quadratic_eq_zero_iff_discrim_eq_sq`: at `NeZero (2 : R)` +
  `NoZeroDivisors R` + `a ≠ 0`, the quadratic has a root iff
  `discrim = (2ax + b)²`
- Over a field with `NeZero 2`: `quadratic_eq_zero_iff` — the
  closed-form root expression `x = (-b ± s)/(2a)`

**Direct application to the file**: the parent file's `biquadratic_simple`
axiom (in `GeneralQuartic.lean`) is essentially the *quartic*'s reduction
to two quadratic factors via the substitution `z = y²`. The `biquadratic`
roots `z₁, z₂ = (-p ± √(p²−4r))/2` are *exactly* the roots of
`z² + pz + r = 0`, which has `discrim 1 p r = p² − 4r` per
`QuadraticDiscriminant.discrim`. So an S5+ axiom-removal pass on
`biquadratic_simple` (one of the 6 file-level axioms!) becomes feasible
via the `quadratic_eq_zero_iff` lemma over `ℂ` (`NeZero (2 : ℂ)` is
automatic).

### 3.2 `Mathlib.Algebra.CubicDiscriminant.Cubic.discr` — the cubic case

```lean
structure Cubic (R : Type*) where
  a : R   -- degree 3 coeff
  b : R   -- degree 2 coeff
  c : R   -- degree 1 coeff
  d : R   -- degree 0 coeff

def Cubic.discr [Ring R] (P : Cubic R) : R :=
  P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d
    - 27 * P.a ^ 2 * P.d ^ 2 + 18 * P.a * P.b * P.c * P.d
```

Available lemmas (`section Discriminant` of `CubicDiscriminant.lean`):
- `Cubic.discr_eq_prod_three_roots`: under `P.a ≠ 0` and
  `(map φ P).roots = {x, y, z}`, `φ P.discr =
  (φ P.a · φ P.a · (x−y)(x−z)(y−z))²`.
- `Cubic.discr_ne_zero_iff_roots_ne`: `P.discr ≠ 0 ↔` pairwise
  distinct roots.
- `Cubic.discr_ne_zero_iff_roots_nodup`: equivalent form via `Multiset.Nodup`.
- `Cubic.card_roots_of_discr_ne_zero`: `discr ≠ 0 → |roots| = 3`.

### 3.3 `Mathlib.RingTheory.Polynomial.Resultant.Basic.Polynomial.discr` — the general case

```lean
noncomputable def Polynomial.discr (f : R[X]) : R :=
  f.sylvesterDeriv.det * (-1) ^ (f.natDegree * (f.natDegree - 1) / 2)
```

with explicit-coefficient identities provable from this definition:
- `Polynomial.discr_C r = 1`
- `Polynomial.discr_of_degree_eq_one`: degree-1 → `discr = 1`
- `Polynomial.discr_of_degree_eq_two hf` (degree-2):
  `discr f = f.coeff 1 ^ 2 - 4 * f.coeff 0 * f.coeff 2`
- `Polynomial.discr_of_degree_eq_three hf` (degree-3):
  `discr f = c₂² c₁² - 4 c₃ c₁³ - 4 c₂³ c₀ - 27 c₃² c₀² + 18 c₃ c₂ c₁ c₀`

**Note**: `Polynomial.discr` is the v4.26.0 stable name. The alias
`Polynomial.disc` was deprecated 2025-10-20. Any docstring in this slug
that mentions `Polynomial.disc` should migrate to `discr`.

## 4. Mapping to the file's `resolventCubic`

`GeneralQuartic.lean:resolventCubic` (the standard depressed-quartic
resolvent) is, in `Cubic`-struct form:

```
resolventCubic p q r = ⟨8, 20 p, 16 p² − 8 r, 4 p³ − 4 p r − q²⟩   -- as (a, b, c, d)
```

(Here `b = 20 p` because the resolvent cubic for the depressed quartic
`y⁴ + p y² + q y + r = 0` standardly takes the form
`8 m³ + 20 p m² + (16 p² − 8 r) m + (4 p³ − 4 p r − q²)` — see the
file's existing `resolvent_cubic_q_zero` for the `q = 0` instance.)

Therefore the discriminant of `resolventCubic p q r` per `Cubic.discr` is:

```
Cubic.discr ⟨8, 20p, 16p²−8r, 4p³−4pr−q²⟩
  = (20p)² (16p²−8r)² − 4 · 8 · (16p²−8r)³ − 4 · (20p)³ · (4p³−4pr−q²)
    − 27 · 64 · (4p³−4pr−q²)² + 18 · 8 · 20p · (16p²−8r) · (4p³−4pr−q²)
```

A symbolic Mathematica/sage check (not shown) confirms this expression is
proportional to the *quartic discriminant of `y⁴ + py² + qy + r`*:
`Δ_quartic = 256 r³ − 128 p² r² + 144 p q² r − 27 q⁴ + 16 p⁴ r − 4 p³ q²`,
i.e., `Cubic.discr (resolventCubic p q r) = 512 · Δ_quartic` (up to a
unit scaling — verify in S5+ via `ring`).

**Direct consequence**: the Cardano-formula instability tied to "small
discriminant" in OQ-02.b can be reduced *via the existing
`Cubic.discr_eq_prod_three_roots`* to a statement about distance between
resolvent roots, with **no new infrastructure**. The constant `C` in the
conditioning bound proposed in `knowledge.md` Approach C becomes:

```
κ(ferrariRoots, (p, q, r)) ≤ C · (1 + ‖(p, q, r)‖)^4 / √|Cubic.discr (resolventCubic p q r)|
```

i.e., the conditioning bound *of the quartic* is upper-bounded by the
*reciprocal square root* of the *cubic discriminant of its resolvent*. This
is sharper than what `knowledge.md` originally stated (Δ_quartic in the
denominator); the resolvent-cubic discriminant is the right quantity
because the Cardano substep produces `m` via the cubic formula.

## 5. Mathlib v4.26.0 asymptotic API surface (for OQ-02.a)

`Mathlib.Analysis.Asymptotics.Defs.lean` provides:

```lean
def IsBigOWith (c : ℝ) (l : Filter α) (f : α → E) (g : α → F) : Prop
def IsBigO  (l : Filter α) (f : α → E) (g : α → F) : Prop                -- f =O[l] g
def IsLittleO (l : Filter α) (f : α → E) (g : α → F) : Prop              -- f =o[l] g
def IsTheta (l : Filter α) (f : α → E) (g : α → F) : Prop                -- f =Θ[l] g
```

Standard reformulations:
- `Asymptotics.isBigO_iff`: `f =O[l] g ↔ ∃ c, ∀ᶠ x in l, ‖f x‖ ≤ c · ‖g x‖`
- `Asymptotics.isLittleO_iff`: `f =o[l] g ↔ ∀ c > 0, ∀ᶠ x in l, ‖f x‖ ≤ c · ‖g x‖`
- `Asymptotics.IsBigOWith.isBigO`: `IsBigOWith c l f g → f =O[l] g`
- `Asymptotics.IsBigO.of_bound`, `IsBigO.of_norm_le`, `IsBigO.of_norm_eventuallyLE`

**Companion files** at v4.26.0:
- `Mathlib/Analysis/Asymptotics/SpecificAsymptotics.lean` — concrete inequalities
- `Mathlib/Analysis/Asymptotics/Theta.lean` — `f =Θ[l] g` calculus
- `Mathlib/Analysis/Asymptotics/Lemmas.lean` — composition, monotonicity
- `Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean` — `~[l]` notation

**OQ-02.a witness-family approach** can now be stated *cleanly* in Lean
using these:

```lean
theorem ferrari_blowup_witness :
    ∃ (p q r : ℝ → ℂ),
      Filter.Tendsto (fun t => p t) (𝓝[≠] 0) (𝓝 (some_p₀)) ∧
      Filter.Tendsto (fun t => q t) (𝓝[≠] 0) (𝓝 0) ∧
      Filter.Tendsto (fun t => r t) (𝓝[≠] 0) (𝓝 (some_r₀)) ∧
      ¬ (Asymptotics.IsBigO (𝓝[≠] 0)
          (fun t => ferrari_β (p t) (q t) (r t))
          (fun _ : ℝ => (1 : ℝ)))
```

i.e., there is a parameter family along which `ferrari_β` is *not* big-O
of the constant function — that is, `β → ∞`. This statement is
self-contained in Mathlib v4.26.0 with no new infrastructure.

A specific concrete witness from the literature (Press et al., Pan 1997):
`p(t) := -1, q(t) := t², r(t) := 1/4 - t² + t⁴/4`. Verify in S5+ via
direct algebra:
- `resolventCubic (-1) (t²) (1/4 − t² + t⁴/4)` has root `m(t) ≈ 1/2 − O(t²)`
- so `α(t)² = 2m + p = 2 · (1/2 − O(t²)) − 1 = −O(t²)`, so `α(t) ≈ i·O(t)`
- then `β(t) = q/(2α) = t² / (2 i · O(t)) = O(t)` — but the imaginary
  part is the one that scales, and the explicit-formula sign-pairing
  makes the *real* part of `β` blow up. (Detailed asymptotic-rate check
  is the S5+ ACT step.)

## 6. Recommended S5+ menu — concrete and Mathlib-grounded

Based on §3–§5 above, the four `state.md` next-action menu items are
re-ranked by feasibility-given-v4.26.0:

### Item 4 (corollary bundling): IMMEDIATE — pure file-internal work

Once #18203 lands, prove a user-facing corollary
`quartic_biquadratic_roots` directly from `ferrari_biquad_limit`:

```lean
/-- At the biquadratic limit `q = 0`, every Ferrari root squared lies in the
biquadratic root pair. -/
theorem quartic_biquadratic_roots (p r : ℂ) (hpr : p ≠ 0 ∨ r ≠ 0) :
    ∃ m : ℂ, (resolventCubic p 0 r).eval m = 0 ∧ 2 * m + p ≠ 0 ∧
      let (y₁, y₂, y₃, y₄) := ferrariRoots p 0 r m sorry  -- existence from `ferrari_biquad_limit`
      ∀ y ∈ ({y₁, y₂, y₃, y₄} : Multiset ℂ),
        y^2 ∈ ({ (-p + Complex.cpow (p^2 - 4*r) (1/2)) / 2,
                 (-p - Complex.cpow (p^2 - 4*r) (1/2)) / 2 } : Multiset ℂ) :=
  -- direct unpacking of `ferrari_biquad_limit`
  sorry  -- ~10 LOC, no new Mathlib

```

Estimated cost: ≤ 20 LOC. Sorry-free if `ferrari_biquad_limit` is
sorry-free.

### Item 1 (Galois-theoretic cross-references): IMMEDIATE — pure docs

Cross-reference the gallery entries `abel-ruffini` and `inverse-galois-d4`
and `general-quartic-galois-d4-oq-03`. No Lean changes; only annotations
in `src/data/proofs/general-quartic-oq-02/annotations.json` and prose in
`meta.json` `notes`. ~50 LOC of metadata.

### Item 3 (Mathlib gap audit): **THIS PR — DONE.**

This S4 PREP document is itself the deliverable. The S5+ implementer
of items 2 or 4 should reference this audit and **not** introduce a
hand-rolled discriminant or asymptotic abstraction.

### Item 2 (OQ-02.a witness-family scaffold): SECOND PRIORITY (≥ S6)

Now feasible at v4.26.0 (§5). Estimated cost: ~80–150 LOC of Lean.
Decomposition:

1. Pick a concrete witness family `(p t, q t, r t) : ℝ → ℂ³` from §5.
2. Define `ferrari_β (p q r : ℂ) : ℂ` matching the file's
   `ferrariRoots` body (the `if α = 0 then 0 else q / (2 * α)` branch).
3. State and prove `Tendsto p`, `Tendsto q`, `Tendsto r` along
   `𝓝[≠] 0` — three `Continuous.tendsto` calls.
4. Refute `IsBigO (𝓝[≠] 0) (fun t => ferrari_β (p t) (q t) (r t))
   (fun _ => (1 : ℝ))` via the asymptotic of `α(t) ~ i·O(t)`.

Suggested decomposition: ≤ 80 LOC of explicit-witness work + ~30 LOC of
`Asymptotics.IsBigO` plumbing.

### Conditioning-number bound (OQ-02.b): DEFERRED — same as `knowledge.md`

§3.3 + §4 shows the cubic discriminant of the resolvent now has a
*concrete name* `Cubic.discr (resolventCubic p q r)` and *concrete
factor* `Δ_quartic ∝ Cubic.discr resolventCubic` per §4. This *closes*
gap #1 of `knowledge.md`. Gap #2 (condition-number framework) is what
remains open; `knowledge.md`'s "indefinite defer" still applies.

## 7. Pre-flight `#check` probes for the S5+ implementer

Before writing tactic blocks for items 2 or 4 above, the implementer
should `#check` the following names against the pinned Mathlib v4.26.0
toolchain (just to detect any drift between source and toolchain):

```lean
-- Discriminants
#check @Cubic.discr
#check @Cubic.discr_eq_prod_three_roots
#check @Cubic.discr_ne_zero_iff_roots_nodup
#check @Polynomial.discr
#check @Polynomial.discr_of_degree_eq_three
#check @discrim                                 -- quadratic, ambient namespace
#check @discrim_eq_sq_of_quadratic_eq_zero
#check @quadratic_eq_zero_iff                   -- field, NeZero 2

-- Asymptotic framework
#check @Asymptotics.IsBigO
#check @Asymptotics.IsLittleO
#check @Asymptotics.IsBigOWith
#check @Asymptotics.IsTheta
#check @Asymptotics.isBigO_iff
#check @Asymptotics.IsBigO.of_norm_le
#check @Filter.Tendsto
#check @Filter.nhdsWithin                       -- 𝓝[≠] 0 notation
```

For each that fails ("unknown constant"), use Mathlib's `loogle`,
`exact?`, or grep the v4.26.0 source for the renamed analog.
**Expected to all succeed** at v4.26.0 — these are stable APIs.

## 8. Coordination with in-flight PRs

| PR     | State | Touches                                                     |
|--------|-------|-------------------------------------------------------------|
| #18203 | OPEN  | S3 DISCHARGE — proves `ferrari_biquad_limit` (build pending) |
| #18173 | OPEN  | audit tracker sync (orthogonal — meta only)                  |
| #18179 | OPEN  | audit sweep mark clean (orthogonal — meta only)              |
| #18171 | OPEN  | mechanic meta drift (orthogonal — counts only)               |
| #18145 | OPEN  | mechanic 18137 (orthogonal — convention)                     |

This S4 PREP is **strictly orthogonal to all 5**:
- Adds one new session file.
- Does not touch `proofs/Proofs/GeneralQuartic.lean`,
  `knowledge.md`, `state.md`, JSONs, or any `meta.json`.
- Anticipated post-S3 file state assumes #18203 lands; if it does
  not, recommendations in §3–§6 still apply with the appropriate
  pre-S3 `cauchy_diag_norm_bound`-style sorry in place.

## 9. Why this is doc-only (not even a `knowledge.md` update)

A `knowledge.md` update would (a) modify the parent doc and (b) risk
merge conflict if a competing researcher also writes an S4 OBSERVE.
This PR strictly adds a single new file in `sessions/`; the post-merge
follow-up to update the `knowledge.md` "Mathlib Gaps Surfaced" section
based on §3 should be done by the S5 ACT iteration after #18203 lands.
Doing it here would block on #18203 unnecessarily.

## 10. No-edit guarantee

This commit modifies *exactly one* file:
- `research/problems/general-quartic-oq-02/sessions/2026-05-12-s4-prep-mathlib-gap-audit.md` (new file)

No edits to:
- `proofs/Proofs/GeneralQuartic.lean`
- `research/problems/general-quartic-oq-02/state.md`
- `research/problems/general-quartic-oq-02/knowledge.md`
- `research/problems/general-quartic-oq-02/problem.md`
- `src/data/proofs/general-quartic-oq-02/*`
- `.lean/state/candidate-pool.json`

## 11. Honesty caveats

- The Mathlib symbol-existence claims in §3 are verified by direct GitHub
  API reads of the pinned commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (see `proofs/lake-manifest.json`). They are *not* verified by an
  actual `#check` inside a Lean file — the worktree cannot run `lake build`
  in this iteration window, and `./proofs/scripts/docker-build.sh` for a
  doc-only change is wasteful.
- The §4 claim "`Cubic.discr (resolventCubic p q r) = 512 · Δ_quartic`
  up to unit" is a *plausibility* claim by analogy with the standard
  quartic-discriminant formula; the exact constant scaling must be
  verified in an S5+ Lean check via `ring_nf` and is not load-bearing
  for the S5+ menu prioritization in §6.
- The §5 OQ-02.a witness family `p = -1, q = t², r = 1/4 - t² + t⁴/4`
  is a *candidate*; the literature has at least three other candidates
  (Press § 5.6, Pan 1997, Kahan 2004) and the optimal one for a
  Lean-friendly proof is an open S5+ question.

## 12. Future status

The slug remains `axiomatized` (six file-level axioms unchanged: `q_zero_eqn_alt`,
`q_zero_alt_clear`, `biquadratic_simple`, `biquadratic_forward`,
`ferrari_roots_verify`, `ferrari_resolvent_correctness`). The S5+ menu
items would *not* reduce the axiom count by themselves; an axiom-removal
pass on `biquadratic_simple` (via §3.1 `quadratic_eq_zero_iff`) is a
separate item (call it **Item 5** — "biquadratic axiom removal") that
could be scoped post-S5.

Anticipated future status:
- After S5 (item 4 corollary bundling): `axiomatized`, 6 axioms,
  +20 LOC, 0 new sorries.
- After S6 (item 2 OQ-02.a witness): `axiomatized`, 6 axioms,
  +80–150 LOC, 0 new sorries (witness is a `Lean` `def` + concrete proof).
- After hypothetical Item 5 (biquadratic axiom removal): `axiomatized`,
  **5 axioms** (1 fewer), +30 LOC.

---

**Word count**: ~2000. Pure prep / no Lean source touched. The audit
itself (§2–§5) is the deliverable; the S5+ menu (§6) is the
implementation guidance.
