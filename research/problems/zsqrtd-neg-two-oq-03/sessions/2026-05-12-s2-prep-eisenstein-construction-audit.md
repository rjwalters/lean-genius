# S2 PREP — Eisenstein integer construction audit and skeleton review

**Date**: 2026-05-12
**Researcher**: researcher-6
**Phase**: PREP (scoping for S2 — does not modify the Lean file)
**Conditional on**: S1 OBSERVE (PR #18226, merged by researcher-5)

This document does **not** propose Lean changes. It audits the S2 Lean
skeleton sketched in `state.md` against the Mathlib v4.26.0 surface and
the closest in-repo precedent (`proofs/Proofs/ZsqrtdNegTwo.lean`), and
flags two specific friction points that will block a naive S2 ACT
implementation.

## The state.md skeleton (recap)

S1 (researcher-5) sketched a ~150-line S2 ACT pattern:

```lean
structure Eisenstein where
  re : ℤ
  im : ℤ

namespace Eisenstein

instance : Zero Eisenstein := ⟨⟨0, 0⟩⟩
instance : One Eisenstein := ⟨⟨1, 0⟩⟩
instance : Add Eisenstein := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg Eisenstein := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Mul Eisenstein :=
  ⟨fun x y => ⟨x.re * y.re - x.im * y.im,
               x.re * y.im + x.im * y.re - x.im * y.im⟩⟩

def norm (z : Eisenstein) : ℤ := z.re ^ 2 - z.re * z.im + z.im ^ 2

theorem norm_nonneg (z : Eisenstein) : 0 ≤ norm z := by
  have h4 : (4 : ℤ) * norm z = (2 * z.re - z.im) ^ 2 + 3 * z.im ^ 2 := by
    simp only [norm]; ring
  nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]

theorem norm_mul (x y : Eisenstein) :
    norm (x * y) = norm x * norm y := by
  simp only [norm, instMul, HMul.hMul]; ring
```

## Audit 1: the algebraic identities are correct

| Claim | Verification |
|---|---|
| `(a + bω)(c + dω) = (ac - bd) + (ad + bc - bd)ω` | `ω² = -1 - ω` ⇒ `(a+bω)(c+dω) = ac + (ad+bc)ω + bd·ω² = ac + (ad+bc)ω + bd(-1-ω) = (ac-bd) + (ad+bc-bd)ω` ✓ |
| `N(a + bω) = a² - ab + b²` | `ω̄ = ω² = -1 - ω`; `(a+bω)(a+bω̄) = (a+bω)(a-b-bω) = a² - ab - abω + abω - b²ω - b²ω² = a² - ab - b²ω + b² + b²ω = a² - ab + b²` ✓ |
| `4(a²-ab+b²) = (2a-b)² + 3b²` | RHS = `4a² - 4ab + b² + 3b² = 4a² - 4ab + 4b²` = `4·(a² - ab + b²)` ✓ |

All three S1 identities check out. The `norm_nonneg` proof is
sound (`nlinarith` discharges from `sq_nonneg` of the two
witnesses).

## Audit 2: `norm_mul` won't close with `simp only [norm, instMul, HMul.hMul]; ring`

**This is the first friction point.** The proposed
`simp only [norm, instMul, HMul.hMul]` does not unfold the
multiplication: `instMul` is the synthesized instance term and
`HMul.hMul` is the heterogeneous-multiplication wrapper that
`*` desugars through, but neither has a `rfl`-shape that exposes
the underlying `Eisenstein` constructor.

**Better pattern** (matches `Mathlib/NumberTheory/Zsqrtd/Basic.lean:164`
template for `Zsqrtd.commRing`):

```lean
@[simp] theorem mul_re (x y : Eisenstein) :
    (x * y).re = x.re * y.re - x.im * y.im := rfl

@[simp] theorem mul_im (x y : Eisenstein) :
    (x * y).im = x.re * y.im + x.im * y.re - x.im * y.im := rfl

theorem norm_mul (x y : Eisenstein) :
    norm (x * y) = norm x * norm y := by
  simp only [norm, mul_re, mul_im]
  ring
```

The same pattern is needed for `Zero`, `One`, `Add`, `Neg`:

```lean
@[simp] theorem zero_re : (0 : Eisenstein).re = 0 := rfl
@[simp] theorem zero_im : (0 : Eisenstein).im = 0 := rfl
@[simp] theorem one_re : (1 : Eisenstein).re = 1 := rfl
@[simp] theorem one_im : (1 : Eisenstein).im = 0 := rfl
@[simp] theorem add_re (x y : Eisenstein) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : Eisenstein) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : Eisenstein) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : Eisenstein) : (-x).im = -x.im := rfl
```

These 8 `rfl` simp lemmas plus the 2 multiplication ones add
~16 LOC to the S2 deliverable estimate (~165 LOC instead of ~150).

## Audit 3: the missing CommRing instance

**This is the second friction point and the larger one.** The S1
skeleton stops at `Mul` but the S3 EuclideanDomain instance derivation
(`norm_mul`, ring axioms) needs full `CommRing Eisenstein`. The
state.md says

> Build CommRing instance via the universal Polynomial.aeval
> approach, OR directly via ext + ring_nf. Pick the simpler one in S2.

The universal `Polynomial.aeval` approach (transport via
`AdjoinRoot (X^2 + X + 1 : ℤ[X])`) is heavyweight at v4.26.0.
The cleaner pattern is the **`Zsqrtd.commRing` template** from
`Mathlib/NumberTheory/Zsqrtd/Basic.lean:164`:

```lean
instance commRing : CommRing Eisenstein := by
  refine
  { Eisenstein.addGroupWithOne with
    npow := @npowRec Eisenstein ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring
```

This requires first establishing `Eisenstein.addGroupWithOne` (via
the additive structure already in S1's `Zero/One/Add/Neg`) — which
in Mathlib is itself a short structure-building incantation:

```lean
instance addCommGroup : AddCommGroup Eisenstein := by
  refine
  { add := (· + ·), zero := 0, neg := (- ·)
    sub := fun x y => x + -y
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_
    sub_eq_add_neg := ?_
    nsmul := nsmulRec
    zsmul := zsmulRec } <;>
  intros <;> ext <;> simp <;> ring
```

Followed by `AddGroupWithOne` (one extra field `intCast` plus 4
lemmas).

**The full ring structure ladder for Eisenstein** is:
1. `AddCommGroup` — ~12 LOC via `refine ... <;> intros <;> ext <;> simp <;> ring`
2. `AddGroupWithOne` — ~10 LOC, requires `intCast` and `natCast`
3. `CommRing` — ~12 LOC via the same `refine` pattern

**Plus** the 10 `@[simp] rfl` field-projection lemmas from Audit 2.

**S2 lean-file estimate (revised)**:

| Block | LOC |
|---|---|
| `structure Eisenstein` + namespace open | 10 |
| `Zero`, `One`, `Add`, `Neg`, `Mul` instances | 12 |
| 10 `@[simp] rfl` projection lemmas | 20 |
| `AddCommGroup` instance via `refine` | 15 |
| `AddGroupWithOne` instance (intCast/natCast) | 15 |
| `CommRing` instance via `refine` | 15 |
| `def norm` + `norm_nonneg` + `norm_mul` | 25 |
| Module docstring + header | 30 |
| **Total S2 ACT estimate** | **~140-150 LOC** |

This matches the state.md table's `~150 lines` line. The `~16 LOC`
adjustment for the projection lemmas is absorbed by leaving headroom
in the original estimate.

## Audit 4: unit group at S2 is premature

The state.md S2 deliverable lists

> A small unit-group sketch: `units_eq` recovering the 6 units
> `{±1, ±ω, ±ω²}` (analog of parent's 2-unit case for `ℤ[√-2]`).

The 6-unit group proof requires showing
`norm z = 1 ↔ z ∈ {±1, ±ω, ±ω²}`. The forward direction needs
the divisor-norm bound (`norm` is multiplicative AND `norm ≥ 1` for
nonzero ⇒ `norm = 1` is the unit characterization), and the
reverse direction requires checking each of the 6 candidates.

This is doable but bumps the S2 LOC budget from ~150 to ~250. The
parent `proofs/Proofs/ZsqrtdNegTwo.lean` has the 2-unit case
inline at ~30 LOC; the 6-unit case for Eisenstein scales to ~80 LOC
because of the `ω²` cases needing the `ω² + ω + 1 = 0` identity
expansion.

**Recommendation**: defer the unit-group sketch from S2 to a
sub-step of S3. S2 should land the **bare ring + norm**
(`CommRing` instance + `norm` + `norm_nonneg` + `norm_mul`), which
is the minimal structure needed by S3's `EuclideanDomain`
derivation. The unit group is a corollary of the Euclidean
structure, not a prerequisite.

Revised S2 LOC estimate: **~140 LOC** (per the table above),
0 sorries (assuming `<;> intros <;> ext <;> simp <;> ring` closes
the ring axioms, which Mathlib's `Zsqrtd.commRing` template
demonstrates is robust).

## Audit 5: R2 (Mathlib cyclotomic) cannot avoid the structure work

The S1 problem.md mentions R2:

> R2 via Mathlib's cyclotomic library (`IsCyclotomicExtension {3} ℚ K`,
> `IsPrimitiveRoot.toInteger`)

At v4.26.0, `IsCyclotomicExtension {3} ℚ K` works in an **abstract**
`K` field with `IsPrimitiveRoot ζ 3`, and `hζ.toInteger : 𝓞 K` is
the ring-of-integers element corresponding to `ω`. Files
`Mathlib/NumberTheory/NumberField/Cyclotomic/Three.lean:38-46`
work in this abstract setting.

**The friction**: our gallery target is `p = x² + 3y²` for prime
`p ≡ 1 (mod 3)` with **concrete** `x, y : ℤ`. Using the abstract
`K` route requires either:

(a) An identification `𝓞 K ≃+* Eisenstein` (where `Eisenstein` is
our concrete `ℤ × ℤ` structure) — a custom ring isomorphism, NOT
provided in Mathlib at v4.26.0 (`grep -rn "Eisenstein" Mathlib`
returns no hits in the NumberTheory tree).

(b) Reformulating the target as
"for prime `p ≡ 1 (mod 3)`, there exist `z : 𝓞 K` with `Algebra.norm ℚ z = p`",
which delegates the integer-coordinate extraction to a
`hζ.toInteger`-coordinate decomposition lemma — also not directly
available in Mathlib at v4.26.0.

Either (a) or (b) costs ~80-150 LOC on its own. So R2 does NOT
beat R1; it merely shifts where the structural work happens, and
adds the friction of pulling in the abstract cyclotomic
infrastructure (heavier imports, slower compile, abstract
quantification clutter in the main theorem).

**Recommendation confirmed**: R1 (concrete Eisenstein structure)
is the right route for the `n = 3` sub-case. R2 should be revisited
only if R3 (typeclass abstraction over `n ∈ {3, 7, 11}`) becomes
the target — at which point R2's abstract-K setup pays off in
factoring out per-`n` glue.

## What this doc does NOT decide

- **Whether to use `xy.re, xy.im` projections or `Eisenstein.mk` pattern
  matching in the field arithmetic of `mul_re/mul_im`.** Both compile;
  the projection form is shorter, the pattern-match form is more
  explicit. Pick one in S2 ACT.
- **Whether to inline the `AddGroupWithOne` instance or use
  Mathlib's `AddGroupWithOne.toAddCommGroup` adapter.** The adapter
  saves ~5 LOC but requires the implementer to remember the
  `intCast` and `natCast` defaulting conventions; the inline form
  is more self-contained.
- **Whether `n = 7, 11` sub-cases should fork from S2 or share a
  parametric `Z[(1+√-n)/2]` definition.** S1 problem.md flags
  this; per the LOC budget, parametric would be ~250 LOC + 100/n,
  vs. independent ~400 LOC per `n`. Decision deferred to S6+ scope.

## Race-safety note

As of this commit:

- `gh pr list --search "zsqrtd-neg-two-oq-03"` shows **only** seeker
  init PR #18166 (no research PRs).
- `git branch -r | grep zsqrtd-neg-two-oq-03` shows no in-flight
  research branches.
- S1 OBSERVE (PR #18226, researcher-5) merged ~4h ago, well outside
  the convergent-claim window for fresh tier-B slugs.

This doc adds zero conflict surface: no `.lean` change, no
`state.md` change, no `knowledge.md` change, no `meta.json` change,
no JSON change. The `sessions/` directory does not exist on
`origin/main` for this slug; this commit creates it.

## Files added (this session)

- `research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-12-s2-prep-eisenstein-construction-audit.md`
  (this file)

## Key Mathlib references located during this audit

- `Mathlib/NumberTheory/Zsqrtd/Basic.lean:33` — `structure Zsqrtd (d : ℤ)`
  (template for our `structure Eisenstein`)
- `Mathlib/NumberTheory/Zsqrtd/Basic.lean:164-180` — `Zsqrtd.commRing`
  via `refine ... <;> intros <;> ext <;> simp <;> ring` (template
  for `Eisenstein.commRing`)
- `Mathlib/NumberTheory/Zsqrtd/Basic.lean:420` — `def Zsqrtd.norm`
  (signature parallel, but ours uses `a² - ab + b²` not `a² - d·b²`
  because Eisenstein is not a `Zsqrtd`)
- `Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean:231` — `instance : EuclideanDomain ℤ[i]`
  template for our S3 `EuclideanDomain Eisenstein`
- `Mathlib/NumberTheory/NumberField/Cyclotomic/Three.lean:38-46` —
  the abstract `IsCyclotomicExtension {3} ℚ K` setting (R2 route;
  not recommended per Audit 5)

## Next action

S2 ACT (separate session): create `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`
along the R1 path with the structure ladder spelled out in Audit 3,
the projection-simp lemmas from Audit 2, and the bare `norm` +
`norm_nonneg` + `norm_mul` triple. Defer unit-group computation to
S3 per Audit 4. Build verification via worktree-local
`./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03`.

Expected S2 deliverable: ~140 LOC, 0 sorries, 0 axioms.
