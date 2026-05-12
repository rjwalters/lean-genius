# Session 2026-05-12 S1 OBSERVE — Mathlib's `AffineCombination.Ceva` already covers n-dim concurrency; mass-point bookkeeping is the missing bridge

**Mode**: FRESH (S1 OBSERVE, doc-only)
**Researcher**: researcher-3
**Outcome**: scouted — Mathlib's `Mathlib.LinearAlgebra.AffineSpace.Ceva`
(Joseph Myers, 2025) already provides the n-dimensional Ceva concurrency
theorem via `AffineIndependent.exists_affineCombination_eq_smul_eq_of_fintype`.
Three S2 targets identified for the genuinely-missing mass-point
bookkeeping lift.

## 1. The slug, taken literally

`cevas-theorem-oq-04` (parent, 242 LOC, verified) is "Ceva's Theorem
via Mass Point Geometry". Its `src/data/proofs/cevas-theorem-oq-04/meta.json`
lists four open questions:

```json
"openQuestions": [
  "Can mass points be generalized to higher-dimensional simplices?",
  "Connection to barycentric coordinates: mass point assignments ARE barycentric coordinates",
  "Can the mass point approach be extended to non-Euclidean Ceva (using sin/sinh ratios)?",
  "Weighted mass points for angle bisectors: masses proportional to opposite side lengths"
]
```

Seeker extracted the first as `cevas-theorem-oq-04-oq-01` on 2026-05-12
(notes: `"AVAILABLE — added by seeker 2026-05-12"`, tier B,
significance 6, tractability 6, tags `mass-point` + `triangle` +
`concurrency`).

The literal question: **Can the parent file's `MassPoint` /
`rD,rE,rF` framework lift from a triangle (3 vertices) to an
n-simplex (n+1 vertices)?**

## 2. What the parent file proves (`CevasTheoremOQ04.lean`, 242 LOC, 0 sorries)

```lean
namespace MassPointCeva

structure MassPoint where
  mA : ℝ; mB : ℝ; mC : ℝ
  hA : 0 < mA; hB : 0 < mB; hC : 0 < mC

noncomputable def rD (mp : MassPoint) : ℝ := mp.mC / (mp.mB + mp.mC)
noncomputable def rE (mp : MassPoint) : ℝ := mp.mA / (mp.mC + mp.mA)
noncomputable def rF (mp : MassPoint) : ℝ := mp.mB / (mp.mA + mp.mB)

-- The Ceva identity for any mass assignment
theorem ceva_identity (mp : MassPoint) :
    rD mp * rE mp * rF mp = (1 - rD mp) * (1 - rE mp) * (1 - rF mp)

-- The biconditional (the existence direction is constructive)
theorem mass_point_iff (d e f : ℝ) (...) :
    d * e * f = (1 - d) * (1 - e) * (1 - f) ↔
    ∃ mp : MassPoint, rD mp = d ∧ rE mp = e ∧ rF mp = f

end MassPointCeva
```

The parent works purely in ℝ-valued ratio arithmetic (no `AffineSpace`
import, no `Module` instances). It is essentially a *real-arithmetic
shadow* of the geometric Ceva theorem.

## 3. Mathlib coverage (`Mathlib.LinearAlgebra.AffineSpace.Ceva`)

`Mathlib/LinearAlgebra/AffineSpace/Ceva.lean` (213 LOC, copyright
2025 Joseph Myers) **already proves both the triangle Ceva identity
and the n-dim concurrency theorem**. Key lemmas:

### Triangle version (matching parent's `ceva_identity`)

```lean
namespace Affine.Triangle
section CommRing

/-- **Ceva's theorem** for a triangle, expressed in terms of multiplying weights. -/
lemma prod_eq_prod_one_sub_of_mem_line_point_lineMap {t : Triangle k P} {r : Fin 3 → k} {p' : P}
    (hp' : ∀ i : Fin 3, p' ∈
      line[k, t.points i, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i)]) :
    ∏ i, r i = ∏ i, (1 - r i)
```

This is `∏ rᵢ = ∏ (1 - rᵢ)` for cevians of a triangle that concur at
`p'`. In parent's notation: `rD rE rF = (1 - rD)(1 - rE)(1 - rF)`.

### Division-form (matching `prod_div_eq_one`)

```lean
section Field
/-- **Ceva's theorem** for a triangle, expressed using division. -/
lemma prod_div_one_sub_eq_one_of_mem_line_point_lineMap {t : Triangle k P} {r : Fin 3 → k}
    (hr0 : ∀ i, r i ≠ 0) {p' : P} (hp' : ...) :
    ∏ i, r i / (1 - r i) = 1
```

This is `(BD/DC)(CE/EA)(AF/FB) = 1` — the classical division-form
Ceva.

### n-dim generalization (THE answer to the slug)

```lean
namespace AffineIndependent

/-- A version of **Ceva's theorem** for an arbitrary indexed affinely
    independent family of points: consider some lines, each through one
    of the points and an affine combination of the points, and suppose
    they concur at `p'`; then `p'` is an affine combination of the points
    with weights proportional to those in the respective affine
    combinations. -/
lemma exists_affineCombination_eq_smul_eq_of_fintype [Fintype ι] {p : ι → P}
    (hp : AffineIndependent k p) {s : Set ι} (hs : s.Nonempty) {w : s → ι → k}
    (hw : ∀ i, ∑ j, w i j = 1) {p' : P}
    (hp' : ∀ i : s, p' ∈ line[k, p i, Finset.univ.affineCombination k p (w i)]) :
    ∃ w' : ι → k, (∑ j, w' j = 1) ∧ Finset.univ.affineCombination k p w' = p' ∧
      ∀ i : s, ∃ r, ∀ j, r * Set.indicator {(i : ι)}ᶜ (w i) j =
        Set.indicator {(i : ι)}ᶜ w' j
```

In English: for an affinely-independent family `p : ι → P` of points
(an arbitrary-dim simplex when `|ι| = n+1`), if cevian-style lines
through each `p i` and some affine combination `Σⱼ w i j · p j` (with
`Σⱼ w i j = 1`) all concur at `p'`, then `p'` itself is an affine
combination with weights `w'` that are *proportional* to each
`w i` restricted to the complement of `i`. This is precisely the
mass-point-style concurrency theorem in arbitrary dimension.

**Conclusion**: the geometric content of the slug is fully covered by
Mathlib. The literal question "Can mass points be generalized?" has
answer **YES, and the generalization is already in Mathlib as of 2025**.

## 4. What is genuinely missing in the gallery

While Mathlib has the concurrency theorem in arbitrary dimension, it
does NOT package the result as a "mass-point" structure with
constructive bijection masses ↔ ratios. Specifically:

- **No `MassPoint n` structure** for an (n+1)-vertex simplex.
- **No mass-to-ratio bijection** in arbitrary dimension. The parent's
  `mass_point_iff` (triangle) lifts conceptually but no Lean version
  exists.
- **No constructive certificate** for n-dim concurrency: Mathlib's
  `exists_affineCombination_eq_smul_eq_of_fintype` is an EXISTENCE
  result (`∃ r, ...`), not a CONSTRUCTIVE one.

The genuinely-missing content lies on three axes:

1. **The mass-point structure** — n+1 positive reals with derived
   face-points and the concurrency point at their normalized centroid.
2. **The mass-to-ratio bijection** — given a target ratio profile
   `r : Fin (n+1) → ℝ` satisfying a generalised Ceva identity, an
   explicit construction of masses realising it.
3. **The bridge to the parent file** — show that for `n = 2`,
   `MassPoint 2` is equivalent to `MassPointCeva.MassPoint`.

## 5. Three narrow S2 targets (in order of recommended priority)

### S2-A (RECOMMENDED). N-dim mass-point structure + concurrency at centroid (~80–120 LOC)

Create `proofs/Proofs/CevasTheoremOQ04OQ01.lean` containing:

```lean
import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.AffineIndependent

namespace NDimMassPoint

variable {k V P : Type*} [Field k] [LinearOrderedField k]
variable [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- An n-dim mass point assignment: positive masses on (n+1) vertices
    of an affinely-independent family. -/
structure MassPoint (n : ℕ) (p : Fin (n+1) → P) (hp : AffineIndependent k p) where
  mass : Fin (n+1) → k
  pos  : ∀ i, 0 < mass i

variable {n : ℕ} {p : Fin (n+1) → P} {hp : AffineIndependent k p}

/-- The global mass center is the weighted affine combination. -/
noncomputable def MassPoint.center (mp : MassPoint n p hp) : P :=
  (Finset.univ : Finset (Fin (n+1))).affineCombination k p
    (fun i => mp.mass i / ∑ j, mp.mass j)

/-- The face-point opposite to vertex `i`: the mass-weighted centroid
    of the (n)-face omitting vertex `i`. -/
noncomputable def MassPoint.facePoint (mp : MassPoint n p hp) (i : Fin (n+1)) : P :=
  (Finset.univ.erase i).affineCombination k p
    (fun j => if j = i then 0 else mp.mass j / ∑ j' ∈ Finset.univ.erase i, mp.mass j')

/-- **N-dim mass-point Ceva concurrency**: All cevians through `p i`
    and `facePoint i` meet at `center`. -/
theorem center_mem_cevian_line (mp : MassPoint n p hp) (i : Fin (n+1)) :
    mp.center ∈ AffineMap.lineMap (p i) (mp.facePoint i) '' Set.univ := by
  -- Algebraic fact: mp.center is a convex combination of p i and mp.facePoint i
  -- with parameter (Σⱼ≠ᵢ mⱼ)/(Σⱼ mⱼ).
  sorry

/-- **N-dim mass-point ratio profile**: r i := (mass j for j ≠ i ⁂ summed) /
    (total mass). These are the n+1 "Ceva ratios" generalising rD, rE, rF. -/
noncomputable def MassPoint.ratio (mp : MassPoint n p hp) (i : Fin (n+1)) : k :=
  (∑ j ∈ Finset.univ.erase i, mp.mass j) / ∑ j, mp.mass j

/-- The ratio sums: Σᵢ r i = n. (Sum of complementary mass fractions.) -/
theorem ratio_sum_eq_dim (mp : MassPoint n p hp) :
    ∑ i, mp.ratio i = n := by
  sorry

end NDimMassPoint
```

**Value**: Defines the missing `MassPoint n` structure, names the
core concurrency theorem, gives the dimensional generalization of the
"r-sum" identity (for n = 2: r1 + r2 + r3 = 2, equivalent to
"sum of complementary fractions = 2" for a triangle).

**Risk**: 2 sorries; both should close cleanly using
`Finset.affineCombination_indicator_subset` + linearity of affine
combinations. ~100 LOC including imports and docstrings.

### S2-B. Bridge to parent (triangle case) (~30–50 LOC)

Show that `NDimMassPoint.MassPoint 2 p hp` for any affinely-independent
`p : Fin 3 → P` recovers the parent's `MassPointCeva.MassPoint`:

```lean
namespace NDimMassPoint

/-- For n = 2 (triangle), the n-dim mass-point structure recovers the
    parent's `MassPointCeva.MassPoint` exactly. -/
def triangleBridge {p : Fin 3 → P} (hp : AffineIndependent k p)
    (mp : MassPointCeva.MassPoint) : MassPoint 2 p hp where
  mass := ![mp.mA, mp.mB, mp.mC]
  pos i := by fin_cases i <;> simp [mp.hA, mp.hB, mp.hC]

/-- The face-points of `triangleBridge mp` match the parent's
    `D, E, F` points, in some chosen orientation. -/
theorem triangleBridge_facePoint_zero (mp : MassPointCeva.MassPoint)
    {p : Fin 3 → P} (hp : AffineIndependent k p) :
    (triangleBridge hp mp).facePoint 0 =
      AffineMap.lineMap (p 1) (p 2) (rD mp) := by
  sorry

/-- The ratio identity in the triangle case matches the parent's
    `ceva_identity` after the bridge. -/
theorem triangleBridge_ceva_identity (mp : MassPointCeva.MassPoint)
    {p : Fin 3 → P} (hp : AffineIndependent k p) :
    let bridged := triangleBridge hp mp
    bridged.ratio 0 * bridged.ratio 1 * bridged.ratio 2 = (n : k) := by
  sorry

end NDimMassPoint
```

**Value**: Provides the categorical / definitional bridge that
justifies calling the n-dim structure a "generalization" of the
parent. Without this bridge, the n-dim version is a separate
construction with no semantic link to the parent's content.

**Risk**: 2 sorries on identification-of-points / arithmetic; both
solvable in ~10-15 LOC each.

### S2-C. Constructive existence (mass-from-ratios) (~50–80 LOC)

Generalize the parent's `masses_from_ceva` to n dimensions: given a
ratio profile `r : Fin (n+1) → k` satisfying the n-dim Ceva identity
(`Σ r i = n` together with some positivity / sum-to-one constraint),
construct explicit masses realising it.

**Strategy**: Set `mass 0 := 1`. Then iteratively solve for
`mass i` (for `i = 1, ..., n`) using the equation
`r i = (Σⱼ≠ᵢ mⱼ) / (Σⱼ mⱼ)`. The system is overdetermined for
`i = n`, and the n-dim Ceva identity is precisely the consistency
condition that makes the system solvable.

**Value**: Constructive certificate; matches the spirit of the
parent's `masses_from_ceva`. Lifts the parent's biconditional
`mass_point_iff` to n dimensions.

**Risk**: ~80 LOC; iteration / induction on `Fin (n+1)` with explicit
formula. The consistency condition is non-trivial in dim ≥ 3
because the n-dim Ceva identity is a *single* polynomial relation in
(n+1) ratios, not a chain of pairwise identities. Sorries: 2–3,
mostly arithmetic.

## 6. Anti-targets

The following should **NOT** be S2 targets:

- **Re-proving `prod_eq_prod_one_sub_of_mem_line_point_lineMap`** in
  mass-point notation: it's already in Mathlib for triangles, and
  the analogous statement for n-dim is implicit in
  `exists_affineCombination_eq_smul_eq_of_fintype` (the proportionality
  multiplier `r` plays the role of the "common ratio" on both sides).
- **Mass-point version of Mathlib's** `exists_affineCombination_eq_smul_eq_of_fintype`:
  trying to express this purely in mass-point language would re-state
  Mathlib's content with different bookkeeping.
- **Hyperbolic / non-Euclidean Ceva**: that's `cevas-theorem-oq-04-oq-03`
  ("Can the mass point approach be extended to non-Euclidean Ceva
  (using sin/sinh ratios)?"), a sibling slug.
- **Angle-bisector mass points**: that's openQuestions[3], another
  sibling.

## 7. Race / saturation context

Pre-claim probe at 2026-05-12 23:08 UTC:

```
cevas-theorem-oq-04-oq-01   open_PRs=0   remote_branches=0   recent_merges=0
```

Genuinely pristine. Among the pristine tier-B candidates at probe
time:

- `triangle-inequality-oq-04-oq-01` (Wiedijk #6, most marketable, race-risky)
- `euler-totient-oq-04-oq-01` (claimed by researcher-3 → PR #18316, S1 OBSERVE)
- `cevas-theorem-oq-04-oq-01` (this session)
- `erdos-659-oq-01-oq-02`
- `ptolemys-complex-proof-oq-02-oq-02` (Wiedijk #95)
- `arithmetic-series-...-oq-03-oq-02` (deep esoteric)
- `sperner-ndim-mathlib-oq-01-oq-04` (signed cell complexes)

Cevas-theorem is Wiedijk #61 — somewhat marketable, but the
sub-OQ "mass points → higher-dim simplices" is sufficiently downstream
(the mass-point angle is itself a stylistic choice, not the headline
result) that competing agents have so far passed it over.

## 8. Honesty assessment

The slug literally asks "can mass points be generalized?". The
honest answer is:
1. **The concurrency theorem itself** generalizes and is in Mathlib.
2. **The bookkeeping device** (the `MassPoint` structure, the
   ratio bijection) does NOT generalize "for free" — it requires a
   genuinely new structure definition and (especially) a new
   constructive existence proof for the mass-from-ratios direction.

So an S2 ACT shipping S2-A would honestly be packaged as:

> "Lean structural definitions for n-dim mass-point bookkeeping,
> built on Mathlib's existing n-dim Ceva concurrency."

NOT as "n-dim Ceva theorem proved". The latter overclaim would
duplicate Mathlib's `exists_affineCombination_eq_smul_eq_of_fintype`
in mass-point notation.

## 9. Recommendation

If a follow-up S2 ACT session is opened, **prefer S2-A** (mass-point
structure + face-points + center) as a single ~100 LOC file with 2
sorries closed via Mathlib's existing affineCombination API. S2-B
(triangle bridge) and S2-C (constructive existence) are natural
follow-up sessions but should NOT be bundled into S2-A — each is its
own ~50–80 LOC concern.

The gallery entry should clearly state in `meta.json`:
- `contribution`: "n-dim mass-point structural lift of `cevas-theorem-oq-04`'s framework"
- `status`: "verified" (after S2-A closes its sorries)
- `dependencies`: ["Mathlib.LinearAlgebra.AffineSpace.Ceva"]

And explicitly NOT claim "n-dim Ceva proved" — that credit goes to
Joseph Myers, 2025.

## 10. No edits to parent state

This session creates exactly one new file:

```
research/problems/cevas-theorem-oq-04-oq-01/sessions/2026-05-12-s01-observe-mathlib-affineCombination-bridge.md
```

No edits to:
- `proofs/Proofs/CevasTheoremOQ04.lean` (parent, 242 LOC verified)
- `src/data/proofs/cevas-theorem-oq-04/meta.json`
- Any parent `research/problems/cevas-theorem-oq-04/*.md`
- Any other gallery / annotation / Lean source.

PR is merge-conflict-free against any parallel claim or future S2 ACT.

---

**Time-budget**: claim → push targeted at ≤ 25 min (per researcher-3
tier-B / orphan-fresh fallback patterns).

**Sorry / axiom delta**: 0 / 0 (doc-only).

**Next-session recommendation**: open S2-A
(`CevasTheoremOQ04OQ01.lean`, `NDimMassPoint.MassPoint n` structure
+ center + facePoint + concurrency theorem, ~100 LOC, 2 closable
sorries).
