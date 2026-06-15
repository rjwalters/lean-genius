# Knowledge Base: cevas-theorem-oq-02-oq-01-oq-02-oq-01

**OQ**: Formalize the projective unification — prove all three cases (spherical,
Euclidean, hyperbolic) from a *single* projective Ceva theorem via the Klein model.

Parent: `cevas-theorem-oq-02-oq-01-oq-02` (Hyperbolic Ceva via Weight Parameters,
`proofs/Proofs/CevasTheoremOQ02OQ01OQ02.lean`).

Phase: OBSERVE → ORIENT. Build-free SURVEY (Docker down + Aristotle 404,
2026-06-13 verification blackout). No Lean committed.

---

## Problem Understanding

The parent file already proves the three classical Ceva theorems share **one
algebraic concurrency criterion**:

> cevians `AD, BE, CF` concur  ⟺  `αD·αE·αF = βD·βE·βF`  ⟺
> `(βD/αD)(βE/αE)(βF/αF) = 1`        (`universal_weight_balance`, parent L254)

and that each geometry's metric side-ratio collapses to the **same** weight ratio:

| Geometry   | bilinear form `m = ⟨B,C⟩`     | ratio fn | side ratio `t(BD)/t(DC)`                       |
|------------|-------------------------------|----------|-----------------------------------------------|
| Spherical  | `+x₁y₁+x₂y₂+x₃y₃`, `m=cos d∈(−1,1)` | `sin`    | `β√(1−m²)/n ÷ α√(1−m²)/n = β/α`                |
| Euclidean  | degenerate, `m = 1`           | identity | `β/α` (barycentric, directly)                 |
| Hyperbolic | `+x₁y₁+x₂y₂−x₃y₃`, `m=cosh d>1`     | `sinh`   | `β√(m²−1)/n ÷ α√(m²−1)/n = β/α`                |

with `n² = α² + 2αβm + β²` in **all three** cases.

**What the parent does NOT do** — and what this OQ asks for: the parent proves the
three side-ratio identities *separately* (one structure `HyperbolicCevianConfig`
for the hyperbolic case, parallel reasoning for the spherical sibling
`cevas-theorem-oq-02-oq-01`) and then observes the criterion matches. It never
exhibits **one geometric object** from which all three descend. The OQ wants the
genuine unification: a single projective Ceva theorem in the **Cayley–Klein /
Beltrami–Klein model** whose three specializations *are* the three geometries.

---

## Insights

### 1. The right ambient object is the Cayley–Klein plane

All three constant-curvature geometries are **Cayley–Klein geometries**: the
projective plane `ℝP²` equipped with an *absolute conic* `Q` (the "absolute"),
with metric defined by cross-ratio against `Q`. Choosing `Q` selects the geometry:

- `Q : x²+y²+z² = 0` (empty over ℝ, the imaginary conic) → **elliptic/spherical**.
- `Q` = the line at infinity doubled (degenerate `z²=0`) → **Euclidean**.
- `Q : x²+y²−z² = 0` (the real Klein-disk boundary circle) → **hyperbolic**.

Encode all three by a single **curvature sign** `κ ∈ {+1, 0, −1}` (ell./eucl./hyp.)
and the symmetric bilinear form `diag(1,1,−κ)` (so the third-coordinate sign is
`−κ`: `κ=−1` gives Minkowski `diag(1,1,1)`-rotation, `κ=+1` gives the elliptic
`diag(1,1,−1)`; the relevant scalar output is `m = ⟨B,C⟩_κ`, see below).

The Cayley–Klein distance between unit points `B,C` is governed by the
curvature-`κ` trig function `cos_κ` via `m = ⟨B,C⟩_κ = cos_κ(d(B,C))`:

```
κ = +1 (spherical):  cos_κ = cos,   m = cos d ∈ (−1,1),   1 − m² > 0
κ =  0 (Euclidean):  limit,         m = 1,                1 − m² = 0
κ = −1 (hyperbolic): cos_κ = cosh,  m = cosh d > 1,       1 − m² < 0
```

### 2. A "Cevian point" is a *projective* point, weight-parametrised

In every Cayley–Klein model a cevian point `D` on geodesic `BC` is the
**projective** point `D ∝ α·B + β·C` (homogeneous coordinates in the `{B,C}`
basis). This is *geometry-independent* — pure projective incidence. The metric
only enters when we measure `d(B,D)`, `d(D,C)`.

Normalising `D` to the model surface uses the **single** norm
`n = √(α² + 2αβm + β²)`, valid for every `κ` (it is just `⟨αB+βC, αB+βC⟩_κ`
expanded, the cross term `2αβ⟨B,C⟩_κ = 2αβm`). This is *the same `n_sq`* the
parent already defines.

### 3. The universal side-ratio (the crux, one identity for all κ)

The curvature-`κ` "sine" satisfies `sin_κ²(d) = 1 − m²` up to the sign that `√|·|`
absorbs. The side ratio is

```
t_κ(BD)/t_κ(DC) = ( β·√|1 − m²| / n ) / ( α·√|1 − m²| / n ) = β/α        (★)
```

**The geometry-specific factor `√|1 − m²|/n` is common to numerator and
denominator and cancels — for every κ, including the Euclidean limit** where
`√|1−m²|→0` but the *ratio* survives (barycentric: `BD/DC = β/α`). This (★) is the
single fact the parent proves three times; the OQ asks to prove it **once**,
abstractly, with `g := √|1−m²|/n` a free nonzero common factor.

### 4. The single projective Ceva theorem

> **Projective Ceva (Cayley–Klein form).** Fix any κ and absolute form `⟨·,·⟩_κ`.
> For triangle `ABC` with cevian points `D∝α_D B+β_D C`, `E∝α_E C+β_E A`,
> `F∝α_F A+β_F B`, the cevians `AD, BE, CF` are concurrent **iff**
> `α_D α_E α_F = β_D β_E β_F`. The metric side-ratio `t_κ` along each side equals
> the weight ratio `β/α` by (★), independent of κ.

The concurrency half is a **projective incidence statement** — the affine Ceva
theorem read in homogeneous `{B,C}/{C,A}/{A,B}` coordinates, where the cevian
weights *are* the barycentric coordinates of `D`. It is invariant under the
projective group preserving `Q` (= the isometry group of the geometry). Proving it
once projectively gives all three metric Ceva theorems as corollaries by plugging
in `κ = +1, 0, −1`. This is the precise sense in which "all three cases follow
from a single projective Ceva theorem via the Klein model".

### 5. Why the Klein (Beltrami–Klein) model specifically

In the Beltrami–Klein disk, hyperbolic geodesics are **Euclidean chords**, so a
hyperbolic cevian and its Euclidean shadow are the *same projective line*.
Concurrency of three chords is a projective property visible in the model picture
itself — the Klein model is exactly the one in which "hyperbolic Ceva = projective
Ceva of chords" is literal, with no transcendental detour. The spherical case is
the antipodal-quotient (elliptic) Cayley–Klein with the imaginary absolute; the
Euclidean case is the degenerate `κ→0` contraction. One model, three absolutes.

---

## Lean Formalisation Plan

Mathlib has **no** Cayley–Klein / projective-metric API (no `CayleyKlein`, no
projective absolute-conic metric). So this is a *definitional* build, not
API-wiring. Reuse the parent's algebra verbatim.

**Step A — generalise the config.** Replace `HyperbolicCevianConfig` (which
hard-codes `1 < m`) with a κ-carrying version whose single positivity hypothesis
is `n² > 0`:

```lean
structure CKCevianConfig where
  κ : ℝ                       -- curvature sentinel (+1 / 0 / −1)
  m : ℝ                       -- ⟨B,C⟩_κ
  α β : ℝ
  hα : 0 < α
  hβ : 0 < β
  hn : 0 < α^2 + 2*α*β*m + β^2 -- n² > 0  (replaces the per-geometry m-bound)
```

`n_sq`, `n_sq_pos` carry over (the parent's `n_sq_pos` only used `α,β>0, m>1`;
with the explicit `hn` field it is immediate — and `hn` is provable from each
geometry's `m`-bound, so no strength is lost).

**Step B — the one abstract ratio lemma.** Factor (★) as geometry-free algebra:

```lean
theorem ck_ratio_cancel (g α β : ℝ) (hg : g ≠ 0) (hα : α ≠ 0) :
    (β * g) / (α * g) = β / α := by field_simp
```

i.e. `hyp_sinh_ratio` with the `√(m²−1)/n` factor abstracted to `g`. This single
identity replaces the three per-geometry derivations.

**Step C — three instantiations (corollaries).** Define
`gSph m n = Real.sqrt (1 - m^2) / n`, `gHyp m n = Real.sqrt (m^2 - 1) / n`,
`gEuc = 1` and feed each to `ck_ratio_cancel`, recovering `sin`-ratio,
`sinh`-ratio, identity-ratio = `β/α`. The Euclidean case is the `m=1` barycentric
limit (`gEuc` constant), so (★) holds without a `√` at all.

**Step D — concurrency.** Reuse the parent's `universal_weight_balance`
*unchanged* (already κ-free) to close
`∏(β/α)=1 ⟺ α_Dα_Eα_F = β_Dβ_Eβ_F`. Top theorem
`projective_ceva_unification` bundles Steps B–D and exhibits the three classical
Ceva theorems as `example`s by instantiating `κ`.

**Estimated size**: ~100–160 LOC, mostly the structure + three `Real.sqrt`
factor definitions; the hard mathematical content (the cancellation, the
criterion) is already proved in the parent and reused. Tractability 8/10 is fair
*for the algebra*; the only genuine modelling decision is how literally to encode
the absolute conic (recommended: keep `κ` a sentinel `ℝ` and the bilinear form
implicit via `m`, rather than building full `ℝP²` projective geometry — the OQ is
about the *unification of the ratio/criterion*, which lives entirely in the
`(m, α, β, n)` algebra).

---

## Dead Ends

- **Building genuine `ℝP²` + absolute-conic projective geometry in Mathlib.**
  Unnecessary: the concurrency criterion and side-ratio are already fully captured
  by the scalar `(m, α, β)` data. Encoding the full projective plane would
  re-derive incidence (`Projectivization`) with no payoff for this OQ. Keep the
  unification at the algebraic/`m`-parameter layer.
- **Forcing one `m`-bound for all geometries.** Spherical needs `m∈(−1,1)`,
  hyperbolic `m>1`; there is no common interval. Resolution: drop the `m`-bound and
  carry `n² > 0` as the single hypothesis (Step A `hn`) — exactly the condition
  both bounds were there to guarantee, and what every downstream proof uses.
- **Treating Euclidean as a separate `√`-bearing case.** It is the `√|1−m²|→0`
  degeneration; writing `sin_0` as a nonzero `√` factor fails. Encode Euclidean
  with `gEuc = 1` (barycentric ratio `β/α`, no radical).

---

## Durable Verification (2026-06-14, build-free)

`verify_ck_unification.py` (this directory) independently re-derives and checks the
entire algebraic + metric core of the unification from first principles, so the
Docker-gated Lean transcription (Steps A–D above) is de-risked before any build.
Run `python3 verify_ck_unification.py` — **all checks pass**. It confirms:

1. **The two core identities** (sympy, exact → 0), matching the parent's
   `hyp_key_identity_BD/DC` (`CevasTheoremOQ02OQ01OQ02.lean:98,105`):
   `(α+βm)² − n² = β²(m²−1)` and `(αm+β)² − n² = α²(m²−1)`, with
   `n² = α²+2αβm+β²`. The script also verifies the **sign-flipped spherical
   reading** `n² − (α+βm)² = β²(1−m²)` is the *same* identity — this is the precise
   sense in which **one** identity covers all three geometries.
2. **The abstract cancellation (★)** `(βg)/(αg) = β/α` (sympy) — the lemma
   `ck_ratio_cancel` of Step B.
3. **Spherical (κ=+1)** side-ratio from genuine S² geometry (unit vectors, `arccos`
   geodesic distances): `sin(d(B,D))/sin(d(D,C)) = β/α`, and the closed forms
   `sin(d(B,D)) = β√(1−m²)/n`, `sin(d(D,C)) = α√(1−m²)/n`.
4. **Hyperbolic (κ=−1)** side-ratio from the genuine hyperboloid model (Minkowski
   form `⟨·,·⟩ = x₁y₁+x₂y₂−x₃y₃`, points with `⟨x,x⟩=−1`, `m = −⟨B,C⟩ = cosh d`):
   `sinh(d(B,D))/sinh(d(D,C)) = β/α` and `sinh(d(B,D)) = β√(m²−1)/n`. The script
   independently checks `⟨D′,D′⟩ = −n²` (so `D = D′/n` is a valid model point).
5. **Euclidean limit (κ=0, m=1)**: `n = α+β` (perfect square), barycentric ratio
   `β/α` with `gEuc = 1` — no radical.
6. **The concurrency criterion** `universal_weight_balance`
   (`CevasTheoremOQ02OQ01OQ02.lean:254`): for a concrete triangle, three cevians
   `AD, BE, CF` are geometrically concurrent (line-intersection test) **iff**
   `α_D α_E α_F = β_D β_E β_F` **iff** `∏(β/α) = 1`, across both concurrent and
   non-concurrent cases.

**Net effect for the Lean build:** every mathematical obligation in the
"Lean Formalisation Plan" is now numerically/symbolically confirmed. The remaining
work is pure transcription of already-validated identities (`ring`/`field_simp`),
plus the `Real.sqrt` factor definitions — the only Docker-gated risk is Lean
plumbing, not mathematics.
