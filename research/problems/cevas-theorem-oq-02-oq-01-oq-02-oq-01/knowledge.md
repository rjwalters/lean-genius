# Knowledge Base: cevas-theorem-oq-02-oq-01-oq-02-oq-01

**OQ**: Formalize the projective unification — prove all three cases (spherical,
Euclidean, hyperbolic) from a *single* projective Ceva theorem via the Klein model.

Parent: `cevas-theorem-oq-02-oq-01-oq-02` (Hyperbolic Ceva via Weight Parameters,
`proofs/Proofs/CevasTheoremOQ02OQ01OQ02.lean`).

Phase: ORIENT → **ACT** (S2, 2026-06-15, researcher-7). The ORIENT plan below
is now implemented in `proofs/Proofs/CevasTheoremOQ02OQ01OQ02OQ01.lean`
(build-pending/UNREGISTERED — Docker `docker info` still hangs this session).

---

## Result (Session 2, 2026-06-15, researcher-7 — ACT, first Lean)

Implemented the ORIENT Lean plan (Steps A–D below) as a self-contained file,
`CevasTheoremOQ02OQ01OQ02OQ01.lean` (0 axioms, 0 sorries):

- `CKCevianConfig` — the κ-carrying config (Step A); single positivity field
  `hn : 0 < α² + 2αβm + β²` replaces the per-geometry m-bound. `n_sq`, `n_sq_pos`
  carry over.
- `ck_ratio_cancel (g α β) (hg : g≠0) (hα : α≠0) : (β*g)/(α*g) = β/α` — the
  crux (★), proved in ONE line by `mul_div_mul_right β α hg` (no `field_simp`,
  division-safe; name confirmed in pinned Mathlib `GroupWithZero/Units/Basic`).
- `ck_side_ratio` — (★) at config level.
- `ck_weight_balance` — the universal concurrency criterion (same field_simp+
  linarith shape the parent's `universal_weight_balance` uses, so build-safe).
- `projective_ceva_unification` — **the single projective Ceva theorem**: three
  configs of arbitrary κ + arbitrary nonzero factors gD,gE,gF; side-ratio
  product = 1 ⟺ αD·αE·αF = βD·βE·βF. Proof = `rw [ck_side_ratio ×3]; exact
  ck_weight_balance`.
- `gSph/gHyp/gEuc` + `gSph_ne/gHyp_ne/gEuc_ne` — the three geometric factors and
  their nonvanishing (via `div_ne_zero`, `Real.sqrt_pos`; both name-confirmed).
- `spherical_ceva_unified / euclidean_ceva_unified / hyperbolic_ceva_unified` —
  the three classical theorems, each = `projective_ceva_unification` with the
  matching factor plugged in. This realizes "all three from one theorem".

All Mathlib identifiers grep-confirmed present in the pinned tree (sibling
`stokes-dd` `.lake/packages/mathlib`): `mul_div_mul_right`, `div_ne_zero`,
`Real.sqrt_pos`. Next live Docker session: register in `Proofs.lean` + build.

---

## Result (Session 4, 2026-06-15, researcher-6 — registration)

The S2/S3 file `CevasTheoremOQ02OQ01OQ02OQ01.lean` is merged to `main` (PRs
#24377, #24430) but was **never machine-checked**: it is absent from
`proofs/Proofs.lean`, so the deployer's `Proofs` build target skipped compiling
it. This session **registers** it (`import Proofs.CevasTheoremOQ02OQ01OQ02OQ01`
inserted alphabetically at `Proofs.lean:496`) so the deployer compiles it on the
next Docker-up cycle, turning "0-sorry by inspection" into machine-verified.

Re-confirmed the full identifier set against the pinned v4.26 sibling
(`/Users/rwalters/GitHub/mathlib4`, matches pin):
`mul_div_mul_right (a b : G₀) (hc : c ≠ 0)` (GroupWithZero/Units/Basic:312 — exact
shape of the crux usage `mul_div_mul_right β α hg`), `div_ne_zero (ha) (hb)`
(GroupWithZero/Units/Basic:237), `sq_nonneg`, `Real.sqrt_pos`. File is 14
theorems + 1 structure + 4 defs, 267 lines.

Blackout still LIVE this session: `docker info` exits 124 (daemon hang); build
remains deferred to the deployer. **Registration is deployer-gated** — a failing
compile blocks merge rather than breaking `main`, so registering blind under
blackout is safe here (no axiom/semantic edit, only an import line).

**Remaining (post-build):** create the gallery entry
`src/data/proofs/cevas-theorem-oq-02-oq-01-oq-02-oq-01/` (deferred until the
build confirms `verified`, to avoid an honesty-policy overclaim pre-compile).

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

---

## Session 3 (2026-06-15, researcher-4) — audit + close the "no strength lost" loop

**Mode**: REVISIT · **Outcome**: progress (audit + 3 lemmas). Docker down
(`docker info` timeout); file stays UNREGISTERED, 0 axioms / 0 sorries.

### Audited the S2 file against the v4.26.0 pin
Confirmed the load-bearing crux: `mul_div_mul_right (a b : G₀) (hc : c ≠ 0) :
a*c/(b*c) = a/b` (`Mathlib/Algebra/GroupWithZero/Units/Basic.lean:312`) — exact
match to `ck_ratio_cancel g α β hg = mul_div_mul_right β α hg`. `gSph`/`gHyp`
nonvanishing via `div_ne_zero` + `Real.sqrt_pos` are sound. `ck_weight_balance`
mirrors the parent's proven `field_simp`+`linarith` shape. High-confidence buildable.

### Closed the documented loose end (`hn` ⟸ each geometry's m-bound)
The S2 structure replaces the parent's per-geometry `m`-bound with the single field
`hn : 0 < α²+2αβm+β²`, claiming "no strength is lost" but never proving it. Added the
three discharging lemmas (build-safe `nlinarith`, identity
`α²+2αβm+β² = (α−β)² + 2αβ(m+1) = (α+β)² + 2αβ(m−1)`):
- `hn_of_cos_gt_neg_one` (spherical, `m > −1`),
- `hn_of_cosh_gt_one` (hyperbolic, `m > 1`),
- `hn_of_eq_one` (Euclidean, `m = 1`, norm `= (α+β)²`).
These let a `CKCevianConfig` be built from each geometry's ordinary distance data,
making the unification's "single hypothesis suffices" claim explicit and machine-checkable.

### Next steps (unchanged)
Build + register `CevasTheoremOQ02OQ01OQ02OQ01.lean` when Docker returns.

---

## Session 5 (2026-06-15, researcher-4) — metric realization (close the abstract-factor gap)

**Mode**: ACT (8 new theorems) · **Outcome**: progress. Docker down
(`docker info` exit 124); file already REGISTERED (`Proofs.lean:499`), so the
deployer compiles it on next Docker-up cycle. Still 0 axioms / 0 sorries.

### The gap closed
`projective_ceva_unification` cancels the geometric factor `g` **abstractly** — it
only needs `g ≠ 0`. The prior `gSph_ne`/`gHyp_ne` lemmas show the factors are
nonzero but never connect them to the **actual** metric. The genuine bridge
identities (`n² − (α+βm)² = β²(1−m²)`) lived only in the parent
(`CevasTheoremOQ02OQ01OQ02.lean:98,105`, hyperbolic-specific). This session adds
the **κ-uniform** realization inside the unification file:

- `ck_metric_BD` / `ck_metric_DC` — one ring identity each, covering all three
  geometries: `n² − (α+βm)² = β²(1−m²)` and `n² − (αm+β)² = α²(1−m²)`. (For
  `m²<1` RHS>0=spherical sin²; `m²>1` RHS<0, sign moves into √(m²−1)=hyperbolic;
  `m=1` vanishes=Euclidean.)
- `gSph_sqrt_BD/DC`, `gHyp_sqrt_BD/DC` — the genuine geodesic numerators in closed
  form: `√(n²−(α+βm)²) = β·√(1−m²)` (=`sin(d(B,D))·n`), hyperbolic analogue with
  `√(m²−1)` (=`sinh·n`). Proof: rw key identity, `Real.sqrt_mul (sq_nonneg β)`,
  `Real.sqrt_sq hβ.le`.
- `spherical_side_ratio_metric` / `hyperbolic_side_ratio_metric` — the **actual**
  metric side-ratio `sin_κ(BD)/sin_κ(DC) = β/α`, derived from the metric
  quantities `√(n²−·²)` (NOT the abstract cancellation): `rw [g._sqrt_BD,
  g._sqrt_DC]; exact mul_div_mul_right β α (sqrt_pos.mpr _).ne'`.

This realizes the unification concretely: the abstract cancellation of
`projective_ceva_unification` IS the true metric side-ratio, not a placeholder —
and the κ-uniform identity replaces the parent's two hyperbolic-only identities.

### Name-checks (pinned v4.26, stokes-dd `.lake/packages/mathlib`)
- `Real.sqrt_mul {x} (hx : 0 ≤ x) (y) : √(x*y)=√x*√y` (`Data/Real/Sqrt.lean:335`)
- `Real.sqrt_sq (h : 0 ≤ x) : √(x^2)=x` (`Data/Real/Sqrt.lean:166`)
- `Real.sqrt_pos : 0 < √x ↔ 0 < x` (`Data/Real/Sqrt.lean:268`)
- `mul_div_mul_right`, `sq_nonneg` — already used in this file.

### Cert
`verify_metric_realization.py` (this dir) re-derives all 8 lemmas: ring identities
(exact 0), radical closed forms, and both side-ratios from genuine S²/hyperboloid
arccos/arccosh distances. All pass.

### Next steps
Build + machine-check on next Docker-up (deployer-gated). Gallery entry handled by
open PR #24567. File now 22 theorems + 1 structure + 4 defs.

---

## Session 6 (2026-06-15, researcher-2) — **BUILD GREEN, MACHINE-VERIFIED**

**Mode**: VERIFY · **Outcome**: milestone. Docker came back **up** this session
(`docker info` OK), so the build all five prior sessions deferred finally ran:

```
LEAN_MEMORY_LIMIT=8192 ./proofs/scripts/docker-build.sh Proofs.CevasTheoremOQ02OQ01OQ02OQ01
⚠ [7743/7743] Built Proofs.CevasTheoremOQ02OQ01OQ02OQ01 (278s)
Build completed successfully (7743 jobs).
```

The file is now **kernel-verified**: 0 axioms, 0 sorries, machine-checked against
the pinned Mathlib. The "0-sorry by inspection / build-pending" caveat every prior
session carried is **discharged**. Sole compiler output was a benign linter
warning — `CevasTheoremOQ02OQ01OQ02OQ01.lean:95:50: unused variable 'hα'` in
`ck_ratio_cancel` (`hα : α ≠ 0` is genuinely unused; `mul_div_mul_right β α hg`
only needs `g ≠ 0`). Not an error; left as-is to keep the verified artifact exactly
as machine-checked. Optional cosmetic follow-up: drop `hα` + update the one call
site (`ck_side_ratio`).

### Gallery entry promoted to verified
`src/data/proofs/cevas-theorem-oq-02-oq-01-oq-02-oq-01/meta.json` (based on the
honest `wip` draft from PR #24567) flipped to **status `verified` / badge
`original`**, assumptions = "None. Fully machine-verified …", stale counts
corrected (lineCount 267→351, theoremCount 14→22 — the S5 metric-realization
lemmas were never reflected), and an originalContributions bullet added for the
`ck_metric_*` / `*_side_ratio_metric` block. **Supersedes PR #24567**, which
correctly deferred the verified flip pending exactly this green build.

### Re-confirmed build-free certs still pass
`verify_ck_unification.py` and `verify_metric_realization.py` both exit 0.

### Slug status: SATURATED + VERIFIED
Nothing further to prove. The OQ is fully realized and machine-checked. Remaining
housekeeping is only merge/dedup of the gallery PRs (#24567 superseded; #23172
DRAFT and #24106 enricher-prefix closable/mergeable by the deployer).

---

## Session 2026-06-18 (researcher-2) — Registry-JSON integrity sync (metadata-only)

**Mode**: DEPTH-FIRST claim landed on an already-COMPLETE slug · **Outcome**: doc-integrity fix.

Claim-random handed me this slug (still in the "available" pool). The work is done: the
Lean file `Proofs/CevasTheoremOQ02OQ01OQ02OQ01.lean` (351 LOC, 0 sorry / 0 axiom, 22 thm)
is registered (`proofs/Proofs.lean:516`) and the gallery `meta.json` is already
`verified` / `original` / axiomCount 0 pointing at the correct file. `state.md` correctly
reads COMPLETED since S6.

**Defect found & fixed:** the *research registry* JSON
(`src/data/research/problems/cevas-theorem-oq-02-oq-01-oq-02-oq-01.json`) was stale —
`status: surveyed`, `phase: ORIENT`, and `leanFiles` pointed at the **parent** file
`CevasTheoremOQ02OQ01OQ02.lean` (a different slug) rather than this slug's verified
`CevasTheoremOQ02OQ01OQ02OQ01.lean`. This made a solved/verified OQ look unsurveyed and
mis-attributed its Lean source. Synced to reality: `status→completed`, `phase→COMPLETED`,
`leanFiles→[CevasTheoremOQ02OQ01OQ02OQ01.lean]`. The legitimate parent reference in
`knownResults.proven` ("Parent CevasTheoremOQ02OQ01OQ02.lean proves the hyperbolic
sinh-ratio…") was preserved. No Lean content changed; the verified meta already covers the
byte-identical file. **Slug remains DONE.**
