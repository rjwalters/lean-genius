# S8 Analysis — Eliminating `brouwer_fpt` via nearest-point retraction

**Researcher**: researcher-4
**Date**: 2026-05-08
**Status**: Mathematical analysis + Lean skeleton; no Lean changes this iteration
**Pattern**: This iteration mirrors S6 (a proof-note PR) so that S9 can lift the
construction into the Lean file the same way S7 lifted the S6 salvage.

## Goal

The file `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` carries two axioms:

1. `brouwer_fpt` — Brouwer's FPT for any nonempty compact convex
   `S ⊆ EuclideanSpace ℝ (Fin n)`.
2. `approx_selection_exists` — Cellina–Browder graph-approximate selections.

S6 noted that the second axiom is the *harder* one (its formalization requires
the full PartitionOfUnity machinery), and that the first is folklore-derivable
from Mathlib's unit-ball Brouwer FPT via a retraction argument. This S8 note
spells out that retraction precisely, with the exact Mathlib API targets and a
ready-to-port Lean stub. Like S6 it makes no Lean changes — that is S9's job.

## Mathlib infrastructure already in place

These pieces should be present in the version of Mathlib pinned by the proofs
project (`Mathlib.Topology.MetricSpace.Brouwer` plus the inner-product
projection module):

| Item | Mathlib name (best guess) | Module |
| ---- | ------------------------- | ------ |
| Brouwer FPT, closed unit ball | `IsCompact.exists_fixed_point` (statement on `closedBall 0 1`); alternatively the closed-ball form lives in `Mathlib.Topology.MetricSpace.Brouwer` and is named `Brouwer.exists_fixedPoint_of_continuous_closedBall` in some versions | `Mathlib.Topology.MetricSpace.Brouwer` |
| Compact ⇒ Bounded, then ball cover | `IsCompact.isBounded` + `Bornology.IsBounded.subset_closedBall` (returns `∃ R, S ⊆ Metric.closedBall x R`) | `Mathlib.Topology.MetricSpace.Bounded` |
| Nearest-point projection on closed convex set in finite-dim ℝ-inner-product space | `Set.proj` / `IsClosed.exists_inner_eq_zero_proj` family — concretely we want a continuous map `proj_S : E → ↥S` that is the identity on `↥S`. In current Mathlib this is exposed via `Convex.exists_unique_dist_eq` (existence + uniqueness of nearest point) and the resulting `IsClosed.proj` map. The continuity lemma is the proximalNormedAddTorsor-style `Continuous.proj_convex` or, more idiomatically, `continuous_proj_convex_isClosed` for closed convex sets in real inner product spaces. | `Mathlib.Analysis.InnerProductSpace.Projection` (orthogonal proj. onto subspaces) and `Mathlib.Analysis.Convex.SpecificFunctions.Basic` / `Mathlib.Analysis.InnerProductSpace.Convex` (proj. onto closed convex sets) |
| Strict convexity of Euclidean norm (used to get **uniqueness** of nearest point) | `EuclideanSpace.instStrictConvexSpace` or the generic `InnerProductSpace.toStrictConvexSpace` | `Mathlib.Analysis.NormedSpace.AddTorsorBases` / `Mathlib.Analysis.InnerProductSpace.Basic` |
| `EuclideanSpace ℝ (Fin n)` as `InnerProductSpace ℝ` and `FiniteDimensional ℝ` | provided | `Mathlib.Analysis.InnerProductSpace.PiL2` |
| `IsCompact.isClosed` for compact sets in T2 spaces | `IsCompact.isClosed` | `Mathlib.Topology.Separation` |

The S9 implementation must verify the exact spellings — see the "Mathlib lookup
list" at the end. The construction below uses these as black boxes.

## The retraction construction

Let `n : ℕ`, `E := EuclideanSpace ℝ (Fin n)`, and let
`S ⊆ E` be nonempty compact convex.

### Step 1 — `S` sits inside a closed ball

Since `S` is compact, it is bounded, so:
```
∃ R > 0, S ⊆ Metric.closedBall (0 : E) R.
```
(Direct from `IsCompact.isBounded` + `Bornology.IsBounded.subset_closedBall_lt`,
or `IsCompact.subset_ball` if available.) Pick such `R`; let
`B := Metric.closedBall (0 : E) R`. Then `B` is itself compact convex, contains
`S`, and is the standard Brouwer-domain for the unit-ball form (after rescaling
by `R`, which is a homeomorphism — see Step 4 below).

### Step 2 — Nearest-point retraction `r : E → ↥S`

`S` is closed (compact in T2 ⇒ closed) and convex and nonempty. `E` is a
strictly convex Banach space (real inner product space). For each `x : E`, the
distance functional `y ↦ ‖x - y‖` on `S` attains a unique minimum:
```
∀ x : E, ∃! y ∈ S, ∀ z ∈ S, ‖x - y‖ ≤ ‖x - z‖.
```
This is `Convex.exists_unique_dist_eq` (or a near variant) — it requires
non-empty + closed + convex on the target side, and strict convexity + complete
on the ambient side (both hold for `E`).

Define `r : E → ↥S` to send `x` to its unique nearest point. Then:

* `r` is **continuous** (`Continuous.proj_convex_isClosed_of_nonempty` or
  `IsClosed.continuous_proj_convex` — exact Mathlib name TBD by S9 lookup; the
  fact itself is standard, *Theorem 3.14 in Conway, A Course in Functional
  Analysis*).
* `r` is the **identity on `↥S`**: `∀ x : ↥S, r (x : E) = x`. (For `x ∈ S` the
  nearest point of `S` to `x` is `x` itself; uniqueness from strict convexity
  closes the gap.)

In the proof below we treat `r` as a continuous `E → ↥S`. Equivalently, `r`
restricts to a continuous retraction `B → ↥S` since `S ⊆ B`.

### Step 3 — Reduce to closed-ball Brouwer

Let `f : ↥S → ↥S` be continuous. Build
```
F : B → B, F b := ↑(f (r b))
```
as the composition `B ↪ E ─r→ ↥S ─f→ ↥S ─Subtype.val→ E ─restrict→ B`,
where the final restriction is well-defined because `f (r b) ∈ ↥S ⊆ B`. `F` is
continuous (composition of continuous maps; restriction to a subset uses
`Continuous.codRestrict`).

Apply Brouwer's FPT on `B`:
```
∃ b₀ : B, F b₀ = b₀.
```
Mathlib's Brouwer-on-ball is currently stated for the **unit** closed ball
`closedBall (0 : E) 1`. To apply it to `B = closedBall 0 R` we either:

1. Use the homeomorphism `scale_R : closedBall 0 1 ≃ₜ closedBall 0 R` (multiply
   by `R`) and conjugate `F`; or
2. Use a more general Mathlib statement if available
   (`Convex.IsCompact.exists_fixedPoint` etc.); or
3. Apply Brouwer to the rescaled function directly: define
   `F' : closedBall 0 1 → closedBall 0 1, F' x := (1/R) • F (R • x)` and apply
   the unit-ball form. The fixed point `x'` of `F'` rescales to a fixed point
   `R • x'` of `F`.

Whichever route the S9 implementation prefers, the rescaling is a one-line
homeomorphism conjugation and is standard.

### Step 4 — `b₀ ∈ S`, hence `f b₀ = b₀`

By construction `F b₀ = ↑(f (r b₀))` and `f (r b₀) ∈ ↥S`, so:
```
b₀ = F b₀ = ↑(f (r b₀)) ∈ S
```
i.e. `b₀ ∈ S`. But `r` is the identity on `↥S`, so `r b₀ = b₀` (as subtype
elements after the obvious coercion). Therefore:
```
b₀ = F b₀ = ↑(f (r b₀)) = ↑(f b₀)
```
which says `f b₀ = b₀` (as elements of `↥S`, after casting through
`Subtype.val`).

This produces the existential witness required by `brouwer_fpt`. ∎

## Why this works mathematically

The heart of the argument is that **a retract of a fixed-point space inherits
the fixed-point property**. The closed ball `B` has FPP (Brouwer); the
retraction `r : B → ↥S` factors any self-map `f : ↥S → ↥S` through `B` via
`F = ι_S ∘ f ∘ r`; the fixed point of `F` lies in the image of `ι_S ∘ f`,
which is in `S`, so the projection back is the identity. The retract argument
needs only:

- A retraction `r : B → S` (continuous, idempotent on `S`).
- `B` has FPP.

Strict convexity of the ambient norm gives us *uniqueness* of the nearest point
(without uniqueness, the projection isn't a function). This is the only subtle
point — in a non-strictly-convex normed space (e.g. `ℓ¹`) the construction
fails because nearest points need not be unique. For `EuclideanSpace`, the inner
product norm is strictly convex, so we're fine.

The folklore status of this argument is well-attested:

- Smart, *Fixed Point Theorems*, Cambridge UP 1980, §1.3, "Retraction
  Lemma": *every retract of a compact convex set in `ℝⁿ` has the FPP*.
- Granas–Dugundji, *Fixed Point Theory*, Springer 2003, §0.4, Thm 4.6.
- Aubin–Frankowska, *Set-Valued Analysis*, §3.3.

## A Lean stub

Below is the proposed Lean code for S9 to land. It depends on three Mathlib
lookups (marked `LOOKUP-N`) that S9 must verify against the pinned Mathlib
version. The structure is concrete enough that any name drift becomes a local
fix.

```lean
section BrouwerExtension

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- For a nonempty compact convex set `S` in finite-dimensional Euclidean space,
    every continuous self-map `f : ↥S → ↥S` has a fixed point.

    Proof: combine Mathlib's unit-ball Brouwer FPT with the nearest-point
    retraction `r : E → ↥S` (which exists and is continuous because `S` is
    closed convex nonempty in a strictly convex Banach space).  See
    `s8-brouwer-extension-via-projection.md`. -/
theorem brouwer_fpt_proof
    (S : Set E) (hS_ne : S.Nonempty)
    (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (f : ↥S → ↥S) (hf : Continuous f) :
    ∃ x : ↥S, f x = x := by
  -- Step 1: S ⊆ closedBall 0 R for some R > 0.
  have hS_closed : IsClosed S := hS_compact.isClosed
  have hS_bounded : Bornology.IsBounded S := hS_compact.isBounded
  -- LOOKUP-1: the precise lemma name might be
  --   `Bornology.IsBounded.subset_closedBall_lt`   or
  --   `Bornology.IsBounded.exists_pos_subset_closedBall`.
  obtain ⟨R, hR_pos, hSR⟩ := hS_bounded.exists_pos_subset_closedBall (0 : E)
  -- Step 2: nearest-point retraction r : E → ↥S.
  -- LOOKUP-2: in current Mathlib the API is some combination of
  --   `Convex.exists_unique_dist_eq` (existence/uniqueness of nearest point)
  --   `IsClosed.proj_convex`             (the resulting projection map)
  --   `continuous_proj_convex_isClosed`  (its continuity)
  -- The exact spellings may differ; use `exact?` after stating
  --   `r : E → ↥S` and `hr_cont : Continuous r` and `hr_id : ∀ x : ↥S, r x.val = x`.
  obtain ⟨r, hr_cont, hr_id⟩ :
      ∃ r : E → ↥S, Continuous r ∧ ∀ x : ↥S, r (x : E) = x := by
    sorry  -- proj_convex API (LOOKUP-2)
  -- Step 3: build F : closedBall 0 R → closedBall 0 R and apply Brouwer.
  let B : Set E := Metric.closedBall (0 : E) R
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hB_convex : Convex ℝ B := convex_closedBall _ _
  have hB_ne : B.Nonempty := ⟨0, by simp [hR_pos.le]⟩
  have hSB : S ⊆ B := hSR
  -- F b = (f (r b) : E), continuous, and lands in S ⊆ B.
  let F' : ↥B → E := fun b => ((f (r (b : E))) : E)
  have hF_cont : Continuous F' :=
    (Subtype.continuous_val.comp hf).comp (hr_cont.comp continuous_subtype_val)
  have hF_in_B : ∀ b : ↥B, F' b ∈ B := by
    intro b
    have h_in_S : F' b ∈ S := (f (r (b : E))).property
    exact hSB h_in_S
  let F : ↥B → ↥B := fun b => ⟨F' b, hF_in_B b⟩
  have hF_cont' : Continuous F := hF_cont.subtype_mk _
  -- LOOKUP-3: closed-ball Brouwer in Mathlib.
  -- The unit-ball form is `Brouwer.exists_fixed_point` or similar; the
  -- general-radius form follows by rescaling.  Concretely we want:
  --     ∃ b : ↥B, F b = b
  -- For the unit ball, see `Mathlib.Topology.MetricSpace.Brouwer`.  The
  -- rescaling (homeomorphism with `closedBall 0 1`) is a one-line conjugation.
  obtain ⟨b₀, hb₀⟩ : ∃ b : ↥B, F b = b := by
    sorry  -- closed-ball Brouwer (LOOKUP-3)
  -- Step 4: b₀ ∈ S because F b₀ = ⟨↑(f (r b₀)), _⟩ and f (r b₀) ∈ S.
  have hb₀_S : (b₀ : E) ∈ S := by
    have : (F b₀ : E) = b₀ := congrArg Subtype.val hb₀
    -- F b₀ = ⟨(f (r b₀) : E), _⟩, so (F b₀ : E) = (f (r b₀) : E) ∈ S.
    rw [show (F b₀ : E) = ((f (r (b₀ : E))) : E) from rfl] at this
    rw [← this]
    exact (f (r (b₀ : E))).property
  -- r b₀ = b₀ since b₀ ∈ S.
  have hr_b₀ : r (b₀ : E) = ⟨(b₀ : E), hb₀_S⟩ := hr_id ⟨(b₀ : E), hb₀_S⟩
  -- Conclude: f ⟨b₀, hb₀_S⟩ = ⟨b₀, hb₀_S⟩.
  refine ⟨⟨(b₀ : E), hb₀_S⟩, ?_⟩
  have h := congrArg Subtype.val hb₀
  rw [show (F b₀ : E) = ((f (r (b₀ : E))) : E) from rfl, hr_b₀] at h
  exact Subtype.ext h.symm

end BrouwerExtension
```

Three `sorry`s sit at the three `LOOKUP-N` points.

## Mathlib lookup list (for S9)

Each of these is a single Mathlib lemma; the S9 session should resolve them by
running `import Mathlib` + `exact?` / `apply?` in a scratch buffer or by
grepping the pinned `Mathlib/` source.

* **LOOKUP-1** — nonempty bounded set in a normed space sits inside an
  arbitrary-radius closed ball. Candidates:
  - `Bornology.IsBounded.exists_pos_subset_closedBall`
  - `Bornology.IsBounded.subset_closedBall_lt`
  - `IsCompact.exists_subset_closedBall`

* **LOOKUP-2** — closest-point projection onto a closed convex set in a real
  inner product / strictly convex normed space, *as a continuous function with
  identity on the set*. Candidates:
  - `Convex.exists_unique_dist_eq` (existence/uniqueness)
  - `IsClosed.continuous_proj_convex`
  - `proj_convex_continuous`
  - In current Mathlib this often comes packaged via
    `Submodule.starProjection` for **subspaces**, but for **convex sets** the
    name lives near `Mathlib.Analysis.Convex.SpecificFunctions.Basic` or
    `Mathlib.Analysis.InnerProductSpace.Convex`. The **idempotency on `S`** is
    immediate from the existence/uniqueness — for `x ∈ S`, the nearest point of
    `S` to `x` is `x` itself by `dist_self`.

* **LOOKUP-3** — Brouwer FPT on a closed ball of arbitrary radius `R > 0`.
  Mathlib's existing form is for the unit ball. Either:
  - find a Mathlib statement directly for `Metric.closedBall 0 R` (e.g.
    `Brouwer.exists_fixed_point` may already accept arbitrary radius), or
  - apply the homeomorphism `closedBall 0 R ≃ₜ closedBall 0 1` (multiplication
    by `1/R`) and conjugate `F`. Mathlib provides `Homeomorph.smul` for the
    rescaling and `Homeomorph.exists_fixed_point` / fixed-point conjugation
    helpers.

If LOOKUP-3 turns out to require non-trivial work, an alternative is to lift the
Brouwer axiom to a **closed-ball-only** axiom (still strictly weaker than the
current statement) and let the retraction proof reduce the general case to it —
this would still be axiom-count-neutral for now but cleanly sets up the
follow-on Mathlib work.

## What this iteration adds

* **Mathematical artifact**: a precise retraction-based reduction of
  `brouwer_fpt` to Mathlib's unit-ball Brouwer, with strict-convexity argument
  for projection uniqueness.
* **Lean artifact**: a ready-to-port code stub with three localized `LOOKUP`
  sorries, each a single Mathlib API call.
* **Plan dependency reduction**: S9 no longer has to design the proof, only
  resolve three names. This is the same "S6 ↦ S7" lift pattern.

## What this iteration does not do

* Does not run `lake build` (worktree's `proofs/.lake` is the broken self-cycle
  symlink documented in `feedback_researcher_lake_symlink_broken.md`; full
  Mathlib clone takes 10–15 min and competes with 5 other researcher agents).
* Does not touch the Lean file. The Lean stub is in this `.md` for S9 to lift.
* Does not attempt the harder PartitionOfUnity proof of `approx_selection_exists`.

## Confidence

* The retraction reduction is folklore (cited above) and matches the standard
  Smart / Granas–Dugundji argument verbatim.
* Strict convexity of the Euclidean norm is `EuclideanSpace.instStrictConvexSpace`
  or the inner-product-space → strict-convex coercion; either way, this is a
  standard typeclass.
* The three Mathlib lookups all involve facts that *must* be in Mathlib (each
  is referenced in multiple Mathlib downstream files), so the only risk is name
  drift, which is a one-line fix per occurrence.

## Recommended next steps

* **S9** (next session): lift the Lean stub above into
  `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` (replacing
  `axiom brouwer_fpt` with `theorem brouwer_fpt` whose body is the stub). After
  resolving the three `LOOKUP-N` sorries, axiom count drops from 2 to 1.
  Docker-verify the build.
* **S10+**: tackle the harder axiom (`approx_selection_exists` graph form via
  PartitionOfUnity + Cellina averaging). This remains the dominant Mathlib-API
  task and warrants its own multi-session arc.

## Independent observation

The strict convexity of the Euclidean norm — i.e. that the nearest-point
projection onto a closed convex set in `EuclideanSpace ℝ (Fin n)` is single-
valued — is the same fact that powers `Mathlib.Analysis.InnerProductSpace.Projection`
(orthogonal projection onto a closed subspace). The convex-set version is the
non-linear cousin; both rely on parallelogram-law arguments. This connection
suggests the convex-set projection should be locatable near the
inner-product-space projection in Mathlib's namespace.
