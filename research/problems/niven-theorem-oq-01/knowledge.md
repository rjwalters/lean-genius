# Niven's Theorem — Research Knowledge

## Problem

**Niven's theorem (Ivan Niven, 1956).** If `θ` is a rational multiple of `π`
(i.e. `θ = (m/n)·π` with `m, n ∈ ℤ`, `n ≠ 0`) and `cos θ` is rational, then
`cos θ ∈ {0, ±1/2, ±1}`.

Equivalently: the only rational values taken by the cosine at rational multiples
of `π` are `0, ±1/2, ±1` (the "nice" angles are multiples of `90°` and `60°`).

No prior gallery entry. Mathlib has the supporting ingredients (Chebyshev
polynomials, roots of unity, integrally-closed `ℤ`) but **not** the assembled
theorem.

## Proof Architecture (two parts)

1. **Algebraic-integer core** — `two_cos_int_of_rational`
   `θ = (m/n)·π ∧ cos θ ∈ ℚ ⇒ 2·cos θ ∈ ℤ`.
   - `θ = (m/n)·π ⇒ n·θ = m·π ⇒ cos(n θ) = (-1)^m ∈ ℤ`.
   - Monic integer Chebyshev (Vieta–Lucas) polynomial `Cₙ` with
     `Cₙ(2 cos θ) = 2 cos(n θ)`. So `2 cos θ` is a root of the **monic integer**
     polynomial `Cₙ(X) − 2cos(nθ)` ⇒ `2 cos θ` is an algebraic integer.
   - A rational algebraic integer is a rational integer (`ℤ` integrally closed
     in `ℚ`) ⇒ `2 cos θ ∈ ℤ`.

2. **Enumeration tail** — `niven` (PROVED, no sorry)
   `|cos θ| ≤ 1 ⇒ 2 cos θ ∈ [-2,2] ∩ ℤ = {-2,-1,0,1,2}`
   `⇒ cos θ ∈ {-1, -1/2, 0, 1/2, 1}`.
   Uses `Real.cos_le_one`, `Real.neg_one_le_cos`, `interval_cases`, `linarith`.

## Current State

- **File**: `proofs/Proofs/NivenTheorem.lean`
- **Status**: `formalized` (1 sorry on the core lemma).
- Tail (`niven`) fully proved from Mathlib trig bounds; the core lemma's
  statement is precise and isolated.
- Build: scaffold submitted to Docker (verifies tail + statement typecheck).
- **Aristotle**: DOWN this session (`prove` → 404 "Resource not found"), so the
  core could not be delegated.

## Mathlib lemma candidates for the core (next session)

Route A — **roots of unity (recommended, strongest Mathlib support):**
- `ζ := Complex.exp (θ·I)`; `2nθ = 2mπ ⇒ ζ^(2n) = 1` so `ζ` is a root of the
  monic `X^(2n) − 1 ∈ ℤ[X]` ⇒ `IsIntegral ℤ ζ`.
- `ζ⁻¹ = conj ζ = ζ^(2n−1)` is also integral; `IsIntegral.add ⇒ IsIntegral ℤ (ζ+ζ⁻¹)`.
- `ζ + ζ⁻¹ = 2·Complex.cos θ = ((2·cos θ : ℝ) : ℂ)` via `Complex.exp_mul_I`,
  `Complex.cos`, `Complex.ofReal_cos`.
- `2 cos θ = (2r : ℚ)` is rational; reflect integrality along injective
  `algebraMap ℚ ℂ` (`isIntegral_algHom_iff` / `IsIntegral.of_injective`), then
  `IsIntegrallyClosed.isIntegral_iff` (with `ℤ`, fraction field `ℚ`) gives
  `∃ k:ℤ, (k:ℚ) = 2r`, i.e. `2 cos θ ∈ ℤ`.

Route B — **Chebyshev (matches pool note):**
- `Polynomial.Chebyshev.T ℝ n` with `T_real_cos` / `cos_nat_mul`:
  `(T ℝ n).eval (cos θ) = cos (n θ)`.
- Needs the monic normalization `Cₙ(x) = 2·Tₙ(x/2)` (leading coeff of `Tₙ` is
  `2^(n−1)`; `Cₙ` is monic over `ℤ`) — this normalization is the main piece
  Mathlib may not provide directly and would need building (~50–100 lines).

`cos(mπ) = (-1)^m`: look for `Real.cos_int_mul_pi` / `Real.cos_nat_mul_pi`
(or derive from `Real.cos_pi`, `Real.cos_add_int_mul_two_pi`, parity cases).

## Next Steps

1. On Aristotle recovery: submit `two_cos_int_of_rational` (isolated, KNOWN
   mathematics) to `aristotle prove_file` — an ideal target.
2. Else formalize Route A manually (~150–250 lines); the four risky Mathlib
   names to confirm first are `Complex.exp_mul_I`, `isIntegral_algHom_iff`,
   `IsIntegrallyClosed.isIntegral_iff`, and a roots-of-unity `IsIntegral` lemma.
3. After a 0-sorry build: register in `proofs/Proofs.lean`, flip status to
   `verified`, add gallery entry `src/data/proofs/niven-theorem-oq-01/`.

## Sessions

### 2026-06-16 (Session 1, FRESH) — researcher-11
- **Outcome**: progress (scaffold + verified tail; core isolated).
- Selected from the `available` pool (all 16 were EMPTY-tier). Rejected
  `lucas-theorem-oq-01` (Mathlib already has `Mathlib.Data.Nat.Choose.Lucas` — a
  from-scratch proof would be a trivial wrapper) and `cube-root-2-irrational-oq-04`
  (the Delian impossibility is already proved as
  `AngleTrisection.cube_doubling_impossible`).
- Niven chosen: famous, Mathlib lacks the assembled theorem, clean route.
- Wrote `proofs/Proofs/NivenTheorem.lean`: statements of `niven` +
  `two_cos_int_of_rational`; proved the enumeration tail; isolated the
  algebraic-integer core as one sorry.
- Docker probe (`alpine echo`) passed, but the actual `docker-build.sh Proofs.NivenTheorem`
  was **SIGTERM-killed during Mathlib cache decompression** under host saturation
  (8+ concurrent `lean4-arm64` containers, likely OOM). No `NivenTheorem.olean` produced
  → scaffold + tail are **build-pending / UNVERIFIED** this session.
- Aristotle DOWN (404 on a trivial probe) so the core could not be delegated.
- Also drafted `proofs/Proofs/NivenTheoremCore.lean` — a full Route-A (roots-of-unity)
  proof attempt of `two_cos_int_of_rational`, also UNVERIFIED (orphan file, not in the
  build graph). Concrete next-session starting point.
- Documented both proof routes with Mathlib lemma candidates.

**Next-session priority order:**
1. When Docker is unsaturated (`docker ps` shows few containers): build `Proofs.NivenTheorem`
   to verify the tail; then build/iterate `NivenTheoremCore.lean`; on success, fold the core
   into `NivenTheorem.lean`, register in `Proofs.lean`, flip to `verified`.
2. When Aristotle recovers (not 404): submit `two_cos_int_of_rational` to `prove_file`.

### 2026-06-16 (Session 2) — researcher-1: Route-A core name-verification + 1 bug flag

Dual blackout again (Aristotle MCP loads but backend 404; Docker down). No build
possible. Source-verified ALL 7 "fragile" Mathlib names in the existing
`NivenTheoremCore.lean` Route-A draft against the v4.26.0 mirror at pin
`2df2f0150c` — **all present with matching signatures**:
- `Complex.exp_int_mul_two_pi_mul_I (n:ℤ) : exp (n*(2*π*I)) = 1`
  (Trigonometric/Basic.lean:1233) ✓
- `Complex.exp_mul_I : exp (x*I) = cos x + sin x*I` (Complex/Trigonometric.lean:506) ✓
- `Complex.ofReal_cos (x:ℝ) : (Real.cos x:ℂ) = cos x` (Complex/Trigonometric.lean:397) ✓
- `monic_X_pow_sub_C (a:R) {n} (h:n≠0)` (Polynomial/Monic.lean:440) ✓
- `isIntegral_algHom_iff (f:A→ₐ[R]B) (hf:Injective f) {x} : IsIntegral R (f x) ↔ IsIntegral R x`
  (IntegralClosure/IsIntegral/Basic.lean:57) ✓
- `IsScalarTower.toAlgHom (R S A) : S →ₐ[R] A`, `toAlgHom_apply : toAlgHom R S A y = algebraMap S A y`
  (Algebra/Tower.lean:137,140) ✓ — takes 3 explicit args, matches `toAlgHom ℤ ℚ ℂ`.
- `IsIntegrallyClosed.isIntegral_iff [IsIntegrallyClosed R] {x:K} : IsIntegral R x ↔ ∃ y:R, algebraMap R K y = x`
  (IntegralClosure/IntegrallyClosed.lean:210) ✓
Also confirmed: `Complex.exp_nat_mul`, `Complex.exp_neg`, `inv_eq_of_mul_eq_one_left`
(Group/Defs.lean:1127, `(h:a*b=1) : b⁻¹=a`), `Int.one_le_abs (h:z≠0) : 1≤|z|`.

⚠ **ONE RESIDUAL BUG to fix on first build** (last block of the draft):
`obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint_q` gives
`hk : algebraMap ℤ ℚ k = 2*r`, but the next line `have : ((k:ℚ):ℝ) = ((2*r:ℚ):ℝ) := by rw [hk]`
rewrites a term `(k:ℚ)` that is only DEFEQ (not syntactically equal) to
`algebraMap ℤ ℚ k`, so `rw [hk]` will fail (no syntactic occurrence). Fix: first
normalize `hk` with `rw [eq_intCast (algebraMap ℤ ℚ)] at hk` (or
`have hk' : (k:ℚ) = 2*r := by exact_mod_cast hk`) to expose `(k:ℚ) = 2*r`, then
proceed. Pure rewriting fix, no math change. Everything else in the draft is
name-verified. Recommended first action when a backend returns: apply this fix,
build `Proofs.NivenTheoremCore`; if green, inline into `NivenTheorem.lean`'s
`two_cos_int_of_rational` (replacing its 1 sorry), register, flip to `verified`.

### 2026-06-16 (Session 3) — researcher-5: STATE CORRECTION (Route-A core is OBSOLETE) + bearer audit

**Mode:** CONTINUE → state reconciliation + build-free bearer audit. **Dual blackout
reconfirmed live** (Docker `docker info` times out; Aristotle MCP `prove` returns
`"Resource not found"` on a trivial `n+0=n` ping). Used the offline mathlib4 checkout at the
exact pin (`2df2f0150c` / v4.26.0).

**⚠ The Session-2 "next steps" are STALE and would waste a cycle.** Session 1/2 left the plan
as: "build `NivenTheoremCore.lean` (Route-A roots-of-unity), fix the one cast bug, then inline
it into `NivenTheorem.lean`'s `two_cos_int_of_rational` sorry." **That sorry no longer exists.**
PR **#25163** (`Research: niven-theorem-oq-01 — discharge core via Mathlib`, merged) discharged
the core directly by citing Mathlib and **removed `NivenTheoremCore.lean` entirely**. The current
`proofs/Proofs/NivenTheorem.lean` on `main` is **0 sorry / 0 axiom / 0 decide**. Do NOT resurrect
the Route-A core — it is obsolete.

**Current true state of `NivenTheorem.lean` (on main, #25163):**
- `two_cos_int_of_rational` — discharged: `rw [hq]; exact Real.isIntegral_two_mul_cos_rat_mul_pi (m/n)`
  to get `IsIntegral ℤ (2 cos θ)`, then `hint.exists_int_iff_exists_rat.mp ⟨2*r, …⟩`. No sorry.
- `niven` — enumeration tail: `interval_cases k` over `2 cos θ ∈ {-2..2}` (bounds from
  `Real.cos_le_one`/`Real.neg_one_le_cos`), 5 `linarith` cases. No sorry.
- **UNREGISTERED** (absent from `Proofs.lean`) and **NO gallery dir**
  (`src/data/proofs/niven-theorem-oq-01/` does not exist) and **NEVER build-verified** (Session 1's
  only build attempt was SIGTERM-killed during Mathlib cache decompression under host saturation).

**Bearer audit (all 3 cited Mathlib lemmas confirmed present @ pin `2df2f01` / v4.26.0):**
- `Real.isIntegral_two_mul_cos_rat_mul_pi (q : ℚ) : IsIntegral ℤ (2 * cos (q*π))` —
  `Mathlib/NumberTheory/Niven.lean:98`, aliased to root namespace at `:103`. ✓
- `IsIntegral.exists_int_iff_exists_rat (h₁ : IsIntegral ℤ x) : (∃ q:ℚ, x=q) ↔ ∃ k:ℤ, x=k` —
  `Niven.lean:32` (dot-notation usage confirmed at `:130`). ✓
- `Real.cos_le_one`, `Real.neg_one_le_cos` — standard, present. ✓
- Tactic glue is routine (`push_cast`, `ring`, `interval_cases`, `linarith`, `exact_mod_cast`) on a
  simple goal — LOW compile risk, but NOT verified (no build).

**Mathlib-coverage honesty (matters for the gallery badge).** Mathlib v4.26.0 ALREADY contains a
top-level `niven (hθ) (hcos) : cos θ ∈ ({-1, -1/2, 0, 1/2, 1} : Set ℝ)` (`Niven.lean:124`, Meiburg–
Broshi 2025), plus `niven_sin` (:141) and `niven_angle_eq` (:149). So this gallery entry is a
**presentation** (keeps the explicit `interval_cases` enumeration for pedagogy, delegates the deep
algebraic-integer step to Mathlib), NOT original formalization. When galleried: `badge` should
reflect "presentation / not a Mathlib gap" (e.g. status `verified`, badge `verified` — NOT
`original`), and the description should state Mathlib already has the theorem.

**Remaining path (single Docker build, no math left):** when a Docker slot is free —
`./proofs/scripts/docker-build.sh Proofs.NivenTheorem`; if green (expected), register in
`Proofs.lean` (alphabetical) and add `src/data/proofs/niven-theorem-oq-01/` (meta.json +
annotations, model on a sibling, node-validate). NOT done under blackout: registering or galleryizing
an unbuilt file is a false-green risk (the file has never compiled in any build graph). No Lean
changed this session; only this knowledge correction + audit.
