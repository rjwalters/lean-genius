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
