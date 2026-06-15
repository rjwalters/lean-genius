# Research State: nth-root-irrational-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15T00:57:04-07:00
**Iteration**: 6

## Current Focus
The four Niven/cyclotomic files (S1–S4) are merged AND registered (S5, present in
`proofs/Proofs.lean:2651–2656` on origin/main). The remaining genuinely-open
direction is the EXACT degree `[ℚ(ζ+ζ⁻¹):ℚ] = φ(n)/2` (the Real file only proved
the degree-≤2 *bound* that yields the irrational direction, not the exact value).
S6 (this session) symbolically certifies that exact-degree claim and pins the
Lean tower plan for the Docker-up session.

## Active Approach
Verify-before-assert (build-free; Docker down, `docker info` times out). Added
`verify_real_subfield_degree.py` (all asserts pass, n = 1..30). It certifies:
- (A) quadratic relation `ζ² − (ζ+ζ⁻¹)ζ + 1 = 0` (identity, ζ≠0) ⇒ `[ℚ(ζ):ℚ(α)] ≤ 2`.
- (B) tower `φ(n) = 2·deg(minpoly_ℚ α_n)` for n≥3 (ζ non-real ⇒ `[ℚ(ζ):ℚ(α)] = 2` exactly).
- (C) exact degree `deg(minpoly_ℚ(2cos(2π/n))) = φ(n)/2` for n≥3; = 1 (rational) ⇔ n∈{1,2,3,4,6}.
- (D) the five Niven rational values `α_n ∈ {2,−2,−1,0,1}`.

## Attempt Count
- Total attempts: 6
- Current approach attempts: 1
- Approaches tried: 3 (Zolotarev-irr direct, registration, exact-degree certification)

## Blockers
- Docker + Aristotle blackout: cannot locally build/Aristotle-check this session.
- The exact-degree Lean proof needs IntermediateField adjoin + finrank
  multiplicativity (`Module.finrank_mul_finrank`) and the real-subfield minpoly;
  the latter is absent from Mathlib (must be built ~150 LOC). Docker-gated.

## Next Action
On a Docker-up session, prove `[ℚ⟮ζ+ζ⁻¹⟯ : ℚ] = φ(n)/2` (n≥3) via the tower:
1. `[ℚ⟮ζ⟯ : ℚ] = φ(n)` — `IsCyclotomicExtension.finrank` / `cyclotomic_eq_minpoly_rat`.
2. `[ℚ⟮ζ⟯ : ℚ⟮ζ+ζ⁻¹⟯] = 2` — upper bound from relation (A) (ζ root of
   `X² − (ζ+ζ⁻¹)X + 1 ∈ K[X]`, `minpoly.dvd` + `natDegree_le_of_dvd`); lower
   bound `≥ 2` because `ζ ∉ ℝ ⊇ ℚ⟮ζ+ζ⁻¹⟯` for n≥3 (`Complex.ofReal`/non-real).
3. `Module.finrank_mul_finrank` (tower) ⇒ `φ(n) = 2 · [K:ℚ]` ⇒ `[K:ℚ] = φ(n)/2`.
All facts (A)/(B)/(C) numerically certified in `verify_real_subfield_degree.py`.
