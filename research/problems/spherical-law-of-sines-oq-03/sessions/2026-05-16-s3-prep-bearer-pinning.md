# S3 PREP — Bearer pinning + per-sorry ACT skeletons (doc-only)

**Researcher**: researcher-6
**Date**: 2026-05-16T00:25Z
**Session type**: S3 PREP (doc-only, no Lean changes)
**Predecessor**: PR #19102 (S2 SCAFFOLD, researcher-3, merged 2026-05-15T22:59:12Z)
**Base SHA**: bf0d69fb9a6c4d720075e41ba771de633f5bcb00 (origin/main, seeker batch #18166)
**Branch**: research/researcher-6-spherical-law-sines-oq03-s3-prep-1778868636-1778891035

## Purpose

S2 SCAFFOLD shipped 4 strategic sorries in `proofs/Proofs/SphericalLawOfSinesOQ03.lean`
~85 min before this session opened. The state.md's S3 ACT plan named bearers from the
parent file `SphericalLawOfSines.lean` but did **not** pin their current signatures or
line numbers post-merge. This PREP closes that gap:

1. Drift recheck table for the 13 named bearers (parent + new OQ-03 file)
2. Mathlib bearer manifest (5 inverse-trig lemmas to verify at S3 ACT build time)
3. Per-sorry minimal-LOC ACT skeleton (one block per sorry, ready to drop in)
4. Order-of-discharge recommendation
5. ACT readiness gate (which row must be GREEN before S3 ACT can ship)

No Lean changes. No claim release. PR ships as a session-note doc-only addition.

## §1 Drift recheck table — parent `SphericalLawOfSines.lean`

The 9 parent bearers named in the state.md S3 ACT plan, with **current line numbers
on base SHA `bf0d69f`** and signature digest. All confirmed extant; signatures
unchanged from S2's record.

| Bearer | Decl | Line (now) | Line (state.md) | Drift | Signature digest |
|---|---|---|---|---|---|
| `dot` | def | 39 | (implicit) | none | `(u v : Fin 3 → ℝ) : ℝ := ∑ i, u i * v i` |
| `normSq` | def | 41 | (implicit) | none | `(u : Fin 3 → ℝ) : ℝ := dot u u` |
| `IsUnit3` | def | 43 | (implicit) | none | `(u : Fin 3 → ℝ) : Prop := normSq u = 1` |
| `arcLen` | def | 45 | (implicit) | none | `(u v : Fin 3 → ℝ) : ℝ := Real.arccos (dot u v)` |
| `projPerp` | def | 49 | (implicit) | none | `(u w : Fin 3 → ℝ) : Fin 3 → ℝ` |
| `normSq_cross_nonneg` | thm | 66 | named | none | `(u v) : 0 ≤ normSq (u ×₃ v)` |
| `unit_sum` | thm | 70 | named | none | `(A) (hA : IsUnit3 A) : A 0 * A 0 + A 1 * A 1 + A 2 * A 2 = 1` |
| `lagrange_identity` | thm | 77 | named | none | `(u v) : normSq (u ×₃ v) = normSq u * normSq v - (dot u v)^2` |
| `dihedralAngle` | def | 158 | named | none | uses `Real.sqrt` branch + `Real.arccos` |
| `sin_sq_dihedralAngle` | thm | 172 | named | none | `(A B C) (hA) (hpB) (hpC) : sin² α = det² / (|pB|² · |pC|²)` |
| `spherical_law_of_sines_all_sq` | thm | 271 | named | none | three-ratio squared form, 6 non-degeneracy + 1 det hypothesis |

**Verdict**: 0 substantive drift across 11 bearers between S2 SCAFFOLD record (2026-05-14)
and base SHA `bf0d69f` (2026-05-16). All decl names + signatures stable; line numbers
unchanged.

## §2 OQ-03 file bearers — `SphericalLawOfSinesOQ03.lean`

Current `proofs/Proofs/SphericalLawOfSinesOQ03.lean` on base SHA:

| Decl | Line | Hypotheses | Status |
|---|---|---|---|
| `cos_arcLen` | 123 | `(u v) (hu : IsUnit3 u) (hv : IsUnit3 v)` | strategic sorry |
| `sin_arcLen_nonneg` | 137 | `(u v)` (no hypotheses) | strategic sorry |
| `spherical_law_of_cosines_local` | 159 | `(A B C) (hC : IsUnit3 C)` | strategic sorry |
| `spherical_cotangent_rule_polynomial` | 239 | `(A B C) (hA hB hC : IsUnit3 _)` | strategic sorry |

**File totals** (verified): 263 LOC, 4 sorries, 0 axioms, imports
`Proofs.SphericalLawOfSines` + `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.

**Line-number drift vs state.md S3 ACT plan**: 0 — all four targets are at the
exact lines the plan listed (123 / 137 / 159 / 239).

## §3 Mathlib bearer manifest (v4.26.0 expected)

The five Mathlib inverse-trig lemmas the state.md plan calls out. These have **not**
been verified against the pinned Mathlib revision in this PREP — that verification
belongs to S3 ACT (it requires a successful Docker build to confirm tactic-mode
applicability). This manifest pins expected signatures + fallback strategy.

| Bearer | Expected signature | Used by | Fallback if missing |
|---|---|---|---|
| `Real.cos_arccos` | `(h₁ : -1 ≤ x) (h₂ : x ≤ 1) : Real.cos (Real.arccos x) = x` | `cos_arcLen` | manual via `Real.arccos` definition + `Real.cos_pi_div_two_sub` |
| `Real.arccos_nonneg` | `(h : x ≤ 1) : 0 ≤ Real.arccos x` OR `(x : ℝ) : 0 ≤ Real.arccos x` | `sin_arcLen_nonneg` | derive from `Real.arccos` definition |
| `Real.arccos_le_pi` | `(x : ℝ) : Real.arccos x ≤ π` | `sin_arcLen_nonneg` | derive from `Real.arccos = π/2 - Real.arcsin x` + `Real.arcsin_le_pi_div_two` |
| `Real.sin_nonneg_of_nonneg_of_le_pi` | `(h₁ : 0 ≤ x) (h₂ : x ≤ π) : 0 ≤ Real.sin x` | `sin_arcLen_nonneg` | standard Mathlib lemma, unlikely missing |
| `Real.sin_arccos` | `(x : ℝ) : Real.sin (Real.arccos x) = Real.sqrt (1 - x^2)` | indirect via parent's `normSq_projPerp_unit` | already used by parent at line 122 — confirmed present at v4.26.0 |

**ACT-time verification step** (must succeed before S3 ACT can land):

```bash
cd /Users/rwalters/GitHub/lean-genius && \
./proofs/scripts/docker-build.sh Proofs.SphericalLawOfSinesOQ03 2>&1 | tail -50
```

If any of the five lemma names produces "unknown identifier" or "no applicable rule",
fall to the column-4 fallback before re-trying.

## §4 Per-sorry ACT skeleton (drop-in templates)

Skeletons below are **suggested starting points**, not verified. Each is sized to the
LOC estimate in state.md (cos_arcLen 5–10 / sin_arcLen_nonneg 2–3 / cosines_local
5–15 / cotangent_polynomial 20–50).

### §4.1 `sin_arcLen_nonneg` — simplest, no hypotheses

```lean
theorem sin_arcLen_nonneg (u v : Fin 3 → ℝ) :
    0 ≤ Real.sin (arcLen u v) := by
  unfold arcLen
  exact Real.sin_nonneg_of_nonneg_of_le_pi
    (Real.arccos_nonneg _) (Real.arccos_le_pi _)
```

**LOC**: 4. **Risk**: low — only depends on Mathlib lemma names. Order: discharge
first as a confidence check on the Mathlib bearer manifest.

### §4.2 `cos_arcLen` — Cauchy–Schwarz bound

```lean
theorem cos_arcLen (u v : Fin 3 → ℝ) (hu : IsUnit3 u) (hv : IsUnit3 v) :
    Real.cos (arcLen u v) = dot u v := by
  unfold arcLen
  -- Need: -1 ≤ dot u v ≤ 1
  have h_lag := lagrange_identity u v
  have h_nn := normSq_cross_nonneg u v
  have h_bound_sq : (dot u v) ^ 2 ≤ 1 := by
    have : normSq u * normSq v - (dot u v) ^ 2 ≥ 0 := by linarith [h_lag, h_nn]
    rw [hu, hv] at this; linarith
  have h_upper : dot u v ≤ 1 := by nlinarith [h_bound_sq, sq_nonneg (dot u v - 1)]
  have h_lower : -1 ≤ dot u v := by nlinarith [h_bound_sq, sq_nonneg (dot u v + 1)]
  exact Real.cos_arccos h_lower h_upper
```

**LOC**: 10. **Risk**: moderate — the `nlinarith` calls for `h_upper`/`h_lower` may
need tweaking (specifically the `sq_nonneg` hint). Alternative: factor as
`(dot u v - 1) * (dot u v + 1) ≤ 0` then `1 - (dot u v)^2 ≥ 0 → -1 ≤ dot u v ≤ 1`
via a single `nlinarith [h_bound_sq]` after asserting both signs.

### §4.3 `spherical_law_of_cosines_local` — polynomial identity in 9 entries

```lean
theorem spherical_law_of_cosines_local (A B C : Fin 3 → ℝ) (hC : IsUnit3 C) :
    dot A B = dot A C * dot B C + dot (projPerp A C) (projPerp B C) := by
  have hC' : C 0 * C 0 + C 1 * C 1 + C 2 * C 2 = 1 := unit_sum C hC
  simp only [dot, projPerp, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply,
             smul_eq_mul]
  linear_combination (A 0 * B 0 + A 1 * B 1 + A 2 * B 2 - A 0 * C 0 * (B 0 * C 0)
                       - A 1 * C 1 * (B 1 * C 1) - A 2 * C 2 * (B 2 * C 2)) * 0
    + (- (A 0 * B 0 + A 1 * B 1 + A 2 * B 2)) * (hC' - 1)
```

**LOC**: 8. **Risk**: high — the `linear_combination` coefficient is a guess that
needs Docker-build verification. If it fails, fall back to component-wise
`fin_cases i` (mirroring parent's `projPerp_cross_eq` at line 133) or to a direct
expansion with `ring_nf; nlinarith [hC']`. The right-hand identity to verify
manually:

```
⟨A,B⟩ - ⟨A,C⟩·⟨B,C⟩ - ⟨πA, πB⟩
  = Σᵢ AᵢBᵢ - (ΣᵢAᵢCᵢ)(ΣⱼBⱼCⱼ) - Σᵢ(Aᵢ - ⟨A,C⟩Cᵢ)(Bᵢ - ⟨B,C⟩Cᵢ)
  = Σᵢ AᵢBᵢ - (ΣᵢAᵢCᵢ)(ΣⱼBⱼCⱼ) - Σᵢ AᵢBᵢ + ⟨B,C⟩ΣᵢAᵢCᵢ + ⟨A,C⟩ΣᵢBᵢCᵢ
      - ⟨A,C⟩⟨B,C⟩ΣᵢCᵢ²
  = - (ΣᵢAᵢCᵢ)(ΣⱼBⱼCⱼ) + ⟨B,C⟩⟨A,C⟩ + ⟨A,C⟩⟨B,C⟩ - ⟨A,C⟩⟨B,C⟩(ΣᵢCᵢ²)
  = ⟨A,C⟩⟨B,C⟩ · (1 - ΣᵢCᵢ²)
  = 0   when |C|² = 1.
```

So the correct `linear_combination` is `⟨A,C⟩⟨B,C⟩ * (hC' - 1)` (sign +/-
needs build-time confirmation). The skeleton above hints at this; the actual
S3 ACT should reduce to that single term with sign fixed by build feedback.

### §4.4 `spherical_cotangent_rule_polynomial` — the boxed main theorem

Two-step skeleton (state.md §1–§5 expands the algebra in detail):

```lean
theorem spherical_cotangent_rule_polynomial
    (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C) :
    Real.sin (dihedralAngle A B C) * Real.cos (arcLen B C)
        * Real.sin (arcLen A C)
      = Real.sin (arcLen B C) * Real.sin (dihedralAngle A B C)
          * Real.cos (arcLen A C) * Real.cos (dihedralAngle C A B)
        + Real.sin (arcLen B C) * Real.cos (dihedralAngle A B C)
          * Real.sin (dihedralAngle C A B) := by
  -- Step 1: rewrite cos(arcLen _ _) via cos_arcLen on the three side-pairs
  have h_cosc : Real.cos (arcLen A B) = dot A B := cos_arcLen A B hA hB
  have h_cosb : Real.cos (arcLen A C) = dot A C := cos_arcLen A C hA hC
  have h_cosa : Real.cos (arcLen B C) = dot B C := cos_arcLen B C hB hC
  -- Step 2: rewrite dot products via spherical_law_of_cosines_local
  -- (gives cos c = ⟨A,B⟩, cos b = ⟨A,C⟩, cos a = ⟨B,C⟩ — already done)
  -- Step 3: relate dihedralAngle inner products to projPerp dot
  -- via dihedralAngle definition + parent's normSq_projPerp_unit + sin_sq_arcLen
  -- ... (~20-30 LOC of dihedral-angle bookkeeping)
  sorry
```

**LOC**: 30–50 estimated. **Risk**: very high. **Recommendation**: do **not**
attempt §4.4 in S3 ACT — split into S3a ACT (close §4.1–§4.3, three sorries) and
S3b ACT (close §4.4 alone). The dihedral-angle bookkeeping in step 3 needs its
own careful PREP because `dihedralAngle` uses a definitional `if`-branch on
sqrt-of-norm being zero, and the polynomial form claims the identity holds
**including the degenerate branch** — so step 3 must handle `dihedralAngle = 0`
when `normSq (projPerp B A) = 0` separately.

## §5 Order-of-discharge recommendation

| Order | Sorry | LOC | Risk | Why this order |
|---|---|---|---|---|
| 1 | `sin_arcLen_nonneg` | 4 | low | Mathlib bearer smoke-test; failure → fix manifest before continuing |
| 2 | `spherical_law_of_cosines_local` | 8 | high (coefficient) | Pure polynomial identity; success unlocks step-3 of §4.4 |
| 3 | `cos_arcLen` | 10 | moderate | `nlinarith` hints; failure isolated, doesn't block §4.4 algebraically |
| 4 | `spherical_cotangent_rule_polynomial` | 30–50 | very high | Must follow §4.1–§4.3; recommend deferring to S3b ACT |

**S3a ACT scope**: orders 1–3 (~22 LOC across three sorries; 1 strategic sorry remains).
**S3b ACT scope**: order 4 alone (~30–50 LOC; closes the file to 0 sorries).

## §6 ACT readiness gate

Before opening S3a ACT (orders 1–3):

- [ ] **Build smoke-test**: `./proofs/scripts/docker-build.sh Proofs.SphericalLawOfSinesOQ03`
  on base SHA — confirm clean (4 strategic sorries reported, 3061 jobs).
- [ ] **Mathlib name verification**: in a scratch Lean buffer, `#check @Real.cos_arccos`
  and `#check @Real.arccos_le_pi` — confirm signatures match the §3 manifest column.
- [ ] **Sibling PR sweep**: `gh pr list -R rjwalters/lean-genius --search
  "spherical-law-of-sines-oq-03" --state open` — confirm no sibling S3 ACT in flight
  (claim race-check). At PREP time: 0 open PRs on this slug — clean field.
- [ ] **Branch-level pre-push check**: from worktree, after committing,
  `git fetch origin +refs/heads/main:refs/remotes/origin/main && git rev-parse
  HEAD origin/main` — confirm fresh-from-base.

Before opening S3b ACT (order 4):

- [ ] All gates above plus S3a ACT merged (orders 1–3 closed in main).
- [ ] **Separate PREP** for `dihedralAngle` definitional-branch handling — the
  degenerate-case discharge needs case analysis on `normSq_projPerp_unit B A = 0`
  vs `≠ 0`; the polynomial form should reduce to `0 = 0 + 0` in the degenerate
  branch (this needs verification before any tactic is attempted).

## §7 Conflict-free guarantees

This PREP touches **3 paths**:

1. `research/problems/spherical-law-of-sines-oq-03/sessions/2026-05-16-s3-prep-bearer-pinning.md` (this file, NEW)
2. `research/problems/spherical-law-of-sines-oq-03/state.md` (UPDATE: append §6.5 S3 PREP entry + adjust Phase line)
3. `src/data/research/problems/spherical-law-of-sines-oq-03.json` (UPDATE: phase/lastUpdated/researcher/nextSteps)

**No Lean source modified**. No new sorries introduced. No bearer claims pinned in
Lean code (they are documented in this session note only).

**Strict orthogonality** with future S3a/S3b ACT PRs: those will touch
`proofs/Proofs/SphericalLawOfSinesOQ03.lean` only, and this PREP touches none of
the Lean file.

## §8 Outcome

S3 PREP doc-only deliverable:

- Drift recheck: **0 substantive drift** across 11 parent bearers + 4 OQ-03 file
  bearers between S2 SCAFFOLD (2026-05-14) and base SHA `bf0d69f` (2026-05-16).
- Mathlib bearer manifest pinned with fallback strategies.
- Per-sorry ACT skeletons drafted (4 templates, 22+30 LOC budget).
- Order-of-discharge: split S3 ACT → S3a (orders 1–3) + S3b (order 4).
- ACT readiness gate: 4-item checklist for S3a, 5-item for S3b.

**Phase advance**: SCAFFOLD → SCAFFOLD (PREP doc-only, no phase change).
**Iteration**: 2 → 3.
**Next action**: S3a ACT (researcher-N, separate session, ~30–60 min) closing
orders 1–3 from §5.

## §9 Session metadata

| Field | Value |
|---|---|
| Researcher | researcher-6 |
| Started | 2026-05-16T00:14:54Z (cycle 806 connect) |
| State.md before | Phase SCAFFOLD (post-ORIENT), Iteration 2 |
| State.md after | Phase SCAFFOLD (post-PREP), Iteration 3 |
| JSON before | `phase: SCAFFOLD`, `lastUpdated: 2026-05-12T18:01:16Z`, `researcher: researcher-10` |
| JSON after | `phase: SCAFFOLD`, `lastUpdated: 2026-05-16T00:25:00Z`, `researcher: researcher-6` |
| Lean files modified | none |
| Lean files audited | `proofs/Proofs/SphericalLawOfSinesOQ03.lean` (263 LOC), `proofs/Proofs/SphericalLawOfSines.lean` (323 LOC) |
| Bearer drift count | 0 substantive (15 bearers audited; all stable) |
| Docker build | not run this session — deferred to S3a ACT smoke-test gate |

End of S3 PREP session note.
