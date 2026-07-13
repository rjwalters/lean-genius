# Session 3: ACT — Ship Kelley–Meka axiomatization (Approach A)

**Date**: 2026-06-03
**Researcher**: researcher-1
**Phase transition**: DECISION-RECORDED → ACT-shipped

## Goal

Execute the next action recorded by Session 2 (2026-05-30): ship Approach A
by axiomatizing the Kelley–Meka 2023 bound and creating the gallery entry.

## What I built

### 1. `proofs/Proofs/SzemerediTheoremOQ01.lean` (89 lines, 1 axiom, 1 theorem, 0 sorries)

```lean
axiom kelley_meka_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (rothNumberNat N : ℝ) ≤
        (N : ℝ) * Real.exp (-(c * Real.log (N : ℝ) ^ ((1 : ℝ) / 12)))
```

Plus the non-axiomatic density-form corollary:

```lean
theorem rothNumberNat_density_le_kelley_meka :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (rothNumberNat N : ℝ) / N ≤
        Real.exp (-(c * Real.log (N : ℝ) ^ ((1 : ℝ) / 12)))
```

**Proof of the corollary**: `obtain` constants from the axiom, take
threshold `max N₀ 1`, derive `1 ≤ N` via `le_max_right`, `(0 : ℝ) < N`
via `Nat.lt_of_succ_le hN1 |> exact_mod_cast` (idiom borrowed from
`SzemerediFullOQ02.lean`), rewrite goal `div_le_iff₀ hN_pos ; mul_comm`,
close by the axiom.

### 2. Gallery entry `src/data/proofs/szemeredi-theorem-oq-01/`

- `meta.json`: status `axiomatized`, badge `axiom`, axiomCount 1, sorries 0,
  lineCount 89, theoremCount 1, definitionCount 0. Three section
  descriptors (preamble, kelley-meka-axiom, density-corollary), four
  cross-references (`szemeredi-theorem`, `szemeredi-full-oq-02`,
  `szemeredi-regularity`, `szemeredi-counting`), four references
  (Kelley–Meka 2023, Behrend 1946, Bloom–Sisask 2020, Roth 1953).
- `annotations.json`: three concept annotations (docstring, axiom,
  density corollary).

### 3. Module registration

Added `import Proofs.SzemerediTheoremOQ01` to `proofs/Proofs.lean`
immediately after `Proofs.SzemerediTheorem`.

## Verification

**Local Docker daemon is in I/O-error state** (`docker images` returns
`input/output error` on `containerd` metadata DB). The
`./proofs/scripts/docker-build.sh` invocation could not run the build.

**Mitigations**:
- The Lean file follows the same idioms as `SzemerediFullOQ02.lean`
  (which builds in CI): `obtain ⟨c, hc, N₀, h⟩`, `Nat.lt_of_succ_le`
  bridge, `div_le_iff₀ ; mul_comm` finish.
- The axiom statement only uses standard Mathlib pieces:
  `rothNumberNat` (from `Mathlib.Combinatorics.Additive.Corner.Roth`),
  `Real.log`, `Real.exp`, `Real.rpow` via `HPow ℝ ℝ ℝ`.
- The post-merge Mechanic / Auditor will run the Docker build and
  verify `axiomCount: 1`, `sorries: 0`, `theoremCount: 1`.

If the build fails, Doctor / Mechanic should be able to fix it without
disturbing the gallery entry: only the Lean file would need adjustment.

## Why this is the right deliverable

Per Session 2's audit, Mathlib's `cornersTheoremBound` is tower-type
(per Mathlib's own docstring) and cannot derive the Kelley–Meka rate.
Approach B (Salem–Spencer quantitative `O(N / log log N)`) is BLOCKED
on upstream Bohr-set / sifted-Fourier / `U^3` infrastructure and is
recommended as a sibling slug `szemeredi-theorem-oq-01-incomplete-01`.
Approach C (Croot–Sisask single lemma) is multi-week research-scale.

Approach A is the only Sn-time deliverable that:
- adds new content to the gallery (the quasi-polynomial-rate statement
  is not derivable from existing Mathlib),
- respects axiom-integrity policy (1 axiom, status `axiomatized`,
  badge `axiom`),
- composes directly with the rest of the Szemerédi line (stated
  against `rothNumberNat`),
- is non-vacuous (density-form corollary is non-axiomatic).

## Open questions generated

1. **Exponent improvement**: Kelley–Meka uses `1/12`; subsequent work
   pushed it up. A follow-up slug could record the current best.
2. **Behrend gap**: `(log N)^{1/12}` (KM) vs `sqrt(log N)` (Behrend) —
   recording the matching lower bound as a sibling slug would frame
   the gap concretely.
3. **Discharging the axiom**: Bohr sets (~500–1000 LOC), sifted
   Fourier on `Z/NZ` with explicit constants (~1000–2000 LOC), `U^3`
   inverse theorem (~1000+ LOC) — coordination with Mathlib.

## Next action (downstream)

- Mechanic / Auditor: Docker-build `Proofs.SzemerediTheoremOQ01` and
  verify metadata (`axiomCount: 1`, `sorries: 0`).
- Curator / Seeker: extract sibling slug
  `szemeredi-theorem-oq-01-incomplete-01` for the BLOCKED Approach B.
- Once Mechanic/Auditor pass, mark slug COMPLETED in tracking JSON.

## Files modified

- `proofs/Proofs/SzemerediTheoremOQ01.lean` (new)
- `proofs/Proofs.lean` (+1 import)
- `src/data/proofs/szemeredi-theorem-oq-01/meta.json` (new)
- `src/data/proofs/szemeredi-theorem-oq-01/annotations.json` (new)
- `src/data/research/problems/szemeredi-theorem-oq-01.json` (currentState
  + knowledge refresh, leanFiles auto-populated by linter)
- `research/problems/szemeredi-theorem-oq-01/state.md` (Phase ACT-shipped)
- `research/problems/szemeredi-theorem-oq-01/knowledge.md` (Session 3 entry)
- `research/problems/szemeredi-theorem-oq-01/sessions/2026-06-03-s3-act-ship-kelley-meka-axiom.md` (this file)
