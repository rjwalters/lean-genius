# S4 — Docker verify + mark COMPLETED

**Slug:** `szemeredi-theorem-oq-01` (Kelley–Meka bounds for 3-AP-free sets)
**Researcher:** researcher-2
**Date:** 2026-06-12
**Phase:** verify → COMPLETED (no Lean diff)
**Predecessor:** S3 ACT (researcher-1, 2026-06-03, PR shipping the Kelley–Meka axiom + corollary).

## §0 Why this session

S3 ACT shipped the slug as "graduation-ready" and its `nextAction`
asked for a post-merge Docker verification before marking COMPLETED.
This session runs that verification and closes the slug. No new math.

## §1 Docker verification

```
./proofs/scripts/docker-build.sh Proofs.SzemerediTheoremOQ01
→ Build completed successfully (3102 jobs).
```

No errors, no `sorry` warnings.

**File state (`Proofs/SzemerediTheoremOQ01.lean`, 88 LOC):**
- 1 axiom — `kelley_meka_bound`: `∃ c > 0, ∃ N₀, ∀ N ≥ N₀,
  rothNumberNat N ≤ N · exp(−c (log N)^(1/12))`. Faithful statement of
  the Kelley–Meka 2023 quantitative 3-AP-free bound (FOCS 2023 / Annals
  2024), legitimately beyond Mathlib v4.26.0.
- 1 theorem — `rothNumberNat_density_le_kelley_meka`: the density form
  `r_3(N)/N ≤ exp(−c (log N)^(1/12))`, proved from the axiom (real
  proof: `div_le_iff₀` + the bound). Not a placeholder.
- 0 sorries.

## §2 Action

- `status` → `completed`; `phase` → COMPLETED with the verification
  stamp.
- The axiom is irreducible (the Kelley–Meka proof is far beyond current
  Mathlib); per the Axiom Integrity Policy the slug is `axiomatized`
  with `axiomCount = 1`.

## §3 Downstream (not this slug)

Sibling slug `szemeredi-theorem-oq-01-incomplete-01` remains for the
BLOCKED Salem–Spencer quantitative lower-bound direction — Curator/Seeker
territory.
