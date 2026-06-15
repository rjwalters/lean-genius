# Research State: inverse-galois-a5-oq-02

## Current State
**Phase**: ACT (staged axiomatized entry SHIPPED + MERGED; 2 axioms remain)
**Path**: full
**Since**: 2026-06-15
**Iteration**: 4

## ⚠ State-sync note (researcher-5, 2026-06-15 S4)
This file's "Iteration 2 / ORIENT / Next Action = ACT stage 1" below was STALE —
the staged ACT it plans was already shipped and merged. Ground truth from
`origin/main`:
- **PR #24264 (MERGED)** — ORIENT certificate + simplicity-collapse pin.
- **PR #24330 (MERGED)** — ACT: proved the PSL(2,7) simplicity-collapse as general
  group theory (`simple168_subgroup_card_collapse`); staged the axiomatized Trinks
  entry `proofs/Proofs/InverseGaloisA5OQ02.lean` (then 3 axioms).
- **PR #24436 (MERGED)** — axiom reduction **3 → 2**: replaced the two order facts
  (`… ∣ 168`, `… ≠ 84`) with one embedding axiom `trinks_gal_embeds_simple168`;
  `|Gal| = 168` is now a *theorem* (`trinks_gal_card`).
- This S4 session: synced gallery `src/data/proofs/inverse-galois-a5-oq-02/meta.json`
  to the post-#24436 file (axiomCount 3 → **2**, lineCount 189 → **197**, rewrote
  the `assumptions` text to describe the actual two axioms). No Lean changes (dual
  blackout: Docker `docker info` hangs; Aristotle `prove` returns 404, both re-tested).

**Registered file `InverseGaloisA5OQ02.lean` (197 lines, 0 sorry, 2 axioms):**
- `trinks_gal_84_dvd` — 84 ∣ |Gal| (Dedekind cycle types, steps 1+3). DEEP.
- `trinks_gal_embeds_simple168` — Gal ↪ simple group of order 168 (irreducibility +
  square disc + deg-15 resolvent, steps 1+2+4). DEEP.
Both are the analysis-heavy multi-week ACT; neither Dedekind's theorem, 'square disc
⟹ ⊆ Aₙ', nor the deg-15 resolvent is in Mathlib 4.26.0. NOTE: this file is **not**
imported in `proofs/Proofs.lean` (not in the aggregate build).

## Current Focus
Certificate and pinning strategy for `Gal(x^7-7x+3 / ℚ) = PSL(2,7)` established and
machine-verified. Staged axiomatized entry SHIPPED (2 deep axioms).

## Active Approach
Trinks' polynomial `f = x⁷ − 7x + 3` via the 5-step certificate (see knowledge.md):
1. irreducible mod 2 ⟹ transitive ⟹ 7 ∣ |G|
2. disc = 3⁸·7⁸ = 194481² ⟹ G ⊆ A₇
3. Frobenius cycle types {(7),(1,2,4),(1,3,3),(1,1,1,2,2)} ⟹ 84 = 4·3·7 ∣ |G|
4. degree-15 PSL(2,7)-resolvent has rational root ⟹ G ≤ PSL(2,7)
5. PSL(2,7) simple ⟹ no index-2 subgroup ⟹ |G| = 168 ⟹ G = PSL(2,7)

## Attempt Count
- Total attempts: 1 (ORIENT)
- Approaches tried: 1 (Trinks + Dedekind/resolvent/simplicity)

## Blockers
None fundamental. The Lean ACT is large: steps 4 (deg-15 resolvent) and 5
(PSL(2,7) simplicity) are the heavy parts and are candidates for axiomatization in
a first staged `axiomatized` entry.

## Next Action
The 2 remaining axioms are both DEEP (Dedekind cycle-type ⟹ divisibility; deg-15
resolvent ⟹ embedding) and have no Mathlib 4.26.0 bearer — they are the genuine
multi-week ACT, not blackout-safe blind targets. Candidate partial reduction for a
Docker-up session: split `trinks_gal_84_dvd` into the provable `7 ∣ |Gal|`
(irreducible ⟹ transitive ⟹ deg ∣ |Gal|, via Galois-action orbit-stabilizer) plus
the still-deep `12 ∣ |Gal|` (Frobenius/Dedekind). Until then this entry is complete
as a staged `axiomatized` gallery item; do NOT re-run ORIENT/ACT-stage-1 (already
merged).

## Durable Artifacts
- `verify_trinks_psl27.py` — exact certificate, ALL CHECKS PASSED.
- `knowledge.md` — full ORIENT writeup + Mathlib bearer map.
