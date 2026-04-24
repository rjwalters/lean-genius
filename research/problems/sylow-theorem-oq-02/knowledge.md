# Knowledge Base: sylow-theorem-oq-02

**Problem**: Sylow Theorem: Complexity of Finding All Sylow p-Subgroups
**Last Updated**: 2026-04-24
**Knowledge Items**: 11

---

## Problem Understanding

The tractable Lean target: formalize the orbit-based enumeration of all Sylow p-subgroups
of a finite group G. The orbit {g·P | g ∈ G} under conjugation covers all Sylow subgroups,
and its cardinality equals [G : N_G(P)] by the orbit-stabilizer theorem.

The complexity question itself (is SylowEnum in P?) is metamathematical and can't be
formalized in Lean. Instead we formalize the orbit enumeration procedure.

---

## Session 2026-04-24 (Session 2)

**Mode**: FRESH (re-opened for gallery entry creation)
**Outcome**: completed — gallery entry created, pool updated to completed

### What I Did

- Discovered pool showed "available" despite problem JSON saying "completed" (sync issue)
- Found PR #12038 was already MERGED — the orbit file was in main
- No gallery entry existed at `src/data/proofs/sylow-theorem-oq-02/` despite merged PR
- Created full gallery entry: meta.json, annotations.json, index.ts
- Updated candidate pool status to "completed"

### Files Modified

- `src/data/proofs/sylow-theorem-oq-02/meta.json` (created)
- `src/data/proofs/sylow-theorem-oq-02/annotations.json` (created, 5 annotations)
- `src/data/proofs/sylow-theorem-oq-02/index.ts` (created)

### Key Findings

- Pool/problem JSON sync issue: pool had "available" but JSON had "completed"
- Root cause: PR #12038 was merged but gallery entry was never created
- SylowTheoremOQ02.lean (5 axioms, profinite theory) is a separate entry (sylow-theorems-oq-02)
- SylowTheoremOQ02Orbit.lean (0 axioms) is the correct proof for this gallery entry

---

## Session 2026-04-23 (Session 1)

**Mode**: FRESH
**Outcome**: completed — 0 sorries, 0 axioms

### What I Did

- Audited Mathlib `GroupTheory.Sylow` (lines 330–430) for exact API signatures
- Confirmed key APIs: `orbit_eq_top`, `stabilizer_eq_normalizer`, `card_eq_index_normalizer`,
  `equivQuotientNormalizer`, `card_dvd_index`
- Confirmed supporting lemmas: `Subgroup.index_eq_one`, `Subgroup.normalizer_eq_top_iff`,
  `Subgroup.card_mul_index`
- Created `proofs/Proofs/SylowTheoremOQ02Orbit.lean` with 9 theorems, 0 sorries, 0 axioms
- Created PR #12038

### Key Findings

- `Sylow.orbit_eq_top P : orbit G P = ⊤` — orbit covers all Sylow p-subgroups
- `Sylow.stabilizer_eq_normalizer P : stabilizer G P = P.normalizer`
- `Sylow.card_eq_index_normalizer P : Nat.card (Sylow p G) = P.normalizer.index`
- `Sylow.equivQuotientNormalizer P : Sylow p G ≃ G ⧸ P.normalizer`
- Chain: `Sylow p G ≃ orbit G P ≃ G / stab G P = G / N_G(P)` gives count directly
- `sylow_unique_iff_normal`: `n_p = 1 ↔ P ◁ G` via `index_eq_one` + `normalizer_eq_top_iff`

### Files Modified

- `proofs/Proofs/SylowTheoremOQ02Orbit.lean` (created, 204 lines)

### Next Steps

The orbit enumeration is complete. Possible follow-up:
- Nilpotent group corollary: G nilpotent ↔ every Sylow p-subgroup is normal
- This would require `Mathlib.GroupTheory.Nilpotent` APIs

---

## Insights

1. The orbit-stabilizer theorem directly gives n_p = [G : N_G(P)] — no new infrastructure needed
2. `Subgroup.normalizer_eq_top_iff : H.normalizer = ⊤ ↔ H.Normal` bridges normality and index
3. `Subgroup.card_mul_index` gives |H| × [G:H] = |G|, enabling orbit-stabilizer formula
4. `Sylow.orbit_eq_top` + `orbitEquivQuotientStabilizer` → `equivQuotientNormalizer` is the full chain
5. The Sylow conjugacy (all Sylow p-subgroups conjugate) is precisely the orbit = ⊤ statement

---

## Dead Ends

None — all APIs existed and the proof was direct composition.
