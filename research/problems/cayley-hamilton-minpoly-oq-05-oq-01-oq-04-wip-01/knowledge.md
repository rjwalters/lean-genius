# Knowledge: Complete Nonderogatory to Cyclic Vector (All Fields)

**Problem**: `cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-01`
**Status**: COMPLETED — WIP05 closes the cluster. WIP04 (general factored case) + WIP05 (UFD factorization wrapper) gives the fully general theorem axiom-free with no factored-form input.

## Session 2026-04-27 (Session 7, researcher-1) — Metadata Sync (No Lean Changes)

**Mode**: REVISIT
**Outcome**: metadata-only

### What I Did

- Audited the WIP04 and WIP05 gallery `meta.json` against the actual `.lean` files; both had stale `lineCount`. The WIP04 entry still described the binary prime-power case from session 4, even though session 5 had replaced the file with the general case.
- Rewrote `src/data/proofs/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-04/meta.json`: title now "General Case (All Fields)"; description, overview, sections, conclusion, crossReferences, and `leanFile.{lineCount, theoremCount}` updated to match the actual 359-line general-case file (1 main theorem + 7 private lemmas + 2 defs).
- Patched `src/data/proofs/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-05/meta.json` `lineCount` 167 → 190 in both `meta.lineCount` and `leanFile.lineCount`. Other fields (theoremCount, axiomCount, sorries, originalContributions) were already accurate.
- Removed the obsolete "close the original sorry in CayleyHamiltonMinpolyOQ05OQ01OQ04.lean" optional follow-up from this problem's JSON: that file already reports 0 sorries / 0 axioms (delegates to WIP04+WIP05 directly per its own status comment, lines 262–266).
- Replaced it with a metadata-discipline note: when proof files change, update both `meta.lineCount` and `leanFile.lineCount` together — both drifted on this cluster.

### Why This Counts as Progress

Per the researcher honesty rules, this session does not produce new mathematics. It restores the ability of future researchers (and the seeker) to read the cluster state correctly: a stale "binary prime power case" description on the file that actually proves the general case would mislead a reviewer into thinking the cluster is unfinished. No Lean files were modified, so no Docker build is needed.

### Files Modified

- `src/data/proofs/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-04/meta.json` (rewrite — general case)
- `src/data/proofs/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-05/meta.json` (lineCount 167 → 190 in two places)
- `src/data/research/problems/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-01.json` (currentState.iteration 3→4, focus, nextAction, nextSteps, lastUpdate)
- `research/problems/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-01/knowledge.md` (this entry)

### Next Steps

No required follow-ups. Optional: refactor WIP04 from `Fin k` to a generic `Fintype σ` so WIP05's reindexing wrapper can be removed (cosmetic refactoring, not new mathematics). The open question on generalizing to other PIDs remains open.

---

## Session 2026-04-27 (Session 6, researcher-10) - WIP05: UFD Wrapper Eliminates Factored-Form Hypothesis

**Mode**: REVISIT
**Outcome**: completed

### What I Did

- Created `CayleyHamiltonMinpolyOQ05OQ01OQ04WIP05.lean` (167 lines, 0 sorries, 0 axioms)
- Proved `nonderogatory_has_cyclic_vector_any_field` taking only `M : Matrix (Fin n) (Fin n) K` and `IsNonderogatory M` — no factorization input
- Added auxiliary `nonderogatory_general_has_cyclic_vector_fintype` reindexing WIP04 from `Fin k` to any `[Fintype σ] [Nonempty σ]`
- Used UFD factorization: `(normalizedFactors f).toFinset` enumerates distinct prime factors with multiplicities
- Build verified via Docker: `./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonMinpolyOQ05OQ01OQ04WIP05`
- Added `import Proofs.CayleyHamiltonMinpolyOQ05OQ01OQ04WIP03/04/05` to `proofs/Proofs.lean`
- Added gallery entry `src/data/proofs/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-05/`

### Key Findings

- **Distinct monic irreducibles in K[X] are auto-coprime**: `Irreducible.coprime_iff_not_dvd` over a PID + `Irreducible.associated_of_dvd` + `eq_of_monic_of_associated` rules out `p ∣ q` when `p ≠ q` and both are monic irreducible
- **`IsCoprime.pow` lifts** coprimality to any powers (m, n) — Mathlib name is `IsCoprime.pow`, NOT `IsCoprime.pow_pow`
- **Multiset → Finset prod identity**: `Finset.prod_multiset_count s : s.prod = ∏ m ∈ s.toFinset, m ^ s.count m`
- **Factorization for monic over field**: `f.Monic → normalize f = f` combines with `prod_normalizedFactors_eq` to give `f = (normalizedFactors f).prod` literally (not just up to associates)
- **`Polynomial.mem_normalizedFactors_iff`** (in `Polynomial` namespace, requires `[Field R]`): `p ∈ normalizedFactors q ↔ Irreducible p ∧ p.Monic ∧ p ∣ q`
- **n=0 trivial-case shortcut**: `exact ⟨Fin.elim0, fun r hr _ => by omega⟩` — `hr : r.natDegree < 0` is impossible, omega derives False, closes any goal
- **Reindexing Fintype to Fin**: `(Fintype.equivFin σ).symm : Fin (Fintype.card σ) ≃ σ` plus `Equiv.prod_comp` handles the rebinding

### Files Modified

- `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP05.lean` (new, 167 lines)
- `proofs/Proofs.lean` (added imports for WIP03, WIP04, WIP05)
- `src/data/proofs/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-05/` (new gallery entry: meta.json, annotations.json, index.ts)

### Next Steps

1. Optional: close the original `sorry` in `CayleyHamiltonMinpolyOQ05OQ01OQ04.lean` by translating WIP05's theorem to the LinearIndependent-style `IsCyclicVector` used there (vs annihilator-style in WIP04/05)
2. Optional: refactor WIP04 to take `[Fintype σ]` directly, removing the WIP05 reindexing wrapper
3. Open question: does this UFD-factorization technique generalize to nonderogatory endomorphisms of f.g. modules over arbitrary PIDs?

---

## Session 2026-04-26 (Session 5) - WIP04: General Case (All k factors) Proved

**Mode**: REVISIT
**Outcome**: completed

### What I Did

- Replaced binary prime-power WIP04 with the **general case**: minpoly = ∏_{i<k} p_i^{e_i} (k pairwise coprime prime powers, any k ≥ 1)
- Proved `nonderogatory_general_has_cyclic_vector` in `GeneralCyclicVector` namespace: 359 lines, 0 sorries, 0 axioms
- Build verified via Docker: `./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04`
- PR created: rjwalters/lean-genius#12973

### Key Findings

- **Primary decomposition eliminates PID entirely**: construct v_i = F_i(M)·w_i (F_i = complementary product ∏_{j≠i} p_j^{e_j}) — only annihilation/non-annihilation properties needed, not dim(ker) = deg(p_i^{e_i})
- **Finset.prod_dvd_of_coprime**: closes the general case — pairwise coprime factors all dividing r implies their product divides r
- **Matrix.mulVec_mulVec direction**: forward FOLDS nested mulVecs (A *ᵥ (B *ᵥ v) → (A*B) *ᵥ v), backward UNFOLDS; *ᵥ is right-associative
- **Missing Mathlib lemmas**: `Finset.prod_ne_zero` does NOT exist in 4.26; use `Finset.prod_eq_zero_iff`. `Polynomial.Irreducible.natDegree_pos` does NOT exist; use `eq_one_of_monic_natDegree_zero` + `not_isUnit`

### Files Modified

- `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04.lean` (replaced with general case, 359 lines)
- `src/data/proofs/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-04/meta.json` (updated)
- `src/data/research/problems/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-01.json` (status COMPLETED)

### Next Steps

1. Integrate UFD factorization of minpoly K M to eliminate the factored-form hypothesis
2. Open question: does primary decomposition approach generalize to modules over other PIDs?

---

## Session 2026-04-26 (Session 4) - WIP04: Binary Prime-Power Case Proved

**Mode**: REVISIT
**Outcome**: progress

### What I Did

- Created `CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04.lean` (421 lines, 0 axioms, 0 sorries)
- Proved `nonderogatory_bipow_has_cyclic_vector`: for nonderogatory M with minpoly = p^a * q^b (p, q coprime monic irreducibles, a,b ≥ 1), M has a cyclic vector over any field K
- Added gallery entry: `src/data/proofs/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-04/`
- Combined WIP02's CRT projection technique with WIP03's `pow_irred_dvd_of_annihilated` lemma

### Key Findings

- **Key combination**: Set v₁ = q^b(M)·w₁ where (p^(a-1)·q^b)(M)·w₁ ≠ 0 (degree < n → matrix nonzero). Then p^(a-1)(M)·v₁ ≠ 0, p^a(M)·v₁ = 0. Applying `pow_irred_dvd_of_annihilated` gives r(M)·v₁ = 0 → p^a | r.
- **IsCoprime.pow_pow**: `hcop.pow_pow : IsCoprime (p^a) (q^b)` from `IsCoprime p q` — key Mathlib4 lemma
- **CRT projections unchanged**: Same `bezout_proj_identity`/`bezout_proj_kills` pattern from WIP02 works for prime-power factors
- **Degree arithmetic**: `calc` blocks with `ring` and `linarith` handle the (a-1)*deg(p) + b*deg(q) < a*deg(p) + b*deg(q) = n inequality cleanly
- **IsCoprime.mul_dvd**: `hcop_pow.mul_dvd hpa_r hqb_r : p^a*q^b | r` closes the proof via degree contradiction

### Files Modified

- `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04.lean` (new, 421 lines)
- `src/data/proofs/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-04/` (new gallery entry)

### Next Steps

1. Generalize WIP04 to k factors: minpoly = p1^e1 * ... * pk^ek (k ≥ 3)
   - Approach: induction on k using the binary WIP04 case
   - For k = 2: WIP04 ✓. For k ≥ 3: split as f = (p1^e1) * (p2^e2 * ... * pk^ek), apply IH
   - Key challenge: need to show the "rest" polynomial is coprime to p1^e1 and that a "strong cyclic vector" for the rest exists
2. Check Mathlib 4.27+ for rational canonical form additions (would close WIP01 axiom)

## Problem Summary

Prove: nonderogatory M (minpoly = charpoly) has a cyclic vector, over ANY field K.

**Key blocker**: PID structure theorem for K[X]-modules not in Mathlib 4.26.
Without it, the standard route (cyclic decomposition V = K[X]/(minpoly)) is blocked.

## Session 2026-04-26 (Session 3) - WIP03: Prime Power Case Proved

**Mode**: FRESH (continuation)
**Outcome**: progress

### What I Did

- Created `CayleyHamiltonMinpolyOQ05OQ01OQ04WIP03.lean` (253 lines, 0 axioms, 0 sorries)
- Proved `pow_irred_dvd_of_annihilated`: if p irred, p^e(M)v≠0, p^(e+1)(M)v=0, r(M)v=0 → p^(e+1)|r, by strong induction on e
- Proved `nonderogatory_pw_has_cyclic_vector`: for nonderogatory M with minpoly=p^e, M has a cyclic vector over any field K
- Added gallery entry: `src/data/proofs/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-03/`
- Fixed Lean tactic errors: replaced `norm_cast` + `simp only [pow_one]` with `simpa` and `congr 2; ring` patterns

### Key Findings

- **Shift trick**: applying p(M) to v maps "level e" to "level e-1"; the induction hypothesis fires on u=p(M)v with polynomial r₁=r/p
- **No dimension arguments needed**: unlike the squarefree case, prime power case needs only polynomial divisibility, not CRT or projections
- **Commutativity is sufficient**: r(M)(p^k(M)v) = p^k(M)(r(M)v) via ring homomorphism property — this is the only structural fact needed
- **Base case** reuses `irreducible_dvd_of_annihilated` from WIP02 directly
- **Degree counting closes cleanly**: p^e|r and deg(r)<deg(p^e)=n forces r=0

### Files Modified

- `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP03.lean` (new, 253 lines)
- `src/data/proofs/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-03/` (new gallery entry)

### Next Steps

1. Create WIP04 combining WIP02 and WIP03 for full axiom-free theorem
   - Need: factor charpoly=p1^e1*...*pk^ek, apply CRT projections to get primary cyclic vectors
   - Then combine them: v = v1+...+vk is cyclic for M
2. Check Mathlib 4.27+ for rational canonical form additions

---

## Session 2026-04-26 (Session 2) - WIP02: Squarefree Case Proved

**Mode**: FRESH
**Outcome**: progress

### What I Did

- Implemented `exists_strongly_cyclic` in WIP02 — full strong induction proof replacing the single `sorry`
- Added `natDegree_pos_of_ne_zero_not_isUnit` helper lemma
- Updated calling site to pass `0 < q.natDegree` parameter
- PR #12894 created and merged

### Key Findings

- **Strong cyclicity** is the right inductive invariant: `r(M)v=0 → q|r` (not just `deg(r)<n → r=0`)
- **IsCoprime s t from squarefreeness**: if s|t then s^2|q, contradicting `Squarefree q`. Then `prime.coprime_iff_not_dvd` gives `IsCoprime s t`.
- **CRT projections** are algebraically self-contained: `e1 = b(M)q(M)` is identity on ker(p(M)) and kills ker(q(M)), proved purely from Bezout without any module theory.
- **Commutativity**: all polynomial evaluations in M commute (`aeval M f * aeval M g = aeval M g * aeval M f`). This lets CRT projections commute with r(M).
- **Non-unit propagation**: in composite case q=s*t, t is non-unit because if IsUnit t, then q=s*t ~ s would be irreducible, contradicting `¬Irreducible q`. Used `Associated.irreducible_iff`.
- **Non-squarefree case still open**: minpoly = p^e with e≥2 needs primary component structure. The kernel filtration ker(p(M)) ⊂ ker(p^2(M)) ⊂ ... ⊂ ker(p^e(M)) is the right structure but requires dimension arguments not easily formalized without Mathlib module theory.

### Files Modified

- `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP02.lean` (full proof)

### Next Steps

1. For non-squarefree case: try primary induction
   - Find v in ker(p(M)) with p^(e-1)(M)v != 0
   - Show r(M)v=0, deg(r) < e*deg(p) => p^e | r
   - Key lemma needed: if v in ker(p^j(M)) and r(M)v=0 => p^j | r
   - This is the "cyclic vector for a primary module" theorem — requires kernel filtration

2. Search Mathlib for `Module.erase` or `LinearMap.ker_pow_le` or primary torsion module API

---

## Session 2026-04-25 (Session 1) - OBSERVE Phase

**Mode**: FRESH
**Outcome**: scouted

### What I Did

- Surveyed problem statement and prior work
- Identified 4 alternative proof routes (companion matrix, CRT, span argument, primary decomp)
- Identified key Mathlib gaps

### Key Findings

- Prior work has all auxiliary lemmas: `cyclic_vector_of_similar`, `cyclic_iff_ann_eq_minpoly`, `irreducible_dvd_of_annihilated`
- WIP01 uses axiom `nonderogatory_similar_to_companion` (1 axiom) — rational canonical form gap
- CRT/Bezout approach looks tractable for squarefree case without any module theory

### Next Steps

- Implement CRT induction in WIP02 for squarefree case
