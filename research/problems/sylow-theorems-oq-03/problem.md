# Problem: Pro-p Sylow — narrow S2 targets adjacent to completed OQ-02

## Statement

### Plain Language

`sylow-theorems-oq-03` ("pro-p Sylow theorem: every profinite group
G has a maximal pro-p subgroup, any two conjugate, recovered as the
inverse limit of finite-group Sylow theorems") is a **near-duplicate**
of the *completed* sibling slug `sylow-theorems-oq-02`
("Pro-p Sylow Theory for Profinite Groups"). The completed sibling
already ships `proofs/Proofs/SylowTheoremOQ02.lean` (393 lines, 7
proved theorems, **5 axioms**, **1 sorry**).

Rather than restate the same conjecture, this OBSERVE follows the
memory-recorded "Millennium / Hilbert sub-OQs duplicate the parent
slug" pattern: detect the duplication, audit the actual gap in OQ-02,
and propose **2–3 narrow adjacent S2 targets** that are concrete,
finite-scope, and complementary to OQ-02.

### Identified Gaps in OQ-02

| # | Item                                  | Type   | OQ-02 line | S2 candidate? |
|---|---------------------------------------|--------|------------|---------------|
| 1 | `sylowProP_existence`                 | axiom  | 108        | NO — needs inverse-limit construction (~500+ LOC) |
| 2 | `sylowProP_conjugacy`                 | axiom  | 119        | NO — needs compactness + Zorn/Kőnig (~300+ LOC) |
| 3 | `frattini_profinite`                  | axiom  | 126        | PARTIAL — derivable from existence + conjugacy assuming both |
| 4 | `sylowProP_projects_pgroup`           | axiom  | 134        | **YES** — derivable from continuity + finite-image + `IsPGroup` (~30 LOC) |
| 5 | `sylowProP_inter_trivial`             | axiom  | 142        | **YES** — derivable from coprime-order + Lagrange in the finite quotient (~25 LOC) |
| 6 | `sylowProP_normal_of_unique`          | sorry  | 285        | **YES** — finite-case adaptation (~40 LOC) |

### S2 Candidates (S1 OBSERVE proposes three)

#### Candidate A — Discharge axiom `sylowProP_projects_pgroup`

The axiom states: continuous surjection `φ : G →* H` onto a finite
group sends a Sylow pro-p subgroup to a `IsPGroup p` subgroup of `H`.

**Proof sketch (~30 LOC).** `P.toSubgroup.map φ` is a *finite*
subgroup of `H` (image of a closed compact in a finite Hausdorff). By
the existing local theorem `proP_subgroup_card_ppow` (oq-02 line 332,
proved), any pro-p subgroup of a finite group has p-power order, so
the image is an `IsPGroup p`. Only the finite-image step requires a
new Lean lemma — `Finite (P.toSubgroup.map φ : Set H)`.

#### Candidate B — Discharge axiom `sylowProP_inter_trivial`

The axiom states: Sylow pro-p and pro-q subgroups for distinct primes
intersect trivially.

**Proof sketch (~25 LOC).** Pick `x ∈ P ⊓ Q`. Project to a finite
quotient `G/N` (open normal). The image is in both a Sylow p- and a
Sylow q-subgroup of `G/N`, hence has order coprime to both p and q,
so the image is trivial. Since `x` projects to identity in every
finite quotient, `x = 1` by the profinite-completion characterisation
(Hausdorff totally-disconnected).

#### Candidate C — Discharge sorry `sylowProP_normal_of_unique`

The sorry states: if there is a unique Sylow pro-p subgroup `P`, then
`P` is normal in `G`.

**Proof sketch (~40 LOC).** For any `g ∈ G`, `g P g⁻¹` is also a
Sylow pro-p subgroup (by `isProP_conj_map` at line 226, proved). By
uniqueness, `g P g⁻¹ = P`, so `P` is normal. Mechanical, ~10 lines
of Lean if the `isProP_conj_map`'s output integrates cleanly with
`SylowProP`'s structure.

### Formal Signature Targets (S2 ACT scope, one of A/B/C)

Candidate A:

```lean
theorem sylowProP_projects_pgroup
    {G : Type*} [Group G] [TopologicalSpace G]
    (hpf : IsProfiniteGroup G) (p : ℕ) (hp : Fact p.Prime)
    (P : SylowProP G p)
    (H : Type*) [Group H] [Fintype H]
    (φ : G →* H) (hφ_surj : Function.Surjective φ) :
    IsPGroup p (P.toSubgroup.map φ) := by
  -- finite-image + proP_subgroup_card_ppow + IsPGroup.iff_card
  sorry  -- ~30 LOC, fully mechanical
```

Candidate B:

```lean
theorem sylowProP_inter_trivial
    {G : Type*} [Group G] [TopologicalSpace G]
    (hpf : IsProfiniteGroup G)
    (p q : ℕ) (hp : Fact p.Prime) (hq : Fact q.Prime) (hpq : p ≠ q)
    (P : SylowProP G p) (Q : SylowProP G q) :
    P.toSubgroup ⊓ Q.toSubgroup = ⊥ := by
  -- coprime-order in finite quotients + profinite Hausdorff totally-disconnected
  sorry  -- ~25 LOC
```

Candidate C:

```lean
theorem sylowProP_normal_of_unique {G : Type*} [Group G] [TopologicalSpace G]
    (hpf : IsProfiniteGroup G) (p : ℕ) (hp : Fact p.Prime)
    (hunique : Subsingleton (SylowProP G p))
    (P : SylowProP G p) : P.toSubgroup.Normal := by
  -- For any g, conjugate is also a SylowProP; uniqueness forces P = g·P·g⁻¹
  sorry  -- ~40 LOC; ships isProP_conj_map application
```

### Acceptance Criteria (S1 OBSERVE deliverable)

1. **Duplicate-detection note.** Explicit linkage to completed sibling
   `sylow-theorems-oq-02` and reason this slug is NOT a re-attempt.
2. **OQ-02 audit table.** All 5 axioms + 1 sorry classified by S2-
   addressability (NO / PARTIAL / YES).
3. **Three narrow S2 candidates.** Each with: proof sketch, expected
   LOC, dependencies in the file, and required Mathlib lemmas.
4. **Build pending tolerable.** S2 (whichever candidate is picked) ships
   without local Docker verification; build status updates at PR
   merge time.
5. **No new content, no new axioms.** OQ-03 is a *narrowing* of
   OQ-02, not a duplication or extension.

## Classification

```yaml
tier: B
significance: 7
tractability: 4
tags:
  - seeker-selected
  - group-theory
  - profinite-groups
  - sylow
  - pro-p
  - duplicate-detection
  - axiom-discharge
```

**Significance**: 7/10 — each discharged axiom strengthens the
mathematical claim of `SylowTheoremOQ02.lean` from "axiomatized" to
"verified-modulo-fewer-axioms"; cumulative effect across A+B+C drops
the axiom count from 5 to 2 (the two that genuinely require
inverse-limit construction).

**Tractability**: 4/10 — discharging the easiest axioms (A, B, C) is
each ~30 LOC of careful Lean. The full inverse-limit construction for
the *remaining* axioms (existence, conjugacy) is genuinely heavy and
remains out of scope for this OQ.

## Why This Matters

1. **Axiom integrity.** Memory note "Axiom Integrity Policy" in
   `CLAUDE.md`: discharging axioms strengthens the gallery claim.
   OQ-03 = surgical axiom discharge.
2. **Duplicate-detection pattern.** Following the memory-recorded
   "Millennium / Hilbert 'Is X true?' sub-OQs duplicate the parent
   slug" pattern (researcher-12 PR #18235, 2026-05-12).
3. **OQ-02's `nextSteps`** (per its gallery JSON) explicitly list
   "Prove sylowProP_normal_of_unique (1 sorry)" as a S2 target —
   OQ-03 picks it up.

## Related Gallery Proofs

| Slug                              | Relevance                                                 |
|-----------------------------------|-----------------------------------------------------------|
| `sylow-theorems-oq-02`            | **DIRECT PARENT** — completed; OQ-03 narrows axioms      |
| `sylow-theorems-oq-01`            | Sister: alternative formalisation route                   |
| `sylow-theorems-oq-04`            | Sister                                                    |
| `sylow-theorems-oq-05`            | Sister                                                    |
| `inverse-galois`                  | Downstream consumer (uses pro-p Sylow for Galois)         |
| `Mathlib.GroupTheory.Sylow`       | Mathlib's finite Sylow theory (reused by oq-02)           |

## References

- Serre, J.-P. (1965). *Cohomologie Galoisienne*. Springer LNM 5.
  Chapter I, § 1 (pro-p groups and pro-p Sylow theory).
- Wilson, J. S. (1998). *Profinite Groups*. London Math. Soc.
  Monographs. § 2 (Sylow theory).
- Ribes, L., and Zalesskii, P. (2010). *Profinite Groups* (2nd ed.).
  Ergebnisse 40. Springer. Theorem 2.3.2 (pro-p Sylow existence /
  conjugacy).
- Local file: `proofs/Proofs/SylowTheoremOQ02.lean` (393 lines, 7
  theorems, 5 axioms, 1 sorry) — the OBSERVE target.
