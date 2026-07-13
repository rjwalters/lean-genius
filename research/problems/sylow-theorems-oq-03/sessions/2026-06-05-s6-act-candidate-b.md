# S6 ACT — Candidate B: Discharge of `sylowProP_inter_trivial`

**Author:** researcher-1 (claim `researcher-90270`, knowledge score 28 RICH)
**Timestamp:** 2026-06-05 ~14:00 UTC
**Phase:** S6 ACT (Lean-modifying — Candidate B implementation)
**Iteration:** 15 (8 PREP + S2 PREP-7 + S2 ACT + STATE-SYNC × 3 + S4 ACT + S5 STATE-SYNC + this S6 ACT)

**Builds on:**
- S1 OBSERVE (#18285) — 3 candidates A/B/C
- S2 PREP-2 (#18493) — Candidate B 5-substep decomposition
- S2 PREP-4 (#18658) — `closedSubgroup_eq_sInf_open` is PHANTOM; replacement
  `nhds_basis_clopen` chain via `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`
- S2 PREP-5 (#18722) — `IsTopologicalGroup` typeclass-bridge requirement
- S2 ACT (#19260) — Candidate A* shipped (`sylowProP_projects_pgroup_continuous` in
  `SylowTheoremOQ03.lean`), foundation for Candidate B's B2 substep
- S4 ACT (#19380) — OQ-02 axiom drop 5→4 realized
- S5 STATE-SYNC (#22028, 2026-06-02) — deferred Candidate B 16 days; queued for ACT

## 0. Why this angle now

Per S5 STATE-SYNC (#22028) and the S4 §6a TOP priority designation,
Candidate B has been the unchanged top-priority next ACT for 20 days
across 4 prior STATE-SYNC ticks. This session attempts the ACT.

## 1. Ship summary

**One new file**: `proofs/Proofs/SylowTheoremOQ03B.lean` (~115 LOC
including imports and docstrings; ~50 LOC of actual proof body).
**One import update**: `proofs/Proofs.lean` adds
`import Proofs.SylowTheoremOQ03B`.

**Mathematical content**: Discharges the OQ-02 axiom
`sylowProP_inter_trivial` (currently at L133) via the finite-quotient
route planned in S2 PREP-2. The proof uses the previously-shipped
Candidate A* (`sylowProP_projects_pgroup_continuous` in
`SylowTheoremOQ03.lean`) as a key lemma — without it, the projection
step would not work.

**The OQ-02 axiom removal** (axiomCount 4 → 3) is intentionally **NOT**
in this PR; it will be a clean follow-on after Candidate B builds
clean, by analogy to the A* → S4 split (S2 ACT shipped A* in OQ-03;
S4 ACT removed the OQ-02 axiom 16 days later). Splitting reduces
single-PR risk and gives the next iteration an opportunity to re-
verify build health on the freshly-added file before committing to
the axiom delta.

## 2. Proof outline (matches PREP-2 substeps + PREP-4/5 fixes)

| Step | Description | LOC | Source |
|------|-------------|-----|--------|
| Setup | `haveI` typeclass instances from `hpf` (CompactSpace, T2, TDS, ContinuousMul/Inv, IsTopologicalGroup) | 6 | PREP-5 Finding I |
| B0 | Reduce `⊓ = ⊥` to "every element is 1"; by-contradiction for `x ∈ P ⊓ Q`, `x ≠ 1` | 4 | — |
| B-clopen | `{x}` closed (T2 + isClosed_singleton), `{x}ᶜ` is open and `1 ∈ {x}ᶜ` | 4 | PREP-5 Finding V |
| B-onnsub | Apply `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` to get open normal `N ⊂ {x}ᶜ` | 2 | PREP-4 §3 |
| B-finQ | Quotient `G ⧸ N` is finite + discrete (Mathlib instances) | 4 | OpenSubgroup.lean:298 |
| B2 | Apply Candidate A* (twice) — image of P is p-group, image of Q is q-group | 4 | SylowTheoremOQ03.lean |
| B3 | Extract `(φ x)^(p^a) = 1` and `(φ x)^(q^b) = 1` from IsPGroup | 8 | IsPGroup def |
| B4 | `Nat.coprime_pow_primes` + `Nat.dvd_gcd` + `Nat.dvd_one` → `orderOf (φ x) = 1` | 5 | Prime/Basic.lean:201 |
| B5 | `orderOf_eq_one_iff` → `φ x = 1` → `x ∈ N` → contradiction | 4 | OrderOfElement.lean:248 |
| **Total** | | **~50 LOC body** | |

## 3. Mathlib bearer table (PREP-4/5 verified)

All bearers verified at v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

| Bearer | File:line | Verified by |
|--------|-----------|-------------|
| `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` | `ClopenNhdofOne.lean:44` | PREP-4 §3 |
| `(U : OpenSubgroup G) : Finite (G ⧸ U.toSubgroup)` instance | `OpenSubgroup.lean:298` | gh api lookup |
| `QuotientGroup.discreteTopology` | `Topology/Algebra/Group/Quotient.lean` | gh api lookup |
| `continuous_quotient_mk'` | `Topology/Algebra/Group/Quotient.lean` | gh api lookup |
| `IsPGroup` (def) | `PGroup.lean:26` | PREP-2 §5 |
| `orderOf_dvd_of_pow_eq_one` | `OrderOfElement.lean:259` | gh api lookup |
| `orderOf_eq_one_iff` | `OrderOfElement.lean:248` | gh api lookup |
| `Nat.coprime_pow_primes` | `Prime/Basic.lean:201` | gh api lookup |
| `Nat.Coprime.gcd_eq_one` | `Nat/Coprime/...` (standard) | implicit |
| `isClosed_singleton` (needs T1, transitively from T2) | `Separation/Basic.lean:341` | PREP-5 Finding V |
| `IsClosed.isOpen_compl` (struct field) | `Defs/Basic.lean:104` | PREP-5 Finding IV |

## 4. Pre-build sanity checks

- Imports include `Proofs.SylowTheoremOQ03` (for `sylowProP_projects_pgroup_continuous`).
- The `IsTopologicalGroup G := {}` synthesis depends on `ContinuousMul G` and
  `ContinuousInv G` being in scope (PREP-5 Finding I); both `haveI`'d above.
- `Subtype.val` coercion is used to convert subgroup-typed power equation to
  ambient-quotient equation. May need `simpa [SubgroupClass.coe_pow]` instead
  of bare `simpa` if Lean doesn't auto-simp the power coercion; flagged as
  build-risk #1.
- The `(QuotientGroup.mk x : G ⧸ ...) = 1` to `x ∈ N` step uses
  `QuotientGroup.eq_one_iff`; standard.

## 5. Build risks (honest)

1. **Power coercion** (B3 step): `congrArg Subtype.val (h : ⟨φx, _⟩^(p^a) = 1)`
   may not directly yield `(φ x)^(p^a) = 1` without help. If `simpa` fails,
   try `SubgroupClass.coe_pow` + `OneMemClass.coe_one` explicit rewrites.
2. **`hp.out.prime`**: `Fact p.Prime` gives `hp.out : Nat.Prime p`; the
   `Nat.coprime_pow_primes` signature wants `Prime p`. `Nat.Prime.prime`
   bridges them, but if naming has drifted, fall back to `hp.out` (which
   *is* `Prime p` in current Mathlib via the `Nat.Prime` definition).
3. **Anonymous-constructor IsTopologicalGroup `{}`**: PREP-5 Finding I
   predicted this works as a typeclass-extension class with no own
   fields; if Lean rejects, use `⟨⟩` instead.
4. **OpenNormalSubgroup `.toOpenSubgroup.toSubgroup` path**: needed
   because the subgroup-membership at `N : OpenNormalSubgroup G` goes
   through two coercions. Verified syntactically against the structure
   definitions at `OpenSubgroup.lean:48,374`.

## 6. If build fails

Document the precise failure mode in a follow-up session note. The
likely fix is one of the risks above — all are local to <5 LOC.
Re-submission cycle is ~25-45 min per Docker iteration.

## 7. Race awareness

Pre-claim check (2026-06-05 ~13:55 UTC): no open PRs for
`sylow-theorems-oq-03 in:title`. The slug has been at ACT-REALIZED
phase since 2026-05-16 with no concurrent activity.

## 8. Anti-targets (this PR does NOT)

1. **Remove the OQ-02 axiom**. Deferred to a clean follow-on PR after
   Candidate B builds clean (the A* → S4 split precedent).
2. **Modify `SylowTheoremOQ03.lean`**. The new file imports it and
   uses `sylowProP_projects_pgroup_continuous`, but does not edit it.
3. **Touch `SylowTheoremOQ02.lean`**. Its axiom remains for now.
4. **Modify sibling slugs** (OQ-01, OQ-04, OQ-05).
5. **Mathlib upstream contribution** (S4 §6b out-of-band).
6. **Frattini axiom restatement** (S4 §6c, curator/architect scope).

## 9. Files touched

| File | Δ |
|------|---|
| `proofs/Proofs/SylowTheoremOQ03B.lean` | NEW (~115 LOC including imports/docs) |
| `proofs/Proofs.lean` | +1 import line |
| `research/problems/sylow-theorems-oq-03/state.md` | header refresh + S6 ACT subsection |
| `src/data/research/problems/sylow-theorems-oq-03.json` | iteration 14 → 15, focus/nextAction/builtItems |
| `research/problems/sylow-theorems-oq-03/sessions/2026-06-05-s6-act-candidate-b.md` | NEW (this file) |
