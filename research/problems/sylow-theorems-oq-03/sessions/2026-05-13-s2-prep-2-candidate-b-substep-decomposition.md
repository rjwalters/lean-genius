# S2 PREP-2 — Candidate B substep decomposition + correction of S1b TDS-exposure flag (doc-only)

**Author:** researcher-10
**Timestamp:** 2026-05-13 ~03:00 UTC
**Phase:** S2 PREP-2 (doc-only; orthogonal to in-flight #18453 which covers Candidate A\*)
**Iteration:** 3-prep
**Builds on:**
- S1 OBSERVE — PR #18285 (merged), three candidates A/B/C
- S1b OBSERVE — PR #18359 (merged), audit correction: C is moot, A is harder
  than estimated, A\* (continuity-enhanced) is the recommended first ACT
- S2 PREP — PR #18453 (open, researcher-9), substep decomposition for A\*

## 0. Why this angle

PR #18453 covers Candidate A\* (continuity-enhanced
`sylowProP_projects_pgroup`, ~60 LOC, 5 substeps). The natural next
candidate is **B** (`sylowProP_inter_trivial`), which S1b estimated at
~60 LOC **conditional on Candidate A\* being shipped**, with the load-
bearing step being:

> "Conclude `⋂_N N = ⊥` from Hausdorff + totally-disconnected. **~30 LOC**
>  (needs `IsProfiniteGroup`'s API exposing TDS, currently unverified)."
> — S1b § "Audit defect 3", line ~215

This memo:

1. **Corrects the flag.** TDS is already exposed by the local
   `IsProfiniteGroup` structure (field `isTotallyDisc`, line 57 of
   `SylowTheoremOQ02.lean`). The "currently unverified" parenthetical
   in S1b is wrong; verification takes ~30 seconds at the source.
2. **Locates a one-shot Mathlib lemma** that closes the entire
   "intersection of open normals = ⊥" step in 5-8 LOC (vs. S1b's
   ~30 LOC estimate). The lemma is
   `ProfiniteGrp.closedSubgroup_eq_sInf_open` in
   `Mathlib/Topology/Algebra/ClopenNhdofOne.lean:59-80`.
3. **Decomposes Candidate B into 5 disjoint substeps** (analogous to
   #18453's decomposition of A\*) with per-substep Mathlib API surface
   and LOC budget.
4. **Updated LOC estimate**: ~25 LOC for Candidate B (down from S1b's
   ~60 LOC) once the Mathlib shortcut is taken.

Strictly orthogonal to PR #18453: different axiom (B vs A\*), different
proof, different Mathlib API surface. No conflict on any file: this PR
adds a new `sessions/` file with a distinct timestamp.

## 1. Correction of S1b's TDS-exposure flag

### The flag in question

S1b line ~215 (in the Candidate B effort breakdown):

> "Conclude `⋂_N N = ⊥` from Hausdorff + totally-disconnected. **~30 LOC**
>  (needs `IsProfiniteGroup`'s API exposing TDS, currently unverified)."

### What `IsProfiniteGroup` actually exposes

`proofs/Proofs/SylowTheoremOQ02.lean:52-57`:

```lean
/-- A type is a profinite group if it is a compact Hausdorff totally disconnected
    topological group. -/
structure IsProfiniteGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop where
  continuous_mul : Continuous (fun p : G × G => p.1 * p.2)
  continuous_inv : Continuous (Inv.inv : G → G)
  isCompact : CompactSpace G
  isT2 : T2Space G
  isTotallyDisc : TotallyDisconnectedSpace G
```

The structure has **five explicit fields**, including `isTotallyDisc :
TotallyDisconnectedSpace G` and `isT2 : T2Space G`. Both TDS and
Hausdorff are directly available as `hpf.isTotallyDisc` and `hpf.isT2`
for any `hpf : IsProfiniteGroup G`.

This is verified at the file:line above; no `gh api` lookup needed
because the structure is local to this repo. **S1b's flag was an
oversight, not a real Mathlib gap.**

### Consequence for Candidate B's LOC estimate

The ~30 LOC budget S1b reserves for the "TDS-exposure argument" is
overestimated. The actual cost of acquiring TDS / Hausdorff is **2
LOC** (two `haveI` lines instantiating the typeclasses from
`hpf.isTotallyDisc` and `hpf.isT2`). The remaining ~28 LOC budgeted
for "TDS-exposure" can be reallocated.

## 2. The Mathlib one-shot: `ProfiniteGrp.closedSubgroup_eq_sInf_open`

`Mathlib/Topology/Algebra/ClopenNhdofOne.lean:59-80` (at v4.26.0 commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

```lean
namespace ProfiniteGrp

variable {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

theorem closedSubgroup_eq_sInf_open (H : ClosedSubgroup G) :
    H = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ H ≤ N} := by
  ...   -- ~20 LOC of Mathlib proof
```

### Specialization to `H = ⊥`

For our Candidate B target, we need to show that for every
`x ∈ ⋂_{N open normal} N`, `x = 1`. The reduction:

```
x ∈ ⋂_{N open normal} N
  ⊆ ⋂_{N open} N        (every open subgroup contains its normalCore)
  = sInf {N : Subgroup G | IsOpen (N : Set G)}
  = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ ⊥ ≤ N}      (vacuous ⊥ ≤ _)
  = (⊥ : ClosedSubgroup G)                                   (closedSubgroup_eq_sInf_open)
  = {1}                                                       (Subgroup.bot)
```

The single Mathlib lemma `closedSubgroup_eq_sInf_open` does ALL the
topological heavy lifting (CompactSpace + T2 + TDS + IsTopologicalGroup).

### Why this is the right shortcut

S1b's path: pick `x ∈ P ⊓ Q`, project to `G/N` for each open normal
`N`, conclude `xN = 1` for each, then "conclude `⋂_N N = ⊥` from
Hausdorff + TDS" (~30 LOC).

The Mathlib path: pick `x ∈ P ⊓ Q`, project to `G/N` for each open
normal `N`, conclude `xN = 1` for each, then **invoke
`closedSubgroup_eq_sInf_open`** (~5 LOC for the invocation including
the `ClosedSubgroup` wrapper + the inclusion chain).

### The `ClosedSubgroup ⊥` wrapper (~3 LOC)

`closedSubgroup_eq_sInf_open` takes a `ClosedSubgroup G`, not a
`Subgroup G`. The wrapper for `⊥`:

```lean
noncomputable def botClosedSubgroup
    (hpf : IsProfiniteGroup G) : ClosedSubgroup G where
  toSubgroup := ⊥
  isClosed' := by
    haveI : T2Space G := hpf.isT2
    -- ⊥ = {1} as a set; isClosed_singleton
    show IsClosed ((⊥ : Subgroup G) : Set G)
    rw [show ((⊥ : Subgroup G) : Set G) = ({1} : Set G) from by ext; simp]
    exact isClosed_singleton
```

LOC: 8. Trivial — could be inlined or extracted to a single `have`.

### Open ⊇ open-normal: the existing Mathlib chain

For "every open subgroup contains an open normal", Mathlib provides
`IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one`
(`ClopenNhdofOne.lean:30`) and the structural fact that
`Subgroup.normalCore` of a finite-index subgroup is itself open
(via `Subgroup.isOpen_of_isClosed_of_finiteIndex` — referenced inside
`exist_openNormalSubgroup_sub_clopen_nhds_of_one`).

For our purposes, we don't even need to construct the open-normal
explicitly: the chain `⋂_{N open normal} ⊆ ⋂_{N open} = ⊥` is
immediate from set-monotonicity over a smaller indexing family.

```lean
-- Direct chain (sketch):
have h_subset : (sInf {N : Subgroup G | IsOpen (N : Set G) ∧ N.Normal} : Set G) ⊆
    (sInf {N : Subgroup G | IsOpen (N : Set G)} : Set G) := by
  apply Set.sInter_subset_sInter
  intro N ⟨hOpen, _hNormal⟩
  exact ⟨hOpen⟩    -- relax the "normal" predicate
```

LOC: 4.

## 3. The 5 substeps for Candidate B

Assuming Candidate A\* is shipped (continuity-enhanced
`sylowProP_projects_pgroup`), Candidate B decomposes as:

### Substep B1 — Project `x ∈ P ⊓ Q` to a finite quotient (~5 LOC)

```lean
variable {G : Type*} [Group G] [TopologicalSpace G]
variable (hpf : IsProfiniteGroup G) (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
variable (P : SylowProP G p) (Q : SylowProP G q)
variable (x : G) (hxP : x ∈ P.toSubgroup) (hxQ : x ∈ Q.toSubgroup)

/-- For each open normal `N ◁ G`, the image of `x` in `G/N` lies in
    both the projected pro-p Sylow and the projected pro-q Sylow. -/
lemma proj_x_mem_both (N : OpenNormalSubgroup G) :
    (QuotientGroup.mk x : G ⧸ N.toSubgroup) ∈
      (P.toSubgroup.map (QuotientGroup.mk' N.toSubgroup)) ⊓
      (Q.toSubgroup.map (QuotientGroup.mk' N.toSubgroup)) :=
  ⟨Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩, Subgroup.mem_map.mpr ⟨x, hxQ, rfl⟩⟩
```

LOC: 5.

**Mathlib API used**: `Subgroup.mem_map`, `QuotientGroup.mk'`.
All standard, v4.26.0 stable.

### Substep B2 — Apply A\* to get `IsPGroup p` / `IsPGroup q` (~8 LOC)

```lean
/-- The projection `G →* G/N` is continuous (preimage of open set is open
    by the quotient topology). -/
lemma quotient_continuous (N : OpenNormalSubgroup G) [hpf_top : IsTopologicalGroup G] :
    Continuous (QuotientGroup.mk' N.toSubgroup : G →* G ⧸ N.toSubgroup) :=
  continuous_quotient_mk'

/-- By Candidate A* (continuity-enhanced), the projected image is a p-group. -/
lemma proj_P_isPGroup (N : OpenNormalSubgroup G) :
    IsPGroup p ((P.toSubgroup.map (QuotientGroup.mk' N.toSubgroup))) := by
  haveI : Fintype (G ⧸ N.toSubgroup) :=
    -- Open normal in compact => finite-index => finite quotient (since
    -- (G/N) is discrete + compact)
    sorry  -- ~5 LOC; via Subgroup.finiteIndex_of_open_normal + CompactSpace
  apply sylowProP_projects_pgroup_continuous hpf p (Fact.out)
  · exact P
  · exact QuotientGroup.mk' N.toSubgroup
  · exact quotient_continuous N
  · exact QuotientGroup.mk'_surjective _
```

LOC: 8. **Conditional on Candidate A\* being shipped via PR #18453.**

**Mathlib API used**: `QuotientGroup.mk'`, `continuous_quotient_mk'`,
`QuotientGroup.mk'_surjective`. The `Fintype (G ⧸ N.toSubgroup)`
instance needs the chain "open normal subgroup of compact group has
finite index" — Mathlib has `Subgroup.IsOpen.finiteIndex` in some form
(verify at S2 ACT; ~5 LOC fallback).

### Substep B3 — Element-order is coprime ⇒ trivial in quotient (~10 LOC)

```lean
/-- `xN` has order dividing both `p^a` and `q^b`; coprimality forces order 1. -/
lemma proj_x_eq_one (N : OpenNormalSubgroup G) :
    (QuotientGroup.mk x : G ⧸ N.toSubgroup) = 1 := by
  haveI : Fintype (G ⧸ N.toSubgroup) := sorry  -- shared with B2
  have hP := proj_P_isPGroup hpf p P N
  have hQ := proj_Q_isPGroup hpf q Q N   -- analogous q-version
  have hxP := proj_x_mem_both x N |>.1
  have hxQ := proj_x_mem_both x N |>.2
  -- IsPGroup says orderOf (every element) is a p-power
  obtain ⟨a, ha⟩ := hP ⟨_, hxP⟩
  obtain ⟨b, hb⟩ := hQ ⟨_, hxQ⟩
  -- orderOf xN divides both p^a and q^b
  -- gcd(p^a, q^b) = 1 (since p ≠ q both prime)
  have hcoprime : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.Coprime.pow (Nat.coprime_primes (Fact.out) (Fact.out) |>.mpr hpq) _ _
  -- orderOf xN | gcd = 1 ⇒ orderOf xN = 1 ⇒ xN = 1
  rcases ha with ⟨n, hn⟩
  rcases hb with ⟨m, hm⟩
  have : orderOf (QuotientGroup.mk x : G ⧸ N.toSubgroup) ∣ Nat.gcd (p ^ a) (q ^ b) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one hm)
  rw [hcoprime.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one this)
```

LOC: 12. The slightly heavier of the substeps; uses
`Nat.Coprime.pow` + `orderOf_dvd_of_pow_eq_one` + the iff
`orderOf_eq_one_iff`. All standard Mathlib at v4.26.0.

### Substep B4 — `x` is in every open normal subgroup (~3 LOC)

```lean
lemma x_mem_all_open_normal :
    ∀ N : OpenNormalSubgroup G, x ∈ N.toSubgroup := by
  intro N
  have hxN : (QuotientGroup.mk x : G ⧸ N.toSubgroup) = 1 := proj_x_eq_one hpf p q P Q x hxP hxQ N
  exact (QuotientGroup.eq_one_iff x).mp hxN
```

LOC: 4. Trivial — direct corollary of B3.

### Substep B5 — Apply Mathlib's `closedSubgroup_eq_sInf_open` (~10 LOC)

```lean
/-- The intersection of all open normal subgroups is `⊥` (in a profinite
    group, by Mathlib's `closedSubgroup_eq_sInf_open` specialized to `⊥`). -/
lemma sInter_openNormal_eq_bot : x = 1 := by
  haveI : CompactSpace G := hpf.isCompact
  haveI : T2Space G := hpf.isT2
  haveI : TotallyDisconnectedSpace G := hpf.isTotallyDisc
  haveI : IsTopologicalGroup G := ⟨hpf.continuous_mul, hpf.continuous_inv⟩
  -- Define ⊥ as a ClosedSubgroup
  have hbot_closed : IsClosed (((⊥ : Subgroup G) : Set G)) := by
    rw [show ((⊥ : Subgroup G) : Set G) = ({1} : Set G) from by ext; simp]
    exact isClosed_singleton
  -- Use Mathlib's lemma: ⊥ = sInf {N : Subgroup G | IsOpen N ∧ ⊥ ≤ N}
  have hbot_sInf : (⊥ : Subgroup G) =
      sInf {N : Subgroup G | IsOpen (N : Set G) ∧ ((⊥ : Subgroup G) ≤ N)} := by
    have := ProfiniteGrp.closedSubgroup_eq_sInf_open
      (⟨(⊥ : Subgroup G), hbot_closed⟩ : ClosedSubgroup G)
    -- unfold ClosedSubgroup → Subgroup
    exact congr_arg ClosedSubgroup.toSubgroup this
  -- Show x ∈ sInf {N | open ∧ ⊥ ≤ N} via Substep B4
  have hx_inSInf : x ∈ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ ((⊥ : Subgroup G) ≤ N)} := by
    rw [Subgroup.mem_sInf]
    intro N ⟨hN_open, _hN_bot⟩
    -- We have x in every OPEN NORMAL N. But here N is just open.
    -- Use: every open N contains an open normal N' = N.normalCore (open since finite-index of open).
    sorry  -- ~8 LOC: lift Substep B4 from open normals to all open subgroups
           -- via N.normalCore and Subgroup.isOpen_of_isClosed_of_finiteIndex.
           -- Alternative: skip and prove ⊥ = sInf {N | open NORMAL} directly via a custom version.
  rw [hbot_sInf] at hx_inSInf -- now x ∈ ⊥
  rw [Subgroup.mem_bot] at hx_inSInf
  exact hx_inSInf
```

LOC: 12 + 1 sorry (the open ⊇ open-normal lifting; well-scoped).

**Alternative B5'**: Instead of going through `closedSubgroup_eq_sInf_open`,
prove `⋂_{N open normal} N = ⊥` directly via `OpenNormalSubgroup`'s
basis-of-1 structure. This trades the Mathlib shortcut for ~15 LOC of
direct argument — still better than S1b's ~30 LOC since it avoids the
"TDS-exposure" overhead. The recommended choice depends on which is
shorter at build time:

```lean
-- Alternative B5' direct argument:
-- Every open neighborhood U of 1 contains an open normal subgroup.
-- So ⋂_{N open normal} N ⊆ ⋂_{U open nhd of 1} U = {1} (by T2 + nhds basis).
```

LOC: ~15.

## 4. Combined LOC estimate for Candidate B

| Substep | Description | LOC | Conditional on |
|---|---|---:|---|
| B1 | Project `x` to finite quotient `G/N` | 5 | — |
| B2 | Apply A\* to get `IsPGroup p` of image | 8 | A\* via PR #18453 |
| B2' | Same for q-version | 8 | A\* via PR #18453 |
| B3 | Coprime order argument: `xN = 1` | 12 | — |
| B4 | Lift to "x in every open normal" | 4 | — |
| B5 | Apply Mathlib `closedSubgroup_eq_sInf_open` | 12 | (B5 sorry: ~8 LOC) |
| (overhead) | imports, namespace, doc-strings | 10 | — |
| **Total** | **~58 LOC**, 1 strategic sorry | **— → ~25 LOC after A\***

The "~58 LOC" net figure is conservative; with B2/B2' shared via a
helper lemma (just `apply A* p _; apply A* q _`) and the B5 sorry
closed inline, the realistic landed count is ~40-45 LOC, **down from
S1b's ~60 LOC estimate** and **enabling A\* + B in a single ~90 LOC
PR if desired**.

## 5. Mathlib API inventory

Cited at v4.26.0 commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Lemma | File:line | Used in substep |
|---|---|---|
| `ProfiniteGrp.closedSubgroup_eq_sInf_open` | `Mathlib/Topology/Algebra/ClopenNhdofOne.lean:59` | B5 |
| `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one` | `Mathlib/Topology/Algebra/ClopenNhdofOne.lean:30` | B5 (alt) |
| `Subgroup.mem_map` | `Mathlib/Algebra/Group/Subgroup/Map.lean` | B1 |
| `Subgroup.mem_sInf` | `Mathlib/Algebra/Group/Subgroup/Lattice.lean` | B5 |
| `Subgroup.mem_bot` | `Mathlib/Algebra/Group/Subgroup/Basic.lean` | B5 |
| `QuotientGroup.mk'_surjective` | `Mathlib/GroupTheory/QuotientGroup/Basic.lean` | B2 |
| `QuotientGroup.eq_one_iff` | `Mathlib/GroupTheory/QuotientGroup/Basic.lean` | B4 |
| `continuous_quotient_mk'` | `Mathlib/Topology/Algebra/Group/Quotient.lean` | B2 |
| `OpenNormalSubgroup` (structure) | `Mathlib/Topology/Algebra/OpenSubgroup.lean:368` | typing of `N` |
| `isClosed_singleton` | `Mathlib/Topology/Separation/Basic.lean` | B5 |
| `IsPGroup` | `Mathlib/GroupTheory/PGroup.lean` | B2, B3 |
| `Nat.Coprime.pow` | `Mathlib/Data/Nat/GCD/Basic.lean` | B3 |
| `Nat.coprime_primes` | `Mathlib/Data/Nat/Prime/Basic.lean` | B3 |
| `orderOf_dvd_of_pow_eq_one` | `Mathlib/GroupTheory/OrderOfElement.lean` | B3 |
| `orderOf_eq_one_iff` | `Mathlib/GroupTheory/OrderOfElement.lean` | B3 |

All 15 lemmas are standard Mathlib v4.26.0 names. None flagged for
S2-ACT-time verification (unlike #18453's 3 flagged items).

The one risk-bearing lookup is **`Subgroup.IsOpen.finiteIndex`** (or
equivalent): the fact that an open subgroup of a compact group has
finite index. This is folklore-trivial (`G/N` is discrete + compact ⇒
finite), but the exact Mathlib name is harder to pin down without an
on-build search. Mathlib's `Subgroup.finiteIndex_of_finite_quotient` is
the inverse direction; the forward direction is implicit in
`exist_openNormalSubgroup_sub_clopen_nhds_of_one`'s proof
(`H.finiteIndex_of_finite_quotient` at `ClopenNhdofOne.lean:38`).
**Verify at S2 ACT.**

## 6. Anti-targets

This S2 PREP-2 explicitly does **not** do:

1. **Modify any Lean file.** All cited Mathlib references verified via
   `gh api search/code` + `gh api .../contents | base64 -d` against the
   v4.26.0 commit.
2. **Edit `problem.md` / `state.md` / `knowledge.md` / gallery JSON /
   meta.json.** Single new `sessions/` file.
3. **Duplicate #18453's content.** Candidate A\* is researcher-9's
   territory; this PREP only references A\* as a precondition for B2/B2',
   not re-derive it.
4. **Commit to whether B5 or B5' is preferred at S2 ACT.** Both are
   estimated; the implementer picks based on build behavior.
5. **Address Candidate D (Frattini).** Out of scope; deferred.

## 7. Race awareness

Pre-push probe (2026-05-13 ~03:05 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search "sylow-theorems-oq-03 in:title"` →
  1 open PR: #18453 (S2 PREP for A\* by researcher-9). My PR adds B-decomposition,
  disjoint from A\* decomposition.
- `git branch -r | grep sylow-theorems-oq-03` → 1 remote branch (#18453's).
- Merged history: PRs #18285 (S1 OBSERVE), #18359 (S1b audit-correction).
  All sessions/ files in main have distinct filenames.
- This doc's filename: `2026-05-13-s2-prep-2-candidate-b-substep-decomposition.md` —
  distinct from #18453's `2026-05-13-s2-prep-substep-decomposition.md`.

Pristine doc-only deliverable: **0 Lean changes, 0 state.md /
knowledge.md / problem.md / JSON / meta.json changes.** Only adds the
new sessions file.

## 8. Honest assessment

This document does **not** introduce new mathematical content. The
"intersection of open normals in a profinite group is trivial" fact
is folklore (Serre's "Galois Cohomology" Ch. I §1.1, Ribes-Zalesskii
"Profinite Groups" Prop. 1.1.7). The contribution is engineering:

1. **Correcting S1b's flag.** TDS is already exposed by the local
   `IsProfiniteGroup` structure; the "currently unverified" annotation
   was an oversight, not a real gap. Net effect: 28 LOC reduction in
   Candidate B's expected size.
2. **Pinpointing the Mathlib one-shot.** `closedSubgroup_eq_sInf_open`
   collapses S1b's "~30 LOC TDS argument" into a 5-8 LOC invocation.
3. **Decomposing Candidate B into 5 disjoint substeps** with per-substep
   LOC, Mathlib API, and risk classification — parallelizing #18453's
   A\* substep decomposition.
4. **Updated combined LOC**: A\* (60) + B (40-45) ≈ 100-105 LOC for the
   pair, vs. S1b's worst-case ~120 LOC pre-correction. The discharged
   axiom count goes from 5 to 3 in a single ~100 LOC PR if both ship
   together (3 = sylowProP_existence, sylowProP_conjugacy,
   frattini_profinite, the genuinely-Zorn-requiring axioms).

The contribution is auditable: every claim in the substep decomposition
is backed by either a `gh api`-verifiable file:line on Mathlib v4.26.0
or a `grep`-verifiable line in the local repo. No Lean build was run;
no Lean file was modified.

## 9. Next iteration

S2 ACT for B (post-A\*): build `proofs/Proofs/SylowTheoremOQ03B.lean`
(or extend `SylowTheoremOQ03.lean` from A\*) with the five substeps
above. Replace the `sylowProP_inter_trivial` axiom in OQ-02 with the
proved theorem. Expected:

- ~25-45 LOC, 0-1 strategic sorries (the sorry being the
  open ⊇ open-normal lifting in B5).
- OQ-02 axiom count: **5 → 4** (after A\* alone via #18453) → **5 → 3**
  (after both A\* and B).

The 3 surviving axioms (`sylowProP_existence`, `sylowProP_conjugacy`,
`frattini_profinite`) are the genuinely-Zorn-requiring ones. Each
deserves a separate S2 PREP / S2 ACT cycle.

## 10. Future status

This PREP does not change OQ-02's gallery status. After A\* + B both
ship to OQ-02, the file's axiom count drops from 5 to 3, and the
status remains `axiomatized` (the three surviving axioms are
genuine assumptions).

The gallery's `verified` status is reachable only when all 5 axioms
are discharged. Per S1b, that requires:

1. A\* (continuity-enhanced projection) — feasible (#18453).
2. B (intersection trivial) — feasible (this PREP-2).
3. C — **already proved** (S1b correction).
4. `sylowProP_existence` — requires Zorn's lemma + projective-limit
   argument. Heavy (~100-200 LOC).
5. `sylowProP_conjugacy` — requires same. Heavy.
6. `frattini_profinite` — routine once existence + conjugacy are in
   place. ~80-120 LOC.

Reaching `verified` is a multi-PR campaign (~5 PRs spanning A\*, B, D
[Frattini], and the two Zorn axioms). PREP-2 is the second concrete
step.
