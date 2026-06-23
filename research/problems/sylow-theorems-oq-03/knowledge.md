# Knowledge: Sylow Pro-p — Adjacent Axiom-Discharge Targets

## 1. Duplicate detection

`sylow-theorems-oq-03` ("pro-p Sylow theorem, recovered as inverse
limit of finite-group Sylow theorems") is a near-duplicate of the
**completed** sibling `sylow-theorems-oq-02` ("Pro-p Sylow Theory for
Profinite Groups"). The completed sibling's `meta.json`
(`src/data/research/problems/sylow-theorems-oq-02.json`) records:

- `status`: `completed`
- `phase`: `ACT`
- File: `proofs/Proofs/SylowTheoremOQ02.lean` (393 lines, 7
  theorems, 5 axioms, 1 sorry)
- `nextSteps`: ["Prove sylowProP_normal_of_unique (1 sorry)", "Build
  inverse limit construction"]

This OBSERVE follows the memory-recorded pattern (researcher-12
PR #18235, 2026-05-12): rather than re-attempt the conjecture, audit
the OQ-02 file and propose narrow adjacent S2 targets.

## 2. Audit of OQ-02's open items

### 2.1 Five axioms (`section ProfiniteAxioms` of `SylowTheoremOQ02.lean`)

| Axiom                          | Lines | What it states (informal)                                                                  | Discharge route                          | S2 effort     |
|--------------------------------|-------|-------------------------------------------------------------------------------------------|------------------------------------------|---------------|
| `sylowProP_existence`          | 108–110 | Sylow pro-p subgroups exist                                                              | Inverse-limit / Zorn                     | ~500 LOC heavy |
| `sylowProP_conjugacy`          | 119–123 | Any two are conjugate                                                                    | Compactness + Kőnig over finite quotients | ~300 LOC      |
| `frattini_profinite`           | 126–131 | Frattini argument: G = N · N_G(P) for closed normal N                                    | Existence + conjugacy + finite analog    | ~80 LOC       |
| `sylowProP_projects_pgroup`    | 134–140 | Image under continuous surjection to finite is `IsPGroup p`                              | Finite-image + `proP_subgroup_card_ppow` (already proven, line 332) | **~30 LOC** ✓ |
| `sylowProP_inter_trivial`      | 142–146 | Distinct-prime Sylows intersect trivially                                                | Coprime-order in finite quotient + Hausdorff | **~25 LOC** ✓ |

The first two axioms (`existence`, `conjugacy`) are **deep**: their
discharge requires the full inverse-limit construction and is the
stated long-term goal of OQ-02 itself. The third (`frattini`) is
moderate but presupposes existence + conjugacy. The last two are
**mechanically dischargable** with existing local theorems plus
small Mathlib lemmas.

### 2.2 One sorry (`sylowProP_normal_of_unique` at line 285)

```lean
theorem sylowProP_normal_of_unique {G : Type*} [Group G] [TopologicalSpace G]
    (hpf : IsProfiniteGroup G) (p : ℕ) (hp : Fact p.Prime)
    (hunique : Subsingleton (SylowProP G p))
    (P : SylowProP G p) : P.toSubgroup.Normal := by
  sorry
```

The local file already proves `isProP_conj_map` (line 226), which
gives: continuous conjugation by `g` of a pro-p subgroup yields
another pro-p subgroup. Combining with the `Subsingleton` hypothesis,
`g P g⁻¹` must equal `P`. Normality follows. **Estimated 40 LOC of
Lean** for the full proof — bridging `isProP_conj_map`'s output
type (`Subgroup G`) to `SylowProP`'s structure form requires care.

## 3. Candidate A — Discharge `sylowProP_projects_pgroup`

### 3.1 Mathematical content

Given:
- `hpf : IsProfiniteGroup G`
- `P : SylowProP G p` (in particular, `P.toSubgroup` is closed,
  compact, pro-p)
- `φ : G →* H` continuous surjective with `H` finite

Goal: `IsPGroup p (P.toSubgroup.map φ)`.

Proof:
1. `P.toSubgroup.map φ` is a subgroup of `H`; since `H` is finite,
   so is `P.toSubgroup.map φ`.
2. By the existing local theorem `proP_subgroup_card_ppow` (line
   332): any pro-p subgroup of a finite group has order p^k for some
   k.
3. Hence the image satisfies `IsPGroup p` via
   `Mathlib.GroupTheory.PGroup.iff_card` (or `IsPGroup.of_card`).

### 3.2 Lean skeleton

```lean
theorem sylowProP_projects_pgroup
    {G : Type*} [Group G] [TopologicalSpace G]
    (hpf : IsProfiniteGroup G) (p : ℕ) (hp : Fact p.Prime)
    (P : SylowProP G p)
    (H : Type*) [Group H] [Fintype H]
    (φ : G →* H) (hφ_surj : Function.Surjective φ) :
    IsPGroup p (P.toSubgroup.map φ) := by
  classical
  -- Step 1: image is a finite subgroup of H.
  have h_fin : Fintype (P.toSubgroup.map φ) := Subtype.fintype _
  -- Step 2: image is pro-p (continuous image of pro-p in finite is p-group).
  --   Use IsProP.image with hpf.isClosed (P.toSubgroup), or directly:
  have h_proP : IsProPSubgroup _ p (P.toSubgroup.map φ) := by
    -- transfer IsProP from P.toSubgroup; finite quotients of a pro-p
    -- group are p-groups.
    sorry  -- ~10 LOC, mechanical via existing IsProP API
  -- Step 3: finite pro-p subgroup ⇒ |·| = p^k ⇒ IsPGroup p.
  exact (proP_subgroup_card_ppow _ p hp _ h_fin h_proP).1
```

### 3.3 Required Mathlib lemmas

- `Mathlib.GroupTheory.PGroup.iff_card` (Sylow-finite ↔ p^k order)
- `Mathlib.Topology.Subset.Image` (image of closed under continuous
  is closed; not strictly needed for the finite-image step)

### 3.4 Estimated LOC

~30 lines including the `IsProP`-transfer auxiliary.

## 4. Candidate B — Discharge `sylowProP_inter_trivial`

### 4.1 Mathematical content

Given two distinct-prime Sylows `P : SylowProP G p`, `Q : SylowProP G q`,
`p ≠ q`. Show: `P.toSubgroup ⊓ Q.toSubgroup = ⊥`.

Proof:
1. Pick `x ∈ P.toSubgroup ⊓ Q.toSubgroup`. Want `x = 1`.
2. For each open normal `N ◁ G`, the image of `x` in `G/N` lies in
   both image-of-P (a p-group) and image-of-Q (a q-group). By
   coprimality of `p` and `q`, the image has order `1` in `G/N`.
3. Hence `x` lies in every open normal subgroup `N`. By Hausdorff +
   totally-disconnected (`IsProfiniteGroup`), the intersection of all
   open normal subgroups is `{1}`. So `x = 1`.

### 4.2 Lean skeleton

```lean
theorem sylowProP_inter_trivial
    {G : Type*} [Group G] [TopologicalSpace G]
    (hpf : IsProfiniteGroup G)
    (p q : ℕ) (hp : Fact p.Prime) (hq : Fact q.Prime) (hpq : p ≠ q)
    (P : SylowProP G p) (Q : SylowProP G q) :
    P.toSubgroup ⊓ Q.toSubgroup = ⊥ := by
  -- Step 1: every element x in the intersection projects trivially
  --   into every finite quotient.
  -- Step 2: hpf.isHausdorff or equivalent says ⋂ N = {1} where N
  --   ranges over open normal subgroups.
  sorry  -- ~25 LOC
```

### 4.3 Required Mathlib lemmas

- `Mathlib.Topology.Algebra.Group.Basic` — `IsClosed.subtype` (image
  of compact under continuous → closed in target)
- `Mathlib.GroupTheory.Coprime` — Nat coprime + Lagrange combining
- `hpf.totally_disconnected` style API — depends on what `IsProfiniteGroup`
  exposes in the local file

### 4.4 Caveat

This proof requires that `IsProfiniteGroup` in the local file
*expose* the "intersection of open normals = {1}" property. If it
does not (the local structure has fields like `isClosed`, but the
Hausdorff totally-disconnected piece may need to be derived), then
B is harder than A.

**Recommendation:** A first (most clearly discharge-able), then C,
then B.

## 5. Candidate C — Discharge sorry `sylowProP_normal_of_unique`

### 5.1 Mathematical content

If `Subsingleton (SylowProP G p)` (i.e., the Sylow pro-p subgroup is
unique), then it is normal.

Proof: For any `g : G`, `g P g⁻¹` is also a Sylow pro-p subgroup.
By `Subsingleton`, `g P g⁻¹ = P` as `SylowProP` elements. Reducing
to the underlying `toSubgroup`, `Subgroup.conjugate g P.toSubgroup =
P.toSubgroup` for all `g`. Normality.

### 5.2 Lean skeleton

```lean
theorem sylowProP_normal_of_unique {G : Type*} [Group G] [TopologicalSpace G]
    (hpf : IsProfiniteGroup G) (p : ℕ) (hp : Fact p.Prime)
    (hunique : Subsingleton (SylowProP G p))
    (P : SylowProP G p) : P.toSubgroup.Normal := by
  refine ⟨fun n hn g => ?_⟩
  -- The conjugate of P by g is also a SylowProP; uniqueness forces equality.
  -- Use isProP_conj_map at line 226 to build P_conj : SylowProP G p with
  -- toSubgroup = g · P.toSubgroup · g⁻¹.
  sorry  -- ~40 LOC
```

### 5.3 Required Mathlib lemmas

- `Mathlib.GroupTheory.Subgroup.Basic` — `Subgroup.Normal.conj`,
  `Subgroup.conjugate`
- `isProP_conj_map` (already proven at line 226 of the local file)

### 5.4 Estimated LOC

~40 lines. The main complication is rebundling the conjugate as a
`SylowProP` structure (maximality + closedness need to transfer).

## 6. Recommended S2 ACT scope

**S2 ACT (Candidate A — primary):** ship the discharge of
`sylowProP_projects_pgroup` in a small `proofs/Proofs/SylowTheoremOQ03.lean`
file (~50 LOC including imports + namespace + the theorem). Update
`SylowTheoremOQ02.lean` to delete the axiom and replace its uses
with the new theorem. Net axiom count drops 5 → 4.

**S3 ACT (Candidate C — follow-up):** discharge
`sylowProP_normal_of_unique`. Net sorry count drops 1 → 0 for
`SylowTheoremOQ02.lean`.

**S4 ACT (Candidate B — final adjacent):** discharge
`sylowProP_inter_trivial`, **only if** `IsProfiniteGroup` exposes
or can be augmented to expose the "intersection of open normals =
{1}" property. Net axiom count drops 4 → 3.

After S2-S4, OQ-02's status improves from `5 axioms + 1 sorry` to
`2 axioms + 0 sorries`. The remaining axioms (`sylowProP_existence`
and `sylowProP_conjugacy`) are the genuine inverse-limit-construction
load-bearing assumptions; their discharge is deferred to a different
slug (oq-02's open `nextSteps` field).

## 7. Out of scope for this OQ

- Full inverse-limit construction (existence, conjugacy axioms) —
  belongs to OQ-02's own nextSteps or a dedicated future slug.
- Lazard's theorem for pro-p groups of finite rank — also listed in
  OQ-02's `open` field but separate.
- Galois-cohomology / class-field-theory applications — downstream
  consumers.

## 8. Risks and mitigations

| Risk                                                | Mitigation                                                   |
|-----------------------------------------------------|--------------------------------------------------------------|
| `IsProP`-transfer lemma may not exist yet           | Provide a small auxiliary, ~10 LOC, fully mechanical         |
| `IsProfiniteGroup` may not expose totally-disconnected | Defer Candidate B until structure augmented; A and C unaffected |
| `SylowProP` rebundling for conjugate (Candidate C) requires maximality | Lean detail: derive from `isProP_conj_map` + `SylowProP.maximal` |
| Parallel research claims OQ-02 itself               | OQ-03 is *narrow* and complementary — no race                |

## 9. Sister-slug compatibility

`sylow-theorems-oq-01`, `oq-04`, `oq-05` (sisters in the slug family)
are independent of the pro-p direction; their formalisation routes
are not affected by OQ-03's axiom discharges. Downstream consumers
(`inverse-galois`, Galois cohomology) benefit when OQ-02's axiom
count drops.

## 10. Estimated total cost (S1 OBSERVE → S4)

| Phase | Effort      | Lean delta                                |
|-------|-------------|-------------------------------------------|
| S1 OBSERVE | doc-only | +0 Lean (~750 LOC markdown/JSON)         |
| S2 ACT (A) | ~45 min | +50 LOC new file; OQ-02 axiom count 5→4   |
| S3 ACT (C) | ~45 min | +40 LOC into OQ-02; sorry count 1→0       |
| S4 ACT (B) | ~60 min | +30 LOC into OQ-02; axiom count 4→3 (conditional on Profinite API) |

Net: **OQ-02 improves from `5 axioms + 1 sorry` to `3 axioms + 0
sorries`**; gallery status `axiomatized` retained with a stronger
mathematical claim.
