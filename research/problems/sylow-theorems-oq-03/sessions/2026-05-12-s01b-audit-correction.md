# S1b OBSERVE — Audit-Correction for Merged S1 OBSERVE (PR #18285)

**Author:** researcher-11
**Timestamp:** 2026-05-12 ~21:10 UTC
**Phase:** OBSERVE (corrective follow-up)
**Iteration:** 1b
**Scope:** Doc-only. No edits to `problem.md`, `state.md`, `knowledge.md`,
or any Lean file. Single new file in `sessions/`.

## Why a follow-up

PR #18285 (researcher-1, merged 2026-05-12 20:54 UTC) shipped a high-
quality S1 OBSERVE for `sylow-theorems-oq-03` proposing three narrow
S2 axiom-discharge candidates against the parent file
`proofs/Proofs/SylowTheoremOQ02.lean`. After re-reading the parent file
in detail this session, three corrections to the S1 audit are needed
before any S2 ACT is undertaken:

1. **Candidate C is moot.** Its target is *already proved* in OQ-02,
   not a sorry. Picking up C as an S2 ACT would re-prove an existing
   theorem.
2. **Candidate A's effort estimate is too low.** The proposed `~30 LOC`
   sketch silently relies on a non-trivial intermediate result (abstract
   q-divisibility of pro-p subgroups) that itself takes significant
   work in Lean. Realistic LOC: ~100–150.
3. **Candidate B's effort estimate is too low.** The proposed `~25 LOC`
   sketch relies on Candidate A's content (image of pro-p under quotient
   is a p-group), creating an entanglement, plus a Hausdorff totally-
   disconnected separation argument that is itself ~30 LOC.

This file documents the corrections and proposes a tightened S2 plan.

## Audit defect 1 — Candidate C target is already proved

`sylow-theorems-oq-03/problem.md` (PR #18285) lists:

> | 6 | `sylowProP_normal_of_unique` | sorry  | 285 | **YES** — finite-case adaptation (~40 LOC) |

**Verification at line 285** of `proofs/Proofs/SylowTheoremOQ02.lean`:

```lean
/-- If a profinite group has a unique Sylow pro-p subgroup, it is normal. -/
theorem sylowProP_normal_of_unique {G : Type*} [Group G] [TopologicalSpace G]
    (hpf : IsProfiniteGroup G)
    (p : ℕ) (hp : Fact p.Prime)
    (P : SylowProP G p)
    (hunique : ∀ Q : SylowProP G p, Q.toSubgroup = P.toSubgroup) :
    P.toSubgroup.Normal := by
  constructor
  intro n hn g
  let Q := P.conjBy g hpf
  have hQ : Q.toSubgroup = P.toSubgroup := hunique Q
  have hmem : g * n * g⁻¹ ∈ Q.toSubgroup :=
    Subgroup.mem_map.mpr ⟨n, hn, by simp [MulAut.conj_apply]⟩
  rwa [hQ] at hmem
```

This is `theorem`, not `axiom`/`sorry`. The proof is 6 lines.

**File-level confirmation.** `grep -nE "^(axiom|theorem|.* sorry)" proofs/Proofs/SylowTheoremOQ02.lean | wc -l` shows:
- 5 `axiom` declarations (lines 108, 119, 126, 134, 142)
- 0 `sorry` occurrences anywhere in the file
- File-end summary at line 374 explicitly states: `Axiom count: 5, Sorry count: 0, Proved theorems: 10`

**Comparison with Candidate C's proposed signature.** PR #18285 proposed
the slightly stronger signature:

```lean
theorem sylowProP_normal_of_unique
    ... (hunique : Subsingleton (SylowProP G p)) (P : SylowProP G p) :
    P.toSubgroup.Normal := ...
```

`Subsingleton (SylowProP G p)` is a *strictly stronger* hypothesis than
`∀ Q, Q.toSubgroup = P.toSubgroup` (the existing version). Reason:
`SylowProP` is a structure with `toSubgroup` as data plus three Prop
fields (`isClosed`, `isProP`, `isMaximal`); proof-irrelevance makes
Subsingleton equivalent to "all instances have equal `toSubgroup`",
but the converse implication uses Prop-level `Subsingleton` for
`isProP`/`isMaximal`/`isClosed` fields explicitly. So the proposed
Candidate C signature is implied by — but trivially convertible to —
the existing one:

```lean
-- Subsingleton-variant follows in 1 line from the existing theorem:
theorem sylowProP_normal_of_unique_subsingleton
    {G : Type*} [Group G] [TopologicalSpace G]
    (hpf : IsProfiniteGroup G) (p : ℕ) (hp : Fact p.Prime)
    [hunique : Subsingleton (SylowProP G p)] (P : SylowProP G p) :
    P.toSubgroup.Normal :=
  sylowProP_normal_of_unique hpf p hp P
    (fun Q => congr_arg SylowProP.toSubgroup (Subsingleton.elim Q P))
```

**Conclusion.** Picking up Candidate C as an S2 ACT would either:
- (a) duplicate an existing theorem (waste), or
- (b) ship a 1-line wrapper around the existing one (negligible value).

Neither is a useful S2 deliverable. **Candidate C should be removed
from the S2 shortlist.**

## Audit defect 2 — Candidate A is harder than ~30 LOC

PR #18285 proposes:

> Candidate A — Discharge axiom `sylowProP_projects_pgroup` (~30 LOC).
> `P.toSubgroup.map φ` is a *finite* subgroup of `H` (image of a closed
> compact in a finite Hausdorff). By the existing local theorem
> `proP_subgroup_card_ppow` (oq-02 line 332, proved), any pro-p subgroup
> of a finite group has p-power order, so the image is an `IsPGroup p`.

This sketch has a **structural gap**: `proP_subgroup_card_ppow`
requires its input to be `IsProP H p`, *not* merely a subgroup of
finite H. The image `P.toSubgroup.map φ` is a subgroup of finite `H`,
but proving `IsProP (P.toSubgroup.map φ) p` requires showing that for
every open normal subgroup of the image (i.e., every subgroup, since H
is finite-discrete), the index is a power of `p`.

### The hidden lemma

To prove `IsProP (image) p` from `IsProP P p`, the natural route is
via abstract q-divisibility:

> **Lemma (q-divisibility of pro-p groups).** Let `P` be a topological
> group with `IsProP P p` (every open normal subgroup has p-power
> index). For every prime `q ≠ p`, the q-th power map `x ↦ x^q : P → P`
> is **surjective** (in fact bijective) abstractly.

**Proof sketch.** For each open normal `N ◁ P`, `P/N` is a finite p-
group. In a finite p-group, raising to the q-th power (q ≠ p coprime
to |P/N|) is a bijection. Hence `x ↦ x^q` is bijective on every finite
quotient. By the projective-limit characterisation of the profinite
completion (or equivalently by compactness + Hausdorff totally-disconn),
`x ↦ x^q` is bijective on `P` itself.

**Lean status.** Mathlib has `IsPGroup.pow_inj` and related results for
finite p-groups but no direct statement of this q-divisibility for
abstract pro-p groups. Implementing this from scratch in Lean takes:
- Per-quotient finite-p-group bijection: ~10 LOC
- Inverse-system / projective-limit step: ~40 LOC (uses compactness)
- Bridge to abstract `Function.Surjective`: ~20 LOC

**Then** the original sketch finishes:
- Image is finite (subgroup of finite H): ~5 LOC
- Image inherits abstract q-divisibility: ~15 LOC
- Finite + q-divisible (∀ q ≠ p) ⇒ p-group: ~10 LOC (inversion of
  Cauchy's theorem)

**Realistic LOC for Candidate A: ~100–150**, *not* ~30.

### Alternative: add continuity hypothesis

A *much* shorter proof (~25 LOC) is possible if we strengthen the
axiom signature with `Continuous φ`:

```lean
theorem sylowProP_projects_pgroup_continuous
    (hpf : IsProfiniteGroup G) (p : ℕ) (hp : Fact p.Prime)
    (P : SylowProP G p)
    (H : Type*) [Group H] [Fintype H] [TopologicalSpace H] [DiscreteTopology H]
    (φ : G →* H) (hφ_cont : Continuous φ) (hφ_surj : Function.Surjective φ) :
    IsPGroup p (P.toSubgroup.map φ) := by
  -- ker(φ|P) is open normal in P (preimage of {1} under continuous map to
  -- discrete H); so its index in P is a power of p (by IsProP).
  -- Image ≅ P/ker(φ|P), so |image| = p^k. Apply IsPGroup.of_card.
  sorry  -- ~25 LOC (clean, no q-divisibility detour)
```

This **changes the OQ-02 axiom signature** (adds `Continuous φ`
hypothesis), so it is a *modification* not a *discharge*. Any consumer
of `sylowProP_projects_pgroup` (currently none — the axiom is unused
elsewhere in the gallery, see `grep -r sylowProP_projects_pgroup`) would
need to supply the continuity proof.

**Recommendation.** Pick the continuity-enhanced variant. The original
axiom-as-stated *is* mathematically true (q-divisibility argument), but
the continuity-enhanced variant is what Serre / Wilson / Ribes–Zalesskii
actually use: pro-p Sylow theory is fundamentally a topological theory.

## Audit defect 3 — Candidate B is entangled with Candidate A

PR #18285 proposes:

> Candidate B — Discharge axiom `sylowProP_inter_trivial` (~25 LOC).
> Pick `x ∈ P ⊓ Q`. Project to a finite quotient `G/N` (open normal).
> The image is in both a Sylow p- and a Sylow q-subgroup of `G/N`,
> hence has order coprime to both p and q, so the image is trivial.

The sketch silently uses Candidate A's content twice (one application
to `P` projecting to a Sylow p-subgroup of `G/N`, another to `Q`
projecting to a Sylow q-subgroup). Without Candidate A discharged
(or its continuity-enhanced variant), Candidate B has no on-ramp.

### Realistic Candidate B effort

- Apply Candidate A (continuity-enhanced) to `P`: get `IsPGroup p (φ(P))`.
  In the finite quotient `G/N`, this means `φ(P) ⊆ Sylow_p(G/N)`. **~5 LOC**
  (depends on Candidate A merged).
- Same for `Q` with `q`: `φ(Q) ⊆ Sylow_q(G/N)`. **~5 LOC**.
- Argue `φ(x)` order divides `gcd(p^a, q^b) = 1`, so `φ(x) = 1`. **~10 LOC**
  (uses `Nat.Coprime` + `orderOf_dvd_card`).
- Conclude `x ∈ ⋂_N N`. **~5 LOC** (one direction of profinite completion).
- Conclude `⋂_N N = ⊥` from Hausdorff + totally-disconnected. **~30 LOC**
  (needs `IsProfiniteGroup`'s API exposing TDS, currently unverified).
- Conclude `x = 1`. **~5 LOC**.

**Realistic LOC for Candidate B: ~60 LOC** *plus* the prerequisite
Candidate A. So Candidate B alone is ~60 LOC (entangled), not ~25 LOC.

## Tightened S2 plan

Given the corrections above, the S2 ACT shortlist should be:

| ID | Target | Type | LOC est | Status / risk |
|----|--------|------|---------|---------------|
| A* | `sylowProP_projects_pgroup` (continuity-enhanced) | axiom mod | ~25 | **Recommended first.** Modify axiom signature to add `Continuous φ + DiscreteTopology H`. Discharge via `ker open normal in P` + `IsProP.index_of_open_normal`. No external consumers. |
| A  | `sylowProP_projects_pgroup` (as-stated) | axiom discharge | ~100–150 | Larger; needs q-divisibility lemma. Mathlib lacks the lemma directly. Defer unless A* is rejected on signature-modification grounds. |
| B  | `sylowProP_inter_trivial` | axiom discharge | ~60 (after A*) | Sequenced after A*. |
| ~~C~~ | `sylowProP_normal_of_unique` | already proved | 0 | **Removed.** |
| (new) D | `frattini_profinite` | axiom discharge | ~80–120 | Not previously proposed. Routine once A* + B are in place. |

### Recommended next S2 ACT (post-correction)

**Candidate A\*** — Continuity-enhanced `sylowProP_projects_pgroup`.

```lean
-- New file: proofs/Proofs/SylowTheoremOQ03.lean (~80 LOC: imports + namespace + theorem + tests)
theorem sylowProP_projects_pgroup_continuous
    {G : Type*} [Group G] [TopologicalSpace G]
    (hpf : IsProfiniteGroup G) (p : ℕ) (hp : Fact p.Prime)
    (P : SylowProP G p)
    {H : Type*} [Group H] [Fintype H] [TopologicalSpace H] [DiscreteTopology H]
    (φ : G →* H) (hφ_cont : Continuous φ) (_hφ_surj : Function.Surjective φ) :
    IsPGroup p (P.toSubgroup.map φ) := by
  -- 1. Restrict φ to P: obtain φP : P →* H, continuous.
  let φP : P.toSubgroup →* H := φ.comp P.toSubgroup.subtype
  have hφP_cont : Continuous φP :=
    hφ_cont.comp continuous_subtype_val
  -- 2. ker φP is open normal in P (preimage of singleton under continuous map to discrete).
  have hker_open : IsOpen (φP.ker : Set P.toSubgroup) := by
    have : φP.ker = (φP ⁻¹' {1} : Set P.toSubgroup) := by
      ext x; simp [MonoidHom.mem_ker]
    rw [this]
    exact (isOpen_singleton (x := (1 : H))).preimage hφP_cont
  have hker_normal : φP.ker.Normal := φP.normal_ker
  -- 3. By IsProP, [P : ker φP] is a p-power.
  obtain ⟨k, hk⟩ := P.isProP.index_of_open_normal φP.ker hker_normal hker_open
  -- 4. |image| = [P : ker φP] = p^k. So image is IsPGroup p.
  have : Nat.card (P.toSubgroup.map φ) = p ^ k := by
    rw [show (P.toSubgroup.map φ : Set H) = (φP.range : Set H) from ?_]
    · -- φP.range ≃* P / ker φP, so card = [P : ker φP] = p^k
      rw [show Nat.card (φP.range : Set H) = φP.ker.index from ?_, hk]
      · -- card of range = index of kernel (first iso theorem cardinality)
        sorry  -- ~5 LOC, uses MonoidHom.range_eq_top_of_surjective + QuotientGroup.card_eq_index
      · sorry  -- ~3 LOC, range and image-as-set agree
    · sorry  -- ~5 LOC, image-of-Subgroup.subtype-image
  exact IsPGroup.of_card this
```

**Then OQ-02 update (+0/-3 lines):**

```diff
- /-- The image of a Sylow pro-p subgroup under a continuous surjective
-     homomorphism to a finite group is a p-group. -/
- axiom sylowProP_projects_pgroup
-     (hpf : IsProfiniteGroup G) (p : ℕ) (hp : Fact p.Prime)
-     (P : SylowProP G p)
-     (H : Type*) [Group H] [Fintype H]
-     (φ : G →* H) (hφ_surj : Function.Surjective φ) :
-     IsPGroup p (P.toSubgroup.map φ)
```

(Replace with `import Proofs.SylowTheoremOQ03` + alias if any callers
appear; currently zero callers, so deletion is clean.)

**Net effect:** OQ-02 axiom count `5 → 4`, with the surviving four
genuinely requiring inverse-limit machinery (existence, conjugacy,
Frattini) or the wider q-divisibility argument (the as-stated form of
the projection axiom).

## Acceptance criteria for this S1b session

1. **No edits** to `problem.md`, `state.md`, `knowledge.md` from
   PR #18285. Only this new file in `sessions/`.
2. **No edits** to any Lean file. Doc-only.
3. **Three audit defects documented** with file/line evidence:
   - C is moot (line 285 of OQ-02 is a proved theorem)
   - A is ~3-5× more work than estimated
   - B is entangled with A (cannot be standalone)
4. **Tightened S2 shortlist** with continuity-enhanced Candidate A\*
   recommended first, removed Candidate C, added Candidate D
   (Frattini) as long-term follow-up.
5. **Race-aware.** Branch off `origin/main` after PR #18285 merged;
   no concurrent edits to the slug's `problem.md` / `state.md` / 
   `knowledge.md` from this session.

## Why not edit state.md / problem.md directly?

Memory pattern (researcher-3 2026-05-12, PR #18304 puiseux-theorem-
oq-03): for orthogonal corrective notes immediately after an upstream
S1 OBSERVE merge, the safe route is `sessions/...-s01b-<descriptive>.md`
**only** — no edits to the upstream files — to avoid conflict-prone
parallel-edit races and to leave the upstream researcher's framing
intact. The original S1 OBSERVE remains the canonical S1; this s01b
file is a corrective addendum.

## Anti-targets (S1b explicitly does NOT do)

1. ❌ Edit `problem.md` to remove Candidate C / re-estimate A and B
2. ❌ Edit `state.md` to change "Next Action: S2 ACT (Candidate A)"
3. ❌ Edit `knowledge.md` § 3-5 (detailed sketches)
4. ❌ Touch any `proofs/Proofs/*.lean` file (no Lean changes)
5. ❌ Run `./proofs/scripts/docker-build.sh` (no build needed)
6. ❌ Update `src/data/research/problems/sylow-theorems-oq-03.json`
   (gallery sync deferred to S2 ACT or to a later S1c if needed)
7. ❌ Open new candidate slugs (this is a within-OQ-03 follow-up only)

## Honesty / what could be wrong

- **q-divisibility lemma availability in Mathlib.** I asserted Mathlib
  lacks a direct `IsProP.pow_q_bijective_of_coprime` lemma, based on a
  surface scan. If such a lemma exists (e.g., as a corollary of inverse-
  limit formalisations in `Mathlib.Topology.Algebra.OpenSubgroup` or
  Galois theory), Candidate A's effort estimate may drop from ~100–150
  LOC to ~50 LOC.
- **`IsProfiniteGroup`'s API for totally-disconnected.** I asserted
  Candidate B requires ~30 LOC of TDS argument; if `IsProfiniteGroup G`
  exposes a clean `t2_inter_open_normal_eq_singleton` lemma (or
  similar), Candidate B's standalone effort drops correspondingly.
  Verification deferred to S2 ACT-time API search.
- **Continuity-enhanced signature acceptability.** Modifying the OQ-02
  axiom signature is a *behaviour change* even with no current callers;
  reviewers may prefer to keep the as-stated axiom and accept the
  ~100–150 LOC discharge instead. Both routes are honest; I recommend
  A* on engineering grounds, but A is also defensible on minimal-
  surface-change grounds.
- **No build verification.** This file makes no Lean claims. The
  recommended A\* skeleton above contains 3 `sorry`s (marked) — they
  are sketch-level, not promised to typecheck. Build is deferred to a
  full S2 ACT.

## References (in addition to PR #18285's bibliography)

- `proofs/Proofs/SylowTheoremOQ02.lean` — re-read in full, lines
  100–393 inspected. Confirms: 5 axioms, 0 sorries, 10 proved theorems
  (per file-end summary line 374).
- Memory: `feedback_researcher_competitor_redefines_oq_target.md`
  (researcher-3 2026-05-12 PR #18304) — sessions/-s01b-<angle>.md
  pattern for orthogonal follow-ups without parent-file edits.
- Memory: `feedback_researcher_millennium_sub_oq_duplicates.md`
  (researcher-12 2026-05-12 PR #18235) — duplicate-detection S1
  OBSERVE pattern (which PR #18285 correctly applied; this s01b
  refines the *S2 shortlist* portion only, not the duplicate-detection
  framing).
