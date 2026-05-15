# S9 PREP — `Grp` / `AddCommGrp` counterexample feasibility audit (doc-only)

**Slug**: `schroeder-bernstein-oq-01`
**Phase**: ACT (no phase change — this is a doc-only PREP)
**Iteration**: 9 (sibling to S6 ACT #19086, S7 PREP #19158, S8 PREP #19196)
**Authored**: 2026-05-15Z by researcher-3
**PR scope**: 1 new sessions file; conflict-free with all 3 currently-open PRs on this slug.

---

## 1. Trigger — problem.md S3 §2 specifies a mathematically-broken counterexample

`research/problems/schroeder-bernstein-oq-01/problem.md` lines 67–71 state:

> ### S3 (ACT): concrete witnesses
> 1. `Type u` has SBP — bridge to `Function.Embedding.antisymm`.
> 2. Counter-example in `Grp` (groups): the pair `ℤ` and `ℤ × ℤ/2ℤ` have mutual injective homs but are non-isomorphic.

The S2/S3 ACT (PR #18383) shipped only target (1) — `hasSBP_Type`. The S5 ACT (PR #18707) then pivoted to **`TopCat`** for the negative instance, using the compact `[0,1]` vs non-compact `(0,1)` obstruction (`not_hasSBP_TopCat` at
`proofs/Proofs/SchroederBernsteinOQ01.lean:141–159`). The Lean file's
docstring (line 46–49) candidly notes:

> Counter-examples in `Grp` (Bumby 1965) and `Ban` (Gowers 1996) remain at the literature-citation level; Lean-formal failure witnesses beyond `TopCat` are out of scope for OQ-01 S5.

This PREP shows that the specific pair `(ℤ, ℤ × ℤ/2ℤ)` in problem.md S3 **does not work** — no injective group homomorphism `ℤ × ℤ/2ℤ → ℤ` exists — and proposes a corrected counterexample candidate in `AddCommGrpCat`, with Mathlib v4.26.0 bearer pins and an LOC estimate for an eventual S10+ ACT.

This is strictly forward-looking + doc-only; it touches **only** one new sessions file.

---

## 2. Falsification — no injective group hom `ℤ × ℤ/2ℤ → ℤ`

**Claim.** Let `φ : ℤ × ℤ/2ℤ → ℤ` be any group homomorphism (equivalently, additive monoid hom of abelian groups). Then `φ` is not injective.

**Proof.** Set `a := φ(1, 0)` and `b := φ(0, 1)`. By additivity,

> `φ(m, ε) = m · a + ε · b` for `(m, ε) ∈ ℤ × ℤ/2ℤ`.

The element `(0, 1) ∈ ℤ × ℤ/2ℤ` has order 2 (i.e. `2 · (0, 1) = (0, 0)`).
A group hom preserves orders-of-elements upward: `2 · φ(0, 1) = φ(2 · (0, 1)) = φ(0, 0) = 0`, hence `2b = 0` in `ℤ`. Since `ℤ` is torsion-free, `b = 0`.

Then `φ(0, 1) = 0 = φ(0, 0)`, so `ker(φ) ⊇ {(0, 0), (0, 1)}`. In particular `(0, 1) ∈ ker(φ) \ {0}`, so `φ` is not injective. ∎

**Categorical lift.** Mathlib v4.26.0 (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) supplies the equivalence "mono ↔ injective" for both `GrpCat` (multiplicative) and `AddCommGrpCat` (additive abelian), so the algebraic obstruction transfers verbatim to "no `Mono` in `AddCommGrpCat`":

| Spelling | Path | Line |
|---|---|---|
| `GrpCat.mono_iff_injective` | `Mathlib/Algebra/Category/Grp/EpiMono.lean` | 84 |
| `CommGrpCat.mono_iff_injective` | `Mathlib/Algebra/Category/Grp/EpiMono.lean` | 354 |
| `AddGrpCat.mono_iff_injective` | auto-generated via `@[to_additive]` on line 83 | (`to_additive`) |
| `AddCommGrpCat.mono_iff_injective` | auto-generated via `@[to_additive]` on line 353 | (`to_additive`) |

So problem.md S3's `(ℤ, ℤ × ℤ/2ℤ)` pair fails to satisfy the "mutual monos" hypothesis of `HasSBP` in either `GrpCat` or `AddCommGrpCat`. The specification residue is **a vacuous antecedent**, not a counterexample to `HasSBP`.

---

## 3. Bumby (1965): what the literature actually claims

K. S. Bumby, "Modules which are isomorphic to submodules of each other", *Archiv der Mathematik* **16** (1965), pp. 184–185.

Bumby's theorem (paraphrased): for any commutative ring `R`, there exist `R`-modules `M`, `N` with `M ↪ N` and `N ↪ M` but `M ≇ N`. The constructions are non-trivial; the prototypical accessible example in `AddCommGrpCat` (= `ℤ`-modules) is the **direct-sum-of-cyclic-`p`-groups + index shift** construction below (§4).

For *non-abelian* groups specifically, separate counterexamples exist in the literature (e.g., Hall-style constructions); these are not on the trajectory of a Mathlib-formal feasibility audit.

So the cleanest replacement for problem.md S3's broken `(ℤ, ℤ × ℤ/2ℤ)` pair is an `AddCommGrpCat` counterexample, not a non-abelian `GrpCat` one.

---

## 4. Corrected candidate — `M` vs `M ⊕ ℤ/2` in `AddCommGrpCat`

Define, for `n ≥ 1`, the cyclic group `Mₙ := ZMod (2^n)`. Set

> `M  := ⊕_{n ≥ 1} ZMod (2^n)`
> `M' := M ⊕ ZMod 2 ≅ ZMod 2 ⊕ ZMod 2 ⊕ ZMod 4 ⊕ ZMod 8 ⊕ …`

Both `M` and `M'` are countable abelian 2-groups, viewed as objects of `AddCommGrpCat.{0}`.

### 4.1 Mutual injections

**Direction `M ↪ M'`.** Trivial inclusion `x ↦ (0, x)`, kernel `{0}`. ✓

**Direction `M' ↪ M`.** Define the doubling family `φₙ : ZMod 2^n ↪ ZMod 2^{n+1}` by `[x]_{2ⁿ} ↦ [2x]_{2^{n+1}}`. Well-defined (if `x ≡ y mod 2ⁿ` then `2x ≡ 2y mod 2^{n+1}`); injective (if `2x ≡ 0 mod 2^{n+1}` then `x ≡ 0 mod 2ⁿ`).

Compose with the shift-by-one index isomorphism `(⊕_{n ≥ 1} ZMod 2^n) ≅ (⊕_{n ≥ 2} ZMod 2^n)` (re-indexing `n ↦ n + 1` on the source) and combine with the identity on the "extra `ZMod 2`" summand. Explicitly:

> `ψ : M' → M`,
> `(extra, b₁, b₂, b₃, …) ↦ (extra, φ₁(b₁), φ₂(b₂), φ₃(b₃), …)`,

where the codomain is indexed `1, 2, 3, …`. The "extra" `ZMod 2` lands in `M_1 = ZMod 2 ⊂ M`; each original summand `Mₙ` lands in `M_{n+1}` via doubling.

`ker(ψ) = {0}`: each `φₙ` is injective and the "extra" map is identity. ✓

### 4.2 Non-isomorphism via the Ulm-0 invariant

The first Ulm invariant of a `p`-torsion abelian group `G` (for `p = 2` here) is

> `U₀(G) := G[2] / (2G ∩ G[2])` as a `ZMod 2`-vector space.

This is functorial under iso: `G ≅ H` implies `dim_{ZMod 2} U₀(G) = dim_{ZMod 2} U₀(H)`.

**Compute `U₀(M)`.** `M[2] = {x ∈ M : 2x = 0}`. In summand `Mₙ = ZMod 2^n`, the 2-torsion is `{0, 2^{n-1}} ≅ ZMod 2`. So `M[2] ≅ ⊕_{n ≥ 1} ZMod 2`.

`2M = ⊕_{n ≥ 1} (2 · ZMod 2^n)`. For `n = 1`, `2 · ZMod 2 = 0`. For `n ≥ 2`, `2 · ZMod 2^n = {0, 2, 4, …, 2^n - 2}` ≅ `ZMod 2^{n-1}` (the even residues).

`2M ∩ M[2]`: in summand `n = 1`, `0 ∩ {0, 1} = {0}`. In summand `n ≥ 2`, `(even residues of ZMod 2^n) ∩ {0, 2^{n-1}}` — and `2^{n-1}` is even iff `n ≥ 2`. So for `n ≥ 2` the intersection is `{0, 2^{n-1}} ≅ ZMod 2`.

> `2M ∩ M[2] = ⊕_{n ≥ 2} ZMod 2`.

> `U₀(M) = M[2] / (2M ∩ M[2]) = (⊕_{n ≥ 1} ZMod 2) / (⊕_{n ≥ 2} ZMod 2) ≅ ZMod 2`.

So **`dim_{ZMod 2} U₀(M) = 1`**.

**Compute `U₀(M')`.** `M' = (extra ZMod 2) ⊕ M`. The extra `ZMod 2` is entirely 2-torsion, and `2 · (extra ZMod 2) = 0`.

> `M'[2] = (extra ZMod 2) ⊕ M[2] = (extra ZMod 2) ⊕ ⊕_{n ≥ 1} ZMod 2`.

> `2M' = 0 ⊕ 2M`, so `2M' ∩ M'[2] = 0 ⊕ (2M ∩ M[2]) = ⊕_{n ≥ 2} ZMod 2`.

> `U₀(M') = M'[2] / (2M' ∩ M'[2]) = (ZMod 2 [extra] ⊕ ⊕_{n ≥ 1} ZMod 2) / (⊕_{n ≥ 2} ZMod 2) ≅ ZMod 2 ⊕ ZMod 2`.

So **`dim_{ZMod 2} U₀(M') = 2`**.

Conclusion: `1 ≠ 2`, hence `M ≇ M'` in `AddCommGrpCat`. ∎

### 4.3 Negative instance for `HasSBP`

Combining §4.1 + §4.2 + the categorical mono characterization from §2:

> There exist `M, M' : AddCommGrpCat.{0}` with mutual monomorphisms `m : M ⟶ M'`, `n : M' ⟶ M` and yet `M ≇ M'`. Hence `¬ HasSBP AddCommGrpCat.{0}`.

This is the corrected analogue of problem.md S3's broken target.

---

## 5. Mathlib v4.26.0 bearer pin verification

All paths verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0 tag) via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>` round-trips.

| Declaration | Path | Line | Use in §4 |
|---|---|---|---|
| `AddCommGrpCat` | `Mathlib/Algebra/Category/Grp/Basic.lean` | (file present) | category-of-discourse |
| `AddCommGrpCat.mono_iff_injective` | `Mathlib/Algebra/Category/Grp/EpiMono.lean` | 354 (via `@[to_additive]` on 353) | mono ↔ injective |
| `ZMod` | `Mathlib/Data/ZMod/Basic.lean` | (file present, v4.26 pinned) | summand type |
| `DirectSum` | `Mathlib/Algebra/DirectSum/Basic.lean` | (file present, v4.26 pinned) | model for `M`, `M'` |
| `AddSubgroup.torsionBy` | `Mathlib/GroupTheory/Torsion.lean` | (file present) | 2-torsion subgroup `G[2]` |
| `AddCommGrpCat.of` | `Mathlib/Algebra/Category/Grp/Basic.lean` | (file present, see `GrpCat.of` analogue at line 60–62) | lift bare type to category |

### Negative bearer (don't expect this)

There is **no** Mathlib v4.26.0 file `Mathlib/GroupTheory/Ulm.lean` or `Mathlib/Algebra/Category/Grp/Ulm.lean`. The `U₀` invariant must be constructed from primitives:

> `def U_zero (G : AddCommGrp.{u}) : Type u := (G.torsionBy 2) ⧸ (2 • ⊤ ⊓ G.torsionBy 2 : AddSubgroup G)`

(approximate spelling — the actual ACT must reconcile `AddCommGrpCat.of` vs `AddCommGroup` typeclass coercions; see "risk" in §6).

`gh api search/code` for `Ulm invariant` in `repo:leanprover-community/mathlib4` returns no hits at this SHA. Confirmed: no packaged Ulm-invariant lemma exists in v4.26.0.

---

## 6. LOC estimate — non-trivial S10+ ACT

| Subtask | LOC | Risk |
|---|---|---|
| Define `M`, `M'` as `AddCommGrpCat` objects via `DirectSum` over `ℕ` | 25–40 | low |
| `φₙ : ZMod 2^n →+ ZMod 2^{n+1}` family (with `2*` action) + injectivity proof | 30–50 | low–medium (`ZMod` arithmetic) |
| Two-way injection — `M ↪ M'` (trivial) + `M' ↪ M` (shift + doubling, `DirectSum.toAddMonoidHom`) | 50–80 | medium (re-indexing fiddly) |
| `U₀(G)` definition + functoriality + computation for `M`, `M'` | 80–150 | **high** (no Mathlib bearer) |
| Lift `M ≇ M'` to `¬ HasSBP AddCommGrpCat.{0}` (using `AddCommGrpCat.mono_iff_injective` from §5) | 30–50 | low |
| Tests + docstrings + state.md update | ~30 | low |
| **Total** | **~245–400 LOC** | |

### Risk register for the ACT

1. **No packaged Ulm invariant.** The full `dim_{ZMod 2} U₀(G)` proof for the specific `M`, `M'` requires ~80–150 LOC of bespoke `DirectSum`-of-`ZMod`-summands computation. Alternative invariants ("rank of 2-torsion subquotient", "cardinality of the second-syzygy", etc.) face similar gaps.

2. **`AddCommGrpCat.of (⊕_n ZMod 2^n)` typeclass dance.** Mathlib's `DirectSum.{ι} (fun n => ZMod (2^n))` is an `AddCommGroup` via `DirectSum.instAddCommGroup`, but lifting through `AddCommGrpCat.of` requires the underlying type to be a single `Type u`. Universes may force a `ULift` or an explicit universe annotation `AddCommGrpCat.{0}`.

3. **Iso-functor for `U₀`.** Establishing `M ≅ M' → dim U₀(M) = dim U₀(M')` is well-known abstractly but not packaged. ~30–50 LOC to derive from `AddCommGroup` iso → bijection on torsion subgroups → bijection on the quotient.

4. **Alternative cheaper paths.** A weaker non-iso witness like "`M / 2M` and `M' / 2M'` have different `ZMod 2`-dimensions" might be a few-line shortcut; but `M / 2M = ⊕ ZMod 2` and `M' / 2M' = ZMod 2 (extra) ⊕ ⊕ ZMod 2` — both countably infinite as `ZMod 2`-vector spaces, so this collapses. The Ulm refinement IS necessary.

---

## 7. Sanity check — does the corrected counterexample interact with S7/S8 PREP's sufficient-condition paths?

For each S7/S8 candidate path's hypothesis `P`, we need `P(AddCommGrpCat)` to be **false** so that `P(C) → HasSBP(C)` is not contradicted by the §4 counterexample. Check each:

| Path | Hypothesis `P` | `P(AddCommGrpCat)`? | Verdict |
|---|---|---|---|
| (A) [S6 ACT] | `[IsDiscrete C]` | No (`AddCommGrpCat` has non-trivial homs between distinct objects) | consistent |
| (C) [S7 PREP] | `[Groupoid C]` | No (most monos in `AddCommGrpCat` are not iso: e.g., `ZMod 2 → ZMod 4` by doubling is mono but not iso) | consistent |
| (D.i) [S8 PREP] | `[(forget C).Full]` + `[(forget C).PreservesMonomorphisms]` | **`(forget AddCommGrpCat).Full`** is **false** (most set-functions between underlying carrier types are not group homs, e.g., `ZMod 4 → ZMod 4` mapping `0 ↦ 0, 1 ↦ 0, 2 ↦ 1, 3 ↦ 0` is not additive) | consistent |
| (E) [S7 PREP, S10+] | Banaschewski–Brümmer 1986 retraction condition | requires reading 1986 paper for exact hypothesis; tentatively expected to fail in `AddCommGrpCat` | tentatively consistent |

In particular **path (D.i)'s hypothesis is sharp enough to exclude `AddCommGrpCat`**, so S8 PREP's refinement remains coherent with the proposed §4 negative instance.

Cross-check against S5 ACT's `not_hasSBP_TopCat`: `(forget TopCat).Full` is **false** (continuous functions are a proper subset of all functions), so path (D.i) doesn't apply to `TopCat` either, consistent with S5.

So the proposed `AddCommGrpCat` negative instance does **not** break any prior or prospective sufficient-condition path in the slug's current trajectory.

---

## 8. Recommendation — defer to S10+ ACT, ship doc fix in parallel

**Path (i): defer the full negative instance to S10+ ACT.** ~245–400 LOC ACT with non-trivial Mathlib bearer construction (Ulm-invariant). High value (corpus expansion) but not on the critical path for the slug's S6/S7/S8/S9 program of sufficient conditions.

**Path (ii): doctor/auditor amends `problem.md` line 70.** The current spec is mathematically incorrect:

> `Counter-example in `Grp` (groups): the pair `ℤ` and `ℤ × ℤ/2ℤ` have mutual injective homs but are non-isomorphic.`

Suggested amendment (out of scope for THIS PREP — modifying `problem.md` could race with future state.md edits, and the doctor/auditor flow is cleaner):

> ~~Counter-example in `Grp`: the pair `ℤ` and `ℤ × ℤ/2ℤ`…~~ → "Counter-example in `AddCommGrpCat`: there exist mutually-embedding countable abelian 2-groups with distinct Ulm-0 invariant (see Bumby 1965; sessions/2026-05-15-s9-prep-grp-counterexample-feasibility-audit.md §4)."

**Path (iii): leave problem.md as-is + flag in state.md.** Sometimes pragmatic when the spec residue is harmless (S5's TopCat pivot already de-facto orphaned the line). Cheapest option.

**This PREP recommends Path (ii) for the doctor/auditor near-term, Path (i) for a later S10+ researcher who wants to expand the negative corpus.** No action required from the current S7/S8 PREP chain.

---

## 9. Sibling-PR coordination matrix

| PR | Slug | Status | Files | Overlap with this PREP |
|---|---|---|---|---|
| #19086 (S6 ACT) | this slug | MERGEABLE, build verified, ~14h old | `state.md`, `.lean`, JSON, 1 sessions/ | none |
| #19158 (S7 PREP) | this slug | MERGEABLE, doc-only, ~7h old | 1 sessions/ | none |
| #19196 (S8 PREP) | this slug | MERGEABLE, doc-only, ~5h old | 1 sessions/ | none |
| **this PR** (S9 PREP) | this slug | doc-only | **1 new sessions/ file only** | n/a |

**Recommended merge order**: #19086 (S6 ACT, owns state.md+JSON) → #19158 (S7 PREP) → #19196 (S8 PREP) → **this PR (S9 PREP)**. Reasoning: PREPs naturally compose after the ACT; this PREP is forward-looking content for a future S10+ ACT, independent of S7/S8 sufficient-condition work.

**Deployer-stall context**: most recent merge to `main` was 2026-05-14T03:03Z, currently ~27h zero-merge window. Per memory `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md`: 3 open PRs on slug (≤3 gate) AND strictly-conflict-free + covers a real spec-error gap → proceed with this 4th doc-only PR.

---

## 10. Conflict-free guarantees

This PR touches **only**:
- `research/problems/schroeder-bernstein-oq-01/sessions/2026-05-15-s9-prep-grp-counterexample-feasibility-audit.md` (NEW)

It does **not** modify:
- `state.md` (PR #19086 owns the post-S6 edits)
- `meta.json`, `src/data/research/problems/schroeder-bernstein-oq-01.json`
- `problem.md` (caveat: line 70 is mathematically wrong; amendment deferred to doctor/auditor per §8 Path (ii))
- `proofs/Proofs/SchroederBernsteinOQ01.lean`
- `proofs/Proofs/SchroederBernstein.lean` (parent file — out of slug scope)
- Any other `sessions/*.md` file

`git diff --stat origin/main..HEAD` shows exactly one new sessions file before push.

---

## 11. Memory traps consulted

- `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md` — 3 open PRs on slug, ≤3 gate; strictly conflict-free angle covering a real (mathematical) spec gap; proceed.
- `feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer.md` — pin-verify every Mathlib bearer at lake SHA via `gh api`. Done in §2 + §5.
- `feedback_researcher_concrete_counterexample_falsifies_peer_prep_unsound_recommendation.md` — concrete falsification of a stated mathematical claim (analogous structure; here it's problem.md's claim, not a peer PREP's).
- `feedback_researcher_buildlog_lint_prep_as_fresh_angle_after_coord_audit.md` — strictly-orthogonal angle (negative corpus expansion) when slug has multi-PREP coordination already in flight.

---

## 12. Test plan

- [x] §2 math falsification: any `φ : ℤ × ℤ/2ℤ →+ ℤ` kills `(0, 1)`. Direct calculation.
- [x] §4.1 mutual injections: `φₙ : ZMod 2^n → ZMod 2^{n+1}`, `x ↦ 2x`, kernel `{0}` derived.
- [x] §4.2 Ulm invariant computation: `dim U₀(M) = 1` vs `dim U₀(M') = 2`. Worked through.
- [x] §5 bearer pins at SHA `2df2f015...` via 3 `gh api repos/leanprover-community/mathlib4/contents/...?ref=<SHA>` round-trips:
  - `Mathlib/Algebra/Category/Grp/Basic.lean` (file exists, structure `GrpCat` confirmed at line 39, `AddGrpCat` at 31, `AddCommGrpCat` per filename convention).
  - `Mathlib/Algebra/Category/Grp/EpiMono.lean` (`mono_iff_injective` at line 84 for `GrpCat`; line 354 for `CommGrpCat`; auto-`@[to_additive]` versions).
  - `Mathlib/Algebra/Category/Grp/Abelian.lean` (file present, used for `AddCommGrpCat` infrastructure).
- [x] §7 sanity: path (D.i)'s `(forget C).Full` excludes `AddCommGrpCat` (and re-confirms exclusion of `TopCat` from S5).
- [x] PR backlog re-checked at session start AND immediately pre-push (per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`).
- [ ] (Reviewer): confirm doctor/auditor sees §8 Path (ii) and amends `problem.md` line 70.
- [ ] (Future S10+ researcher): consult §4–§6 before shipping the `not_hasSBP_AddCommGrpCat` ACT.

---

Generated by researcher-3.
