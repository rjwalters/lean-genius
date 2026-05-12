# Current State

**Phase**: ACT (S3c-prep — gallery & parent meta synced to reflect Approach A + Approach B preliminaries; Sylow drift unblocked upstream)
**Since**: 2026-05-12 (S3c-prep, doc-only)
**Iteration**: 5

## Latest Iteration: S3c-prep — gallery + parent meta sync (researcher-9, 2026-05-12)

Doc-only iteration synthesising the four prior iterations into the
gallery & parent meta. No Lean changes; no new theorems or sorries.

**Upstream unblock noted.** `SylowTheoremOQ01.lean` drift (the umbrella
blocker called out in S3a-build-verify) was fixed in commit
`ba135dd66a2` (PR #18160, merged 2026-05-12): four call sites
`(Nat.Prime.prime h.h?).factorization` → `h.h?.factorization`, removing
the `And.factorization` parse error at Mathlib v4.26.0. The
`LagrangeTheoremOQ01OQ01OQ01` and `LagrangeTheoremOQ01OQ01OQ01ApproachB`
files are therefore now expected to build through the umbrella; a
follow-up Docker rebuild is the appropriate next confirmation step but
is gated on Mathlib cold-cache provisioning (~45 min fresh-clone in
researcher worktrees per `feedback_researcher_lake_symlink_broken.md`).

**Deliverables in this iteration:**

1. `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/meta.json`
   - Added `additionalFiles: ["Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean"]`
     so the gallery's leanFile picker discovers the Approach B
     preliminaries file alongside Approach A's main file.
   - Extended `tags` with `approach-b-preliminaries`, `cyclic-units`,
     `ZMod` to reflect S3a/S3b content.
   - Extended `originalContributions` with two new bullets covering
     `isCyclic_units_zmod` / `card_units_zmod` (S3a) and
     `exists_unit_of_order_p` (S3b).
   - Refined `openQuestions[0]` into separate S3c (lift to AddAut) and
     S3d (assemble semidirect product) bullets, with explicit Mathlib
     API leads (`zmodEquivZPowers`, `ZMod.lift`, `SemidirectProduct.card`).

2. `src/data/proofs/lagrange-theorem-oq-01-oq-01/meta.json` (parent)
   - Marked `openQuestions[0]` as partially resolved: the `p = 2`
     specialisation is supplied by this entry (`DihedralGroup q`);
     general-`p` case remains open with Approach B preliminaries
     landed.
   - Added `crossReferences` entry `extended-by` pointing to this
     entry with status summary (Approach A complete, S3a/S3b
     preliminaries landed, S3c/S3d open).

3. `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md`
   - This entry; also records the SylowTheoremOQ01 drift-fix landing.

**No Lean changes**. The two existing Lean files
(`LagrangeTheoremOQ01OQ01OQ01.lean`, `LagrangeTheoremOQ01OQ01OQ01ApproachB.lean`,
6 + 6 declarations across 140 + 152 lines, 0 sorries, 0 axioms) are
unmodified.

## Earlier Iteration: S3a-build-verify (researcher-9, 2026-05-12)

Mechanic-style PR per the S3a-prep state.md "Next Action" (one-shot
umbrella wiring + Docker build).

**Deliverable.** Added two import lines to `proofs/Proofs.lean`:

```
import Proofs.LagrangeTheoremOQ01OQ01OQ01
import Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachB
```

Both lines inserted alphabetically (after
`Proofs.LagrangeTheoremOQ01OQ01`, before `Proofs.LagrangeTheoremOQ01OQ02`).

**Docker build attempt.** `Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachB`
build fails on the transitively-imported `Proofs.SylowTheoremOQ01`,
NOT on the Lagrange S3a building blocks. First errors:

```
Proofs/SylowTheoremOQ01.lean:57:31: Invalid field `factorization`:
  The environment does not contain `And.factorization`
Proofs/SylowTheoremOQ01.lean:60:31: Invalid field `factorization`:
  The environment does not contain `And.factorization`
Proofs/SylowTheoremOQ01.lean:112:9: Tactic `rcases` failed:
  `x✝ : ?m.30` is not an inductive datatype
... (additional cascade errors in SylowTheoremOQ01)
```

The root cause is **pre-existing Mathlib drift** in
`Proofs/SylowTheoremOQ01.lean` at v4.26.0; the file has not been
updated since 2024 (latest commit
`e5c13e673e6` audit-only) while Mathlib's `Nat.factorization` API
moved. `Proofs.SylowTheoremOQ01` is already imported by
`Proofs/Proofs.lean` line 2746 on `origin/main`, so the umbrella
build was already broken before this PR's two new imports — adding
the Lagrange OQ01OQ01OQ01 files does NOT introduce new breakage.

**Lagrange S3a files themselves:** un-verified by this PR's run, but
the dependency chain is
`LagrangeTheoremOQ01OQ01OQ01ApproachB → LagrangeTheoremOQ01OQ01OQ01 → LagrangeTheoremOQ01OQ01 → SylowTheoremOQ01`,
so the cascade prevents any build attempt from reaching the Lagrange
files. The Lagrange S3a content (Approach A's `DihedralGroup` witness
and Approach B's `(ZMod q)ˣ` cyclic-units + order-`p` extraction) is
not implicated.

**Recommended follow-up (separate mechanic-fix PR):** Repair
`SylowTheoremOQ01.lean` by replacing the `And.factorization` /
`rcases` patterns (lines 57, 60, 69, 71, 112, 132, etc.) with the
v4.26.0-correct `Nat.Prime` destructuring (likely
`hp.factorization` is being miscued because `hp : Nat.Prime h.p` got
shadowed by an inner `And.intro`). After Sylow is fixed, the Lagrange
S3a build chain unblocks.

**Files modified by this PR.**
- `proofs/Proofs.lean` — two import lines.
- `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md` —
  this entry.

## Iteration 3: S3a-prep (researcher-12, 2026-05-12)

Approach B preliminaries: created
`proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean` (~165 lines,
3 theorems + 1 instance + 3 examples, 0 sorries, 0 axioms).

Deliverables:

1. **`isCyclic_units_zmod`** (instance): `(ZMod q)ˣ` is cyclic for any
   prime `q` (via Mathlib `isCyclic_of_subgroup_isDomain`).

2. **`card_units_zmod`** (theorem): `Fintype.card (ZMod q)ˣ = q - 1`
   for any prime `q` (via `ZMod.card_units_eq_totient` and
   `Nat.totient_prime`).

3. **`exists_unit_of_order_p`** (theorem): for each prime `p ∣ q - 1`,
   there exists `g : (ZMod q)ˣ` with `orderOf g = p`. Constructed as
   `g₀ ^ ((q - 1) / p)` for a generator `g₀`; the order calculation
   mirrors `Proofs.LagrangeTheoremOQ01OQ03.orderOf_pow_div_of_dvd`
   (Hall's theorem for cyclic groups) using `orderOf_pow'`,
   `Nat.gcd_eq_right`, `Nat.div_dvd_of_dvd`, and `Nat.div_div_self`.

4. **Sanity examples** at `(p, q) = (2, 3), (3, 7), (5, 11)`,
   instantiating the existence theorem at the smallest cases relevant
   to the deferred S3d construction (orders 6, 21, 55 non-abelian
   groups).

Build verification deferred to a follow-up `*-prep` PR per the same
precedent as S2 (`bezout-identity-oq-01-oq-01-oq-01-oq-01` PR #17990,
`cube-root-3-irrational-oq-04` PR #17718). All Mathlib API calls in
this file are already exercised elsewhere in the repository (see
inline `## API verification` block in the new file).

## Earlier Iteration: S2 (researcher-9, 2026-05-12)

Implemented Approach A in `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01.lean`
(140 lines, 6 theorems, 0 sorries, 0 axioms):

1. **Main existence theorem** `exists_noncyclic_of_order_two_mul_odd_prime`
   (lines 55-84): for every odd prime `q`, exhibits `DihedralGroup q` as
   a non-cyclic group of order `2q`. Uses `DihedralGroup.card` and
   `DihedralGroup.not_isCyclic` from Mathlib.

2. **Divisibility certificate** `two_dvd_sub_one_of_odd_prime`
   (lines 86-102): confirms `2 ∣ (q-1)` for any odd prime `q`, certifying
   the OQ's premise.

3. **Four concrete corollaries** (lines 104-139): existence witnesses for
   orders 6 (`DihedralGroup 3 ≅ S₃`), 10 (`D₅`), 14 (`D₇`), 22 (`D₁₁`).

Gallery entry created at `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/`
(meta.json + annotations.json + index.ts) with 4 deep annotations.

Build verification deferred to follow-up `*-prep` PR per the precedent in
`bezout-identity-oq-01-oq-01-oq-01-oq-01` (PR #17990) and
`cube-root-3-irrational-oq-04` (PR #17718). The pinned-rev API was
verified directly via GitHub raw read at S1 and re-confirmed at S2.

## Earlier Iteration: S1 (researcher-10, 2026-05-12)

S1 (researcher-10): Survey three approaches to constructing an explicit
non-cyclic group of order `pq` whenever `p | (q-1)`. Settled on
**Approach A** (specialize to `p = 2`, use Mathlib's `DihedralGroup q`)
as the S2 attack target — single PR, ~50 lines Lean, requires only the
stable `DihedralGroup.card` + `DihedralGroup.not_isCyclic` API.

The parent `Proofs/LagrangeTheoremOQ01OQ01.lean` (169 lines, 13 theorems,
0 sorries, 0 axioms) classifies pq-groups via Sylow theory and proves the
universal cyclic statement `pq_unique_when_coprime` when `p ∤ (q-1)`, plus
the conditional non-abelian fact `lagrange_pq_nonabelian_n_p_eq_q` when
`p | (q-1)` (but only assuming `¬ IsCyclic G`). What is *missing* is an
existence witness for the non-cyclic case: an explicit group `G` with
`|G| = p*q` and `¬ IsCyclic G`. This OQ supplies that.

## Active Approach

**Approach A: Specialize to `p = 2`, use `DihedralGroup q`**

For `q` an odd prime, `DihedralGroup q` has cardinality `2*q = p*q` and
is non-cyclic (`q ≠ 1`). Mathlib provides both facts at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```lean
theorem DihedralGroup.card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n
theorem DihedralGroup.not_isCyclic (h1 : n ≠ 1) : ¬ IsCyclic (DihedralGroup n)
```

The `NeZero q` instance follows from `q` prime (positive); `q ≠ 1` from
`Nat.Prime.one_lt`. The condition `2 | (q - 1)` follows from `q` being
odd (which holds for any prime `q ≠ 2`).

## Blockers

None mathematical.

**Practical**: the `proofs/.lake` symlink in researcher worktrees points
to itself (see `feedback_researcher_lake_symlink_broken.md`), forcing any
Docker build to fresh-clone Mathlib (~25 min). S1 is doc-only, so unaffected.
S2 will need a build verification but can be deferred to a follow-up
`*-prep` PR per the precedent in
`bezout-identity-oq-01-oq-01-oq-01-oq-01` (PR #17990) and
`cube-root-3-irrational-oq-04` (PR #17718).

## Next Action

**S3a-build-rerun OR S3c (action sequence after this iteration)**:

* **S3a-build-rerun** (low-risk, mechanic-style verification PR).
  Now that `SylowTheoremOQ01.lean` v4.26.0 drift was fixed in PR
  #18160, the import chain
  `LagrangeTheoremOQ01OQ01OQ01ApproachB → LagrangeTheoremOQ01OQ01OQ01 → LagrangeTheoremOQ01OQ01 → SylowTheoremOQ01`
  should compile end-to-end. Re-run `./proofs/scripts/docker-build.sh
  Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachB` (the deepest target in
  the chain); on green, flip the gallery `badge` / `status` from
  `verified` *with build-pending caveat* to fully build-verified and
  update both files' implicit "build pending" annotations. Expected
  build time ≈ 45 min on cold worktree cache.

* **S3c (Approach B continuation, substantive Lean addition)**: Lift
  the order-`p` unit `g ∈ (ZMod q)ˣ` produced by
  `exists_unit_of_order_p` to a non-trivial group homomorphism
  `φ : ZMod p →* AddAut (ZMod q)` (note: `AddAut` of the additive
  cyclic group `ZMod q`, *not* `MulAut`; multiplication by a unit is an
  *additive* automorphism of the ring). The natural choice sends
  `1 : ZMod p` to `mulLeft g.val : ZMod q ≃+ ZMod q`. Concrete pieces:

  - `unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q)` via Mathlib's
    `DistribMulAction (ZMod q)ˣ (ZMod q)` infrastructure
    (`MulAction.toEndomorphism` upgraded with the additive
    distributivity instance, or directly `DistribMulAction.toAddEquiv`).
  - Non-triviality of `unitToAddAut g`: equivalent to `g.val ≠ 1` in
    `ZMod q`, follows from `orderOf g = p ≥ 2`.
  - Pack into `ZMod p →* AddAut (ZMod q)` via `zmodEquivZPowers`
    (`Multiplicative (ZMod p) ≃* Subgroup.zpowers g'` for `g' :=
    unitToAddAut g`), or equivalently use `ZMod.lift p ⟨g', hg'⟩` with
    `hg'` the `g' ^ p = 1` certificate from `orderOf` analysis.

  Estimated effort: ~50-80 lines new Lean in `ApproachB.lean`, 1
  session, single PR with Docker build verification.

Outline retained in the "Future Iterations (Deferred)" section below.

The S2 deliverable now in main file (target of S2 iteration):

**S2 (researcher-9, COMPLETE)**: Implement Approach A in a new file
`proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01.lean`. Three deliverables:

1. **Main existence theorem** (~15 lines):
   ```lean
   import Mathlib
   import Proofs.LagrangeTheoremOQ01OQ01

   namespace LagrangeOQ01OQ01OQ01

   /-- When `q` is an odd prime, `DihedralGroup q` is a non-cyclic group
       of order `2q`. This exhibits a non-cyclic witness in the case
       `p = 2`, `q` odd prime (where `p | q - 1` holds because `q - 1` is
       even). -/
   theorem exists_noncyclic_of_order_two_mul_odd_prime
       {q : ℕ} (hq : Nat.Prime q) (hq_ne_two : q ≠ 2) :
       ∃ (G : Type) (_ : Group G) (_ : Fintype G),
         Fintype.card G = 2 * q ∧ ¬ IsCyclic G := by
     haveI : NeZero q := ⟨hq.ne_zero⟩
     refine ⟨DihedralGroup q, inferInstance, inferInstance,
             DihedralGroup.card, ?_⟩
     exact DihedralGroup.not_isCyclic (fun h => hq.one_lt.ne' h.symm)
   ```

2. **Concrete corollaries** matching parent's `order_*_non_unique` lemmas
   (~30 lines, one per case):
   ```lean
   /-- Order 6 = 2 × 3: a non-cyclic group exists (S₃ ≅ DihedralGroup 3). -/
   theorem exists_noncyclic_of_order_6 :
       ∃ (G : Type) (_ : Group G) (_ : Fintype G),
         Fintype.card G = 6 ∧ ¬ IsCyclic G :=
     exists_noncyclic_of_order_two_mul_odd_prime
       (by norm_num : Nat.Prime 3) (by norm_num)

   /-- Order 10 = 2 × 5: a non-cyclic group exists (DihedralGroup 5). -/
   theorem exists_noncyclic_of_order_10 : ... := ...

   /-- Order 14 = 2 × 7: a non-cyclic group exists (DihedralGroup 7). -/
   theorem exists_noncyclic_of_order_14 : ... := ...

   /-- Order 22 = 2 × 11: a non-cyclic group exists (DihedralGroup 11). -/
   theorem exists_noncyclic_of_order_22 : ... := ...
   ```

3. **Gallery entry** at `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/`
   (meta.json + annotations.json + index.ts; ~80 lines). After S2 lands,
   update `lagrange-theorem-oq-01-oq-01` parent meta.json's
   `relatedProofs` / `openQuestions` to mark this OQ as resolved (at least
   for the `p = 2` specialization).

**Estimated effort for S2**: 1 session, single PR, ~50 lines of new Lean
(1 main theorem + 4 corollaries + namespace boilerplate; no helper
lemmas needed because `DihedralGroup.card` and `DihedralGroup.not_isCyclic`
are both direct).

## Future Iterations (Deferred)

**S3+ (Approach B): general `p, q` with `p | (q-1)`**. Construct
`ZMod q ⋊[φ] ZMod p` where `φ : ZMod p →* MulAut (ZMod q)` is non-trivial.
Required pieces:

- ~~(S3a) Show `(ZMod q)ˣ` is cyclic of order `q-1` for `q` prime~~
  **COMPLETE** in `ApproachB.isCyclic_units_zmod` (instance) and
  `ApproachB.card_units_zmod` (theorem).
- ~~(S3b) Extract an element of order `p` from `(ZMod q)ˣ`~~
  **COMPLETE** in `ApproachB.exists_unit_of_order_p` via the
  `g₀ ^ ((q - 1) / p)` construction (Hall's-theorem-for-cyclic-groups
  recipe from `Proofs.LagrangeTheoremOQ01OQ03`).
- (S3c) Lift to a non-trivial hom `φ : ZMod p →* MulAut (ZMod q)`.
- (S3d) Assemble `ZMod q ⋊[φ] ZMod p`, verify `Nat.card = p * q`,
  prove `¬ IsCyclic`.

~200 lines total, 3-4 sessions, multi-PR.

**S4+ (Optional gallery enhancement)**: Add explicit multiplication-table
examples for order-21 and order-55 non-abelian groups as supplementary
content. ~50 lines per case.

## Attempt Counts

- Total attempts: 1 (S1 survey)
- Current approach attempts: 0 (no Lean changes yet)
- Approaches tried: 0 (3 surveyed: A=DihedralGroup q for p=2,
  B=ZMod q ⋊ ZMod p in general, C=direct small-case construction)

## Open files

- `problem.md` — Full problem statement, three approaches, sub-lemma list,
  Mathlib API map.
- `knowledge.md` — S1 session note: parent context, API verification at
  pinned rev, edge-case analysis.

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/problem.md` (~280 lines)
- `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md` (this file)
- `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/knowledge.md` (S1 session note)
- `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-01.json` (research index entry)
