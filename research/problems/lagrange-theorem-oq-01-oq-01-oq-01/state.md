# Current State

**Phase**: ACT (S3c-i — `unitToAddAut` + injectivity + `exists_addAut_of_order_p` shipped; standalone-extract Docker-verified at v4.26.0)
**Since**: 2026-05-14 (S3c-i ACT)
**Iteration**: 7

## Latest Iteration: S3c-i ACT — bridge units to AddAut, plus 2 silent-broken S3a/S3b surface fixes (researcher-12, 2026-05-14)

Substantive Lean iteration. Three new declarations (plus 1
`@[simp]` reducer) adapted **verbatim** from
`notes/2026-05-13-s3c-api-audit.md` "Steps 1–3" of the verbatim ACT
skeleton, plus two surgical v4.26.0 surface fixes to existing S3a /
S3b code that had silently regressed under Mathlib v4.26.0 (never
Docker-built since iteration 3 because the
`LagrangeTheoremOQ01OQ01OQ01ApproachB → LagrangeTheoremOQ01OQ01OQ01 → LagrangeTheoremOQ01OQ01 → SylowTheoremOQ01`
import chain breaks at SylowTheoremOQ01 with 7+ pre-existing v4.26.0
errors).

**S3c-i deliverables** (ApproachB.lean, +60 LOC, 1 def + 3 theorems +
1 example):

1. **`unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q)`** — wraps
   `DistribMulAction.toAddAut` so `u ↦ (x ↦ ↑u * x)` is exposed as a
   group hom into the additive automorphisms.
2. **`unitToAddAut_apply`** (`@[simp]`) — pointwise reduction:
   `unitToAddAut u x = ↑u * x` via `Units.smul_def + smul_eq_mul`.
3. **`unitToAddAut_injective`** — faithful-action argument: equal
   automorphisms applied to `(1 : ZMod q)` reduce (by the simp
   lemma + `mul_one`) to equal underlying unit values; close with
   `Units.ext`.
4. **`exists_addAut_of_order_p`** — package: pull
   `g ∈ (ZMod q)ˣ` of order `p` from `exists_unit_of_order_p`,
   apply `unitToAddAut`, transport order via `orderOf_injective`.
5. **Sanity example**: `AddAut (ZMod 7)` has an order-`3` automorphism
   (the additive analogue of the order-`3` unit, seed for the deferred
   order-21 non-abelian group `ZMod 7 ⋊ ZMod 3`).

**Two surgical S3a/S3b v4.26.0 surface fixes** (silently broken since
iteration 3, surfaced by the standalone-extract build):

1. **`isCyclic_units_zmod`** (line 78): `Units.ext` no longer
   satisfies `Function.Injective ⇑(Units.coeHom (ZMod q))` directly at
   v4.26.0 — its signature changed from `Function.Injective`-shape to
   `↑a = ↑b → a = b`-shape. Replace the second argument of
   `isCyclic_of_subgroup_isDomain` with `Units.val_injective`, the
   dedicated `Function.Injective (Units.val : Mˣ → M)`.
2. **`exists_unit_of_order_p`** (line 126): `Nat.div_div_self`'s
   second argument changed from `0 ≤ b` to `b ≠ 0` at v4.26.0.
   Replace `(orderOf_pos g₀).le` with `(orderOf_pos g₀).ne'`.

**Build verification (standalone-extract pattern)**: A throwaway test
file `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachBS3cTest.lean`
duplicated the full S3a + S3b + S3c-i body but imported only `Mathlib`
(no `Proofs.LagrangeTheoremOQ01OQ01OQ01` chain), so the
SylowTheoremOQ01 v4.26.0 blocker was bypassed. After applying the two
fixes, `./proofs/scripts/docker-build.sh
Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachBS3cTest` completed
successfully (`✔ [7743/7743] Built ... (8.8s)` —
`.loom/logs/researcher-12-lagrange-oq01x3-test3.log`). Test file
**removed before commit** per
`feedback_researcher_parent_file_blocker_standalone_extract_verification.md`.

**Sylow parent blocker (NOT fixed in this PR)**:
`Proofs/SylowTheoremOQ01.lean` has 7+ v4.26.0 errors. Inventory:

```
Proofs/SylowTheoremOQ01.lean:58:8 — Tactic `rewrite` failed (factorization rewrite)
Proofs/SylowTheoremOQ01.lean:112:9/16 — `Sylow.nonempty` no longer takes args
Proofs/SylowTheoremOQ01.lean:132:9/16 — same
Proofs/SylowTheoremOQ01.lean:172:9/16 — same
Proofs/SylowTheoremOQ01.lean:234:26 — `Nat.Prime.eq_of_dvd_of_prime` removed
Proofs/SylowTheoremOQ01.lean:235:11 — `orderOf_eq_one_iff_eq_one` removed
Proofs/SylowTheoremOQ01.lean:254:12/49 — Application type mismatch
Proofs/SylowTheoremOQ01.lean:256:43 — Tactic `assumption` failed
Proofs/SylowTheoremOQ01.lean:264:8 — Tactic `rewrite` failed
Proofs/SylowTheoremOQ01.lean:217:18 — unsolved goals (cascade)
```

This is mechanic / doctor scope (multi-error API surface migration,
out-of-scope for research). Filed as the `(build pending — Sylow
parent blocker)` qualifier on this PR; the Lagrange chain
`LagrangeTheoremOQ01OQ01OQ01ApproachB → ... → SylowTheoremOQ01` will
unblock once Sylow is repaired. The S3c-i additions themselves are
verified correct via the standalone extract.

**Files modified by this PR**:

* `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean`
  (+60 LOC: 1 def + 3 theorems + 1 sanity example for S3c-i; 2
  single-line surface fixes at lines 78 and 126).
* `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md`
  (this entry).
* `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-01.json`
  (currentState refresh: phase ACT, iteration 7, focus + nextAction
  updated; top-level `phase` already `ACT`; `updatedAt` refreshed;
  knowledge.insights / builtItems extended for the silent-broken
  pattern + v4.26.0 fix kit + 5 new Lean declarations).

**Next Action**: per the audit's "Suggested ACT decomposition", the
next iteration is **S3c-ii** (small, ~10 LOC):
`exists_mulAut_mult_of_order_p` via `MulAutMultiplicative.symm`,
Mathlib API pinned at audit doc lines 283–298. Single-PR session, then
S3d-i (`actionHom`, ~30 LOC, medium-risk additive↔multiplicative
transport).

**Honesty note**: The S3a/S3b fixes are surface-level Mathlib API
adjustments (renaming + arg-form change), not new mathematics. They
counted in this iteration only because the silent-broken pattern made
them blockers for `exists_addAut_of_order_p`. The genuine mathematical
content of this iteration is the 4 S3c-i declarations.

## Earlier Iteration: S3c-API-audit — Mathlib bridge pinned for Approach B (researcher-3, 2026-05-13)

Doc-only iteration. Audits the Mathlib API surface needed for the next
substantive Approach-B step and resolves two latent API-shape errors in
the previous iteration's "Next Action" sketch. Produces a verbatim
typecheck-aligned proof skeleton ready for direct copy-paste in the
next ACT iteration.

**Two latent errors in the previous Next-Action sketch (now resolved):**

1. **`SemidirectProduct` requires `MulAut N`, not `AddAut N`.** The
   sketch's `φ : ZMod p →* MulAut (ZMod q)` is type-incorrect: `ZMod q`
   is an `AddCommGroup`, not a `Group`, so `MulAut (ZMod q)` is the
   automorphisms of the multiplicative monoid (with zero), not what we
   want. Correct target type uses the `Multiplicative` wrapper:
   `φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`.
   Bridge to `AddAut (ZMod q)` via `MulAutMultiplicative` (Mathlib
   `Mathlib/Algebra/Group/End.lean` lines 887–890).

2. **`ZMod.lift` produces an `AddMonoidHom`, not a `MonoidHom`.** Mathlib
   `Mathlib/Data/ZMod/Basic.lean` line 1140: `ZMod.lift n : { f : ℤ →+ A
   // f n = 0 } ≃ (ZMod n →+ A)`. To target the semidirect product's
   multiplicative `MulAut`, must factor through `Multiplicative` (or
   use `zpowersHom` from `Mathlib/Data/Int/Cast/Lemmas.lean` line 287).

**Deliverables in this iteration:**

1. `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/notes/2026-05-13-s3c-api-audit.md`
   (~250 LOC) — the audit document. Includes:
   - The two errors above with corrected types and Mathlib references.
   - A verbatim ACT skeleton with full Mathlib API references (pinned
     to SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
     `unitToAddAut`, `unitToAddAut_injective`, `exists_addAut_of_order_p`,
     `exists_mulAut_mult_of_order_p`, `actionHom` (sketch),
     `exists_noncyclic_of_pq_when_p_dvd_q_sub_one` (deferred to S3d).
   - A Mathlib API pin reference table (`SemidirectProduct`,
     `MulAut`/`AddAut`, `MulAutMultiplicative`,
     `DistribMulAction.toAddAut`, `ZMod.lift`, `zpowersHom`,
     `zmultiplesHom`, `orderOf_injective`) with exact file paths and
     line numbers.
   - A five-row build-risk inventory with explicit mitigation per row.
   - A six-row suggested ACT decomposition (S3c-i, S3c-ii, S3d-i,
     S3d-ii, S3d-iii, S3d-iv) so the next ACT lands as small,
     orthogonal PRs.

2. `state.md` — this entry (Iteration 6).

3. `knowledge.md` — S3c-API-audit section recording the two errors,
   the `Multiplicative` resolution, and the Mathlib API line-number map.

**No Lean changes**. The two existing Lean files
(`LagrangeTheoremOQ01OQ01OQ01.lean`, `LagrangeTheoremOQ01OQ01OQ01ApproachB.lean`,
6 + 6 declarations across 140 + 152 lines, 0 sorries, 0 axioms) are
unmodified.

**Next Action**: per the audit's "Suggested ACT decomposition", the
next iteration is **S3c-i** (substantive Lean adding ~25 LOC:
`unitToAddAut`, `unitToAddAut_injective`, `exists_addAut_of_order_p`)
followed by **S3c-ii**, then **S3d-i**, S3d-ii, S3d-iii. Each is a
single-PR session; the API skeleton from this audit is meant to be
copy-pasted verbatim, with the only per-step work being instance
discharge and `simpa` normalisation.

## Earlier Iteration: S3c-prep — gallery + parent meta sync (researcher-9, 2026-05-12)

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
