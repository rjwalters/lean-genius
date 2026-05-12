# Current State

**Phase**: ORIENT
**Since**: 2026-05-12 (S3 refinement, researcher-4 audit + researcher-1 recovery)
**Iteration**: 3

## Current Focus

S3 (researcher-4, 2026-05-12): **Mathlib AlgHom.IsArithFrobAt API
audit at v4.26.0** (`rev 2df2f01...`). Replaces S1's hand-waved
Mathlib references (which predated `Mathlib.RingTheory.Frobenius`)
with concrete, source-verified declaration names. S4 ACT now has a
precise import-and-API-call list rather than an exploratory phase.

Key findings (see `knowledge.md` "S3 — ORIENT refinement" section):

1. **`Mathlib.RingTheory.Frobenius`** (Andrew Yang, Mathlib 2025) is
   the canonical Frobenius infrastructure. Provides
   `AlgHom.IsArithFrobAt`, `IsArithFrobAt` (group-action version),
   `IsArithFrobAt.exists_of_isInvariant` (the existence theorem),
   `arithFrobAt R G Q : G` (explicit choice of Frobenius element).
   **Supersedes** S1's conjectural `Ideal.Quotient.frobenius` name
   (which does not exist).
2. **`Mathlib.RingTheory.Invariant.Basic`** provides the
   decomposition-group surjection (`stabilizerHom_surjective`) and
   the Galois-as-invariant theorem (`Algebra.isInvariant_of_isGalois`).
3. **`Mathlib.NumberTheory.RamificationInertia.Galois`** provides
   `inertiaDegIn`, `ramificationIdxIn`, and
   `card_inertia_eq_ramificationIdxIn`.
4. **The residual Mathlib gap** is the single bridge inequality
   `orderOf (arithFrobAt R G Q) ≥ inertiaDegIn (Q.under R) S`
   (equality at unramified primes). This is the genuine new content
   for S4 ACT, ~100-150 Lean lines, NOT the typeclass plumbing or
   the prime-ideal existence (each ≤100 lines).

S2's scaffold is unchanged. S3 is doc-only and adds zero Lean lines.

The parent file's status remains **`axiomatized`** (1 axiom, 0
sorries, 84 theorems, 2067 lines). Eliminating `three_dvd_gal_card`
would upgrade the parent to **`verified`** (badge `original`,
axiomCount 0) — a flagship status change for the gallery's first
non-solvable inverse-Galois realisation. S5 will perform that
replacement once S4 discharges the sorry.

## Active Approach

**R1 (specialised Dedekind at `(q, p) = (q, 7)`).**

S2 deliverables (this iteration, complete):

1. **`proofs/Proofs/InverseGaloisA5Dedekind.lean`** (76 lines, 1 sorry):

   ```lean
   import Mathlib
   import Proofs.InverseGaloisA5

   namespace InverseGaloisA5Dedekind

   open Polynomial InverseGaloisA5

   -- Precondition: 7 ∤ disc(q) = 32000² = 1_024_000_000
   theorem seven_nondiv_disc : ¬ (7 : ℤ) ∣ 1024000000 := by
     intro ⟨k, hk⟩; omega

   -- Sole S2 sorry: existence of an order-3 Galois element.
   -- Discharged in S3 via the Frobenius construction at p = 7.
   theorem exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3 := by sorry

   -- Trivial bridge: orderOf σ = 3 ⇒ 3 ∣ Fintype.card q.Gal.
   theorem three_dvd_gal_card_proved : 3 ∣ Fintype.card q.Gal := by
     obtain ⟨σ, hσ⟩ := exists_gal_order_three
     rw [← hσ]
     exact orderOf_dvd_card

   end InverseGaloisA5Dedekind
   ```

2. **`proofs/Proofs.lean`**: added `import Proofs.InverseGaloisA5Dedekind`
   between `InverseGaloisA5` and `InverseGaloisA5Resultant`.

3. **No parent-file changes**: parent still uses `axiom three_dvd_gal_card`.
   The axiom replacement happens in S4 after S3 proves the supporting
   theorems.

Net delta this session: +1 sorry (in the new companion file), 0 axiom
delta on the parent, 0 sorry delta on the parent.

## Blockers

None mathematical: Dedekind's theorem is classical, and the specialised
form needed for `(q, 7)` is a routine ramification-inertia computation.

Practical:

- **Mathlib API exploration**: `Mathlib.NumberTheory.RamificationInertia.Galois`
  contains the Frobenius framework but the exact API surface for
  extracting an explicit prime ideal and its Frobenius generator
  needs verification at the pinned revision. S3 will spend the first
  ~30 lines on import-and-API-probing.
- **Docker build cost**: This S2 PR is small (one new 76-line file,
  one import-list line), but the umbrella `import Mathlib` still
  forces a full Mathlib build. Build verification deferred to
  deployer/auditor per gallery `(build pending)` convention.
- **Worktree `.lake` symlink**: known broken on this worktree (per
  memory entry `Researcher — broken proofs/.lake symlink`); any S3
  PR runs `docker-build` ⇒ ≥45 min build window. Plan accordingly.

## Next Action

**S4 (any researcher): R1 ACT — discharge `exists_gal_order_three`
using the pinned `AlgHom.IsArithFrobAt` API surface.**

Concrete plan (one deliverable, ~230-360 Lean lines per the S3 audit,
-1 sorry):

1. **Typeclass plumbing (~30-50 lines).** Use
   `Algebra.isInvariant_of_isGalois` and
   `IsIntegralClosure.MulSemiringAction` to give `q.Gal` a
   `MulSemiringAction` on `𝓞 q.SplittingField`. Confirm
   `Algebra.IsInvariant ℤ 𝒪 q.Gal` and `Finite q.Gal`.
2. **Prime ideal above 7 (~100-150 lines).** Exhibit a prime
   `Q : Ideal 𝒪` over 7 with `Q.IsPrime`, `Finite (𝒪 ⧸ Q)`, and
   `inertiaDegIn (Q.under ℤ) 𝒪 = 3`. The inertia-degree value
   follows from the parent's `cubic_factor_no_roots_mod7` via the
   residue-field-degree-3 over `𝔽_7` argument.
3. **Define the Frobenius element (~1 line).** `σ := arithFrobAt ℤ q.Gal Q`.
4. **Show `orderOf σ = 3` (~100-150 lines).** Use:
   - `IsArithFrobAt.arithFrobAt` (the Frobenius congruence);
   - `Ideal.Quotient.stabilizerHom_surjective` to lift the
     residue-side Frobenius order back to `q.Gal`;
   - `FiniteField.pow_card` for the residue-side order (= 3 since
     `[𝒪 ⧸ Q : ℤ ⧸ (7)] = inertiaDegIn = 3`);
   - `card_inertia_eq_ramificationIdxIn` and unramifiedness
     (`ramificationIdxIn = 1` since `7 ∤ disc(q) = 32000²`) to bound
     the lifting from above.
5. **Plumbing to `exists_gal_order_three` (~5-10 lines).** Already
   structurally proved in S2 (`obtain ⟨σ, hσ⟩ := this; refine ⟨σ, hσ⟩`).

If S4 stalls on step 2 (the explicit prime-ideal construction in
Mathlib's API), fall back to R3 (resolvent sextic) per
`problem.md` Q3.

After S4 completes, **S5 CLOSE** will splice the proved theorem into
the parent file (`axiom three_dvd_gal_card` →
`theorem three_dvd_gal_card := InverseGaloisA5Dedekind.three_dvd_gal_card_proved`)
and bump the parent's meta.json (status `axiomatized` → `verified`,
badge `axiom` → `original`, axiomCount 1 → 0).

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| S1.1 | Verified no open PR / remote branch / recent merge for slug | safe to claim |
| S1.2 | `claim-problem.sh claim inverse-galois-a5-oq-01` from `$REPO_ROOT` | claimed |
| S1.3 | `git checkout -b research/inverse-galois-a5-oq-01-s1-observe-<ts> origin/main` | clean branch |
| S1.4 | Read parent `Proofs/InverseGaloisA5.lean` lines 260-310 + 715-810 (Part XII) | identified the axiom + supporting decidables |
| S1.5 | Surveyed Mathlib `RamificationInertia.*` modules + `Perm.Cycle.Type` | API map drafted |
| S1.6 | Drafted three discharge routes R1/R2/R3 with effort estimates | strategy clear |
| S1.7 | Wrote problem.md, knowledge.md, state.md, and JSON gallery entry | S1 OBSERVE complete |
| S1.8 | Commit + push + PR with label `research` (PR #18129) | merged 2026-05-12T13:18Z |
| S2.1 | researcher-5 claimed slug via `claim-random` (RICH score 19) | claimed 2026-05-12T14:16Z |
| S2.2 | Fixed worktree `.lean/state` symlink (per memory note); fresh branch off `origin/main` | clean state |
| S2.3 | Probed open PRs for slug — none open; safe to push S2 | no race |
| S2.4 | Wrote `proofs/Proofs/InverseGaloisA5Dedekind.lean` (76 lines, 1 sorry) | scaffold built |
| S2.5 | Updated `proofs/Proofs.lean` import list | module registered |
| S2.6 | Updated state.md, knowledge.md, JSON for S2 | docs synced |
| S2.7 | Commit + push + PR `(build pending)` per gallery convention | PR #18155 merged 2026-05-12T15:04Z |
| S3.1 | researcher-4 claimed slug via `claim-random` (RICH score 20) | claimed 2026-05-12T16:08Z |
| S3.2 | Re-checked open PRs / recent merges — none in last hour | safe to ship doc-only refinement |
| S3.3 | Read `Mathlib/RingTheory/Frobenius.lean` (v4.26.0) via `gh api` — confirmed `AlgHom.IsArithFrobAt`, `arithFrobAt`, `exists_of_isInvariant` | API pinned |
| S3.4 | Read `Mathlib/RingTheory/Invariant/Basic.lean` — confirmed `stabilizerHom_surjective`, `Algebra.isInvariant_of_isGalois` | bridge identified |
| S3.5 | Read `Mathlib/NumberTheory/RamificationInertia/Galois.lean` — confirmed `inertiaDegIn`, `card_inertia_eq_ramificationIdxIn` | inertia identities pinned |
| S3.6 | Updated knowledge.md with pinpointed API audit + refined S4 ACT plan | S3 ORIENT refinement complete |
| S3.7 | researcher-4's S3 audit committed to orphan branch `research/inverse-galois-a5-oq-01-s3-1778605805` (no PR created — agent crashed mid-step before `gh pr create`) | orphan recovered |
| S3.8 | researcher-1 (RICH score 20, claim 2026-05-12T19:14Z) replayed orphan's 3 changed files onto fresh `origin/main` (no open PRs / recent merges for slug) | safe replay |
| S3.9 | Commit + push + PR `(doc-only)` — provenance to researcher-4 in commit message | this PR |

## Honest Calibration

S3 produces (in this iteration):

- **Three updated session docs** (`state.md`, `knowledge.md`, JSON
  gallery entry).
- **Zero Lean changes.**
- **A pinpointed Mathlib API audit** (Frobenius.lean, Invariant/Basic.lean,
  RamificationInertia/Galois.lean) that S4 ACT will operate on.

S3 does **not**:

- Discharge any sorry (`exists_gal_order_three` still open).
- Modify any Lean file.
- Change the parent's axiom count or sorry count.
- Upgrade the gallery status.

S3's deliverable is **strictly preparatory** but high-leverage:
S1 OBSERVE was drafted before `Mathlib.RingTheory.Frobenius` was
inspected first-hand (it was added during the 2025 Mathlib cycle but
its API names had not been verified at the pinned revision). S4 ACT
now has a precise import-and-API-call list rather than an
exploratory phase.

The **realistic estimate** for closing the OQ from here: 2 more
sessions (S4 Frobenius discharge ~230-360 Lean lines → S5 parent
integration ~10 Lean + meta.json), delivering a `verified`-status
upgrade for the parent `inverse-galois-a5` flagship proof.

## References Captured

- Dummit & Foote (2004), §14.8: standard Dedekind theorem statement.
- Neukirch (1999), Theorem I.9.6: Frobenius element framework.
- Lang (1994), §I.7: decomposition group at unramified primes.
- Cohen (1993), §6.4: computational algorithm (useful for R1 specialisation).
- Mathlib modules: `NumberTheory.NumberField.Basic`,
  `NumberTheory.NumberField.Discriminant`,
  `NumberTheory.RamificationInertia.*`,
  `GroupTheory.Perm.Cycle.Type`,
  `GroupTheory.OrderOfElement` (provides `orderOf_dvd_card`).

See `knowledge.md` for the full Mathlib-gap table and Lean skeleton.
