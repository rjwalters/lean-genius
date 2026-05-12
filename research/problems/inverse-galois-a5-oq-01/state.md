# Current State

**Phase**: ORIENT
**Since**: 2026-05-12 (S2, researcher-5)
**Iteration**: 2

## Current Focus

S2 (researcher-5, 2026-05-12): Lean scaffold for R1 (specialised
Dedekind at `p = 7`). Created `proofs/Proofs/InverseGaloisA5Dedekind.lean`
(76 lines, 1 substantive sorry) and registered it in
`proofs/Proofs.lean`. The scaffold compresses S1's planned 4-sorry
skeleton (`seven_unramified`, `𝔭₃`, `𝔭₃_inertia_deg`, `frob₃`,
`frob₃_order_eq_three`) into a single existence-of-order-3-element
sorry so that S3 has one focused Mathlib-API question instead of four
interlocking constructions.

The parent file's status remains **`axiomatized`** (1 axiom, 0
sorries, 84 theorems, 2067 lines). Eliminating `three_dvd_gal_card`
would upgrade the parent to **`verified`** (badge `original`,
axiomCount 0) — a flagship status change for the gallery's first
non-solvable inverse-Galois realisation. S4 will perform that
replacement once S3 discharges the sorry.

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

**S3 (any researcher): R1 ACT — discharge `exists_gal_order_three`.**

Concrete plan (one deliverable, ~300-500 Lean lines, -1 sorry):

1. **Establish 7 is unramified in K = q.SplittingField.** Use
   `seven_nondiv_disc` and the chain disc(O_K) ∣ disc(q) (from
   the q's minimal-polynomial-discriminant divides ring-of-integers-
   discriminant up to a square factor). Mathlib has
   `Algebra.discr_of_pow_eq` and friends.
2. **Exhibit a prime ideal 𝔭 of O_K above 7 with inertia degree 3.**
   Use `Ideal.exists_isMaximal_ne_bot_of_isPrime` plus the
   factorisation `q mod 7 = (X-5)(X-6)(X³+6X²+4X+1)` from the
   parent's Part XII. The cubic factor's degree (= 3) corresponds
   to a prime of inertia degree 3. Mathlib's
   `Mathlib.NumberTheory.RamificationInertia.Basic` provides
   `Ideal.inertiaDeg`.
3. **Extract the Frobenius generator frob₃ ∈ q.Gal.** Use
   `Mathlib.NumberTheory.RamificationInertia.Galois` (specifically
   the Galois decomposition-group framework, which exposes the
   Frobenius automorphism at an unramified prime).
4. **Prove `orderOf frob₃ = 3`.** At an unramified prime the
   decomposition group is cyclic and its order equals the inertia
   degree (= 3); the Frobenius generates this group; hence
   `orderOf frob₃ = 3`.

If S3 stalls on step 2 (the explicit prime-ideal construction in
Mathlib's API), fall back to R3 (resolvent sextic) per
`problem.md` Q3.

After S3 completes, S4 will splice the proved theorem into the
parent file (`axiom three_dvd_gal_card` →
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
| S2.7 | (pending) Commit + push + PR `(build pending)` per gallery convention | next |

## Honest Calibration

S2 produces:

- One **new Lean file** (`InverseGaloisA5Dedekind.lean`, 76 lines, 1 substantive sorry).
- One **import-list line** in `proofs/Proofs.lean`.
- **Three updated session docs** (`state.md`, the JSON gallery entry,
  `knowledge.md` log-line).

S2 does **not**:

- Discharge any sorry (the sole sorry is left for S3).
- Modify the parent `InverseGaloisA5.lean`.
- Change the parent's axiom count (still 1).
- Upgrade the gallery status (still `axiomatized`).

The next iteration (S3 ACT) is where axiom-elimination value is
delivered. The **realistic estimate** for closing the OQ remains
2 more sessions (S3 Frobenius discharge → S4 parent integration),
delivering a `verified`-status upgrade for the parent
`inverse-galois-a5` flagship proof.

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
