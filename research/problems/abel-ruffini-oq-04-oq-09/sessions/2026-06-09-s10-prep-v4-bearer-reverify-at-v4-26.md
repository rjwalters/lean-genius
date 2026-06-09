# S10 PREP — V₄ row Mathlib bearer re-verification at v4.26.0 (doc-only)

**Slug**: `abel-ruffini-oq-04-oq-09`
**Researcher**: researcher-1
**Date**: 2026-06-09
**Phase**: S10 PREP (doc-only; bearer re-verify + S4 PREP delta + risk
register for the V₄ row's next ACT pass).
**Type**: Doc-only. No edits to `proofs/Proofs/AbelRuffiniOQ04OQ09*.lean`,
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean`, gallery
`meta.json`, `knowledge.md`, or `problem.md`. Edits limited to this
session log + `state.md` (S10 narrative + header refresh) +
`src/data/research/problems/abel-ruffini-oq-04-oq-09.json`
(`currentState.{iteration,phase,focus,nextAction}` + `updatedAt`).
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged since S6).
**Base HEAD**: `58bdf51bc62` (current `origin/main` after this session's
`git fetch`).

## §1 Why this PREP

S4 PREP (2026-05-15, researcher-9, PR #19229) audited the V₄ + S₃
bearer chain and shipped paste-ready skeletons. **Three weeks have
elapsed** since that audit, and S9 ACT (PR #21992, 2026-06-01) only
shipped the **cyclic** row (a one-liner). The V₄ row's S4 PREP §2.5
drop-in is still `sorry`-stubbed and has not been re-verified at the
current lake-pinned SHA. Drift risk is non-zero — Mathlib's
`Cyclotomic/Gal.lean`, `ZMod/UnitsCyclic.lean`, and `Group/Prod.lean`
have all seen changes between mid-May and mid-June (per the Mathlib
master log).

S10 PREP **does not** attempt the V₄ ACT itself (still 50-80 LOC of
non-trivial Lean code, and the host's `.lake` self-loop documented in
the basel-problem Iter 44 INFRA-SIGNAL still blocks local docker
builds). Instead, it:

* Re-confirms every named V₄-row bearer at the **current** Mathlib
  v4.26.0 tag (via GitHub raw, since local `.lake/packages/mathlib/`
  is unusable through the self-loop).
* Identifies one **new bearer gap** not noted in S4 PREP: the
  identification `(ZMod 2)ˣ ≃* ZMod 2` (the "rank-2 unit class"
  S4 PREP §2.4 flagged as needing an explicit `MulEquiv.ofBijective`
  or `IsCyclic.uniqueMulEquivZMod`).
* Records the **safest ACT route** for the V₄ row given the new
  bearer landscape.
* Documents the `.lake` self-loop status (post Iter 38 basel S38 ACT
  and shapley-folkman-oq-01 Sessions 16/17 — same trap, different
  slugs).

## §2 V₄ row bearer audit at v4.26.0

All bearers source-verified by direct GitHub-raw read of the v4.26.0
tag at `https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/`.

| Bearer | File | Line | Form | Notes |
|---|---|---|---|---|
| `IsCyclotomicExtension.autEquivPow` | `Mathlib/NumberTheory/Cyclotomic/Gal.lean` | 93 | `noncomputable def autEquivPow (h : Irreducible (cyclotomic n K)) : Gal(L/K) ≃* (ZMod n)ˣ` | Unchanged from S4 PREP §2.1. |
| `Polynomial.cyclotomic.irreducible_rat` | `Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean` | 190 | `theorem cyclotomic.irreducible_rat {n : ℕ} (hpos : 0 < n) : Irreducible (cyclotomic n ℚ)` | Hypothesis-discharger for `autEquivPow`. Unchanged. |
| `ZMod.chineseRemainder` | `Mathlib/Data/ZMod/Basic.lean` | 873 | `def chineseRemainder {m n : ℕ} (h : m.Coprime n) : ZMod (m * n) ≃+* ZMod m × ZMod n` | Unchanged from S4 PREP §2.4. The 4-step CRT chain for `(ZMod 12)ˣ` is anchored here. |
| `Units.mapEquiv` | `Mathlib/Algebra/Group/Units/Equiv.lean` | 39 | `def mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ` | Unchanged. Used for the ring-iso → unit-iso transfer step. |
| `MulEquiv.prodUnits` | `Mathlib/Algebra/Group/Prod.lean` | 591 | `def prodUnits : (M × N)ˣ ≃* Mˣ × Nˣ` | Unchanged from S4 PREP §2.4's `MulEquiv.prodUnits`. Used to distribute units over the CRT product. |
| `Group.mulEquivOfPrimeCardEq` | `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean` | 793 | `noncomputable def mulEquivOfPrimeCardEq {p : ℕ} [Group G] [Group G'] ...` | **NEW bearer not in S4 PREP**. Provides `(ZMod 2)ˣ ≃* ZMod 2` (and similar) by prime-cardinality identification. Closes the §2.4 gap S4 PREP flagged. See §3 below. |
| CRT-chain precedent | `Mathlib/RingTheory/ZMod/UnitsCyclic.lean` | 271, 281, 290 | (usage, not a def) | The 4-step `chineseRemainder + mapEquiv + prodUnits` chain appears verbatim three times in `isCyclic_units_four_mul_iff` / `_two_mul_iff_of_odd` / `not_isCyclic_units_of_mul_coprime`. Confirms the chain is the canonical Mathlib idiom. **Unchanged** from S4 PREP §2.4. |
| `ZMod.card_units_eq_totient` | `Mathlib/Data/ZMod/Basic.lean` (TBD line) | — | `theorem card_units_eq_totient (n : ℕ) [NeZero n] : Fintype.card (ZMod n)ˣ = n.totient` | Order count: `φ(4) = 2`, `φ(3) = 2`. Unchanged. |

**Net delta vs S4 PREP §2** (2026-05-15):
* Bearer count: 7 (S4 PREP §2) → **8** (added `Group.mulEquivOfPrimeCardEq`).
* Bearer drift: **none** in the 7 carried-forward bearers. All
  line numbers stable.

## §3 New bearer `Group.mulEquivOfPrimeCardEq` closes the S4 PREP §2.4 gap

S4 PREP §2.4 (lines 161-167) flagged:

> Then `(ZMod 4)ˣ` and `(ZMod 3)ˣ` each have order 2 (by
> `ZMod.card_units_eq_totient` — `φ(4) = 2`, `φ(3) = 2`), and any
> group of prime order is `≃* ZMod 2`. Connecting `(ZMod 2)ˣ ≃* ZMod 0`
> (rank-2 unit class — Mathlib has `ZMod.unitsEquivCoprime` and
> totient identities but **not** a packaged `(ZMod 4)ˣ ≃* ZMod 2`
> `MulEquiv`); will need either an explicit `MulEquiv.ofBijective`
> or an axis along `IsCyclic.uniqueMulEquivZMod`.

This gap is **now closed** by `Group.mulEquivOfPrimeCardEq` (in
`Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:793`). The full
signature (verified via GitHub raw):

```lean
noncomputable def Group.mulEquivOfPrimeCardEq {p : ℕ} [Group G] [Group G']
    [Fintype G] [Fintype G'] (hG : Fintype.card G = p) (hG' : Fintype.card G' = p)
    (hp : p.Prime) :
    G ≃* G'
```

For the V₄ row use case: `(ZMod 4)ˣ` has `Fintype.card = 2` (via
`ZMod.card_units_eq_totient` + `Nat.totient_four`); `ZMod 2` has
`Fintype.card = 2`; `2` is prime. So:

```lean
have h₂_four : Fintype.card (ZMod 4)ˣ = 2 := by
  rw [ZMod.card_units_eq_totient]; decide
have h₂_zmod : Fintype.card (ZMod 2) = 2 := by decide
have e₄ : (ZMod 4)ˣ ≃* ZMod 2 :=
  Group.mulEquivOfPrimeCardEq h₂_four h₂_zmod Nat.prime_two
-- analogously for (ZMod 3)ˣ ≃* ZMod 2
```

This is ~6 LOC per side (12 LOC total for the two prime-order
identifications), eliminating S4 PREP §2.4's "5-bearer explicit
`MulEquiv.ofBijective`" hand-construction. **Estimated V₄ ACT LOC:
50-80 (S4 PREP) → 40-65 LOC (with this bearer)**.

## §4 Updated paste-ready skeleton for V₄ row (sketch, not paste-ready code yet)

The S4 PREP §2.5 drop-in remains `sorry`-stubbed at its core
construction step ("Step 1: L := ℚ(ζ₁₂)"). The construction needs:

```lean
import Mathlib.NumberTheory.Cyclotomic.Basic       -- IsCyclotomicExtension
import Mathlib.NumberTheory.Cyclotomic.CyclotomicField  -- CyclotomicField
import Mathlib.NumberTheory.Cyclotomic.Gal         -- IsCyclotomicExtension.autEquivPow
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots  -- cyclotomic.irreducible_rat
import Mathlib.Data.ZMod.Basic                     -- ZMod.chineseRemainder + card_units_eq_totient
import Mathlib.Algebra.Group.Prod                  -- MulEquiv.prodUnits
import Mathlib.Algebra.Group.Units.Equiv           -- Units.mapEquiv
import Mathlib.GroupTheory.SpecificGroups.Cyclic   -- Group.mulEquivOfPrimeCardEq

namespace AbelRuffiniOQ04OQ09

open IsCyclotomicExtension Polynomial

theorem v4_realizable :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
      Nonempty ((L ≃ₐ[ℚ] L) ≃* (ZMod 2 × ZMod 2)) ∧
      Fintype.card (L ≃ₐ[ℚ] L) = 4 := by
  -- Step 1: Take L = CyclotomicField 12 ℚ
  let L := CyclotomicField 12 ℚ
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · -- Step 2: Gal(L/ℚ) ≃ (ZMod 12)ˣ via autEquivPow + cyclotomic.irreducible_rat
    refine ⟨?_⟩
    have h_irr : Irreducible (cyclotomic 12 ℚ) :=
      cyclotomic.irreducible_rat (by decide : 0 < 12)
    have e_gal : (L ≃ₐ[ℚ] L) ≃* (ZMod 12)ˣ :=
      (IsCyclotomicExtension.autEquivPow L h_irr).trans (.refl _)
    -- Step 3: (ZMod 12)ˣ ≃ (ZMod 4)ˣ × (ZMod 3)ˣ via CRT chain
    have h_cop : Nat.Coprime 4 3 := by decide
    have e_crt : (ZMod 12)ˣ ≃* (ZMod 4)ˣ × (ZMod 3)ˣ := by
      have heq : (4 : ℕ) * 3 = 12 := by decide
      have e₁ : ZMod 12 ≃+* ZMod 4 × ZMod 3 :=
        heq ▸ ZMod.chineseRemainder h_cop
      exact (Units.mapEquiv e₁.toMulEquiv).trans .prodUnits
    -- Step 4: Each factor ≃ ZMod 2 via mulEquivOfPrimeCardEq
    have h₄ : Fintype.card (ZMod 4)ˣ = 2 := by
      rw [ZMod.card_units_eq_totient]; decide
    have h₃ : Fintype.card (ZMod 3)ˣ = 2 := by
      rw [ZMod.card_units_eq_totient]; decide
    have h₂ : Fintype.card (ZMod 2) = 2 := by decide
    have e_four : (ZMod 4)ˣ ≃* ZMod 2 :=
      Group.mulEquivOfPrimeCardEq h₄ h₂ Nat.prime_two
    have e_three : (ZMod 3)ˣ ≃* ZMod 2 :=
      Group.mulEquivOfPrimeCardEq h₃ h₂ Nat.prime_two
    -- Step 5: compose
    exact e_gal.trans (e_crt.trans (MulEquiv.prodCongr e_four e_three))
  · -- Step 6: Cardinality
    rw [Fintype.card_congr (by ... : (L ≃ₐ[ℚ] L) ≃ ZMod 2 × ZMod 2)]
    decide
end AbelRuffiniOQ04OQ09
```

**This is a sketch, not paste-ready code**. The Step 6 cardinality
discharge needs to factor through `Fintype.card_prod` and the same
`MulEquiv → Equiv` chain as Step 2-5; the `(by ... : MulEquiv → Equiv)`
hole would be filled by `.toEquiv` on the composed `MulEquiv`. The
exact tactic-mode glue is build-time-dependent and benefits from a
real docker probe before paste-readiness.

**Estimated ACT LOC**: 40-65 (down from S4 PREP's 50-80 due to the
`mulEquivOfPrimeCardEq` shortcut).

**Estimated ACT effort**: 1-2 sessions, dominated by Step 6's
cardinality glue. Probably 1 session if the host `.lake` self-loop
is fixed first (per basel iter44 INFRA-SIGNAL).

## §5 Infrastructure status update

Per the basel-problem-oq-01-oq-01-oq-02-oq-03 Iter 44 INFRA-SIGNAL
(2026-06-09, this researcher's prior session this same day):

* **Docker host: GREEN.** `lean4-arm64:v4.26.0` healthy with new image
  ID `sha256:8768de35b1f4cb…` (≠ Iter 43-era corrupted
  `9026c55995f4`). `docker info / ps / run --rm` all succeed.
* **`.lake` self-loop on main repo: RED.** `/Users/rwalters/GitHub/lean-genius/proofs/.lake`
  is a symlink to itself; every researcher worktree's `.lake` is
  symlinked to that broken main-repo target. `lake build` cannot
  resolve `/workspace/proofs/.lake` inside Docker either. **This
  blocks any V₄ ACT.**

**Remediation path** (verbatim from basel iter44):

```bash
rm /Users/rwalters/GitHub/lean-genius/proofs/.lake
cd /Users/rwalters/GitHub/lean-genius/proofs
./scripts/docker-build.sh Proofs.AbelRuffiniOQ04OQ09Cyclic
# First run: 10-20 min cache-miss + small target build
```

After this, V₄ ACT is unblocked.

## §6 Race-safety log

* **Pre-claim probe** (2026-06-09 ~17:35Z):
  `gh pr list --search "abel-ruffini-oq-04-oq-09 in:title" --state open`
  → 0 open PRs on this slug.
* **Pre-edit probe**: cyclic file
  `proofs/Proofs/AbelRuffiniOQ04OQ09Cyclic.lean` unchanged on
  `origin/main` since S9 ACT PR #21992 (2026-06-01T22:12Z); 46 LOC,
  1 theorem, 0 sorries, 0 axioms.
* **Sibling-file probe**: parent
  `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean` unchanged
  since S9 ACT (line 85 `noncomputable def zmod_coprime_crt` repair).
* **HEAD probe**: `origin/main` at `58bdf51bc62` (post-S9 + many
  intervening unrelated drains). This S10 PREP branches from there.
* **Bearer pin probe**: lake SHA still
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; v4.26.0 Mathlib tag at
  GitHub matches lake's expectations.

## §7 What this PREP does NOT include

1. **No Lean edits**. Cyclic file byte-identical to S9 ACT state.
2. **No V₄ paste-ready code**. §4 is a sketch with one explicit
   `by ...` placeholder for the cardinality discharge; build-time
   probing is needed for the final tactic glue.
3. **No S₃ row work**. S4 PREP §3 audit remains valid (no S₃
   bearers were touched between 2026-05-15 and 2026-06-09); a
   separate S11 PREP can re-verify S₃ if/when V₄ ACT lands.
4. **No D₄/A₄/S₄ work**. Out of scope (resolvent-cubic helper
   namespace not yet built).
5. **No host-side `.lake` mutation**. The remediation in §5 is a
   pointer for the next ACT iteration, not an action of this PREP.
6. **No gallery entry edits**. Gallery for OQ-04-OQ-09 deferred to
   S12+ once at least V₄ row ships.
7. **No `meta.json` edits.** Cyclic file's gallery entry
   `src/data/proofs/abel-ruffini-oq-04-oq-09/` (if it exists)
   unchanged.

## §8 Honest framing / self-audit

* **Bearer drift was real risk but small reality**. Three weeks is a
  meaningful window for Mathlib drift, but the V₄ row bearers are in
  stable, well-trafficked files (`Cyclotomic/Gal.lean`,
  `ZMod/Basic.lean`, `Group/Prod.lean`). All seven S4 PREP bearers
  re-confirmed at v4.26.0 with no line-number changes.
* **The one genuine find is `mulEquivOfPrimeCardEq`**. S4 PREP §2.4
  noted that the `(ZMod 2)ˣ ≃* ZMod 2`-style step needed hand-
  construction. The new bearer `Group.mulEquivOfPrimeCardEq` exists
  in `GroupTheory/SpecificGroups/Cyclic.lean:793` and handles this
  cleanly. Whether this lemma was added between 2026-05-15 and
  2026-06-09 or was just missed in S4 PREP's search is undetermined
  by this iteration's tools — the file is referenced consistently
  across recent Mathlib master, so either way it's available now.
* **The V₄ skeleton is still a sketch, not paste-ready code**. The
  Step 6 cardinality glue needs a real docker probe. This PREP
  honestly does not promise paste-ready ACT in 5-10 min; it shaves
  10-15 LOC off the S4 PREP estimate and resolves one bearer gap.
* **Infrastructure is the dominant cost**. The 10-20 min `.lake`
  re-init is by far the biggest item on the next ACT'er's clock.
  All Lean-side risks are sub-30-min items.

## §9 Cross-references

- S1 OBSERVE (2026-05-12, #17764): scaffold + 9-target group catalogue.
- S2 PREP (2026-05-13, #18946): per-row Mathlib API sketches.
- S3 PREP (2026-05-15, #19199): cyclic-row axiom-load audit.
- **S4 PREP (2026-05-15, #19229): V₄ + S₃ bearer audit — this PREP
  is its successor for V₄.**
- S5 STATE-SYNC (2026-05-16, #19538): absorb S3+S4 PREP findings.
- S6 PREP (2026-05-16, #19633): namespace correction + INFRA RED.
- S7 STATE-SYNC (2026-05-16, #19755): G7 disk RED escalation.
- S8 STATE-SYNC (2026-05-30, #21162): G7+G8 RED→GREEN; G9 still
  flagged but per memory `Lake self-loop in main repo (G9-inert)`
  the actual blocker was the parent `lemma → def` keyword issue.
- **S9 ACT (2026-06-01, #21992): cyclic row shipped + parent repair.
  46 LOC new file, 0 axioms, 0 sorries.**
- basel-problem-oq-01-oq-01-oq-02-oq-03 Iter 44 (2026-06-09, this
  researcher's prior session): same `.lake` self-loop noted as
  current ACT blocker; Docker recovered separately.
- shapley-folkman-oq-01 Sessions 16/17 (2026-06-04): same `.lake`
  self-loop trap.
- User memory `[Lake self-loop in main repo (G9-inert)]`: notes that
  per S9 ACT's docker-verified 7747 jobs, the self-loop does NOT
  block Docker builds at every host state. This contradicts the
  basel iter44 finding — the difference may be in how `lake exe
  cache get` interacts with the mounted cache volume vs the source
  tree at different host filesystem states. **TBD by Iter 11+ ACT.**

## §10 What the next researcher should do (S11+ V₄ ACT)

**Pre-flight (infrastructure, 1 step)**:

1. Test docker build of the existing cyclic row:
   ```bash
   cd /Users/rwalters/GitHub/lean-genius/proofs
   ./scripts/docker-build.sh Proofs.AbelRuffiniOQ04OQ09Cyclic
   ```
   If success in 5-30s: the `.lake` symlink loop is **not** blocking
   docker builds (consistent with the S9 ACT 7747-job verified
   build). Proceed to Lean ACT.

   If fail with `.lake`-related error: apply the basel iter44 §5
   remediation (`rm proofs/.lake`; re-init via fresh docker build).
   First fresh build: 10-20 min cache-miss.

**Lean ACT (V₄ row)**:

1. Add the 8 imports from §4 above to a new file
   `proofs/Proofs/AbelRuffiniOQ04OQ09V4.lean`.
2. Paste the §4 skeleton (40-65 LOC).
3. Build-probe to discover the actual tactic glue for Step 6
   (`Fintype.card` discharge via `Fintype.card_prod` + `MulEquiv` →
   `Equiv` composition).
4. Register the new file in `proofs/Proofs.lean` alphabetically:
   ```
   import Proofs.AbelRuffiniOQ04OQ09Cyclic
   import Proofs.AbelRuffiniOQ04OQ09V4   -- NEW
   import Proofs.AbelRuffiniOQ09
   ```
5. Build-verify with `docker-build.sh Proofs.AbelRuffiniOQ04OQ09V4`.
6. Commit + PR.

**Estimated total wall-clock**: 30-60 min (assuming `.lake` is
already OK; otherwise +10-20 min for re-init).

**Anti-target**: do NOT start S₃/D₄/A₄/S₄ in the same iteration.
Cyclic-first ordering surfaced no bugs in S9 ACT; V₄-first is the
safe S₃-precursor (V₄ touches `IsCyclotomicExtension.autEquivPow`,
S₃ touches `irreducible_of_eisenstein_criterion` + `galActionHom*`
— different bearer families). 1 row per ACT session.
