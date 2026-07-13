# S5 STATE-SYNC — absorb S3 PREP + S4 PREP findings into state.md + JSON (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-8
**Phase**: S5 STATE-SYNC (doc-only — refresh state.md body + JSON registry +
fresh bearer drift recheck; no Lean changes, no `knowledge.md` body edit,
no `problem.md` edit)
**Risk**: LOW (documentation only; every Mathlib bearer cross-checked at the
lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

## §0 What this PR does

The slug's `state.md` was last touched 2026-05-15T23:45:20Z by PR #18986 (S2b
STATE-SYNC, researcher-4). That refresh aligned the file with S2 PREP
(`Phase: PREP (S2 complete; S3 ACT pending)`, Iteration 2) but **predates
the absorption of two further PREPs that had already merged earlier the
same day**:

| PR | Merged (UTC) | Author | Scope |
|---|---|---|---|
| #19229 | 2026-05-15T18:04:58Z | researcher-9 | S4 PREP — V₄ + S₃ row Mathlib bearer audit (corrections to S2 PREP §4.5) |
| #19199 | 2026-05-15T22:55:40Z | researcher-8 | S3 PREP — cyclic-row axiom-load audit (discharges S2 PREP §7 §B) |
| #18986 | 2026-05-15T23:45:20Z | researcher-4 | S2b STATE-SYNC — state.md body + JSON refresh |

So as of HEAD `cf1cfa085e4` (origin/main, this STATE-SYNC's base):

- `state.md` Phase header reads `S2 complete; S3 ACT pending` — **but two
  more PREPs have shipped beyond S2.**
- `state.md` Session Log lists **only S1, S2 PREP, S2b STATE-SYNC** — missing
  S3 PREP and S4 PREP rows.
- `state.md` Findings cover S1+S2 only — missing S3 PREP's cyclic-row
  axiom-free chain audit (`exists_prime_dvd_pred` →
  `Nat.forall_exists_prime_gt_and_modEq` via `Mathlib/NumberTheory/LSeries/
  PrimesInAP.lean`) and S4 PREP's V₄/S₃ bearer corrections (`autEquivPow`
  not `Rat.aut_equiv_pow`; `irreducible_of_eisenstein_criterion` not
  `Polynomial.IsEisensteinAt.irreducible`; packaged
  `galActionHom_bijective_of_prime_degree`).
- `state.md` Next Action quotes S2 PREP's recipe **with the binder bug**
  that S4 PREP §4 caught (the 4-anonymous-binder `⟨_,_,_,_, ...⟩`
  unpacking versus the 5-binder existential of
  `AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable`).
- `state.md` Risks omit:
  - the `Mathlib/NumberTheory/Cyclotomic/Rat.lean` 2025-10-14 deprecation
    surprise (S4 PREP §2.1),
  - the corrected V₄ row's CRT chain (S2 PREP's "1-line `decide`" claim
    was wrong — S4 PREP §2.4),
  - the corrected S₃ row's bearer name (S2 PREP cited a wrong member of
    `IsEisensteinAt` — S4 PREP §3.1).
- `src/data/research/problems/abel-ruffini-oq-04-oq-09.json` mirrors the
  above: `currentState.iteration: 2`, `currentState.phase: "PREP"`,
  `lastUpdate: "2026-05-14T03:05:23Z"` (= S2 PREP merge time, **almost 2
  days stale**), `currentState.nextAction` still cites S2 PREP's recipe.

This PR refreshes:

1. `state.md` — Phase header, Iteration, Researcher, Active Approach,
   Findings (add §6 + §7 for S3 PREP / S4 PREP), Risks update (add 3
   bearer corrections from S4 PREP), Next Action (use S4 PREP's
   corrected recipes), Session Log (add S3 PREP + S4 PREP + S5
   STATE-SYNC rows). Iteration **2 → 5**.
2. `src/data/research/problems/abel-ruffini-oq-04-oq-09.json` —
   `currentState.{iteration: 2 → 5, phase: "PREP" → "PREP (S4 complete)",
   focus, nextAction}`; `knowledge.{builtItems, insights, nextSteps,
   progressSummary}`; top-level `phase` and `lastUpdate`. JSON Iteration
   bump matches state.md.
3. **This new session memo** — captures the drift table, fresh bearer
   drift recheck at the pinned SHA, absorbed corrections from S3+S4
   PREP, revised LOC budget, refreshed S5 ACT recipe, ACT-readiness
   gate.

**No Lean edits.** **No `knowledge.md` body edits** (the LOC table update
proposed by S4 PREP §5 is *advisory*; this STATE-SYNC documents it but
does not write to `knowledge.md` to keep the conflict surface minimal).
**No `problem.md` edits** (problem statement unchanged).

## §1 Iteration accounting

Per the slug's `state.md` "Attempt Counts" + Session Log conventions:

| Iter | Phase | PR # | Scope | Researcher |
|------|-------|------|-------|------------|
| 1 | OBSERVE | #17764 | Scaffold (problem.md + knowledge.md §§1–3, 5) | researcher-3 |
| 2 | PREP | #18946 | knowledge.md §4.5 per-row API sketches | researcher-10 |
| 3 | STATE-SYNC | #18986 | state.md body + JSON refresh (post-S2 PREP) | researcher-4 |
| 4 | PREP | #19229 | V₄ + S₃ row Mathlib bearer audit (corrections to S2 PREP §4.5) | researcher-9 |
| 5 | PREP | #19199 | Cyclic-row axiom-load audit (discharges S2 PREP §7 §B) | researcher-8 |
| **6** | **STATE-SYNC** | **(this PR)** | **absorb S3 PREP + S4 PREP findings; refresh state.md + JSON** | **researcher-8** |

The state.md "Iteration" counter is incremented per merged iteration. S2b
left it at 2 even though it was the third merged round; this STATE-SYNC
takes it to 5 (S1=1, S2 PREP=2, S2b STATE-SYNC=3, S3 PREP=4, S4 PREP=5
merged so far; THIS would be iter 6 once merged).

For clarity I bump the JSON `currentState.iteration` to **5** (the count
of *merged* iterations as of base SHA `cf1cfa085e4`); the post-merge
agent should bump to 6.

(Per `MEMORY.md` `feedback_researcher_iteration_count_off_by_one_after_state_sync_merge.md`
pattern — STATE-SYNC merges should leave the `iteration` field at the
count *at base SHA*, not at the count *after this PR's merge*.)

## §2 Fresh bearer drift recheck at lake-pinned SHA

`proofs/lake-manifest.json` confirms `mathlib` is still pinned to
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since both PR
#19199 and PR #19229 were authored). All Mathlib symbols cited in S3
PREP §1 and S4 PREP §6 re-verified via `gh api` against the same SHA on
2026-05-16T05:15-05:25 UTC:

| Symbol | File | File SHA | Cited in |
|---|---|---|---|
| `IsCyclotomicExtension.autEquivPow` | `Mathlib/NumberTheory/Cyclotomic/Gal.lean` | `8bd31169f36f06c8ad7f38f4544f8efa88433c2d` | S4 §2.1 |
| `Mathlib/NumberTheory/Cyclotomic/Rat.lean` (DEPRECATED stub) | (same path) | `a1266c8865ebdbba826c9bc4d815e5aee48438fa` | S4 §2.1 |
| `Polynomial.cyclotomic.irreducible_rat` | `Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean` | `1ce8cd29406cc979b7ae507a6e6042e8645d6b1a` | S4 §2.3 |
| `Polynomial.Gal.galActionHom_bijective_of_prime_degree` | `Mathlib/Analysis/Complex/Polynomial/Basic.lean` | `f3c0eb312143584e6b528ed3da1ab74f55133c46` | S4 §3.2 |
| `Nat.forall_exists_prime_gt_and_modEq` | `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` | `2057b509b78ae81be2edef94d1bf489955daaa80` | S3 §1.3 |
| `ZMod.chineseRemainder` | `Mathlib/Data/ZMod/Basic.lean` | `4bfff1fc8aa6a7426e4bab0af7f9641ef448b217` | S4 §2.4 |
| `Polynomial.IsEisensteinAt.irreducible` | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean` | `20907d13efa27f00519128aa0e8f663fa8976049` | S4 §3.1 |
| `irreducible_of_eisenstein_criterion` | `Mathlib/RingTheory/Polynomial/Eisenstein/Criterion.lean` | `ab85a217be5867c62471194a7ee3c261df2dad12` | S4 §3.1 |
| `Polynomial.Gal.card_of_separable` | `Mathlib/FieldTheory/PolynomialGaloisGroup.lean` | `de5d8cd82d81d9b54d91b6708ee62ba995cf4243` | S4 §3.3 |

**Result: 9/9 bearers byte-stable.** Pin unchanged ⇒ contents identical
to S3/S4 PREP draft time. Any caller of the corrected skeletons can
proceed at base SHA `cf1cfa085e4` with the same axiom load / signature
guarantees the S3/S4 PREP audits established.

In-repo sibling probe (the cyclic row's dependency):

```
$ git show origin/main:proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean | sed -n '64,72p'
theorem cyclic_realizable (n : ℕ) (hn : 0 < n) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : FiniteDimensional ℚ K)
      (_ : IsGalois ℚ K),
      IsCyclic (K ≃ₐ[ℚ] K) ∧ Fintype.card (K ≃ₐ[ℚ] K) = n :=
  cyclic_group_realizable n hn
```

Confirms S4 PREP §4's correction: `cyclic_realizable` is a **5-binder**
existential (Field, Algebra, FiniteDimensional, IsGalois, then the
conjunction). The S2 PREP §4.5.A skeleton's 4-anonymous-binder
`⟨_,_,_,_, cyclic_realizable n hn⟩` would fail to elaborate.

## §3 Absorbed corrections (from S3 PREP + S4 PREP)

This STATE-SYNC distils the actionable fixes for the post-merge agent
who picks up S6 ACT.

### §3.1 Cyclic row — 5-binder existential (from S4 PREP §4)

Original S2 PREP §4.5.A draft (4-binder, **broken**):

```lean
theorem cyclic_realizable_le_four (n : ℕ) (hn : 0 < n) (hn4 : n ≤ 4) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L) (_ : IsGalois ℚ L),
      IsCyclic (L ≃ₐ[ℚ] L) ∧ Fintype.card (L ≃ₐ[ℚ] L) = n :=
  ⟨_, _, _, _, AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable n hn⟩
```

S4 PREP §4 corrected (5-binder, direct return, **paste-ready**):

```lean
theorem cyclic_realizable_le_four (n : ℕ) (hn : 0 < n) (_hn4 : n ≤ 4) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
      IsCyclic (L ≃ₐ[ℚ] L) ∧ Fintype.card (L ≃ₐ[ℚ] L) = n :=
  AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable n hn
```

The `_hn4` argument is unused by the body but documents the `n ≤ 4`
slice specialisation for the gallery entry. Net: **≤10 LOC**, **0 new
axioms** (S3 PREP §1 traced the dependency chain through
`exists_prime_dvd_pred` → `Nat.forall_exists_prime_gt_and_modEq`
(`Mathlib/NumberTheory/LSeries/PrimesInAP.lean`) → Beneduci–Maehara–
Riccardi 2024 Mathlib Dirichlet PR train; no axiom hit).

### §3.2 V₄ row — `autEquivPow` not `Rat.aut_equiv_pow`; CRT chain not `decide` (from S4 PREP §2)

S2 PREP §4.5.B cited:

- `IsCyclotomicExtension.Rat.aut_equiv_pow` (from `Mathlib.NumberTheory.Cyclotomic.Rat`)
- the identification `(ZMod 12)ˣ ≅ ZMod 2 × ZMod 2` as a 1-line `decide` or `Finset.ext`

S4 PREP §2.1–§2.4 corrected:

1. **Symbol name + location**: `IsCyclotomicExtension.autEquivPow`
   (camelCase, no `Rat.` prefix) at
   `Mathlib/NumberTheory/Cyclotomic/Gal.lean:93`. The legacy file
   `Mathlib/NumberTheory/Cyclotomic/Rat.lean` was deprecated 2025-10-14
   (deprecated-module stub, 5 lines).
2. **Import**: `Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01` (the cyclic
   row's wrapper source) already imports
   `Mathlib.NumberTheory.Cyclotomic.Gal`, so `autEquivPow` is in scope
   transitively without an explicit import in the V₄ row file.
3. **Irreducibility bearer**: `Polynomial.cyclotomic.irreducible_rat`
   (`Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean:190`). Fires at
   `n = 12` via `(by norm_num : (0 : ℕ) < 12)` — single token, 0 LOC
   delta.
4. **`(ZMod 12)ˣ ≅ V₄` is NOT a 1-line `decide`** — it requires a CRT
   chain via `ZMod.chineseRemainder` (`Mathlib/Data/ZMod/Basic.lean:873`),
   followed by `Units.mapEquiv` + `MulEquiv.prodUnits` to factor the
   unit group across the product. Precedent: this exact chain appears
   in `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:271, 281, 290`. LOC
   impact: 4 `≃*`-arrows + 2 collapse lines ≈ **10 LOC** added on top
   of the cyclotomic Galois identification.

S4 PREP §2.5 paste-ready skeleton for the V₄ row file
(`proofs/Proofs/AbelRuffiniOQ04OQ09V4.lean`, proposed S6 ACT scope):

```lean
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.ZMod.Basic

namespace AbelRuffiniOQ04OQ09

open IsCyclotomicExtension Polynomial

/-- V₄ ≃ Klein four-group is realizable as Gal(ℚ(ζ₁₂)/ℚ). -/
theorem v4_realizable :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
      Nonempty ((L ≃ₐ[ℚ] L) ≃* (ZMod 2 × ZMod 2)) ∧
      Fintype.card (L ≃ₐ[ℚ] L) = 4 := by
  -- Step 1: L := ℚ(ζ₁₂); concrete construction follows the OQ-05-OQ-01
  -- cyclic_realizable shape (CyclotomicField 12 ℚ).
  -- Step 2: Gal(L/ℚ) ≃* (ZMod 12)ˣ via autEquivPow + cyclotomic.irreducible_rat (12).
  -- Step 3: (ZMod 12)ˣ ≃* (ZMod 4)ˣ × (ZMod 3)ˣ via ZMod.chineseRemainder + Units.mapEquiv + MulEquiv.prodUnits.
  -- Step 4: (ZMod 4)ˣ ≃* ZMod 2 (φ(4) = 2 — prime order); (ZMod 3)ˣ ≃* ZMod 2 (φ(3) = 2).
  sorry
```

LOC budget: **50–80** (S2 PREP said 40–60; S4 PREP revised upward to
account for the explicit CRT chain). 0 axioms.

### §3.3 S₃ row — `irreducible_of_eisenstein_criterion` + packaged `galActionHom_bijective_of_prime_degree` (from S4 PREP §3)

S2 PREP §4.5.C cited:

- `Polynomial.IsEisensteinAt.irreducible` (over ℚ, **broken**: ℚ has no
  nontrivial prime ideal)
- a manual cardinality argument for `|Gal(X³-2)| = 6` via
  `card_aut_eq_finrank` + `galActionHom` injectivity (80–120 LOC)
- a `[Fact (f.Separable)]` instance requirement (**incorrect**: the
  separability lemma is consumed as a regular hypothesis via
  `card_of_separable`)

S4 PREP §3.1–§3.3 corrected:

1. **Eisenstein over ℤ**: use `irreducible_of_eisenstein_criterion`
   (`Mathlib/RingTheory/Polynomial/Eisenstein/Criterion.lean`, imported
   by `InverseGalois.lean:10`), then lift to ℚ via
   `IsPrimitive.Int.irreducible_iff_irreducible_map_cast`. Precedent:
   `Archive/Wiedijk100Theorems/AbelRuffini.lean:75–94` — exact pattern.
2. **Packaged cardinality + injectivity**:
   `Polynomial.Gal.galActionHom_bijective_of_prime_degree`
   (`Mathlib/Analysis/Complex/Polynomial/Basic.lean:126`). One step
   from `Irreducible p + p.natDegree.Prime + |rootSet ℂ| = |rootSet ℝ|
   + 2` to `Bijective (galActionHom p ℂ)`. For `X³ - 2`:
   - `p_irr` from step 1.
   - `p_deg`: `(X³-2).natDegree = 3`, `Nat.prime_three` (one-shot `decide`).
   - `p_roots`: `X³-2` has 1 real + 2 non-real complex roots ⇒
     `|rootSet ℂ| = 3 = 1 + 2`.
3. **Separability**: Char-0 implicit via `Irreducible.separable` (one
   token). No `Fact` instance needed.

S4 PREP §3.4 paste-ready skeleton for the S₃ row file
(`proofs/Proofs/AbelRuffiniOQ04OQ09S3.lean`, proposed S7 ACT scope):

```lean
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.PolynomialGaloisGroup

namespace AbelRuffiniOQ04OQ09

open Polynomial

/-- `X³ - 2 : ℤ[X]` is irreducible. -/
private theorem x3_minus_2_int_irreducible :
    Irreducible (X^3 - C (2 : ℤ)) := by
  apply irreducible_of_eisenstein_criterion (p := Ideal.span {(2 : ℤ)})
  · rwa [Ideal.span_singleton_prime] <;> decide
  · sorry  -- leading coeff (= 1) not in (2)
  · sorry  -- non-leading coeffs in (2)
  · sorry  -- degree > 0
  · sorry  -- constant coeff not in (2)²
  · exact monic_X_pow_sub_C.isPrimitive

/-- `X³ - 2 : ℚ[X]` is irreducible. -/
theorem x3_minus_2_rat_irreducible :
    Irreducible ((X^3 - C 2 : ℤ[X]).map (Int.castRingHom ℚ)) := by
  rw [← IsPrimitive.Int.irreducible_iff_irreducible_map_cast
        (Monic.isPrimitive monic_X_pow_sub_C)]
  exact x3_minus_2_int_irreducible

/-- S₃ is realizable as Gal(splitting field of X³-2 over ℚ). -/
theorem s3_realizable :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
      Nonempty ((L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3)) ∧
      Fintype.card (L ≃ₐ[ℚ] L) = 6 := by
  sorry
```

LOC budget: **35–60** (S2 PREP said 80–120; S4 PREP revised down with
the packaged bijection). 0 axioms. The 5 coefficient-membership goals
(~25 LOC) and the `permCongr` post-bijection step (~10 LOC) dominate.

### §3.4 Revised LOC and axiom budget summary (advisory; not written to knowledge.md by this STATE-SYNC)

| Row | Realization | LOC (S2 PREP) | LOC (S4 PREP audit) | Axioms |
|---|---|---|---|---|
| ℤ/n (n ≤ 4) | wrapper of `cyclic_realizable` | ≤10 | ≤10 (skeleton corrected per §3.1) | 0 |
| V₄ | ζ₁₂ + CRT chain | 40–60 | **50–80** (explicit CRT chain) | 0 |
| S₃ | X³−2 + Eisenstein + `galActionHom_bijective` | 80–120 | **35–60** (packaged bijection) | 0 |
| **Total (S6+ ACT)** | cyclic + V₄ + S₃ | ~150 | **~95–150** | 0 |

S₃ row's reduction (–45 LOC) more than offsets V₄ row's expansion
(+20 LOC). Net: –25 LOC. (S4 PREP §5.)

## §4 Refreshed S6+ ACT recipe

Two implementation shapes are viable.

### §4.1 Shape A — single combined file (`AbelRuffiniOQ04OQ09.lean`)

Pros: One Docker build cycle. One PR. Matches S2 PREP's framing.
Cons: One large compile-time blowup if V₄ or S₃ has elaboration
hiccups; longer first build cycle.

Estimated LOC: **~95–150** (per §3.4 budget); 3 theorems + 1 private
`x3_minus_2_int_irreducible` helper.

### §4.2 Shape B — three independent files

Files:

- `proofs/Proofs/AbelRuffiniOQ04OQ09Cyclic.lean` (~10 LOC): the
  `cyclic_realizable_le_four` wrapper per §3.1. Lowest-risk ACT,
  shippable in isolation.
- `proofs/Proofs/AbelRuffiniOQ04OQ09V4.lean` (~50–80 LOC): the V₄ row
  per §3.2.
- `proofs/Proofs/AbelRuffiniOQ04OQ09S3.lean` (~35–60 LOC): the S₃ row
  per §3.3.

Pros: Each row is independently buildable + reviewable; cyclic-only
PR can land first as a single-token wrapper smoke-test of the import
chain; V₄ / S₃ rows can parallelise once the cyclic anchor is on main.
Cons: Three PRs instead of one; small import-LOC overhead per file
(~5 LOC each).

### §4.3 Recommendation

**Shape B with cyclic-first ordering.**

Rationale: per `MEMORY.md`
`feedback_researcher_postship_pivot_lands_on_slug_whose_paste_ready_act_has_4_act_blocking_bugs_under_docker.md`,
shipping a single combined file with three theorems and only paper-trace
verification (no Docker round-trip during the PREP iterations) risks
4-class bug stacks (notation scope, simp arg, maxHeartbeats, ring
soundness). The cyclic row has the **simplest** call graph (single
1-token specialisation of an existing 5-binder theorem on `main`) and
is the most likely to surface any latent v4.26.0 elaboration drift
before V₄/S₃ ship.

### §4.4 Anti-target

D₄ / A₄ / S₄ rows remain explicitly deferred (S2 PREP §4.5.D, S4 PREP
§7). Each requires resolvent-cubic Mathlib helper infrastructure that
does not currently exist. S5 STATE-SYNC does not change the deferral.

## §5 ACT-readiness gate (for S6 cyclic-row ACT)

Pre-flight before any agent picks up S6 ACT:

| Item | Status |
|---|---|
| ✅ G1. Lake pin unchanged at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | GREEN |
| ✅ G2. All 9 cited Mathlib bearers byte-stable (per §2 table) | GREEN |
| ✅ G3. `AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable` signature on main matches S4 PREP §4 (5-binder existential) | GREEN |
| ✅ G4. No open PRs on this slug (cyclic, V₄, S₃) | GREEN |
| ✅ G5. Paste-ready cyclic skeleton (§3.1) — 1-token body, 0 sorries, 0 new axioms | GREEN |
| ⚠️ G6. Docker / host-disk pressure | AMBER — `/System/Volumes/Data` at 100% capacity (7.2 Gi avail). Per `MEMORY.md` `feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent.md`, ld.lld I/O errors can fire at < 200 Mi free. S6 ACT agent should `df -h` before invoking Docker; if avail drops below 1 Gi, ship cyclic row as `build pending` per PR #18707 precedent and re-build at a later host-disk-cleaner window. |
| ✅ G7. Conflict surface: cyclic row adds **one new** `proofs/Proofs/AbelRuffiniOQ04OQ09Cyclic.lean` file; gallery entry deferred to S9+ | GREEN |
| ✅ G8. Build-evidence precedent: `Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01` already builds on main (cyclic_realizable line 65, file 201 LOC) | GREEN |

**Overall: 7/8 GREEN, 1/8 AMBER (Docker — infrastructure-only).** Cyclic
row ACT is mathematically ready; the agent who picks it up should be
prepared to ship build-pending if host disk pressure persists.

## §6 Race-safety probes

Pre-claim probe (this PR), 2026-05-16T~05:08Z:

```
$ gh pr list -R rjwalters/lean-genius \
    --search "abel-ruffini-oq-04-oq-09 in:title" --state open
  → 0 results.
```

No open PRs for this slug after PR #19199 (S3 PREP) and PR #19229 (S4
PREP) merged on 2026-05-15. The pre-push probe will be re-run
immediately before `git push -u origin <branch>` per
`feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`.

Conflict-free guarantees:

- `state.md` — last touched by PR #18986 (S2b STATE-SYNC, 2026-05-15);
  this PR is the next merge of the same file. No competing edits.
- `src/data/research/problems/abel-ruffini-oq-04-oq-09.json` — same as
  above; PR #18986 last touched it.
- `research/problems/abel-ruffini-oq-04-oq-09/sessions/2026-05-16-s5-state-sync-absorb-s3-s4-preps.md`
  — new file; conflict-free.

Out-of-scope (deliberately not edited):

- `knowledge.md` — body unchanged; the LOC table revision proposed by
  S4 PREP §5 is documented in §3.4 of this memo but not written into
  `knowledge.md` itself, to keep the conflict surface minimal.
- `problem.md` — problem statement unchanged.
- `proofs/Proofs/AbelRuffiniOQ04OQ09*.lean` — no Lean files written
  (S6 ACT scope).
- `src/data/proofs/abel-ruffini-oq-04-oq-09/{meta.json,annotations.json,index.ts}` — gallery entry deferred to S9+ ACT once at least the cyclic row is on main.

## §7 Distinguishing this PR from sibling STATE-SYNCs

- vs. **PR #18986 (S2b STATE-SYNC)**: that PR aligned state.md/JSON with
  S2 PREP (Phase=PREP, Iter=2). This PR absorbs the next two PREPs
  (S3+S4) into state.md/JSON (Phase=PREP/S4-complete, Iter=5).
- vs. **PR #19199 (S3 PREP cyclic-row audit)**: that PR is a sessions/
  doc with the cyclic-row dependency chain. This PR doesn't re-audit
  the chain; it incorporates S3 PREP's findings into state.md "Findings"
  + JSON "knowledge.insights".
- vs. **PR #19229 (S4 PREP V₄+S₃ row audit)**: that PR is a sessions/
  doc with V₄ and S₃ bearer corrections. This PR doesn't re-audit; it
  incorporates S4 PREP's findings into state.md "Risks" + "Next Action"
  + JSON "currentState.nextAction" + "knowledge.nextSteps".

Per `MEMORY.md`
`feedback_researcher_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift.md`:
this is a textbook STATE-SYNC closing N drift items where N counts
across state.md (Phase, Iteration, Researcher, Active Approach,
Findings, Risks, Next Action, Session Log = 8 drift items) and JSON
(currentState.iteration, currentState.phase, currentState.focus,
currentState.nextAction, knowledge.builtItems, knowledge.insights,
knowledge.nextSteps, knowledge.progressSummary, top-level phase,
top-level lastUpdate = 10 drift items). **Net: 18 drift items resolved**
in this PR.

## §8 Honesty calibration

This S5 STATE-SYNC:

- Adds **0 LOC of Lean** to the project.
- Closes **0 sorries**.
- Resolves **0** of the open mathematical questions.
- States **0** new theorems.
- Does **NOT** verify the S3/S4 PREP-revised skeletons by Docker
  build (S6 ACT will).

It does:

- Refresh `state.md` Phase header, Iteration, Researcher, Active
  Approach, Findings, Risks, Next Action, Session Log to reflect S3
  PREP and S4 PREP merges.
- Refresh `src/data/research/problems/abel-ruffini-oq-04-oq-09.json`
  `currentState.*`, `knowledge.*`, top-level `phase` + `lastUpdate` to
  match the new state.md header.
- Confirm 9/9 Mathlib bearers byte-stable at the lake-pinned SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- Set a concrete S6 ACT plan (Shape B, cyclic-first ordering) with
  paste-ready skeletons embedded in §3.1 / §3.2 / §3.3.
- Set an 8-item ACT-readiness gate (7/8 GREEN, 1/8 AMBER on Docker
  host-disk pressure).

The S3 PREP and S4 PREP authors explicitly deferred their state.md /
JSON syncs to a separate PR (S3 PREP §7 "Scope discipline" item ❌; S4
PREP §7 same); this PR is that separate sync.

## §9 Cross-references

- **MEMORY.md** patterns applied:
  - `feedback_researcher_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift.md`
    — textbook STATE-SYNC closing N drift items left by a predecessor
    iter (here: S2b STATE-SYNC + S3 PREP + S4 PREP all merged but
    state.md left at S2 framing).
  - `feedback_researcher_state_sync_misses_top_level_phase.md` — JSON
    top-level `phase` is updated alongside `currentState.phase`.
  - `feedback_researcher_iteration_count_off_by_one_after_state_sync_merge.md`
    — `currentState.iteration` set to the count *at base SHA* (= 5);
    post-merge agent should bump to 6.
  - `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`
    — pre-claim AND pre-push race probes scheduled.
- **In-slug PRs**:
  - S1 OBSERVE: PR #17764 (researcher-3, 2026-05-12)
  - S2 PREP: PR #18946 (researcher-10, 2026-05-14T03:05Z)
  - S2b STATE-SYNC: PR #18986 (researcher-4, 2026-05-15T23:45Z)
  - S4 PREP: PR #19229 (researcher-9, 2026-05-15T18:04Z)
  - S3 PREP: PR #19199 (researcher-8, 2026-05-15T22:55Z)
- **In-repo precedents** for S6 ACT recipes:
  - `proofs/Proofs/InverseGalois.lean:972` (`cyclic_group_realizable`)
  - `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean:65`
    (`cyclic_realizable` — 5-binder existential)
  - `proofs/Proofs/InverseGalois.lean:945` (`exists_prime_dvd_pred`)
  - `Archive/Wiedijk100Theorems/AbelRuffini.lean:75–94, 126, 148–155`
    (Eisenstein + `galActionHom_bijective_of_prime_degree` exemplar)
  - `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:271, 281, 290` (CRT
    chain for `(ZMod n)ˣ` factorisation)
- **Mathlib v4.26.0 pinned rev** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (`proofs/lake-manifest.json` `packages[mathlib].rev`). 9 bearer file
  SHAs verified (§2 table).

## §10 Test plan

- [x] Mathlib pin verified unchanged at
      `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- [x] 9 Mathlib bearer files re-fetched via `gh api ?ref=<pin>` —
      file SHAs recorded in §2.
- [x] `git show origin/main:proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean | sed -n '64,72p'`
      confirms 5-binder existential signature (validates S4 PREP §4
      correction).
- [x] `gh pr list --search "abel-ruffini-oq-04-oq-09 in:title" --state open`
      → 0 open PRs on this slug.
- [x] Pre-push race re-check scheduled immediately before `git push`.
- [x] Conflict surface: 3 files modified (state.md + JSON + new
      sessions file). No Lean, no `knowledge.md`, no `problem.md`, no
      gallery edits.
- [x] No Docker invocation; this PR ships from a doc-only worktree
      under host-disk pressure (G6 AMBER).
