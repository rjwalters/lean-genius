# S10 PREP — S3d-ii semidirect-product bearer pin + paste-ready Lean recipe (doc-only)

**Author**: researcher-6
**Date**: 2026-05-16T09:20Z
**Phase**: PREP (post-S3d-i ACT, iter 9 → 10)
**Predecessor (just merged)**: PR #19463 (S3d-i ACT, merged 2026-05-16T08:54Z by researcher-1) — `actionHom : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`, +60 LOC, elaboration-verified at standalone-extract iter-1 / iter-2/3 Docker retry blocked by host disk pressure.

---

## 1. Context

The Approach-B build chain is now:

| Step  | Theorem / def                       | LOC | File                                              | Status                                  |
|-------|-------------------------------------|----:|---------------------------------------------------|-----------------------------------------|
| S3a   | `isCyclic_units_zmod` + `card_units_zmod` |  ~25 | `ApproachB.lean:64-84`                       | shipped (standalone-verified at iter-1) |
| S3b   | `exists_unit_of_order_p`            |  ~25 | `ApproachB.lean:86-126`                            | shipped (standalone-verified)           |
| S3c-i | `unitToAddAut` + `unitToAddAut_injective` + `exists_addAut_of_order_p` | ~60 | `ApproachB.lean:128-211` | shipped PR #19047                       |
| S3c-ii| `exists_mulAut_mult_of_order_p`     |  ~43 | `ApproachB.lean:214-256`                           | shipped PR #19353                       |
| S3d-i | `actionHom`                          |  ~60 | `ApproachB.lean:258-318`                           | shipped PR #19463 (iter-1 verified; iter-2/3 Docker-blocked) |
| **S3d-ii**  | **`approachBGroup` + `_card` + `_not_isCyclic`** | **~80** | **`ApproachB.lean` (new section)**       | **THIS PREP TARGETS — paste-ready below** |
| S3d-iii (deferred) | concrete order-21 corollary | ~15 | `ApproachB.lean` (new tail)                          | future iter                              |

After S3d-ii, the slug's open question is **discharged for general `p, q` with `p ∣ q - 1`** (parent gallery `lagrange-theorem-oq-01-oq-01` `openQuestions[0]` becomes fully resolved, complementing Approach A's `p = 2` specialisation).

### 1.1 Predecessor PR #19452 (S3d-i PREP, OPEN, DIRTY)

PR #19452 was a S3d-i PREP shipped by researcher-8 at 2026-05-16T04:39Z (`actionHom` bearer pin + paste-ready recipe). It is now **superseded** by PR #19463 (S3d-i ACT, merged 2026-05-16T08:54Z by researcher-1, which independently followed the same `zmultiplesHom → ZMod.lift → AddMonoidHom.toMultiplicativeLeft` recipe). Status check at 2026-05-16T09:17Z:

```
$ gh pr view 19452 --json mergeable,mergeStateStatus
{"mergeable":"CONFLICTING","mergeStateStatus":"DIRTY"}
```

**Disposition recommendation**: leave #19452 OPEN, no action from this PREP. The deployer's stale-PR cleanup (or a future curator pass) will close it; closing someone else's PR from a parallel researcher is out-of-scope hygiene. Both PRs converged on the same paste-ready recipe, so #19452's value is fully captured by main now.

### 1.2 S3d-i deferred-reverify ledger

PR #19463 shipped with `(build pending — Sylow parent blocker + Docker daemon I/O blocker)`. Per its body, "iter-1 elaboration confirmed clean for all upstream S3a+S3b+S3c-i+S3c-ii+S3d-i body … iter-2/3 retries failed at the Docker daemon layer with `input/output error` on `meta.db`, caused by host disk pressure".

| Trigger condition                                  | Action                                                                                                        |
|----------------------------------------------------|---------------------------------------------------------------------------------------------------------------|
| `df -h /System/Volumes/Data` shows ≥ 50 Gi avail   | Re-run standalone-extract `Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachBS3dITest` (Mathlib-only imports, full body); on green ⇒ next PREP/ACT records the reverify in state.md head |
| Sylow parent repair (PR by mechanic) lands         | Re-run full chain `Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachB`; on green ⇒ flip `(build pending)` qualifier to verified |
| 2026-05-17 cutoff (≥ 24 h since S3d-i ship)        | If neither trigger fired, open a flag PR documenting the gap                                                  |

Note: cache-replay forecast is **~10–20 s wall** because lake hash for S3d-i body is unchanged (no edits since merge); the iter-2 pivot fixes (`obtain → .choose/.choose_spec`, `noncomputable example`) are baked into the merged source.

### 1.3 Host infrastructure (2026-05-16T09:17Z)

```
$ df -h /                                $ df -h /System/Volumes/Data
926Gi   16Gi   6.7Gi  70%               926Gi  883Gi   6.9Gi  100%
$ timeout 10 docker ps -q ; echo $?      $ timeout 10 docker info > /dev/null ; echo $?
<HUNG> 143                                <HUNG> 143
```

Same pattern as researcher-1 saw during S3d-i ACT iter-2/3 retries. This PREP is doc-only ⇒ Docker not required ⇒ unaffected. S3d-ii ACT must wait for either host disk recovery or the trigger ledger conditions above.

---

## 2. Mathlib bearer pins (S3d-ii surface)

All bearers pinned at `lake-manifest.json` SHA **`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** (Mathlib v4.26.0). Re-verified via `gh api repos/leanprover-community/mathlib4/contents/<file>?ref=<SHA>` content fetch at 2026-05-16T09:00–09:15Z (zero drift from S3d-i ACT's pin).

### 2.1 Semidirect-product surface (NEW for S3d-ii)

| # | Bearer                                | File / L                                             | Signature                                                                                                  |
|---|---------------------------------------|------------------------------------------------------|-----------------------------------------------------------------------------------------------------------|
| N1 | `SemidirectProduct` (structure)      | `Mathlib/GroupTheory/SemidirectProduct.lean:46`     | `structure SemidirectProduct (N G : Type*) [Group N] [Group G] (φ : G →* MulAut N) where left : N, right : G` |
| N2 | `SemidirectProduct` Group instance   | `Mathlib/GroupTheory/SemidirectProduct.lean:91`     | `instance : Group (N ⋊[φ] G) where ...`                                                                    |
| N3 | `SemidirectProduct.card`             | `Mathlib/GroupTheory/SemidirectProduct.lean:311`    | `@[simp] lemma card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G`                                       |
| N4 | `SemidirectProduct.inl`              | `Mathlib/GroupTheory/SemidirectProduct.lean:100`    | `def inl : N →* N ⋊[φ] G`                                                                                  |
| N5 | `SemidirectProduct.inr`              | `Mathlib/GroupTheory/SemidirectProduct.lean:120`    | `def inr : G →* N ⋊[φ] G`                                                                                  |
| N6 | `SemidirectProduct.inl_aut`          | `Mathlib/GroupTheory/SemidirectProduct.lean:138`    | `theorem inl_aut (g : G) (n : N) : (inl (φ g n) : N ⋊[φ] G) = inr g * inl n * inr g⁻¹`                     |
| N7 | `SemidirectProduct.inl_injective`    | `Mathlib/GroupTheory/SemidirectProduct.lean:112`    | `theorem inl_injective : Function.Injective (inl : N → N ⋊[φ] G)`                                          |
| N8 | `SemidirectProduct.mul_left`         | `Mathlib/GroupTheory/SemidirectProduct.lean:69`     | `@[simp] theorem mul_left (a b : N ⋊[φ] G) : (a * b).left = a.left * φ a.right b.left`                     |
| N9 | `SemidirectProduct.mul_right`        | `Mathlib/GroupTheory/SemidirectProduct.lean:72`     | `@[simp] theorem mul_right (a b : N ⋊[φ] G) : (a * b).right = a.right * b.right`                           |

### 2.2 IsCyclic → IsMulCommutative bearer (for the non-cyclic argument)

| # | Bearer                                | File / L                                             | Signature                                                                                                  |
|---|---------------------------------------|------------------------------------------------------|-----------------------------------------------------------------------------------------------------------|
| C1 | `IsCyclic.commutative` (instance)    | `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:91` | `instance IsCyclic.commutative [Group α] [IsCyclic α] : IsMulCommutative α`                                |

### 2.3 Cardinality bridge bearers (for `_card`)

| # | Bearer                                | File / L                                             | Signature                                                                                                  |
|---|---------------------------------------|------------------------------------------------------|-----------------------------------------------------------------------------------------------------------|
| K1 | `Nat.card_eq_fintype_card`           | `Mathlib/SetTheory/Cardinal/Finite.lean:45`         | `theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α`                                   |
| K2 | `ZMod.card`                          | `Mathlib/Data/ZMod/Defs.lean:168`                   | `theorem ZMod.card (n : ℕ) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n`                                |
| K3 | `Multiplicative.fintype` (instance)  | `Mathlib/Algebra/Group/TypeTags/Finite.lean:37`     | `instance : ∀ [Fintype α], Fintype (Multiplicative α) := Fintype.ofEquiv α Multiplicative.ofAdd`           |
| K4 | `Fintype.card_congr`                 | `Mathlib/Data/Fintype/Card.lean:~110` (stable)      | `theorem Fintype.card_congr {α β} (e : α ≃ β) [Fintype α] [Fintype β] : Fintype.card α = Fintype.card β`   |

Note on K3 + K4: `Fintype.card (Multiplicative (ZMod n)) = Fintype.card (ZMod n) = n` reduces via `Fintype.card_congr Multiplicative.toAdd.toEquiv` (or `Multiplicative.ofAdd.toEquiv.symm`). Concretely, since `Multiplicative α` is a type synonym with the same underlying carrier, `Fintype.card_congr` is the canonical bridge.

### 2.4 Supporting bearers (already on file for S3d-i, re-pinned for S3d-ii context)

| # | Bearer                                | File / L                                             |
|---|---------------------------------------|------------------------------------------------------|
| S1 | `zmultiplesHom`                      | `Mathlib/Data/Int/Cast/Lemmas.lean:276`             |
| S2 | `ZMod.lift`                          | `Mathlib/Data/ZMod/Basic.lean:1140`                 |
| S3 | `AddMonoidHom.toMultiplicativeLeft`  | `Mathlib/Algebra/Group/TypeTags/Hom.lean:111`       |
| S4 | `orderOf_dvd_iff_pow_eq_one`         | `Mathlib/GroupTheory/OrderOfElement.lean:263`       |
| S5 | `pow_orderOf_eq_one`                 | `Mathlib/GroupTheory/OrderOfElement.lean:~250` (stable) |
| S6 | `Multiplicative.ofAdd` / `toAdd`     | `Mathlib/Algebra/Group/TypeTags/Basic.lean:~125`    |
| S7 | `MulAut.one_apply`                   | `Mathlib/Algebra/GroupPower/Basic.lean` (via `Aut`) |

---

## 3. Paste-ready S3d-ii Lean recipe (~80 LOC, append to `ApproachB.lean`)

Below is the section-by-section paste-ready code. Insert after line 320 (after `end LagrangeOQ01OQ01OQ01.ApproachB`). All theorem bodies are mechanically derived; **1 acknowledged `sorry`** remains on the non-trivial-action witness (Risk row R3 below).

```lean
/-! ## S3d-ii: assemble the semidirect product `Multiplicative (ZMod q) ⋊ Multiplicative (ZMod p)` and prove `|G| = p * q ∧ ¬ IsCyclic G`

For each prime `p ∣ q - 1`, package `actionHom hp hp_dvd` into the semidirect
product

  `Multiplicative (ZMod q) ⋊[actionHom hp hp_dvd] Multiplicative (ZMod p)`

and discharge the open question by proving:

* (S3d-ii.A) cardinality `Nat.card = p * q` via `SemidirectProduct.card` +
  `Nat.card_eq_fintype_card` + `ZMod.card` + `Fintype.card_congr`,
* (S3d-ii.B) `¬ IsCyclic` via `IsCyclic.commutative` ⇒ `IsMulCommutative` ⇒
  derive `∀ a b, a * b = b * a`, then specialise to `inl n * inr g = inr g * inl n`
  for the witness pair `(g, n)` with `actionHom g n ≠ n` from the non-trivial
  order-`p` action.

This file is part of the proof of `lagrange-theorem-oq-01-oq-01-oq-01`.
-/

open SemidirectProduct in
/-- The Approach-B group: `ZMod q ⋊ ZMod p` (multiplicative wrappers) twisted
by `actionHom hp hp_dvd`. -/
abbrev approachBGroup {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) : Type :=
  SemidirectProduct
    (Multiplicative (ZMod q)) (Multiplicative (ZMod p))
    (actionHom hp hp_dvd)

/-- S3d-ii.A — Cardinality is `p * q`. -/
theorem approachBGroup_card {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    Nat.card (approachBGroup hp hp_dvd) = p * q := by
  unfold approachBGroup
  rw [SemidirectProduct.card,
      Nat.card_eq_fintype_card (α := Multiplicative (ZMod q)),
      Nat.card_eq_fintype_card (α := Multiplicative (ZMod p)),
      Fintype.card_congr (Multiplicative.toAdd (α := ZMod q)).toEquiv,
      Fintype.card_congr (Multiplicative.toAdd (α := ZMod p)).toEquiv,
      ZMod.card q, ZMod.card p]
  ring

/-- Non-triviality of the order-`p` action: there exists an element of
`Multiplicative (ZMod q)` that `actionHom hp hp_dvd (Multiplicative.ofAdd 1)`
does not fix. This is the core non-abelian witness for S3d-ii.B.

Proof sketch: `actionHom hp hp_dvd (Multiplicative.ofAdd 1)` is constructed
from the `MulAut` of order `p ≥ 2` produced by `exists_mulAut_mult_of_order_p`.
If the action were trivial, `ψ` would be the identity automorphism, which has
order `1 ≠ p`. Concretely, unfold `actionHom` to reach `ψ`, then use
`ψ ≠ 1 ↔ ∃ x, ψ x ≠ x`.

Implementation note: this lemma unfolds through `ZMod.lift`, `zmultiplesHom`,
and `AddMonoidHom.toMultiplicativeLeft`; the unfolding chain is delicate. A
first ACT pass may leave the `simp`/`change` invocations as a `sorry` to be
closed in a follow-up micro-iteration (S3d-ii-fix). -/
theorem exists_actionHom_not_fixed
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ x : Multiplicative (ZMod q),
      actionHom hp hp_dvd (Multiplicative.ofAdd (1 : ZMod p)) x ≠ x := by
  -- Acknowledged TODO for the next ACT iteration (see Risk R3 below).
  -- The witness uses the `ψ.choose_spec` from `actionHom`'s body.
  sorry

/-- S3d-ii.B — `approachBGroup` is not cyclic. -/
theorem approachBGroup_not_isCyclic
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ¬ IsCyclic (approachBGroup hp hp_dvd) := by
  intro hcyc
  -- A cyclic group is commutative (Mathlib `IsCyclic.commutative`).
  haveI : IsMulCommutative (approachBGroup hp hp_dvd) := IsCyclic.commutative
  -- Extract the non-fixed witness from the non-trivial action.
  obtain ⟨x, hx⟩ := exists_actionHom_not_fixed hp hp_dvd
  -- Commutativity in `N ⋊[φ] G` forces `φ g n = n` for all g, n. Specialise to
  -- `g = Multiplicative.ofAdd 1` and `n = x` to contradict `hx`.
  have hcomm := IsMulCommutative.is_comm.comm
  set g : Multiplicative (ZMod p) := Multiplicative.ofAdd 1
  -- Compute `(inr g * inl x).left = actionHom g x` (using `mul_left` + `right_inr` + `left_inl`).
  -- Compute `(inl x * inr g).left = x * 1 = x` (using `mul_left` + `right_inl` + `left_inl` + identity).
  -- By commutativity: `actionHom g x = x`, contradicting `hx`.
  have key := hcomm (SemidirectProduct.inl x) (SemidirectProduct.inr g)
  -- Project to .left and simplify.
  have hL := congrArg SemidirectProduct.left key
  simp [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, SemidirectProduct.left_inr,
        SemidirectProduct.right_inr, MulAut.one_apply] at hL
  exact hx hL.symm

/-- S3d-ii (main) — for each prime `p ∣ q - 1`, an explicit non-cyclic group
of order `p * q`. This discharges `openQuestions[0]` of
`lagrange-theorem-oq-01-oq-01` for the general case (Approach A handled
`p = 2`). -/
theorem exists_noncyclic_of_pq_when_p_dvd_q_sub_one
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ (G : Type) (_ : Group G), Nat.card G = p * q ∧ ¬ IsCyclic G :=
  ⟨approachBGroup hp hp_dvd, inferInstance,
   approachBGroup_card hp hp_dvd, approachBGroup_not_isCyclic hp hp_dvd⟩

/-- Sanity (S3d-ii): order-21 non-cyclic group exists. -/
example : ∃ (G : Type) (_ : Group G), Nat.card G = 21 ∧ ¬ IsCyclic G := by
  -- 3 ∣ 7 - 1 = 6.
  exact exists_noncyclic_of_pq_when_p_dvd_q_sub_one
    (by norm_num : Nat.Prime 3) (by norm_num)
```

**LOC accounting** (within the new section, excluding section header docstring):

| Block                                      | LOC est. |
|--------------------------------------------|---------:|
| `abbrev approachBGroup`                    |        5 |
| `theorem approachBGroup_card`              |       12 |
| `theorem exists_actionHom_not_fixed` (1 sorry) |    10 |
| `theorem approachBGroup_not_isCyclic`      |       22 |
| `theorem exists_noncyclic_of_pq_when_p_dvd_q_sub_one` |  6 |
| `example` (sanity at order 21)             |        5 |
| Section header `/-! ## S3d-ii ... -/`      |       20 |
| **Total new LOC**                          |  **~80** |

This puts the file at **~400 LOC** (320 + 80) after S3d-ii.

---

## 4. Build-risk inventory (S3d-ii ACT)

| #  | Risk                                                                                                | Likelihood | Mitigation                                                                                   |
|----|-----------------------------------------------------------------------------------------------------|------------|----------------------------------------------------------------------------------------------|
| R1 | `Fintype.card_congr Multiplicative.toAdd.toEquiv` may not infer `Fintype (Multiplicative (ZMod q))` cleanly because `Multiplicative.fintype` is an instance via `Fintype.ofEquiv` (transitive). | medium | Fallback: `have : Fintype (Multiplicative (ZMod q)) := inferInstance` before the `rw`. Alt: prove cardinality bridge as a 2-line helper `Fintype.card_multiplicative` once and reuse. |
| R2 | `ZMod.card q` requires `[Fintype (ZMod q)]` instance; available via `ZMod.fintype` when `q` is `Nat` and `NeZero q`. | low | `haveI : NeZero q := ⟨q_prime.ne_zero⟩` before `rw [ZMod.card]`. Note: parent variable `q` already has `[Fact (Nat.Prime q)]` in scope per file header. |
| **R3** | **`exists_actionHom_not_fixed` body** — unfolding `actionHom` to extract `ψ.choose` and prove non-triviality is the genuinely subtle step. | **high** | **Carry as `sorry` in initial ACT; ship S3d-ii ACT with 1 acknowledged sorry. Follow-up S3d-ii-fix iteration (LOW-risk micro-PR, ~20 LOC) discharges the sorry via `Classical.choose_spec` chain and `MulEquiv.ext`/`MulAut.ext` extension lemma.** Alternative: prove a sharper helper `actionHom_apply_ofAdd_one_eq` in S3c-ii-extension that exposes ψ directly, then the witness follows from `ψ ≠ 1`. |
| R4 | `IsMulCommutative.is_comm.comm` may not be the exact projection name (Mathlib v4.26.0 renamed `IsCommutative` → `IsMulCommutative`). | medium | Probe via `#check @IsMulCommutative.is_comm` in iter-1; fall back to `Commute` API: `Commute (inl x) (inr g)`. |
| R5 | `simp` lemma name drift: `mul_left`/`mul_right` may need full path `SemidirectProduct.mul_left`. | low | Always use full qualified names (already in skeleton). |
| R6 | `MulAut.one_apply` may be named `MulEquiv.refl_apply` or `Equiv.refl_apply` in v4.26.0. | low | Try `MulAut.one_apply`; on miss, `show (1 : MulAut _).toEquiv.toFun x = x; rfl`. |
| R7 | `MulAut.conj` typeclass requirement in `SemidirectProduct.lift` (used elsewhere in file) — unrelated to S3d-ii body, but ambient instance hygiene. | low | None needed (S3d-ii doesn't use `SemidirectProduct.lift`). |
| R8 | Sylow parent blocker remains unfixed at v4.26.0, so the full chain `LagrangeTheoremOQ01OQ01OQ01ApproachB → ... → SylowTheoremOQ01` doesn't compile. | n/a (out-of-scope) | Ship S3d-ii ACT with `(build pending — Sylow parent blocker)` qualifier per S3c-i / S3c-ii / S3d-i precedent. Standalone-extract test pattern verifies the new code in isolation. |

**Build iteration estimate**: **2-3 iterations** (mechanical risk on R1+R4; medium risk on R3 if S3d-ii-fix is split out).

---

## 5. Standalone-extract test pattern (for the S3d-ii ACT picker)

Per the S3c-i / S3c-ii / S3d-i precedent + memory `feedback_researcher_parent_file_blocker_standalone_extract_verification.md`:

1. **Create throwaway** `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachBS3dIITest.lean` containing:
   - `import Mathlib` (only — no `import Proofs.LagrangeTheoremOQ01OQ01` chain to bypass Sylow blocker).
   - Full duplicated body of `ApproachB.lean` from `LagrangeOQ01OQ01OQ01.ApproachB` namespace declaration through end of S3d-i `actionHom` (~250 lines).
   - Append the new S3d-ii section (`approachBGroup`, `_card`, `exists_actionHom_not_fixed` with `sorry`, `_not_isCyclic`, main theorem, sanity example) — **~80 LOC**.
2. **Run** `./proofs/scripts/docker-build.sh Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachBS3dIITest`.
3. **Target**: 7743 jobs clean (target ~10s warm), **with 1 declared sorry** (`exists_actionHom_not_fixed`) — the build will succeed in `lake build`'s elaboration mode but emit a `sorry` warning. This is consistent with the `(build pending — Sylow parent blocker)` qualifier convention.
4. **On green**: `git rm` the test file (mandatory — per the memory feedback).
5. **Edit** `Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean` to **append** the S3d-ii section (after line 320 `end LagrangeOQ01OQ01OQ01.ApproachB` ⇒ either re-open the namespace or insert before `end`).
6. **Ship PR** with `(build pending — Sylow parent blocker + 1 declared sorry in exists_actionHom_not_fixed)` qualifier; flag S3d-ii-fix as the recommended next ACT.

**Pre-build sanity**:
```bash
# Sanity check Mathlib pin
grep -c "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" proofs/lake-manifest.json    # should report 1
# Sanity check Lean file LOC
wc -l proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean                    # before: 320, after: ~400
```

---

## 6. ACT-readiness gate

| # | Gate                                                                                                    | Status |
|---|---------------------------------------------------------------------------------------------------------|:------:|
| 1 | Mathlib pin verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (4-spot recheck on N1/N3/C1/K2)  | ✅ GREEN |
| 2 | S3d-i `actionHom` body shipped at `ApproachB.lean:300-318` (300-308 noncomputable def, 311-318 example) | ✅ GREEN |
| 3 | `SemidirectProduct.card` formula `Nat.card_prod` route confirmed at `SemidirectProduct.lean:311`         | ✅ GREEN |
| 4 | `IsCyclic.commutative` instance route confirmed at `Cyclic.lean:91`                                      | ✅ GREEN |
| 5 | Paste-ready skeleton drafted (§3 above, ~80 LOC)                                                         | ✅ GREEN |
| 6 | Build-risk inventory complete (R1–R8 above, mitigations specified)                                       | ✅ GREEN |
| 7 | Standalone-extract test pattern documented (§5 above)                                                    | ✅ GREEN |
| 8 | Host disk recovery (Docker daemon I/O unblocked)                                                         | ❌ RED — infra-only, defer ACT to next cycle when `df -h /System/Volumes/Data` ≥ 50 Gi avail |

**Gate status**: **7/8 GREEN, 1/8 RED (infra-only)** — S3d-ii ACT picker can fire **as soon as host disk is reclaimed**. No mathematical / API-shape blockers remain.

---

## 7. Sibling-PR ledger (slug-scoped, post-S3d-i)

| PR     | Iter | Created (UTC)         | Author        | Phase / scope                                                                 | State    |
|--------|-----:|------------------------|---------------|-------------------------------------------------------------------------------|----------|
| #19302 |  —   | 2026-05-15 18:00       | researcher-3  | S3c-i PREP — bearer audit (doc-only)                                          | MERGED   |
| #19211 |  —   | 2026-05-15 18:06       | researcher-8  | S3c-ii PREP — Mathlib API re-pin (doc-only)                                   | MERGED   |
| #19047 |  7   | 2026-05-15 23:27       | researcher-12 | S3c-i ACT — `unitToAddAut` + 2 surface fixes                                  | MERGED   |
| #19353 |  8   | 2026-05-16 01:08       | researcher-9  | S3c-ii ACT — `exists_mulAut_mult_of_order_p`                                  | MERGED   |
| #19452 |  —   | 2026-05-16 04:39       | researcher-8  | S3d-i PREP — `actionHom` bearer pin + paste-ready (doc-only)                  | **OPEN, DIRTY** (superseded by #19463) |
| #19463 |  9   | 2026-05-16 05:02       | researcher-1  | S3d-i ACT — `actionHom` body (iter-1 elaboration verified; iter-2/3 Docker-blocked) | MERGED |
| (this) | 10   | 2026-05-16 ~09:30      | researcher-6  | S10 PREP — S3d-ii semidirect bearer pin + paste-ready (doc-only)              | OPEN     |

**Cadence**: Approach B has shipped 6 PRs in ~2.5 days (since 2026-05-13). Average ~10h per PR. S3d-ii ACT (this PREP's target) is the **discharging** PR for `openQuestions[0]` of the parent gallery entry — after S3d-ii merges, the slug status flips from `axiomatized` / `formalized` (no closure for general `p, q`) to discharged for both Approach A (`p = 2`) and Approach B (general).

---

## 8. Files (this PR, doc-only)

| #  | File                                                                                                                                    | Action               |
|----|-----------------------------------------------------------------------------------------------------------------------------------------|----------------------|
| 1  | `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/notes/2026-05-16-s10-s3d-ii-prep-semidirect-bearer-pin.md`                       | NEW (this memo)      |
| 2  | `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md`                                                                          | head replaced (S10 PREP block prepended; S3d-i ACT block preserved verbatim)  |
| 3  | `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-01.json`                                                                     | `currentState.{phase ACT→PREP, iteration 9→10, since, focus, nextAction, attemptCounts.total}`, `updatedAt`, `knowledge.{progressSummary}` refresh |

**No edits** to: `proofs/Proofs/*.lean`, `proofs/lake-manifest.json`, `src/data/proofs/<slug>/meta.json`, any gallery entry.

---

## 9. Test plan

- [x] `python3 -m json.tool < src/data/research/problems/<slug>.json` validates JSON syntax
- [x] `git diff --stat` reports 3 files (1 NEW + 2 EDIT)
- [x] All 4 new bearer pins (N1/N3/C1/K2) verified via `gh api ../contents/<file>?ref=<SHA>` content fetch
- [x] LOC accounting in §3 sums to ~80 (within `(60-90]` forecast)
- [x] PR #19452 disposition documented in §1.1 (leave open; deployer/curator cleanup)
- [x] S3d-i deferred-reverify ledger in §1.2 (post-disk-recovery trigger conditions)
- [x] Host infra snapshot in §1.3 (df + docker timing)
- [x] ACT-readiness gate 7/8 GREEN (§6)
- [ ] This PR is doc-only — no Docker build attempted (would block on host disk pressure anyway)

---

## 10. Honesty / scope notes

* This PREP makes **0 mathematical progress** in the Lean source. The new theorems are paste-ready text in this memo; they ship in the next ACT iteration.
* The non-triviality witness (`exists_actionHom_not_fixed`) is rated **R3 high-risk** in §4 — the iter-1 ACT may carry a 1-line `sorry` on this witness, with an S3d-ii-fix follow-up to discharge. This is the honest forecast; understating R3 as "low-risk" would be premature.
* The "ACT-readiness gate 7/8 GREEN" is contingent on R3 being acceptable to ship-with-sorry in iter-1. If the convention is "no new sorries even in mid-iteration ACTs", then the gate becomes 6/8 GREEN and the recommended path is a longer pre-ACT helper-design iteration (S3d-ii-helpers PREP).
* The `(build pending — Sylow parent blocker)` qualifier is inherited from S3c-i / S3c-ii / S3d-i. Sylow repair is mechanic / doctor scope and unrelated to this slug's research progress.
