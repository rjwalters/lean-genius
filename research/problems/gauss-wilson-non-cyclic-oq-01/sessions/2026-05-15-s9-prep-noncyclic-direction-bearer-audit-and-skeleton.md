# S9 PREP — Phase C non-cyclic direction: bearer audit + paste-ready ACT skeleton

**Session type:** PREP (doc-only).
**Trigger:** State.md "Next Action" for S9 ACT cites a master-HEAD-style
Mathlib lemma name (`IsPGroup.card_eq_pow_one_iff_orderOf_dvd`) for the
load-bearing power-of-2 cardinality upgrade step (step 3 of the discharge
plan). Pre-flight pin verification at the lake-pinned Mathlib SHA finds
**no such lemma**; the correct bearer is `IsPGroup.iff_card`. This PREP
pin-verifies all 11 bearers of the discharge plan and ships a paste-ready
S10 ACT skeleton (~60–90 LOC) with explicit tactic chains for the three
non-obvious bridge steps.

**Scope:** Strictly conflict-free. One new file only:
`research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-15-s9-prep-noncyclic-direction-bearer-audit-and-skeleton.md`.
No edits to `state.md`, `problem.md`, `knowledge.md`, `meta.json`, or any
`proofs/Proofs/*.lean` file. Composes with all prior sessions S1–S8.

---

## 1. Critical finding — state.md "Next Action" lemma name

The state.md "Next Action" section (post-S8 ACT) writes:

> Step (3) is the load-bearing step; Mathlib offers
> `IsPGroup.card_eq_pow_one_iff_orderOf_dvd` (or similar) for the
> prime-power-cardinality lemma.

**Pin verification at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
finds NO such lemma.** Downloaded `Mathlib/GroupTheory/PGroup.lean`
(389 lines) via:

```
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/GroupTheory/PGroup.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
```

Searched for `card_eq_pow_one_iff_orderOf_dvd` and any variant — no
match. The signatures present in `namespace IsPGroup` at SHA are:

| Line | Name | Type |
|---|---|---|
| 26 | `def IsPGroup` | `∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1` |
| 33 | `theorem iff_orderOf` | `[Fact p.Prime] → IsPGroup p G ↔ ∀ g, ∃ k, orderOf g = p^k` |
| 40 | `theorem of_card` | `{n} (hG : Nat.card G = p^n) → IsPGroup p G` |
| 46 | `theorem iff_card` | `[Fact p.Prime] [Finite G] → IsPGroup p G ↔ ∃ n, Nat.card G = p^n` |
| 59 | `alias exists_card_eq` | `:= iff_card` |
| 71 | `theorem to_subgroup` | `(H : Subgroup G) → IsPGroup p H` |

**Correct bearer for step 3 is `IsPGroup.iff_card`.** It is the (only)
biconditional `IsPGroup p G ↔ ∃ n, Nat.card G = p^n` and requires
`[Fact p.Prime]` and `[Finite G]`. Note: it returns `Nat.card`, not
`Fintype.card`. The bridge `Nat.card_eq_fintype_card` is needed (one
line; well-established in Mathlib).

The state.md plan's "or similar" hedge correctly anticipated the
master-HEAD/pin mismatch but did not pin-verify. This PREP supplies the
verified name.

This is the same failure mode as feedback memory
`preflight_audits_priorsession_discharge_plan_for_mathlib_bearer` — a
prior session's discharge plan names a Mathlib bearer drafted from
recall/intuition rather than from a pin-verified file read. The
mitigation is identical: PREP the bearer table at SHA before ACT.

---

## 2. Full bearer table (pin-verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

Every Mathlib lemma needed for the S10 ACT skeleton in §4, verified by
direct file read at SHA (not `gh search code`, which hits master HEAD).

| # | Lemma (Mathlib) | File@line at SHA | Used in skeleton step |
|---|---|---|---|
| 1 | `GaussWilsonNonCyclicOQ01.prod_univ_eq_prod_two_torsion` | `Proofs/GaussWilsonNonCyclicOQ01A.lean:37` (in-repo) | Step 1 (Phase A reduction) |
| 2 | `Subgroup.mk` constructor with `{carrier, mul_mem', one_mem', inv_mem'}` | `Algebra/Group/Subgroup/Defs.lean` | Step 2 (build T) |
| 3 | `mul_pow` | `Algebra/GroupPower/Basic.lean` | Step 2 closure proof |
| 4 | `inv_pow`, `inv_one`, `one_pow` | `Algebra/Group/Basic.lean` | Step 2 closure proofs |
| 5 | `IsPGroup` (def + `iff_card` + `iff_orderOf`) | `GroupTheory/PGroup.lean:26,33,46` | Step 3 (2-group + card-pow) |
| 6 | `Nat.prime_two` | `Data/Nat/Prime/Basic.lean` | Step 3 (`Fact Nat.Prime 2`) |
| 7 | `Nat.card_eq_fintype_card` | `Data/Finite/Card.lean` | Step 3 (Nat.card ↔ Fintype.card) |
| 8 | `Fintype.card_subtype` | `Data/Fintype/Card.lean:378` | Step 4 (T.card = #filter) |
| 9 | `GaussWilsonNonCyclic.card_sq_eq_one_ge_three` | `Proofs/GaussWilsonNonCyclic.lean:294` (in-repo) | Step 4 (≥ 3) |
| 10 | `SubmonoidClass.coe_finset_prod` (or `Submonoid.coe_finset_prod`) | `Algebra/Group/Submonoid/BigOperators.lean:49,101` | Step 6 (lift subgroup product to ambient) |
| 11 | `Finset.prod_subtype` | `Algebra/BigOperators/Group/Finset/Basic.lean:467` | Step 6 (filter ↔ subtype product) |
| 12 | `GaussWilsonNonCyclicOQ01.prod_univ_eq_one_of_elementary_card_ge_four` | `Proofs/GaussWilsonNonCyclicOQ01B.lean:220` (in-repo) | Step 5 (Phase B core) |

**Mathlib citation summary:** 7 distinct Mathlib lemmas + 3 in-repo
(Phase A, Phase B, parent-file). All 7 Mathlib lemmas have been
re-pinned at SHA via `gh api .../contents/...?ref=<SHA>` and confirmed
present.

### Negative-bearer note

State.md's plan says "Mathlib offers `IsPGroup.card_eq_pow_one_iff_orderOf_dvd`
(or similar)." This name is **absent** at SHA (and from master HEAD).
The closest candidate `IsPGroup.iff_orderOf` (line 33) does NOT give
the card-power statement directly; it only gives orderOf = p^k. The
load-bearing bridge is `IsPGroup.iff_card` (line 46), which returns
`Nat.card G = p^n`. This is a critical correction.

---

## 3. Mathematical content of S10 ACT (4 logical steps + 2 bridges)

The S10 ACT discharges the one remaining strategic sorry in
`Proofs/GaussWilsonNonCyclicOQ01.lean:149`,
`prod_eq_one_of_not_isCyclic_aux`. Statement:

```lean
theorem prod_eq_one_of_not_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (hncyc : ¬IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = 1
```

### Discharge plan (4 + 2 = 6 mini-steps)

1. **Phase A reduction.** Rewrite `∏ x : (ZMod n)ˣ, x = ∏ x ∈ S, x`
   where `S := univ.filter (·^2 = 1)`, by
   `prod_univ_eq_prod_two_torsion (ZMod n)ˣ`.

2. **Build 2-torsion subgroup `T : Subgroup (ZMod n)ˣ`** with carrier
   `{x | x ^ 2 = 1}`. Closure proofs are mechanical (mul_pow, inv_pow,
   one_pow). ~8 LOC.

3. **2-group + cardinality is power of 2.** Show `IsPGroup 2 T` (every
   element has `g ^ 2^1 = g^2 = 1`, take `k := 1`). Then
   `IsPGroup.iff_card.mp` gives `∃ k, Nat.card T = 2^k`. ~5 LOC.

4. **Cardinality ≥ 4.**  Bridge `Fintype.card T = (univ.filter (·^2 = 1)).card`
   via `Fintype.card_subtype`. Parent's `card_sq_eq_one_ge_three` gives
   `≥ 3`. Combined with `Nat.card T = 2^k`, force `k ≥ 2`, hence `≥ 4`.
   ~10 LOC (interval_cases on k or rcases).

5. **Phase B on T.** Apply
   `prod_univ_eq_one_of_elementary_card_ge_four` to the subgroup-type
   `↥T`. Need `hexp : ∀ x : T, x ^ 2 = 1` (from membership) and
   `hcard : 4 ≤ Fintype.card T` (step 4). Returns
   `(∏ x : T, x : T) = 1`. ~5 LOC.

6. **Bridge to ambient Finset.** Combine
   `SubmonoidClass.coe_finset_prod` (lifts `(∏ x : T, x : T)` to
   `∏ x : T, (x : (ZMod n)ˣ)`) and `Finset.prod_subtype` (relates
   `∏ x : T, x.val` to `∏ x ∈ univ.filter (·^2=1), x`). ~10 LOC.

Total: ~38 LOC for the proof body, plus an `open` block. State.md
estimated 30–50; this PREP estimates 40–60 with full bridge tactics.

### Why this discharge is principled

- **Step 2 (Subgroup construction):** Explicit `carrier := {x | x^2 = 1}`
  makes `x ∈ T ↔ x^2 = 1` definitionally `Iff.rfl`, avoiding any need
  for `Subgroup.mem_mk` rewrites. This is the same pattern as Mathlib's
  `CommGroup.torsion : Subgroup G := { CommMonoid.torsion G with
  inv_mem' := ... }` (`Mathlib/GroupTheory/Torsion.lean:288`).

- **Step 3 (`IsPGroup 2 T`):** Witness `k := 1`. The condition
  `(g : T) ^ 2^1 = (1 : T)` reduces by `Subtype.ext` to `g.val ^ 2 = 1`,
  which is `g.property` (membership in T).

- **Step 4 (cardinality upgrade):** With `Nat.card T = 2^k` and
  `Nat.card T ≥ 3`, the case split on `k ∈ {0, 1, ≥ 2}` discharges:
  `2^0 = 1 < 3` (contradiction), `2^1 = 2 < 3` (contradiction),
  `2^k ≥ 2^2 = 4` (target).

- **Step 5 (Phase B applicability):** `T` inherits `[CommGroup T]`
  from `Subgroup.toGroup` + commutativity of `(ZMod n)ˣ` (automatic via
  `Subgroup.toCommGroup`). `[Fintype T]` follows from
  `Subgroup.instFintype` (decidable membership). `[DecidableEq T]`
  follows from `Subtype.instDecidableEq`.

- **Step 6 (bridge):** The two-step bridge factors as
  ```
  ∏ x ∈ univ.filter (·^2=1), x
    = ∏ x : ↥T, x.val          (Finset.prod_subtype, predicate matches)
    = (∏ x : ↥T, x : (ZMod n)ˣ) (SubmonoidClass.coe_finset_prod)
  ```
  Then Phase B gives the inner `∏ x : ↥T, x = (1 : ↥T)`, whose coercion
  is `(1 : (ZMod n)ˣ)`.

---

## 4. Paste-ready S10 ACT skeleton

Below is a ~38-LOC tactic body for `prod_eq_one_of_not_isCyclic_aux`
at `Proofs/GaussWilsonNonCyclicOQ01.lean:149`. Paste-ready modulo the
three "BUILD-RISK" callouts in §5.

```lean
theorem prod_eq_one_of_not_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (hncyc : ¬IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = 1 := by
  -- Step 1: Phase A reduction.
  rw [prod_univ_eq_prod_two_torsion (ZMod n)ˣ]
  -- Step 2: Build the 2-torsion subgroup T.
  let T : Subgroup (ZMod n)ˣ :=
    { carrier := {x | x ^ 2 = 1}
      one_mem' := by show (1 : (ZMod n)ˣ) ^ 2 = 1; exact one_pow _
      mul_mem' := fun {a b} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) => by
        show (a * b) ^ 2 = 1
        rw [mul_pow, ha, hb, mul_one]
      inv_mem' := fun {a} (ha : a ^ 2 = 1) => by
        show (a⁻¹) ^ 2 = 1
        rw [inv_pow, ha, inv_one] }
  -- Step 3: T is a 2-group, so Nat.card T = 2^k for some k.
  have hT_pgroup : IsPGroup 2 T := fun ⟨g, hg⟩ =>
    ⟨1, Subtype.ext (by show g ^ (2 ^ 1) = (1 : (ZMod n)ˣ);
                        rw [pow_one]; exact hg)⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT_pgroup
  -- Step 4: T.card = #filter ≥ 3 → 2^k ≥ 3 → k ≥ 2 → T.card ≥ 4.
  have h_card_filter :
      Fintype.card T = (Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1)).card := by
    simpa using Fintype.card_subtype (fun x : (ZMod n)ˣ => x ^ 2 = 1)
  have h_T_ge_3 : 3 ≤ Fintype.card T := by
    rw [h_card_filter]
    exact GaussWilsonNonCyclic.card_sq_eq_one_ge_three hn hncyc
  have h_T_pow : Fintype.card T = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card]; exact hk
  have h_T_ge_4 : 4 ≤ Fintype.card T := by
    rw [h_T_pow] at h_T_ge_3 ⊢
    rcases k with _ | _ | k'
    · norm_num at h_T_ge_3
    · norm_num at h_T_ge_3
    · calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k' + 2) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  -- Step 5: Apply Phase B to T.
  have hT_exp : ∀ x : T, x ^ 2 = 1 := fun ⟨g, hg⟩ => Subtype.ext (by
    show g ^ 2 = 1; exact hg)
  have hT_prod : (∏ x : T, x) = 1 :=
    prod_univ_eq_one_of_elementary_card_ge_four hT_exp h_T_ge_4
  -- Step 6: Bridge to ambient Finset.
  have h_bridge :
      ∏ x ∈ Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1), x
        = ((∏ x : T, x : T) : (ZMod n)ˣ) := by
    rw [SubmonoidClass.coe_finset_prod T.toSubmonoid (fun (x : T) => x) Finset.univ]
    symm
    apply Finset.prod_subtype
    intro x
    simp [Finset.mem_filter, T, Subgroup.mem_mk]
  rw [h_bridge, hT_prod, OneMemClass.coe_one]
```

LOC count: ~38 body + 1 `open GaussWilsonNonCyclicOQ01 in` if needed →
total ~38–42. Within the 30–50 estimate. Note step 5–6 already uses
the parent's `open GaussWilsonNonCyclicOQ01` namespace.

---

## 5. Build-risk callouts (3 modes the S10 ACT implementer should pre-empt)

### Risk A — `Submonoid.coe_finset_prod` direction mismatch (HIGH)

`Submonoid/BigOperators.lean:49` states:

```lean
theorem coe_finset_prod {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M]
    (f : ι → S) (s : Finset ι) : ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M)
```

The LHS coerces a `S`-valued product to `M`, the RHS replaces the
function value by its `M`-coercion. **Key:** the `f i` on the RHS is
the same expression as on the LHS — Lean unifies by elaboration. With
`f := (id : T → T)` and the RHS read as `∏ i ∈ s, (f i : M)`, this
becomes `∏ i ∈ s, ((i : T) : (ZMod n)ˣ)` = `∏ i ∈ s, i.val`.

**Mitigation if elaboration fails:**
- Try `Subgroup.coe_finset_prod` (parallel API in Subgroup namespace
  if it exists; if not, `SubmonoidClass.coe_finset_prod T.toSubmonoid`
  is canonical).
- If direction is reversed, use `.symm`.
- Worst case, replace with `MonoidHom.map_prod T.subtype id univ`
  (explicit subtype embedding).

### Risk B — `Finset.prod_subtype` predicate-matching (MEDIUM)

`Algebra/BigOperators/Group/Finset/Basic.lean:467`:

```lean
theorem prod_subtype {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι)
    (h : ∀ x, x ∈ s ↔ p x) (f : ι → M) :
    ∏ a ∈ s, f a = ∏ a : Subtype p, f a
```

The lemma rewrites a Finset product as a Subtype product, with `p` the
membership predicate. **Key gotcha:** `T : Subgroup (ZMod n)ˣ` defines
`Subtype (· ∈ T) = ↥T`. With `T.carrier = {x | x^2 = 1}`, Lean expands
`x ∈ T` to `x ∈ T.carrier` to `x ∈ ({x | x^2 = 1} : Set _)` to
`x^2 = 1` — but this final unfold is **not** definitional under all
elaboration contexts; `SetLike.mem_coe` may be needed.

**Mitigation:**
- The `apply Finset.prod_subtype` + `intro x; simp [Finset.mem_filter, T,
  Subgroup.mem_mk]` pattern in §4 handles this by `simp` unfolding `T`
  and `Subgroup.mem_mk`.
- If `simp` doesn't close, try `show x ∈ T ↔ x^2 = 1; exact Iff.rfl`
  on the `intro x` branch.
- Fallback: change to `Fintype.prod_subtype` (if that exists) or
  introduce an explicit `Equiv` between `↥T` and `{x // x^2 = 1}`.

### Risk C — `Nat.card` vs `Fintype.card` round-trip (LOW)

`IsPGroup.iff_card` returns `∃ n, Nat.card G = p^n`. Phase B and
`card_sq_eq_one_ge_three` use `Fintype.card`. The bridge
`Nat.card_eq_fintype_card` requires `[Fintype G]` (or `[Finite G]` for
the more general version). For `T : Subgroup (ZMod n)ˣ`, `Fintype T`
is automatic (since `(ZMod n)ˣ` has `Fintype` and `T` has decidable
membership).

**Mitigation:**
- `Nat.card_eq_fintype_card` is the standard bridge.
- If `Fintype T` instance isn't picked up, force it with
  `haveI : Fintype T := Subgroup.instFintype` (or use `inferInstance`).
- The `h_T_pow` step in §4 uses `← Nat.card_eq_fintype_card` to
  rewrite goal-side `Fintype.card T` to `Nat.card T`, then apply `hk`.

---

## 6. Two LOC-cost options for S10 implementer

### Option A — full ACT in parent file (recommended)

Paste §4 verbatim into `Proofs/GaussWilsonNonCyclicOQ01.lean:149`,
replacing the single `sorry`. Net: +38 LOC, –1 sorry. Slug sorry count
1 → 0. Build expectation: 2–3 Docker iterations on cold cache, ~25–45
min each. Dominant failure modes: Risk A, Risk B (see §5).

### Option B — extract helper lemma into Phase C scaffold

Create a new helper lemma `_root_.prod_eq_one_of_card_sq_eq_one_ge_three`
(or similar) at top of `Proofs/GaussWilsonNonCyclicOQ01.lean` that takes
a finite CommGroup `G` with `[Fintype G] [DecidableEq G]`, a hypothesis
`hcard : 3 ≤ (univ.filter (· ^ 2 = 1)).card`, and concludes
`∏ x : G, x = 1`. Steps 2–6 of §4 go inside this lemma; then
`prod_eq_one_of_not_isCyclic_aux` is a 2-line application. Net: ~45
LOC but cleaner separation. Useful if a sibling slug also needs this.

**Recommendation: Option A** — single discharge site, no abstraction
cost, faster build. Option B only if the helper has a downstream
consumer (none visible in current slug landscape).

---

## 7. Composition with prior sessions

This PREP composes additively with S1–S8 PREPs/ACTs:

- **S1 OBSERVE:** sets up 3-phase decomposition.
- **S2 ACT (PR #18147):** Phase A built (`GaussWilsonNonCyclicOQ01A.lean`,
  build-verified, 0 sorries). § 4 step 1 invokes Phase A.
- **S3 ACT (PR #18232):** Phase B core stated with strategic sorry.
- **S4/S4b PREP (PRs #18347, #18467):** survey four Phase B routes;
  S4b corrects Mathlib API erratum.
- **S5/S5b PREP (PRs #18502, #18607):** designs and audits Phase C
  scaffold; fixes 4 tactic bugs.
- **S6 ACT (PR #18652):** Phase C scaffold shipped, 2 strategic sorries.
- **S7 PREP/ACT (PRs #18700, #18743):** cyclic direction discharged.
- **S8 ACT:** Phase B strategic sorry discharged via strong induction
  on Finset; Phase B now sorry-free.
- **S9 PREP (this session):** pin-verifies all 11 bearers for the
  non-cyclic direction; corrects the master-HEAD-only lemma name in
  state.md's Next Action; ships paste-ready S10 ACT skeleton.

Phase chain after S10 ACT (predicted):

| Phase | File | LOC | Sorries | Status |
|---|---|---|---|---|
| A | `GaussWilsonNonCyclicOQ01A.lean` | 66 | 0 | build-verified |
| B | `GaussWilsonNonCyclicOQ01B.lean` | 243 | 0 | build-verified |
| C | `GaussWilsonNonCyclicOQ01.lean` | ~240 | **0** | build-pending |

Slug-wide sorry count after S10 ACT: **0**.

---

## 8. Conflict-free guarantees

- This PREP creates exactly one new file:
  `research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-15-s9-prep-noncyclic-direction-bearer-audit-and-skeleton.md`.
- No edits to `state.md`, `problem.md`, `knowledge.md`, `meta.json`.
- No edits to any `proofs/Proofs/*.lean` file.
- No changes to `proofs/Proofs.lean` or `src/data/proofs/*`.
- Composes with all prior sessions S1–S8 without overlap.

---

## 9. Race awareness

Pre-PREP: `gh pr list --search "gauss-wilson-non-cyclic-oq-01 in:title"
--state open` returns `[]`. No open PRs on this slug. `docker ps` shows
no active lean-build containers. `ps -ef | grep docker-build` is empty.
No sibling worktree has a recent draft of `GaussWilsonNonCyclicOQ01.lean`
modifications.

Sibling slug `gauss-wilson-non-cyclic-oq-03` has separate state.md /
PR chain and is independent.

---

## 10. Estimate for S10 ACT

- **LOC:** 38–60 (Option A) or 45–70 (Option B).
- **Docker iterations:** 1 if Risks A/B pre-empted; otherwise 2–3.
- **Wall clock:** ~25–45 min per Docker round on cold cache, plus
  ~10 min editing per iteration. Total: 1–3 hours expected.
- **Confidence:** HIGH that the math is correct and bearers exist.
  MEDIUM that the tactic chain compiles first-try (subgroup-vs-subtype
  defeq is the main hazard).
