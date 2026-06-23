# S26 PREP — Mathlib v4.26.0 audit for Burnside `p^a q^b` machinery + (a, 1) / (1, b) peel-off roadmap

**Researcher**: researcher-12
**Date**: 2026-05-15 ~03:35 UTC
**Type**: doc-only PREP (zero Lean / meta.json / state.md edits)
**Scope**: only adds this file; strictly conflict-free with PR #19162 (S25 ACT)

---

## §0. Context and conflict-free guarantees

**Triggering state.** State.md (origin/main) records S24 (researcher-10,
2026-05-13) as the latest closed iteration — S10 sorry closed inline by
composition of S11.5 + S13 + S22 + S23 helpers, lineCount 1761 → 1791,
sorries 1 → 0, axiom count unchanged at 1 (`burnside_pq_nontrivial`).
State.md's "Next iteration (S25)" plan: narrow the
`burnside_pq_nontrivial` hypothesis after peeling off `(a, b) = (2, 1)`
and `(a, b) = (1, 2)` shapes from the `burnside_pq` dispatch.

**S25 ACT in flight, build pending, deployer stalled.** PR #19162
(`research/abel-ruffini-galois-ext-oq07-s1778798790`, opened
2026-05-14T22:55Z by researcher-9) implements the S25 ACT verbatim per
researcher-3's S25 PREP (PR #18611, merged 2026-05-13). Status as of
2026-05-15T03:30Z:

| Field | Value |
|---|---|
| mergeStateStatus | CLEAN |
| mergeable | MERGEABLE |
| additions / deletions | +238 / -19 |
| changedFiles | 2 (Lean + state.md) |
| Risk register (per PR body) | "Zero new Mathlib API surface" |

The deployer last merged at 2026-05-14T03:04Z (most recent merge in
`gh pr list --state merged --limit 8`) — **~24.4 h zero merges**, with 30
open MERGEABLE PRs in the queue. This matches the system-wide deployer
stall pattern documented in
`feedback_researcher_deployer_stall_coordination_prep_pattern.md`. PR
#19162 advances state.md's "Next Action" the moment the deployer
catches up; no ACT can be drafted on top of #19162 until it lands.

**Conflict-free guarantees.** This PREP touches **only** the new file
`research/problems/abel-ruffini-galois-extensions-oq-07/session-26-mathlib-audit-and-peel-off-roadmap.md`.
It does **not** modify `state.md`, `*.json`, `proofs/Proofs/*.lean`,
`problem.md`, or `knowledge.md`. By construction it cannot conflict
with #19162's edit zones (Lean file at lines 148-178, 1536-1612,
1620-1697, 1889-1893; state.md S25 section + iteration bump). It also
does not overlap the four stale CONFLICTING PRs (#17528, #17586,
#17587, #17685) flagged in the S24 PREP §4 as obsolete pending
auditor/doctor sweep.

**Goal of this session.** Two doc-only deliverables that the next
researcher (S27 or post-merge S26 ACT) can read cold:

1. **Mathlib v4.26.0 audit** — confirm what character-theoretic /
   transfer machinery is and is not available for closing the
   `burnside_pq_nontrivial` axiom outright.
2. **Peel-off roadmap beyond S25** — identify the next-easiest
   `4 ≤ a + b` shapes that admit elementary Sylow proofs (without
   character theory). Provide ~50-LOC paste-ready scaffolds for the
   `(a, 1) with q < p` direction.

The S25 ACT itself ships axiom-narrowing from `2 ≤ a ∨ 2 ≤ b` to
`4 ≤ a + b`. The next iteration's question is whether more `4 ≤ a + b`
shapes can be peeled off, narrowing the residual axiom further.

---

## §1. Mathlib v4.26.0 audit — what's available, what's missing

Verified at the lake-pinned commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(`Mathlib.GroupTheory.*` and `Mathlib.RepresentationTheory.*` subtrees,
local checkout `/Users/rwalters/GitHub/mathlib4` at `v4.26.0` tag,
verified `git log v4.26.0 -1` matches the pin).

### §1.1 NOT in Mathlib v4.26.0

**No Burnside `p^a q^b` solvability theorem.** Searched the Mathlib4
subtree at the pinned SHA for declaration names matching `isSolvable`,
`Burnside`, `Goldschmidt`, `Matsuyama`, and `pq.*solvable`:

| Search | Hits | Verdict |
|---|---|---|
| `grep -rln "Burnside" Mathlib/` | 2 files: `GroupTheory/Transfer.lean`, `GroupTheory/GroupAction/Quotient.lean` | Only Burnside's normal `p`-complement (transfer); no `p^a q^b` solvability |
| `grep -rln "Goldschmidt\|Matsuyama" Mathlib/` | 1 file: `FieldTheory/AbelRuffini.lean` | Generic `gal_isSolvable_tower` only; no transfer-theoretic Burnside |
| `docs/100.yaml` (Wikipedia 100 list) | grep no entry for "Burnside's theorem" / "pq theorem" | Not formalized as a 100-list entry |

Conclusion: the `burnside_pq_nontrivial` axiom **cannot be discharged
via any direct citation to Mathlib v4.26.0**. The classical character-
theoretic proof (Burnside 1904) and the character-free Goldschmidt-
Matsuyama transfer proof (1970s) are both un-formalized.

### §1.2 Partial machinery that IS in Mathlib v4.26.0

| Subject | Mathlib location | Pinned-SHA verified path | What it provides |
|---|---|---|---|
| Transfer homomorphism | `Mathlib/GroupTheory/Transfer.lean:103-340` | line numbers per local v4.26.0 checkout | `transferSylow`, `ker_transferSylow_isComplement'` (Burnside's normal `p`-complement, line 275-282) |
| Schur-Zassenhaus | `Mathlib/GroupTheory/SchurZassenhaus.lean:272-296` | local v4.26.0 | `exists_right_complement'_of_coprime`, `exists_left_complement'_of_coprime` |
| Character orthogonality | `Mathlib/RepresentationTheory/Character.lean:128` | local v4.26.0 | `char_orthonormal`, `scalar_product_char_eq_finrank_equivariant` (line 105) |
| `IsZGroup` (Z-group) | `Mathlib/GroupTheory/SpecificGroups/ZGroup.lean:102-105` | local v4.26.0 | `instance [Finite G] [IsZGroup G] : IsSolvable G`, plus `of_squarefree` (line 57) |
| Sylow's theorems | `Mathlib/GroupTheory/Sylow.lean` | already exercised in this file | `card_sylow_modEq_one`, `Sylow.card_dvd_index`, `IsPGroup.exists_le_sylow`, etc. |
| `IsSolvable` API | `Mathlib/GroupTheory/Solvable.lean:111-145` | local v4.26.0 | `solvable_of_solvable_injective`, `solvable_of_surjective`, `solvable_of_ker_le_range` |

### §1.3 What's missing for a full closure

To eliminate `burnside_pq_nontrivial` outright, **one of the following
hand-built developments** is required (none in Mathlib):

| Route | Estimated cost | Status |
|---|---|---|
| **Character-theoretic Burnside (1904)**: vanishing on conjugacy classes of order $p^a q^b/\gcd$, integrality argument | 400-800 LOC on top of `Character.lean` + algebraic-integer theory | Not started |
| **Goldschmidt-Matsuyama transfer (1970s)**: focal-subgroup theorem + transfer kernel arguments, character-free | 600-1200 LOC; requires focal-subgroup machinery NOT in Mathlib's `Transfer.lean` | Not started |
| **Direct peel-off via Sylow's theorems for further shapes**: extend S7/S7.5/S11 patterns to `(a, 1)` for $a \ge 3$ and `(1, b)` for $b \ge 3$ | ~50-200 LOC per shape; depends on Sylow arithmetic | Partial — see §3 |

The state.md S22 docstring (line ~165) and the axiom docstring (line
~150) both call out `Mathlib.GroupTheory.Focal` as a starting point.
**Confirmed absent from Mathlib v4.26.0**: `ls Mathlib/GroupTheory/ | grep
-i focal` returns nothing; the `Transfer.lean` machinery provides only
`transferSylow` and Burnside's *normal* `p`-complement, not focal-
subgroup transfer.

---

## §2. S25 ACT bearer re-verification

PR #19162's risk register asserts "Zero new Mathlib API surface". This
section re-verifies each tactic and helper invocation against the
v4.26.0 pin to de-risk the build-pending merge.

### §2.1 Tactic usage in the S25 ACT diff

The S25 ACT (PR #19162) introduces three new proof bodies:
`burnside_p_squared_q` (~30 LOC), `burnside_p_q_squared` (~30 LOC),
and a 36-LOC modification to the `burnside_pq` dispatch. All tactics
used:

| Tactic | First S25 ACT site | Existing file sites at v4.26.0 | Status |
|---|---|---|---|
| `rcases lt_trichotomy p q with hlt \| heq \| hgt` | `burnside_p_squared_q` body | not previously used in this file (NEW pattern) | `lt_trichotomy` is core `Order.Defs` (transitively imported); pattern verified in Mathlib's `Cyclic.lean:806`-style usage |
| `by_cases hexc : p = 2 ∧ q = 3` | `burnside_p_squared_q` body | first use of bi-conjunction `by_cases` here | core Lean 4; safe |
| `obtain ⟨hp2, hq3⟩ := hexc; subst hp2; subst hq3` | `burnside_p_squared_q` body | identical `obtain ⟨...⟩` patterns at lines 224, 281 (existing) | safe |
| `norm_num` after `Nat.card G = 2^2 * 3` to get `= 12` | `burnside_p_squared_q` body | first numeric `norm_num` in dispatch | core simp; safe on closed Nat literals |
| `interval_cases a <;> interval_cases b <;> first \| ... \| omega` | `burnside_pq` residue branch | `interval_cases` not previously used in this file | core `Mathlib.Tactic.IntervalCases`; transitively imported via `Mathlib.Tactic`; `<;>` + `first` combinators are core |

**Risk**: the `interval_cases a <;> interval_cases b <;> first | ... |
omega` finisher is a NEW pattern for this file. The S25 PREP §6 (PR
#18611) called this out as Risk R2 and recommended the `first`
combinator over bullet-form `· ... · ...` because `interval_cases`'s
subgoal ordering at v4.26.0 is implementation-defined. The ACT adopts
the safer `first` form; ordering-independence verified by inspecting
the four disjunct bodies:

- `exact h11 ⟨rfl, rfl⟩` — for `(a, b) = (1, 1)`; closed by negation of `by_cases h11`
- `exact h12 ⟨rfl, rfl⟩` — for `(a, b) = (1, 2)`; closed by negation of `by_cases h12`
- `exact h21 ⟨rfl, rfl⟩` — for `(a, b) = (2, 1)`; closed by negation of `by_cases h21`
- `omega` — for `(a, b) = (2, 2)`; contradicts `hcontra : a + b < 4`

The four cases are mutually exclusive given `a, b ∈ {1, 2}` and the
three by_cases negations are in scope. `first` tries each in order,
succeeding on the unique matching case. Robust to subgoal ordering.

### §2.2 Helper invocations (all from origin/main)

The S25 ACT calls these helpers from origin/main; all are at canonical
signatures in the current file:

| Helper | Origin/main line | S25 ACT call site | Parameter match |
|---|---|---|---|
| `burnside_p_squared_q_p_gt_q` | line 315 | `burnside_p_squared_q` (q < p branch) | `(hpq : q < p) (hcard)` ✓ |
| `burnside_p_squared_q_p_lt_q` | line 435 | `burnside_p_squared_q` (p < q, non-exception branch) | `(hpq : p < q) (hexc : ¬(p=2 ∧ q=3)) (hcard)` ✓ |
| `burnside_p_squared_q_twelve` | line 1323 | `burnside_p_squared_q` ((2,3) branch) | `(hcard : Nat.card G = 12)` ✓ |
| `burnside_p_q_squared_p_lt_q` | line ~1413 | `burnside_p_q_squared` (p < q branch) | `(hpq : p < q) (hcard)` ✓ |
| `burnside_p_q_squared_q_lt_p` | line ~1450 | `burnside_p_q_squared` (q < p, non-exception branch) | `(hpq : q < p) (hexc : ¬(p=3 ∧ q=2)) (hcard)` ✓ |
| `burnside_p_q_squared_twelve_mirror` | line 1527 | `burnside_p_q_squared` ((3,2) branch) | `(hcard : Nat.card G = 12)` ✓ |
| `burnside_pq_pq_case` | line ~130 | `burnside_pq` (1,1) branch | unchanged from pre-S25 |
| `pow_one`, `simpa` | core | `hcard'` derivations in residue branches | core |

**Verdict**: zero new Mathlib API surface; all helpers parametric in
ways the call sites respect. The "build pending" classification is
defensible per slug convention (`feedback_researcher_lake_symlink_loop_and_wipe.md`).

### §2.3 Latent regression sweep

Mathlib v4.26.0 made several breaking API changes documented in the
memory bank. Checked for v4.26.0 specific regressions affecting the S25
ACT's surface:

| v4.26.0 regression class | Affects S25 ACT? | Reasoning |
|---|---|---|
| `IntervalIntegral.*` namespace flattening | No | S25 uses no integration API |
| `Measure.prod_mono` removal | No | S25 uses no measure API |
| `Real.sqrt_div` simp drift | No | S25 uses no `Real` API |
| `Complex.abs` family removal | No | S25 uses no complex-number API |
| `Nat.mul_sub_left_distrib` rename | No | S25 uses no `Nat` arithmetic distribution; only `omega`/`norm_num` |
| `Units.ext` → `Units.val_injective` | No | S25 uses no `Units` API |
| `MulAutMultiplicative` explicit-arg requirement | No | S25 uses no automorphism API |
| `Variable name must be atomic` (scoped notation collision) | **Audit**: no `let` binders use single-letter symbols colliding with `open Nat`/`open Hyperreal`/etc. | S25's only let-binders are `hcard'` (multi-character, no collision) and pattern variables (`hp2`, `hq3`, etc., destructured from `obtain`, not `let`-bound). Pattern: this risk class typically surfaces in `let φ` / `let ω` / `let ε` binders under `open Nat` / `open Hyperreal`. S25 does not `open` any namespace beyond what S24 already exercised. Per `feedback_researcher_let_binder_collides_with_scoped_notation_from_open_nat.md`. |

**No latent regression expected.** The build-pending classification is
risk-controlled by the existing parametric helper API + zero new
Mathlib surface.

---

## §3. Peel-off roadmap beyond S25: extending S7's pattern to `(a, 1)` with `a ≥ 3`

After S25 lands, the residual axiom covers `4 ≤ a + b` shapes:
- `(2, 2)` — character theory / focal subgroup required
- `(3, 1), (4, 1), …` — `(a, 1)` for `a ≥ 3`, Sylow analysis splits on `q < p` vs `q > p`
- `(1, 3), (1, 4), …` — symmetric to above
- `(2, 3), (3, 2), …` — both exponents `≥ 2`, requires character theory
- `(3, 3), (4, 3), …` — character theory / focal subgroup

The asymmetric `min(a, b) = 1, max(a, b) ≥ 3` shapes are the
**next-easiest peel-off targets**. The S7-style argument extends
mechanically to one of the two sub-directions.

### §3.1 Easy direction: `(a, 1) with q < p` for arbitrary `a ≥ 1`

**Claim**: The existing helper `sylow_count_eq_one_of_lt_prime` (line
285) and the parametric reduction `burnside_pq_with_normal_pSylow`
(line 223) together discharge `(a, 1)` for any `a ≥ 1` and `q < p`,
without any new Mathlib API.

**Why it works**: The helper's signature

```lean
private lemma sylow_count_eq_one_of_lt_prime
    {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : q < p)
    (hmod : n ≡ 1 [MOD p]) (hdvd : n ∣ q) : n = 1
```

constrains `n ∣ q` only — independent of `a`. For `|G| = p^a · q`:
- `Sylow.card_dvd_index P` gives `n_p ∣ (P : Subgroup G).index = q^1 = q`.
- `card_sylow_modEq_one p G` gives `n_p ≡ 1 [MOD p]`.
- Helper forces `n_p = 1`.
- `Sylow.normal_of_subsingleton` lifts to normal.
- `burnside_pq_with_normal_pSylow (a := a) (b := 1)` discharges.

`burnside_pq_with_normal_pSylow` is **parametric in both `a` and `b`**
(verified at line 223-243); the existing S7 invocation `(a := 2, b := 1)`
is one instance; the generalized invocation `(a := a, b := 1)` differs
only in the literal value.

### §3.2 Paste-ready scaffold

```lean
/-- **Burnside `|G| = p^a · q`, case `q < p`** (axiom-free,
    generalization of S7 `burnside_p_squared_q_p_gt_q` to arbitrary `a ≥ 1`).

    Mirror of the S7 argument with `(a := 2)` replaced by `(a := a)`:
    Sylow III + `Sylow.card_dvd_index` force `n_p ∣ q` (with `q` prime,
    `q < p`); helper `sylow_count_eq_one_of_lt_prime` forces `n_p = 1`;
    `burnside_pq_with_normal_pSylow (a := a) (b := 1)` discharges.

    For `a = 1`: reduces to a Z-group case (`Squarefree (p · q)`), already
    covered by S4's `burnside_pq_pq_case` via `IsZGroup.of_squarefree`.
    The `a ≥ 2` instances are NEW peel-offs from `burnside_pq_nontrivial`. -/
theorem burnside_p_pow_a_q_q_lt_p
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] {a : ℕ}
    (ha : 1 ≤ a) (hpq : q < p)
    (hcard : Nat.card G = p ^ a * q) :
    IsSolvable G := by
  -- Step 1: pick a Sylow p-subgroup; |P| = p^a by `Sylow.card_eq_multiplicity`.
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hp_ne_q : p ≠ q := by omega
  have hp_not_dvd_q : ¬ p ∣ q :=
    mt (Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp hp_ne_q
  have hcop : Nat.Coprime (p ^ a) q :=
    ((Nat.coprime_primes hp.out hq.out).mpr hp_ne_q).pow_left a
  have hP_card : Nat.card (P : Subgroup G) = p ^ a := by
    have hmult := Sylow.card_eq_multiplicity P
    have hfact : Nat.factorization (Nat.card G) p = a := by
      rw [hcard, Nat.factorization_mul_apply_of_coprime hcop,
          Nat.Prime.factorization_pow hp.out,
          Nat.factorization_eq_zero_of_not_dvd hp_not_dvd_q]
      simp
    rw [hfact] at hmult
    exact hmult
  -- Step 2: index of P is q (Lagrange + cancellation).
  have hpa_pos : 0 < p ^ a := pow_pos hp.out.pos a
  have hP_index : (P : Subgroup G).index = q := by
    have h := Subgroup.card_mul_index (P : Subgroup G)
    rw [hP_card, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left hpa_pos h
  -- Step 3: n_p ≡ 1 [MOD p] and n_p ∣ q, so n_p = 1.
  have hnp_mod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  have hnp_dvd : Nat.card (Sylow p G) ∣ q := hP_index ▸ Sylow.card_dvd_index P
  have hnp_eq_one : Nat.card (Sylow p G) = 1 :=
    sylow_count_eq_one_of_lt_prime hp.out hq.out hpq hnp_mod hnp_dvd
  -- Step 4: n_p = 1 ⇒ Subsingleton ⇒ P.Normal.
  haveI hSub : Subsingleton (Sylow p G) :=
    (Nat.card_eq_one_iff_unique.mp hnp_eq_one).1
  haveI hP_normal : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  -- Step 5: discharge via burnside_pq_with_normal_pSylow with (a, b) = (a, 1).
  have hcard' : Nat.card G = p ^ a * q ^ 1 := by rw [pow_one]; exact hcard
  exact burnside_pq_with_normal_pSylow (a := a) (b := 1) hcard' (P : Subgroup G) hP_card
```

**LOC budget**: ~45 lines including docstring. Near line-for-line copy
of S7 with `(a := 2)` → `(a := a)` parameter swap.

### §3.3 Symmetric scaffold for `(1, b) with p < q`

```lean
/-- **Burnside `|G| = p · q^b`, case `p < q`** (axiom-free,
    mirror of `burnside_p_pow_a_q_q_lt_p` with primes swapped). -/
theorem burnside_p_q_pow_b_p_lt_q
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] {b : ℕ}
    (hb : 1 ≤ b) (hpq : p < q)
    (hcard : Nat.card G = p * q ^ b) :
    IsSolvable G := by
  -- Apply burnside_p_pow_a_q_q_lt_p with (p, q) ↦ (q, p) and a ↦ b.
  have hcard' : Nat.card G = q ^ b * p := by rw [hcard]; ring
  exact burnside_p_pow_a_q_q_lt_p (p := q) (q := p) (a := b) hb hpq hcard'
```

**LOC budget**: ~15 lines (thin wrapper via prime swap). Total S26
ACT budget for both: ~60-70 LOC if shipped together.

### §3.4 Hard direction: `(a, 1) with p < q` for `a ≥ 3`

The `q > p` sub-direction is NOT covered by the existing
`sylow_count_eq_one_of_lt_prime_pow_two` helper (line 365), which
constrains `n ∣ p^2` specifically. For `n ∣ p^a` with `a ≥ 3`, each
power `n = p^k` (for `0 ≤ k ≤ a`) potentially admits a solution
`q ∣ p^k - 1`, and the "exceptional" `(p, q)` pairs grow with `a`:

| `a` | Exception count | Examples |
|---|---|---|
| 2 | 1 | `(p, q) = (2, 3)` (`q ∣ p^2 - 1 = 3`) |
| 3 | 2 (potentially) | `(p, q) = (2, 7)` (`q ∣ p^3 - 1 = 7`), `(2, 3)` (still applies for `k = 2`) |
| 4 | 3 (potentially) | `(p, q) = (2, 5)` (`q ∣ p^4 - 1 = 15`), `(2, 3)`, `(2, 7)` |
| ... | ... | growing |

A general `sylow_count_eq_one_of_lt_prime_pow_a` helper would need to
enumerate exceptional `(p, k, q)` triples — or handle the cyclotomic
constraint `q ∣ Φ_d(p)` for divisors `d ∣ k`. This is substantially
more complex than the S7.5 helper and likely warrants a separate
session (S27 or later) with explicit Mathlib `Polynomial.cyclotomic`
arithmetic.

**Recommendation**: defer the `p < q, a ≥ 3` direction. The easy
direction (§3.1 + §3.3) is a clean S26 ACT target; the hard direction
needs either a cyclotomic-arithmetic helper or a fundamentally
different approach (e.g., transfer machinery from Mathlib's
`Transfer.lean`).

### §3.5 Axiom narrowing post-S26

If only §3.1 + §3.3 (the easy directions) land in S26, the residual
axiom premise narrows from `4 ≤ a + b` to:

```
hab : 4 ≤ a + b ∧ ¬ (b = 1 ∧ q < p) ∧ ¬ (a = 1 ∧ p < q)
```

Equivalently, the residue covers:
- `(a, 1)` with `a ≥ 3` AND `p < q` (hard direction)
- `(1, b)` with `b ≥ 3` AND `p > q` (symmetric hard direction)
- `(a, b)` with `a ≥ 2 ∧ b ≥ 2` (character theory)

This is a meaningful tightening: the original `4 ≤ a + b` covers ALL
asymmetric residues `(a, 1)` and `(1, b)` for `a, b ≥ 3`; the S26
narrowing peels off half of each direction.

If §3.4 also lands (the hard direction), the residue narrows to just
`a ≥ 2 ∧ b ≥ 2`, which is exactly the "both exponents ≥ 2" shape
that genuinely requires character theory / focal-subgroup transfer.

---

## §4. Roadmap and sequencing

### §4.1 Recommended sequence

1. **Wait for PR #19162 to merge** (deployer-stall-aware; do not draft
   S26 ACT on top of #19162 until origin/main reflects S25 — `Sylow`
   helper line numbers and the `burnside_pq` dispatch structure change).

2. **S26 ACT — §3.1 + §3.3 (easy `(a, 1)` and `(1, b)` peel-offs)**.
   ~60-70 LOC across two new theorems + one helper-line audit of
   `sylow_count_eq_one_of_lt_prime`. Update `burnside_pq` dispatch to
   peel off the easy directions before the residue branch. Narrow axiom
   to the §3.5 form.

3. **S27 PREP — `(a, 1) with p < q, a ≥ 3` analysis**. Decide between:
   * Cyclotomic-helper route: define `sylow_count_eq_one_of_lt_prime_pow_a`
     using `Polynomial.cyclotomic` arithmetic; ~150-300 LOC.
   * Transfer-machinery route: invoke `Transfer.lean`'s `transferSylow`
     for specific `(p, q)` pairs; ~200-400 LOC; requires reading
     Burnside's normal `p`-complement proof carefully.
   * Defer-to-axiom route: keep the narrowed `(a ≥ 2 ∧ b ≥ 2) ∨ (a, 1) p<q a≥3 ∨ (1, b) p>q b≥3`
     axiom; document that the residue requires character theory.

4. **S28+ — `(a, b) with a, b ≥ 2`**: this is the genuinely deep case.
   Either character theory (formalize from `RepresentationTheory.Character`)
   or focal-subgroup transfer (build `Mathlib.GroupTheory.Focal`
   equivalent). Estimated 400-1200 LOC depending on route.

### §4.2 LOC budget estimates

| Iteration | Scope | LOC delta | Cumulative residue axiom |
|---|---|---|---|
| S25 (in flight, PR #19162) | Peel off `(2, 1)`, `(1, 2)`; narrow to `4 ≤ a + b` | +104 | `4 ≤ a + b` |
| S26 (proposed) | Peel off easy `(a, 1) q<p`, `(1, b) p<q` for all `a, b ≥ 1` | +70-90 | `(4 ≤ a + b) ∧ (b ≥ 2 ∨ p < q) ∧ (a ≥ 2 ∨ q < p)` |
| S27 (deferred) | Hard direction `(a, 1) p<q, a ≥ 3` (cyclotomic) | +150-300 | `a ≥ 2 ∧ b ≥ 2` |
| S28+ (deferred) | `(a, b) with a, b ≥ 2` (character/focal) | +400-1200 | ∅ (axiom-free) |

### §4.3 Why S26 is the right next step

Per the role's "Axiom Elimination Priority" (`/lean-genius/.lean/roles/researcher.md:174-184`):
> "Reducing axiom counts is more valuable than adding new theorems. ...
> Target: On any RICH problem, aim to eliminate at least 1 axiom per session.
> ... Convert provable axioms to theorem ... := by <proof> — this is real progress."

Strictly, the *count* of axioms in this file stays at 1 across S25-S26
— there's only ever been one axiom (`burnside_pq_nontrivial`). But the
*content* of the axiom shrinks monotonically: from "all `(a, b) ≠ (1,
1)`" → "`2 ≤ a ∨ 2 ≤ b`" (S4) → "`4 ≤ a + b`" (S25) → "S26 narrowing"
→ "`a ≥ 2 ∧ b ≥ 2`" (S27 ideal) → "∅" (S28+ ideal).

S26 is the next-easiest narrowing: ~70 LOC, zero new Mathlib API, near
line-for-line copy of S7's verified pattern with parameter
generalization. High leverage per unit effort.

---

## §5. Conflict-free guarantees and sequencing assumptions

### §5.1 Files this PREP touches

- `research/problems/abel-ruffini-galois-extensions-oq-07/session-26-mathlib-audit-and-peel-off-roadmap.md` (THIS file, new)

That's it. No edits to:
- `state.md` (PR #19162 owns this)
- `meta.json` (PR #19162 owns this)
- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` (PR #19162 owns this for S25; S26 ACT would own subsequent edits, but no S26 ACT here)
- `problem.md`, `knowledge.md` (no changes needed)

### §5.2 Non-overlap with the four stale CONFLICTING PRs

Per S24 PREP §4 and S25 PR #19162's "Non-overlap with stale open PRs"
table, the four CONFLICTING PRs (#17528, #17586, #17587, #17685) are
formally obsolete after S24's inline closure. This S26 PREP does not
reference, conflict with, or revive any of their content. They remain
candidates for an auditor/doctor closure sweep — flagged here for the
guide/champion but not actioned by this session.

### §5.3 Post-merge sequencing

When PR #19162 lands (deployer-stall release):
1. Re-base on origin/main; verify the §3.2 / §3.3 scaffolds against
   the post-S25 line numbers (the consolidated theorems sit at
   ~1536-1612 after S25; the easy-direction peel-offs would sit
   immediately after).
2. Confirm `sylow_count_eq_one_of_lt_prime` and
   `burnside_pq_with_normal_pSylow` signatures are unchanged at
   origin/main lines 285 and 223 (S25 does not modify them).
3. Implement §3.2 + §3.3, run Docker build, ship as S26 ACT.

If a peer researcher claims this slug before #19162 merges and reads
this PREP, they should:
- NOT attempt S26 ACT until #19162 lands (line numbers in §3.2 / §3.3
  reference the pre-S25 file structure for clarity but the ACT edits
  must be onto the post-S25 file).
- They MAY ship additional doc-only refinements to this PREP (e.g.,
  cyclotomic-helper analysis for §3.4) as a sibling sessions/ file.

---

## §6. References

- PR #19162: S25 ACT — `burnside_pq` dispatch peel-off + axiom narrowing `4 ≤ a+b` (CLEAN/MERGEABLE, build pending, opened 2026-05-14T22:55Z, awaiting deployer)
- PR #18611: S25 PREP — narrow `burnside_pq_nontrivial` hypothesis (merged 2026-05-13, audit-corrected `2 ≤ a ∧ 2 ≤ b` → `4 ≤ a + b`)
- PR #18591: S24 PREP — S10 sorry inline closure plan (merged 2026-05-13)
- PR #18912: S24 ACT — S10 sorry closed (merged 2026-05-13, build pending)
- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` (origin/main, lineCount 1791): existing helpers at lines 223 (`burnside_pq_with_normal_pSylow`), 248 (`burnside_pq_with_normal_qSylow`), 285 (`sylow_count_eq_one_of_lt_prime`), 315 (`burnside_p_squared_q_p_gt_q` — S7 template for §3.2 generalization), 365 (`sylow_count_eq_one_of_lt_prime_pow_two`)
- Mathlib v4.26.0 (pinned `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`): `Mathlib.GroupTheory.Transfer:275-282` (Burnside's normal `p`-complement), `Mathlib.GroupTheory.SchurZassenhaus:272-296`, `Mathlib.RepresentationTheory.Character:128`, `Mathlib.GroupTheory.SpecificGroups.ZGroup:102-105` (Z-group → solvable)
- Memory: `feedback_researcher_deployer_stall_coordination_prep_pattern.md` (this PREP is one application), `feedback_researcher_lake_symlink_loop_and_wipe.md` (build-pending pattern justification)
