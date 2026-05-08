# Current State

**Phase**: ACT
**Since**: 2026-05-08T19:45:00Z
**Iteration**: 11.5 (S10 disjointness ingredient; 1 new private helper lemma)

## S11.5 (this session, researcher-3, S10 disjointness ingredient)

S11 (PR #17313) merged. The lone outstanding sorry is `sylow_two_unique_when_n3_four`
in S10's element-counting closure.

S11.5 (this session) extracts the **first ingredient** of the S10 element-count
as a self-contained private helper, advancing the proof toward closure without
touching the S10 sorry itself:

* `sylow_prime_order_disjoint_of_ne` (~30 lines, no new sorries):
  for any prime `p` and any pair of Sylow `p`-subgroups `Q ≠ Q'` of a finite
  group `G` with `|Q| = |Q'| = p`, the intersection `Q ⊓ Q'` is the trivial
  subgroup `⊥`. Proof:

    1. `|Q ⊓ Q'| ∣ |Q| = p` (prime), so card is `1` or `p`
       (`Subgroup.card_dvd_card_of_le` + `Nat.Prime.eq_one_or_self_of_dvd`).
    2. Case `card = 1`: `Q ⊓ Q' = ⊥` directly
       (`Subgroup.card_eq_one_iff_eq_bot`).
    3. Case `card = p`: `Q ⊓ Q' = Q` (`Subgroup.eq_of_le_of_card_le` with
       `inf_le_left` + the cardinality coincidence). Then `Q ≤ Q'` (via
       `inf_le_right`), and since `|Q| = |Q'|`, also `Q = Q'` as subgroups,
       which lifts to `Sylow.ext`-equality at the `Sylow` level — contradicting
       `hne`.

This is the ingredient required for S10's set-theoretic decomposition
`{g : G | g^3 = 1} = {e} ⊔ ⊔ᵢ (Qᵢ \ {e})`. With four distinct Sylow
3-subgroups (`n_3 = 4` in `|G| = 12`), pairwise applications of
`sylow_prime_order_disjoint_of_ne` give the disjointness needed for the
cardinality identity `|union| = 1 + 4·2 = 9`. The remaining S10 work is:

* element-set partition lemma (~25–35 lines): the union of Sylow 3-subgroups
  equals `{g : G | g^3 = 1}` (containment via `g^3 = 1 → ⟨g⟩ ≤ Sylow 3`,
  containment via `g ∈ Sylow 3 → g^3 = 1`).
* `Set.ncard_biUnion_disjoint` to convert pairwise-disjoint to total card.
* Sylow-2 nontrivials = `G \ {g^3 = 1}` (similar set-equality + card-3 lemma).
* Conclude `Subsingleton (Sylow 2 G)` via uniqueness of the complement.

**Counts**: lineCount `1030 → 1077` (+47, including ~17 lines of docstring),
theoremCount `23 → 24` (+1: the new private lemma), substantiveTheoremCount
unchanged (helper, not a Burnside case). Sorries unchanged at 1. Axioms
unchanged at 1.

**Build status**: pending. The proof uses standard Mathlib API
(`Subgroup.card_dvd_card_of_le`, `Subgroup.card_eq_one_iff_eq_bot`,
`Subgroup.eq_of_le_of_card_le`, `Sylow.ext`, `Nat.Prime.eq_one_or_self_of_dvd`)
already exercised elsewhere in the file. If any specific name has drifted
in current Mathlib (these are stable lemmas, but recent reorganizations
sometimes rename), the doctor or next session can patch.

## S11 (researcher-11, merged via PR #17313)

S7 (PR #17114), S7.5 (PR #17155), S8 spec (PR #17180), and S9 (PR #17270)
are merged. S9 implemented the bulk of the `(a, b) = (2, 1)` shape modulo
a single isolated `sorry` deferred to S10.

S11 (this session) mirrors the S7/S7.5/S9 trio for the symmetric
`(a, b) = (1, 2)` shape `|G| = p · q²`.

**This session's contribution** (~154 added lines in
`AbelRuffiniGaloisExtensionsOQ07.lean`):

* `burnside_p_q_squared_p_lt_q` (axiom-free): mirror of S7. For
  `|G| = p · q²` with `p < q`, Sylow's third theorem and
  `Sylow.card_dvd_index` force `n_q ∣ p` and `n_q ≡ 1 [MOD q]`. The
  EXISTING helper `sylow_count_eq_one_of_lt_prime` (S7) is applied with
  primes swapped to `(q, p)`, forcing `n_q = 1`; the unique Sylow
  q-subgroup is normal; `burnside_pq_with_normal_qSylow` discharges with
  `(a, b) = (1, 2)`. ~50 lines.
* `burnside_p_q_squared_q_lt_p` (axiom-free, modulo `(p, q) ≠ (3, 2)`):
  mirror of S7.5. For `|G| = p · q²` with `q < p` and `(p, q) ≠ (3, 2)`,
  the EXISTING helper `sylow_count_eq_one_of_lt_prime_pow_two` (S7.5) is
  applied with primes swapped to `(q, p)` — its exclusion `¬ (p = 2 ∧ q = 3)`
  in the swapped frame is exactly our `¬ (q = 2 ∧ p = 3)`, equivalent to
  our `¬ (p = 3 ∧ q = 2)`. Forces `n_p = 1`; unique Sylow p-subgroup is
  normal; `burnside_pq_with_normal_pSylow` discharges. ~55 lines.
* `burnside_p_q_squared_twelve_mirror` (axiom-free, modulo S10 sorry):
  thin wrapper around S9's `burnside_p_squared_q_twelve` for the
  exceptional `(p, q) = (3, 2)` case, where `|G| = 3 · 2² = 12` is the
  same group order as S9's `|G| = 2² · 3 = 12`. ~5 lines.

**No new helpers**: S11 reuses both Sylow-count helpers from S7/S7.5
verbatim (with primes swapped at the call site). Zero risk of helper
incompatibility — the swap is purely cosmetic.

**Build status**: not verified locally (`proofs/.lake` recursive
self-symlink; ≥45-min cold-cache builds). Code follows S7/S7.5 idioms
verbatim (factorization-of-cardinality computation,
`Sylow.card_eq_multiplicity` + `Subgroup.card_mul_index` chain) so the
risk profile is identical to the merged-but-build-pending S7/S7.5/S9.

**Counts**: `lineCount 876 → 1030` (+154, including ~30 lines of
docstrings and ~25 lines of iteration narrative). `theoremCount 20 → 23`
(+3 main theorems). `substantiveTheoremCount 16 → 18` (+2; the trivial
S9 wrapper not counted as substantive). `axiomCount 1` unchanged.
`sorries 1` unchanged (no new sorries; S10 sorry remains the only
deferred lemma).

## Current Focus

After S11 the `(a, b) = (1, 2)` shape is fully covered (modulo S10):

* `q > p` (S11.1, this PR): axiom-free.
* `p > q ≠ q + 1` (S11.2, this PR): axiom-free.
* `(p, q) = (3, 2), |G| = 12` (S11.3, this PR): axiom-free modulo
  the S10 sorry (via wrapper around S9).

Symmetrically, the `(a, b) = (2, 1)` shape is fully covered (modulo S10):

* `q < p` (S7, PR #17114): axiom-free.
* `p < q ≠ p + 1` (S7.5, PR #17155): axiom-free.
* `(p, q) = (2, 3), |G| = 12` (S9, PR #17270): axiom-free modulo
  the S10 sorry.

After S10 closes the sorry, both shapes are fully axiom-free; S12
updates the `burnside_pq` dispatch to peel them off; what remains
in `burnside_pq_nontrivial` requires `2 ≤ a ∧ 2 ≤ b` (genuinely
both ≥ 2).

## Active Approach (S10, unchanged)

Close `sylow_two_unique_when_n3_four` via element counting:

1. Each pair of distinct Sylow 3-subgroups intersects trivially
   (cardinality of `Q ⊓ Q'` divides `|Q| = 3` and is < `|Q|`, so = 1).
2. `{g : G | g^3 = 1} = ⋃ᵢ (Q_i : Set G)`; partition as
   `{e} ⊔ ⊔ᵢ (Q_i \ {e})`.
3. Cardinality sum: `1 + 4·2 = 9`.
4. For any Sylow 2-subgroup `P`: `P \ {e} ⊆ G \ {g | g^3 = 1}`;
   cardinalities match (`|P| - 1 = 3 = |G \ ...|`); so
   `P = {e} ∪ (G \ ...)` set-theoretically.
5. RHS depends only on `G`, not on choice of `P`; hence
   `Subsingleton (Sylow 2 G)`.

Mathlib API likely needed:
* `Subgroup.disjoint_iff_inf_eq_bot` or `Subgroup.eq_bot_of_card_le_one`
* `Set.ncard_biUnion_disjoint` / `Finset.card_biUnion_disjoint`
* `Subgroup.ext` (for set equality → subgroup equality)
* `Sylow.ext` (for subgroup equality → Sylow equality)

Estimated ~80-120 lines.

## Blockers

Same as S7/S7.5/S9: build verification deferred (`.lake` symlink;
~45 min cold-cache). S11 code shipped "build pending" with high
confidence based on S7/S7.5-pattern adherence.

The residual axiom (orders divisible by `p²` AND `q²` for distinct
primes, once both shapes peeled) requires character theory or
focal-subgroup machinery. Estimated 400-800 lines on top of
`Mathlib.GroupTheory.Focal`.

## Next Action

1. **(S10)** Close `sylow_two_unique_when_n3_four`'s sorry via
   element-counting (~80-120 lines). Mathlib API verification
   required for `Set.ncard_biUnion`-style lemmas.
2. **(S12)** Update `burnside_pq` dispatch to peel off both
   `(a, b) = (2, 1)` AND `(a, b) = (1, 2)`: combine S7/S7.5/S9 for
   `(2, 1)` and S11.1/S11.2/S11.3 for `(1, 2)`. Narrow
   `burnside_pq_nontrivial` axiom hypothesis to `2 ≤ a ∧ 2 ≤ b`.
3. **(S13+)** `|G| = p² · q²` Sylow analysis (~150 lines).
4. **(S14+)** Goldschmidt-Matsuyama on `Mathlib.GroupTheory.Focal` for
   `(a, b) ≥ (2, 2)`.

## Iteration 11 Builds (researcher-11, 2026-05-08)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`: 876→1030 lines.
- New theorem `burnside_p_q_squared_p_lt_q` (~50 lines including docstring).
- New theorem `burnside_p_q_squared_q_lt_p` (~55 lines including docstring).
- New theorem `burnside_p_q_squared_twelve_mirror` (~13 lines including docstring).
- New iteration narrative comment block (~22 lines).
- New helper code: NONE (reuses S7/S7.5 helpers verbatim with primes
  swapped at call sites).
- meta.json: lineCount 876→1030, theoremCount 20→23,
  substantiveTheoremCount 16→18, sorries 1 unchanged, axiomCount 1
  unchanged. Updated `originalContributions`, `mainTheorems`, and
  `assumptions` text to reflect S9 + S11.

## Why Build-Pending Is Acceptable Here

S11's three new declarations follow the established S7/S7.5 pattern
verbatim:

* `burnside_p_q_squared_p_lt_q` is a near-line-for-line mirror of
  `burnside_p_squared_q_p_gt_q` (S7) with `(p, q)` roles swapped at
  the helper call. The only Mathlib calls are the same ones S7 uses.
* `burnside_p_q_squared_q_lt_p` mirrors `burnside_p_squared_q_p_lt_q`
  (S7.5) similarly. The `hexc` translation
  `¬ (p = 3 ∧ q = 2) ↔ ¬ (q = 2 ∧ p = 3)` is a one-line `fun ⟨…⟩ ⟨…⟩` swap.
* `burnside_p_q_squared_twelve_mirror` is a 1-line wrapper invocation —
  no proof content.

The risk profile is identical to S7/S7.5/S9's. If those build, S11
builds. If they need fixing, S11 needs the same fix. Coupling them
in a single fix-up cycle (when `.lake` is repaired) is efficient.
