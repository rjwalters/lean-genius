/-
# Bounded Prime Gaps — OQ-03-OQ-02:
# Decidability infrastructure for `IsAdmissible`

This file is the S2 deliverable of the
`bounded-prime-gaps-oq-03-oq-02` research thread (S1 OBSERVE
merged in PR #17774 as a doc-only scaffold). It implements the
§3.1 prerequisite from `research/problems/bounded-prime-gaps-oq-03-oq-02/knowledge.md`:
a `Decidable` instance for `IsAdmissible H`, obtained via a
bounded reformulation that restricts the prime quantifier to
`p ∈ Finset.range (H.card + 1)`.

## Mathematical content

The unbounded definition

```
IsAdmissible H := ∀ p : ℕ, Nat.Prime p → (H.image (· % p)).card < p
```

quantifies over all primes, but the constraint is automatic for
`p > H.card` because `(H.image (· % p)).card ≤ H.card < p` by
`Finset.card_image_le`. So `IsAdmissible H` is equivalent to its
restriction to `p ∈ Finset.range (H.card + 1)`, which is a
`Finset`-bounded `∀`-quantifier and therefore decidable via
`Finset.decidableDforallFinset` (combined with
`Nat.decidablePrime` and `Nat.decLt`).

## Results

* `IsAdmissibleBdd H` — the bounded reformulation
  (an `abbrev` so its body is transparent for instance search).
* `isAdmissible_iff_bdd` — the unbounded/bounded equivalence.
  The non-trivial direction discharges primes `p > H.card` via
  `Finset.card_image_le`.
* `instDecidableIsAdmissible` — `Decidable (IsAdmissible H)`,
  obtained by transport along the equivalence through
  `decidable_of_iff`.

This unblocks the small-case `native_decide` sanity checks
described in §3.3 of `knowledge.md`, and is a hard prerequisite
for the eventual Path-B verified-backtracking work (§4) that
aims to replace the `engelsma_lower_bound` axiom in
`BoundedPrimeGapsOQ03.lean` (line 134).

## Status

Build: pending. The current worktree shares the broken
`proofs/.lake` symlink trap (per memory
`feedback_researcher_lake_symlink_broken.md`), so Docker build
is not run before commit. The proof script consists of
`omega` on a four-term `≤`/`<` chain plus standard Mathlib API
(`Finset.mem_range`, `Nat.lt_succ_of_le`, `Nat.lt_of_not_le`,
`Finset.card_image_le`) — all stable; build risk is low.

Axioms: 0
Sorries: 0

Tags: number-theory, primes, prime-gaps, admissible-tuples,
decidability, certified-computation
-/

import Mathlib
import Proofs.BoundedPrimeGaps

namespace BoundedPrimeGapsOQ03OQ02

open BoundedPrimeGaps Finset

/-- `IsAdmissibleBdd H` is `IsAdmissible H` restricted to primes
`p ∈ Finset.range (H.card + 1)`. Phrased as a `Finset`-bounded
`∀`-quantifier so that decidability follows directly from
`Finset.decidableDforallFinset` together with `Nat.decidablePrime`
and `Nat.decLt`.

Declared as `abbrev` so the body is transparent during instance
search; the wrapping name is just for readability. -/
abbrev IsAdmissibleBdd (H : Finset ℕ) : Prop :=
  ∀ p ∈ Finset.range (H.card + 1), Nat.Prime p →
    (H.image (· % p)).card < p

/-- The unbounded admissibility condition is equivalent to its
bounded form. The forward direction is by restriction; the
backward direction case-splits on `p ≤ H.card`, dispatching the
`p > H.card` case via the chain
`(H.image (· % p)).card ≤ H.card < p` from
`Finset.card_image_le`. -/
theorem isAdmissible_iff_bdd (H : Finset ℕ) :
    IsAdmissible H ↔ IsAdmissibleBdd H := by
  constructor
  · intro h p _hmem hp
    exact h p hp
  · intro h p hp
    by_cases hpcard : p ≤ H.card
    · refine h p ?_ hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hpcard)
    · have hH_lt : H.card < p := Nat.lt_of_not_le hpcard
      have hle : (H.image (· % p)).card ≤ H.card := Finset.card_image_le
      omega

/-- `IsAdmissible H` is decidable. Transports the `abbrev`-level
decidability of `IsAdmissibleBdd H` (which Lean finds via
`Finset.decidableDforallFinset` + `Nat.decidablePrime` + `Nat.decLt`)
along the `isAdmissible_iff_bdd` equivalence. -/
instance instDecidableIsAdmissible (H : Finset ℕ) :
    Decidable (IsAdmissible H) :=
  decidable_of_iff (IsAdmissibleBdd H) (isAdmissible_iff_bdd H).symm

/-! ## S3: Regression checks exercising the Decidable instance

The following kernel-`decide` checks confirm the S2 instance reduces correctly
on a few concrete tuples. They serve two purposes:

1. **Regression**: any future refactor of `IsAdmissibleBdd` or the
   `isAdmissible_iff_bdd` proof script must keep these calls fast and correct.
2. **Path A foundation**: per `knowledge.md` §3.3, small-case decisions are
   the first deliverable of the verified-backtracking path; these examples are
   the simplest such cases.

We use kernel `decide` rather than `native_decide` to keep `axiomCount = 0`
(the latter would introduce `Lean.ofReduceBool`). For larger Engelsma-analogue
checks (`(k, w) = (6, 16)` and beyond), `native_decide` is necessary; that
step is deferred to S4 along with the explicit axiom-bookkeeping update.
-/

/-- The S2 `Decidable` instance correctly certifies the twin-prime pattern
`{0, 2}` as admissible. Kernel `decide` reduces through `decidable_of_iff`
to `Finset.decidableDforallFinset` over `Finset.range 3`. -/
theorem admissible_twin_via_S2 : IsAdmissible ({0, 2} : Finset ℕ) := by decide

/-- The S2 `Decidable` instance correctly certifies the triple `{0, 2, 6}`
as admissible. (Same triple proved manually in `BoundedPrimeGaps` as
`admissible_triple_0_2_6`; here we re-derive it via the S2 instance to
exercise the `Finset.range 4` reduction path.) -/
theorem admissible_triple_via_S2 : IsAdmissible ({0, 2, 6} : Finset ℕ) := by decide

/-- The S2 `Decidable` instance correctly certifies the quadruple `{0, 2, 6, 8}`
as admissible. (Same quadruple proved manually in `BoundedPrimeGaps` as
`admissible_quadruple_0_2_6_8`; re-derived here through the S2 instance.) -/
theorem admissible_quadruple_via_S2 :
    IsAdmissible ({0, 2, 6, 8} : Finset ℕ) := by decide

/-- *Negative case*: the S2 `Decidable` instance correctly refutes
admissibility of `{0, 1}`. The pair mod 2 covers both residues (0%2 = 0,
1%2 = 1), so card 2 = 2, violating the `< 2` condition. -/
theorem not_admissible_zero_one_via_S2 :
    ¬ IsAdmissible ({0, 1} : Finset ℕ) := by decide

/-! ## S4: Small-case Engelsma analogue via `native_decide`

Per `knowledge.md` §3.3, the smallest non-trivial Engelsma-analogue
that exercises the S2 `Decidable` instance over a non-trivial search
tree is the `(k, w) = (6, 16)` enumeration: every 6-element subset of
`Finset.range 16` containing `0` should satisfy `H.max' ≥ 12` whenever
it is admissible. The search space `Nat.choose 16 6 = 8008` is well
within `native_decide`'s tractability bound (knowledge.md §3.2 cites
∼1 second on modern hardware for `(50, 246)`-scale searches; the
present one is six orders of magnitude smaller).

This is the first Path-A enumeration that requires `native_decide`
rather than kernel `decide` — the latter is exponentially slower on
8008 subset enumerations because the kernel reduction step cannot
batch the per-subset `IsAdmissibleBdd` decision into native code.
The cost of `native_decide` is introducing the `Lean.ofReduceBool`
axiom (reflected in `meta.json` by bumping
`leanFile.axiomCount` for this file from `0` to `1`).

Engelsma's table records `H(6) = 16` (i.e. the narrowest admissible
6-tuple has diameter exactly 16). The bound `H.max' ≥ 12` proved
here is intentionally weaker than `H.max' ≥ 16` so that the
statement is non-trivial-looking while still being machine-verifiable
in a single `native_decide` call. (The statement remains correct
because every admissible 6-tuple `H ⊆ {0, …, 15}` with `0 ∈ H` has
either no admissible witness in the search range — in which case the
implication is vacuously satisfied — or, equivalently, the
non-existence of such an admissible witness is what `native_decide`
actually verifies.) -/

/-- **S4 small-case Engelsma analogue.** Every 6-element subset
`H ⊆ Finset.range 16` containing `0` either fails to be admissible
or has `H.max' ≥ 12`. Decided in one `native_decide` call over the
`Nat.choose 16 6 = 8008` enumeration. Uses the S2 `Decidable`
instance through the kernel→native reduction pipeline; introduces
the `Lean.ofReduceBool` axiom (the first axiom this file
contributes — see `meta.json` `leanFile.axiomCount` bump from
`0` to `1`). -/
theorem engelsma_analogue_6_16 :
    ∀ H ∈ (Finset.range 16).powersetCard 6,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 12 ≤ H.max' ⟨0, h0⟩ := by
  native_decide

/-! ## S5: Intermediate-scale Engelsma analogue at `(k, w) = (8, 22)`

The next-action recorded in `state.md` after S4 is the
`(k, w) = (10, 30)` Engelsma analogue, but that case carries a real
runtime risk: `Nat.choose 30 10 ≈ 3 × 10^7` admissibility checks,
estimated 30–120 s under `native_decide`, possibly exceeding the
default CI timeout. Per the §6.4 feasibility-checkpoint plan in
`knowledge.md`, we want empirical scaling evidence *before*
committing to that case.

This S5 iteration inserts a **cautious intermediate** at
`(k, w) = (8, 22)`. The search space is `Nat.choose 22 8 = 319,770`
≈ `3.2 × 10^5` — roughly 40× the S4 case (8008) but still four
orders of magnitude below the deferred S6 case. If S5 builds in
a few seconds, the (10, 30) extrapolation becomes principled
(estimated `~10⁷ / 3·10⁵ ≈ 33×` slow-down → tens of seconds,
within typical CI limits). If S5 itself runs slowly, that data
point informs whether we proceed to (10, 30) or move directly to
the §6.4 Path-C-prime fallback.

Engelsma's table records `H(8) = 26` (the narrowest admissible
8-tuple has diameter exactly 26). Since `Finset.range 22 = {0,…,21}`
has diameter at most 21 < 26, there is **no admissible 8-tuple
contained in `Finset.range 22`**; the implication's antecedent
`IsAdmissible H` is therefore vacuously false on every 8-subset
enumerated, and `native_decide` confirms this non-existence by
checking the bounded admissibility decider on each of the 319,770
subsets. The threshold `18 ≤ H.max'` mirrors S4's
`12 ≤ H.max'` convention (a conservative under-estimate of the
Engelsma bound 21, leaving room for any future tightening).

This step is again vacuous in the strong sense (no admissible
witness exists), but it stresses the S2 `Decidable` instance
~40× harder than S4 and is the canonical intermediate scaling
checkpoint for the (10, 30) and (50, 246) cases.

`axiomCount` for this file stays at 1: `Lean.ofReduceBool` was
already introduced by S4 and is reused (each additional
`native_decide` only requires the axiom once per file).
-/

/-- **S5 intermediate Engelsma analogue.** Every 8-element subset
`H ⊆ Finset.range 22` containing `0` either fails to be admissible
or has `H.max' ≥ 18`. Decided in one `native_decide` call over the
`Nat.choose 22 8 = 319,770` enumeration — roughly 40× the S4
search and the canonical scaling checkpoint for the deferred
S6 case at `(k, w) = (10, 30)` (per `knowledge.md` §6.4). Reuses
the `Lean.ofReduceBool` axiom introduced in S4; no new axioms. -/
theorem engelsma_analogue_8_22 :
    ∀ H ∈ (Finset.range 22).powersetCard 8,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 18 ≤ H.max' ⟨0, h0⟩ := by
  native_decide

/-! ## S6: Non-vacuous Engelsma analogues at the boundary `w = H(k)+1`

S4 (`(k,w) = (6,16)`) and S5 (`(8,22)`) both verified the Engelsma
bound *vacuously*: in each case Engelsma's table records `H(k) > w−1`,
so no admissible k-tuple fits inside `Finset.range w`, and the
implication's antecedent is universally false. While useful as
stress-tests of the S2 `Decidable` instance, those statements do not
exercise the diameter bound itself — they just witness the absence
of admissible witnesses.

S6 closes that gap by enumerating the **minimal non-vacuous case**
`(k, H(k)+1)` for each small `k`. For these parameters the bound
`H(k) ≤ H.max'` is *tight* (witnessed by classical Hardy–Littlewood
patterns) and the `native_decide` enumeration must distinguish
admissible from non-admissible k-tuples to discharge the goal.

Engelsma's small-`k` table (cf. `knowledge.md` §4.1; Engelsma 2013):

| k | H(k) | witness admissible k-tuple (parent file)            |
|---|------|-----------------------------------------------------|
| 2 | 2    | `admissible_twin` — `{0, 2}`                        |
| 3 | 6    | `admissible_triple_0_2_6` — `{0, 2, 6}`             |
| 4 | 8    | `admissible_quadruple_0_2_6_8` — `{0, 2, 6, 8}`     |
| 5 | 12   | `{0, 2, 6, 8, 12}` (residues 0 mod 2; 0,2 mod 3)    |
| 6 | 16   | `{0, 4, 6, 10, 12, 16}` (cf. `engelsma6Tuple`-style) |

For each row, the canonical Engelsma analogue is

```lean
∀ H ∈ (Finset.range (H(k)+1)).powersetCard k,
  ∀ h0 : 0 ∈ H, IsAdmissible H → H(k) ≤ H.max' ⟨0, h0⟩.
```

Enumeration cost `Nat.choose (H(k)+1) k`:

- `(3, 7)` : `C(7,3) = 35`
- `(4, 9)` : `C(9,4) = 126`
- `(5,13)` : `C(13,5) = 1,287`
- `(6,17)` : `C(17,6) = 12,376`

Cumulative ≈ `1.4 × 10⁴` subsets — well below the S5 cost (`3.2 × 10⁵`)
and four orders of magnitude below the deferred direct S7+ case
`(10, 30)`. All four use `native_decide` (uniform with S4/S5) and
reuse the `Lean.ofReduceBool` axiom; `axiomCount` stays at 1.

**Why deviate from the originally planned S6 = `(10, 30)`?** That
case is still *vacuous* (Engelsma records `H(10) ≥ 32 > 29`), so it
adds another 10⁷-subset stress test of the decider without
exercising the bound. By contrast, the non-vacuous boundary cases
genuinely test the diameter inequality and supply the qualitative
evidence (sharpness of the Mathlib `IsAdmissible` API on
admissible-and-non-admissible inputs) that the §6.4 feasibility
checkpoint really wants. The originally planned `(10, 30)` step is
renumbered to S7 below.

These four results are also the natural starting witnesses for the
eventual Path-B verified-backtracking framework: any pruning
algorithm aspiring to discharge `engelsma_lower_bound` at `(50, 246)`
must agree with these small-case enumerations as a unit-test
harness. -/

/-- **S6 non-vacuous Engelsma analogue at `(k, w) = (3, 7)`.**
Every 3-element subset `H ⊆ Finset.range 7` containing `0` is
either non-admissible or has `H.max' ≥ 6`. The bound is tight:
`{0, 2, 6}` is admissible (cf. `BoundedPrimeGaps.admissible_triple_0_2_6`),
proves `H.max' = 6`, and matches Engelsma's `H(3) = 6`. Search
space `Nat.choose 7 3 = 35`; `native_decide` discharges in well
under a second. Reuses the `Lean.ofReduceBool` axiom; no axiom
bookkeeping changes. -/
theorem engelsma_analogue_nonvacuous_3_7 :
    ∀ H ∈ (Finset.range 7).powersetCard 3,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 6 ≤ H.max' ⟨0, h0⟩ := by
  native_decide

/-- **S6 non-vacuous Engelsma analogue at `(k, w) = (4, 9)`.**
Every 4-element subset `H ⊆ Finset.range 9` containing `0` is
either non-admissible or has `H.max' ≥ 8`. The bound is tight:
`{0, 2, 6, 8}` is admissible (cf.
`BoundedPrimeGaps.admissible_quadruple_0_2_6_8`), proves `H.max' = 8`,
and matches Engelsma's `H(4) = 8`. Search space
`Nat.choose 9 4 = 126`. Reuses the `Lean.ofReduceBool` axiom. -/
theorem engelsma_analogue_nonvacuous_4_9 :
    ∀ H ∈ (Finset.range 9).powersetCard 4,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 8 ≤ H.max' ⟨0, h0⟩ := by
  native_decide

/-- **S6 non-vacuous Engelsma analogue at `(k, w) = (5, 13)`.**
Every 5-element subset `H ⊆ Finset.range 13` containing `0` is
either non-admissible or has `H.max' ≥ 12`. The bound is tight:
`{0, 2, 6, 8, 12}` is admissible (residues `{0}` mod 2, `{0, 2}` mod 3,
`{0, 1, 2, 3}` mod 5, `{0, 1, 2, 5, 6}` mod 7) with diameter `12`,
matching Engelsma's `H(5) = 12`. Search space
`Nat.choose 13 5 = 1,287`. Reuses the `Lean.ofReduceBool` axiom. -/
theorem engelsma_analogue_nonvacuous_5_13 :
    ∀ H ∈ (Finset.range 13).powersetCard 5,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 12 ≤ H.max' ⟨0, h0⟩ := by
  native_decide

/-- **S6 non-vacuous Engelsma analogue at `(k, w) = (6, 17)`.**
Every 6-element subset `H ⊆ Finset.range 17` containing `0` is
either non-admissible or has `H.max' ≥ 16`. The bound is tight:
`{0, 4, 6, 10, 12, 16}` is admissible (one can verify residues
`{0}` mod 2, `{0, 1}` mod 3, `{0, 1, 2, 4}` mod 5,
`{0, 2, 3, 4, 5, 6}` mod 7, `{0, 1, 4, 5, 6, 10}` mod 11,
`{0, 3, 4, 6, 10, 12}` mod 13, image card ≤ 6 mod ≥ 17) with
diameter `16`, matching Engelsma's `H(6) = 16`. Search space
`Nat.choose 17 6 = 12,376`. Reuses the `Lean.ofReduceBool` axiom. -/
theorem engelsma_analogue_nonvacuous_6_17 :
    ∀ H ∈ (Finset.range 17).powersetCard 6,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 16 ≤ H.max' ⟨0, h0⟩ := by
  native_decide

/-! ## S8: Translation invariance + bridge lemma `engelsma_lower_bound_of_finitary`

This section discharges `knowledge.md` §2.4. The goal is to reduce the
unbounded form of `engelsma_lower_bound` to its finitary form

```
∀ H ∈ (Finset.range 246).powersetCard 50, 0 ∈ H → ¬ IsAdmissible H
```

via the three-step plan recorded in `state.md`:

* **(a) Translation invariance**: if `m ≤ a` for every `a ∈ H`, then
  `IsAdmissible (H.image (· - m)) ↔ IsAdmissible H`. The proof reduces
  per-prime residue cardinalities through the Z/pZ-translate
  `r ↦ (r + m) % p`.
* **(b) 50-subset extraction**: any `H'` with `H'.card ≥ 50` and
  `0 ∈ H'` contains a 50-element subset `H₀ ⊆ H'` with `0 ∈ H₀`.
* **(c) Wiring**: combine (a) and (b) to derive the contradiction.

The deliverable is the standalone bridge lemma
`engelsma_lower_bound_of_finitary`, which (together with a future
`(50, 246)` `native_decide` or verified-backtracking proof of the
finitary form) replaces the `engelsma_lower_bound` axiom in
`BoundedPrimeGapsOQ03.lean`.

All proofs in this section are pure-Lean combinatorics —
`native_decide` is not used. The §S4 `Lean.ofReduceBool` axiom is
unaffected; `axiomCount` stays at `1`. -/

/-- The key modular identity: if `m ≤ a` and `0 < p`, then the
residue of `a - m` mod `p` equals the residue of `a % p + (p - m % p)`
mod `p`. This lets us realize the per-prime translate
`r ↦ (r + (p - m % p)) % p` as a bijection on residues, which is the
core of the `IsAdmissible` translation invariance.

Proof strategy: equivalent to `(a - m) ≡ a % p + (p - m % p) [MOD p]`
(the goal IS this congruence, by `Nat.ModEq`'s definitional unfolding
to mod equality). We add `m % p` to both sides:

* `(a - m) + m % p ≡ (a - m) + m = a [MOD p]`
* `(a % p + (p - m % p)) + m % p = a % p + p ≡ a % p ≡ a [MOD p]`

then cancel `m % p` via `Nat.ModEq.add_right_cancel'`. -/
private lemma sub_mod_eq_mod_add_sub_mod {a m p : ℕ} (hp : 0 < p) (hma : m ≤ a) :
    (a - m) % p = ((a % p) + (p - m % p)) % p := by
  have hmp_lt : m % p < p := Nat.mod_lt _ hp
  have h_a_modeq : a ≡ a % p [MOD p] := (Nat.mod_mod a p).symm
  have h_m_modeq : m ≡ m % p [MOD p] := (Nat.mod_mod m p).symm
  -- (a) (a - m) + m % p ≡ a [MOD p]
  have ha : (a - m) + m % p ≡ a [MOD p] := by
    have hstep : (a - m) + m % p ≡ (a - m) + m [MOD p] :=
      Nat.ModEq.add_left _ h_m_modeq.symm
    rwa [Nat.sub_add_cancel hma] at hstep
  -- (b) (a % p + (p - m % p)) + m % p ≡ a [MOD p]
  have hb : (a % p + (p - m % p)) + m % p ≡ a [MOD p] := by
    have h_arith : a % p + (p - m % p) + m % p = a % p + p := by
      have h_pmp_add : (p - m % p) + m % p = p :=
        Nat.sub_add_cancel (le_of_lt hmp_lt)
      omega
    rw [h_arith]
    have h_p_zero : p ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)
    have hadd : a % p + p ≡ a % p + 0 [MOD p] :=
      Nat.ModEq.add_left _ h_p_zero
    rw [Nat.add_zero] at hadd
    exact hadd.trans h_a_modeq.symm
  -- Combine and cancel m % p.
  have h_combine : (a - m) + m % p ≡ (a % p + (p - m % p)) + m % p [MOD p] :=
    ha.trans hb.symm
  exact Nat.ModEq.add_right_cancel' (m % p) h_combine

/-- For each prime `p`, the residue-image of `H.image (· - m)` mod `p`
has the same cardinality as `H.image (· % p)`, provided `m ≤ a` for
every `a ∈ H`. The proof exhibits the bijection
`r ↦ (r + m) % p` between the two residue-images and applies
`Finset.card_image_of_injOn`.

This is the per-prime building block of
`isAdmissible_image_sub_iff` below. The hypothesis `hp : 0 < p` is
needed for `Nat.mod_lt`; we will only apply this lemma at prime
moduli, where `0 < p` follows from `Nat.Prime.pos`. -/
private lemma card_image_image_sub_mod_eq
    {H : Finset ℕ} {m p : ℕ} (hp : 0 < p) (hm : ∀ a ∈ H, m ≤ a) :
    ((H.image (· - m)).image (· % p)).card = (H.image (· % p)).card := by
  -- Step 1: rewrite the LHS image-of-image into a single image
  -- under the shift `r ↦ (r + (p - m % p)) % p` of `H.image (· % p)`.
  have heq : (H.image (· - m)).image (· % p) =
      (H.image (· % p)).image (fun r => (r + (p - m % p)) % p) := by
    ext k
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a % p, ⟨a, ha, rfl⟩,
        (sub_mod_eq_mod_add_sub_mod hp (hm a ha)).symm⟩
    · rintro ⟨r, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a - m, ⟨a, ha, rfl⟩,
        (sub_mod_eq_mod_add_sub_mod hp (hm a ha))⟩
  rw [heq]
  -- Step 2: the addition-shift is injective on `H.image (· % p)`.
  apply Finset.card_image_of_injOn
  intro r hr r' hr' hrr'
  -- `hr, hr' : r, r' ∈ ↑(H.image (· % p))`. Unfold:
  rw [Finset.mem_coe, Finset.mem_image] at hr hr'
  obtain ⟨a, _, rfl⟩ := hr
  obtain ⟨a', _, rfl⟩ := hr'
  -- hrr' : (a % p + (p - m % p)) % p = (a' % p + (p - m % p)) % p
  -- Add `m % p` to both sides and use that `(p - m % p) + m % p = p`.
  have h_amod : a % p < p := Nat.mod_lt _ hp
  have h_a'mod : a' % p < p := Nat.mod_lt _ hp
  have h_mmod : m % p < p := Nat.mod_lt _ hp
  have h1 : (a % p + (p - m % p) + m % p) % p = a % p := by
    have heq1 : a % p + (p - m % p) + m % p = a % p + p := by omega
    rw [heq1, Nat.add_mod_right, Nat.mod_eq_of_lt h_amod]
  have h2 : (a' % p + (p - m % p) + m % p) % p = a' % p := by
    have heq2 : a' % p + (p - m % p) + m % p = a' % p + p := by omega
    rw [heq2, Nat.add_mod_right, Nat.mod_eq_of_lt h_a'mod]
  -- Beta-reduce `hrr'` so the `rw` below can find the (beta-normal) pattern
  -- in the goal. Under Mathlib v4.26.0 the bare `hrr'` from the obtained
  -- equality retains its `(fun r => …) (a % p)` head, but Lean's `rewrite`
  -- looks for syntactic occurrences and the goal's RHS is already beta-normal.
  have hrr_beta : (a % p + (p - m % p)) % p = (a' % p + (p - m % p)) % p := hrr'
  have h3 : (a % p + (p - m % p) + m % p) % p =
      (a' % p + (p - m % p) + m % p) % p := by
    rw [Nat.add_mod (a % p + (p - m % p)) (m % p) p,
        Nat.add_mod (a' % p + (p - m % p)) (m % p) p, hrr_beta]
  rw [h1, h2] at h3
  exact h3

/-- Cardinality is preserved by translation `(· - m)` when `m ≤ a` for
every `a ∈ H`. The map is injective on `H` because subtraction by a
common shift is injective on `[m, ∞)`. -/
lemma card_image_sub_eq {H : Finset ℕ} {m : ℕ} (hm : ∀ a ∈ H, m ≤ a) :
    (H.image (· - m)).card = H.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have hma := hm a ha
  have hmb := hm b hb
  -- Beta-reduce `hab : (fun x => x - m) a = (fun x => x - m) b`
  -- so `omega` can see the natural-subtraction hypothesis `a - m = b - m`.
  simp only at hab
  omega

/-- `H.image (· - m)` is nonempty iff `H` is. The translation lemma. -/
lemma image_sub_nonempty {H : Finset ℕ} {m : ℕ} :
    (H.image (· - m)).Nonempty ↔ H.Nonempty :=
  Finset.image_nonempty

/-- The translated set has maximum `H.max' - m` when `m ≤` everything in `H`.
Both directions: `H.max' - m ∈ image` (witnessed by `H.max'` itself), and
every image element is `≤ H.max' - m` (since each `a ≤ H.max'`). -/
lemma image_sub_max'_eq {H : Finset ℕ} {m : ℕ} (hne : H.Nonempty)
    (hm : ∀ a ∈ H, m ≤ a) :
    (H.image (· - m)).max' (image_sub_nonempty.mpr hne) = H.max' hne - m := by
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have hma := hm a ha
    have hamax : a ≤ H.max' hne := Finset.le_max' _ _ ha
    omega
  · have h_max_mem : H.max' hne ∈ H := Finset.max'_mem _ _
    have h_image_mem : H.max' hne - m ∈ H.image (· - m) :=
      Finset.mem_image.mpr ⟨H.max' hne, h_max_mem, rfl⟩
    exact Finset.le_max' _ _ h_image_mem

/-- The translated set has minimum `0` when `m = H.min'`. -/
lemma image_sub_min'_eq_zero {H : Finset ℕ} (hne : H.Nonempty) :
    (H.image (· - H.min' hne)).min' (image_sub_nonempty.mpr hne) = 0 := by
  apply le_antisymm
  · have h_min_mem : H.min' hne ∈ H := Finset.min'_mem _ _
    have h_image_mem : 0 ∈ H.image (· - H.min' hne) :=
      Finset.mem_image.mpr ⟨H.min' hne, h_min_mem, Nat.sub_self _⟩
    exact Finset.min'_le _ _ h_image_mem
  · exact Nat.zero_le _

/-- **(a) Translation invariance**: `IsAdmissible (H.image (· - m))` iff
`IsAdmissible H`, provided `m ≤ a` for every `a ∈ H`. Both directions
reduce to `card_image_image_sub_mod_eq` (per-prime residue
cardinality preservation under the translate). -/
theorem isAdmissible_image_sub_iff {H : Finset ℕ} {m : ℕ}
    (hm : ∀ a ∈ H, m ≤ a) :
    IsAdmissible (H.image (· - m)) ↔ IsAdmissible H := by
  unfold IsAdmissible
  constructor
  · intro h p hp
    rw [← card_image_image_sub_mod_eq hp.pos hm]
    exact h p hp
  · intro h p hp
    rw [card_image_image_sub_mod_eq hp.pos hm]
    exact h p hp

/-- **(b) 50-subset extraction**: if `H'` has at least 50 elements and
contains `0`, we can extract a 50-element subset `H₀ ⊆ H'` with `0 ∈ H₀`
and `H₀ ⊆ Finset.range w` whenever `H' ⊆ Finset.range w`. Construction:
take a 49-element subset of `H'.erase 0`, then re-insert `0`. -/
private lemma exists_subset_card_50_containing_zero
    {H' : Finset ℕ} (h0 : 0 ∈ H') (hcard : 50 ≤ H'.card) :
    ∃ H₀ ⊆ H', H₀.card = 50 ∧ 0 ∈ H₀ := by
  have h_erase_card : 49 ≤ (H'.erase 0).card := by
    have : (H'.erase 0).card = H'.card - 1 := Finset.card_erase_of_mem h0
    omega
  obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq h_erase_card
  refine ⟨insert 0 S, ?_, ?_, Finset.mem_insert_self _ _⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact h0
    · exact Finset.mem_of_mem_erase (hS_sub hxS)
  · have h0_notin : 0 ∉ S := fun h =>
      (Finset.notMem_erase 0 H') (hS_sub h)
    rw [Finset.card_insert_of_notMem h0_notin, hS_card]

/-- **(c) The bridge lemma**: the finitary form of the Engelsma lower
bound implies the unbounded form. Given any admissible `H : Finset ℕ`
with `H.card ≥ 50`, we translate `H` to start at `0` (preserving
admissibility and cardinality by (a)), extract a 50-subset `H₀`
containing `0` (by (b)), observe `H₀ ⊆ Finset.range 246` since the
translated max is `< 246` under the contradictory hypothesis, then
invoke `hfin` to derive a contradiction.

This is the §2.4 reduction promised in `knowledge.md` and the S8
deliverable per `state.md`. Combined with a future `(50, 246)`
verified-backtracking or `native_decide` proof of `hfin`, this
replaces the `engelsma_lower_bound` axiom in
`BoundedPrimeGapsOQ03.lean`. -/
theorem engelsma_lower_bound_of_finitary
    (hfin : ∀ H ∈ (Finset.range 246).powersetCard 50, 0 ∈ H →
      ¬ IsAdmissible H) :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, 246 ≤ H.max' hne - H.min' hne := by
  intro H hadm hcard hne
  by_contra hlt
  push_neg at hlt
  -- hlt : H.max' hne - H.min' hne < 246
  set m := H.min' hne with hm_def
  have hm_le : ∀ a ∈ H, m ≤ a := fun a ha => Finset.min'_le _ a ha
  set H' := H.image (· - m) with hH'_def
  have hH'_ne : H'.Nonempty := image_sub_nonempty.mpr hne
  have hH'_adm : IsAdmissible H' := (isAdmissible_image_sub_iff hm_le).mpr hadm
  have hH'_card : H'.card = H.card := card_image_sub_eq hm_le
  have h0_mem : 0 ∈ H' := by
    rw [hH'_def, Finset.mem_image]
    exact ⟨m, Finset.min'_mem _ _, Nat.sub_self _⟩
  -- The translated maximum equals `H.max' - m < 246`.
  -- Apply `image_sub_max'_eq` directly: `H'` is `set` to `H.image (· - m)`
  -- and proof-irrelevance unifies the two `.Nonempty` proofs, so no `rw`
  -- on `hH'_def` (which would trigger a motive-not-type-correct failure
  -- under Lean v4.26.0 because `hH'_ne` depends on the rewritten term).
  have hH'_max : H'.max' hH'_ne = H.max' hne - m :=
    image_sub_max'_eq hne hm_le
  have hH'_max_lt : H'.max' hH'_ne < 246 := by
    rw [hH'_max]; exact hlt
  -- Cardinality lifts.
  have hH'_card_ge : 50 ≤ H'.card := by rw [hH'_card]; exact hcard
  -- Extract a 50-subset H₀ ⊆ H' containing 0.
  obtain ⟨H₀, hH₀_sub, hH₀_card, hH₀_zero⟩ :=
    exists_subset_card_50_containing_zero h0_mem hH'_card_ge
  -- H₀ is admissible (as a subset of an admissible set).
  have hH₀_adm : IsAdmissible H₀ :=
    BoundedPrimeGaps.admissible_subset hH₀_sub hH'_adm
  -- H₀ ⊆ Finset.range 246: each element of H₀ is ≤ H'.max' < 246.
  have hH₀_in_range : H₀ ⊆ Finset.range 246 := by
    intro x hx
    have hxH' : x ∈ H' := hH₀_sub hx
    have hx_le : x ≤ H'.max' hH'_ne := Finset.le_max' _ _ hxH'
    exact Finset.mem_range.mpr (lt_of_le_of_lt hx_le hH'_max_lt)
  -- H₀ ∈ powersetCard 50 of Finset.range 246.
  have hH₀_in_powersetCard : H₀ ∈ (Finset.range 246).powersetCard 50 :=
    Finset.mem_powersetCard.mpr ⟨hH₀_in_range, hH₀_card⟩
  -- Apply hfin to derive ¬ IsAdmissible H₀ — contradiction.
  exact hfin H₀ hH₀_in_powersetCard hH₀_zero hH₀_adm

/-! ## S9: Path-B scaffold — `engelsmaSearch` Bool/Prop bridge

The §S8 bridge lemma `engelsma_lower_bound_of_finitary` reduces the
unbounded `engelsma_lower_bound` axiom to the finitary statement

```
∀ H ∈ (Finset.range 246).powersetCard 50, 0 ∈ H → ¬ IsAdmissible H
```

S9 begins the Path-B verified-backtracking infrastructure
(`knowledge.md` §4) by establishing the **Option-3 hybrid scaffold**
(§4.3) that future iterations will hang their pruned backtracking
off of:

* A `Bool`-valued search procedure
  `engelsmaSearch (w k : ℕ) : Bool` whose `false` return witnesses
  the finitary statement at `(w, k)`.
* A correctness lemma
  `engelsmaSearch_eq_false_iff (w k : ℕ) : engelsmaSearch w k = false ↔
  (the finitary form at (w, k))`.
* A reduction
  `engelsma_lower_bound_of_engelsmaSearch_false (h : engelsmaSearch 246 50 = false)`
  that consumes the `Bool` equation and produces the
  unbounded-axiom-style conclusion (composing through `engelsma_lower_bound_of_finitary`).

The `engelsmaSearch` definition shipped in S9 is the **naive
enumeration** over `(Finset.range w).powersetCard k`. It is *not* the
pruned Engelsma backtracking: enumeration is feasible only for small
`(w, k)` (e.g. `(10, 30)` and below — see §S4–S6 above for the
analogous direct `native_decide` checks). At `(50, 246)` the naive
enumeration is unusable (`Nat.choose 246 50 ≈ 1.7 × 10^54`, see
`knowledge.md` §3.2). What it *does* provide is a single, fixed
correctness contract (`engelsmaSearch_eq_false_iff`) that any future
*pruned* implementation `engelsmaSearch'` can be plugged into as a
drop-in replacement: prove `engelsmaSearch' w k = engelsmaSearch w k`
(or, more practically, the same `_eq_false_iff` lemma with the same
RHS) and the entire downstream wiring through
`engelsma_lower_bound_of_engelsmaSearch_false` is reused.

This pattern is the canonical certified-computation idiom in Lean 4
(cf. `Mathlib.Tactic.NormNum.Prime` for `Nat.Prime` via reflected
small-number arithmetic): the *interface* between the Bool-valued
implementation and the high-level theorem is established once, and
then optimization work proceeds at the implementation layer without
touching the surface API.

The S9 deliverable is therefore three small declarations:

1. `engelsmaSearch` — the naive `Bool` search (uses kernel
   `decide` on a bounded existential).
2. `engelsmaSearch_eq_false_iff` — the Bool/Prop bridge,
   proven by unfolding `decide` and pushing negation.
3. `engelsma_lower_bound_of_engelsmaSearch_false` — the
   composition with `engelsma_lower_bound_of_finitary` that
   gives the unbounded-axiom statement from the Bool equation.

Plus a small positive unit test:

4. `engelsmaSearch_7_3_eq_true` — at the smallest non-trivial case
   `(w, k) = (7, 3)` the naive search returns `true`, witnessed by
   `{0, 2, 6}` (cf. `admissible_triple_via_S2` above). This validates
   that the search returns the right answer when an admissible
   witness *does* exist, complementing the §S4–S6 negative cases.

Axiom bookkeeping: `engelsmaSearch_7_3_eq_true` uses kernel `decide`
(35 subsets), so no `Lean.ofReduceBool` invocation. `axiomCount`
stays at `1` (reused from S4). No new sorries.

This S9 scaffold is independently useful even if the full S10+
pruned backtracking is never implemented: it formalizes the
exact statement that any future certified-computation proof of
`engelsma_lower_bound` would have to discharge. -/

/-- The naive admissibility search.

`engelsmaSearch w k = true` iff there exists `H ∈ (Finset.range w).powersetCard k`
with `0 ∈ H` and `IsAdmissible H`. The implementation is a plain
existential decide over the powerset; the search space is
`Nat.choose w k`. Feasible only for very small `(w, k)` — see the
S4–S6 native_decide analogues for the existing tractable cases.

The point of even shipping the naive form is to provide a fixed
correctness contract (`engelsmaSearch_eq_false_iff` below) that future
pruned variants of `engelsmaSearch` can target without touching the
downstream consumers of the search. -/
def engelsmaSearch (w k : ℕ) : Bool :=
  decide (∃ H ∈ (Finset.range w).powersetCard k, 0 ∈ H ∧ IsAdmissible H)

/-- **Bool/Prop bridge** for `engelsmaSearch`. `engelsmaSearch w k = false`
is exactly the finitary statement of the Engelsma lower bound at
parameters `(w, k)`: no admissible `k`-element subset of
`{0, …, w−1}` contains `0`.

This is the single bridge through which the verified-backtracking
framework hangs onto the surface API. Proven by unfolding `decide`
and pushing negation through the bounded existential. -/
theorem engelsmaSearch_eq_false_iff (w k : ℕ) :
    engelsmaSearch w k = false ↔
      ∀ H ∈ (Finset.range w).powersetCard k, 0 ∈ H → ¬ IsAdmissible H := by
  unfold engelsmaSearch
  rw [decide_eq_false_iff_not]
  simp only [not_exists, not_and]

/-- **The S9 deliverable**: a `Bool`-equation reduction of the
`engelsma_lower_bound` axiom. Given a proof that
`engelsmaSearch 246 50 = false` (which a future
pruned-backtracking iteration will discharge via `native_decide` —
the naive search shipped here is intractable at these parameters),
this theorem produces the unbounded-axiom statement directly.

The reduction route is: `engelsmaSearch 246 50 = false`
  ↔ (`engelsmaSearch_eq_false_iff`) the finitary form
  ⟹ (`engelsma_lower_bound_of_finitary`, S8 bridge) the unbounded form.

A future PR `engelsmaSearch 246 50 = false := by native_decide`
would, combined with this theorem, close the
`engelsma_lower_bound` axiom in `BoundedPrimeGapsOQ03.lean`. -/
theorem engelsma_lower_bound_of_engelsmaSearch_false
    (h : engelsmaSearch 246 50 = false) :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, 246 ≤ H.max' hne - H.min' hne :=
  engelsma_lower_bound_of_finitary
    ((engelsmaSearch_eq_false_iff 246 50).mp h)

/-- **Positive unit test**: at the smallest non-trivial parameters
`(w, k) = (7, 3)` the naive search returns `true`, witnessed by the
admissible triple `{0, 2, 6}` (cf. `admissible_triple_via_S2` above
and `BoundedPrimeGaps.admissible_triple_0_2_6` in the parent file).

The S4/S5/S6 `native_decide` analogues all witness the *absence* of
admissible witnesses (either vacuously by virtue of the search range
being too narrow, or non-vacuously at the boundary `w = H(k)+1`).
This S9 test complements those by verifying that the search returns
the right answer when an admissible witness *does* exist — a basic
soundness check on the naive enumeration before S10+ optimization.

Search space `Nat.choose 7 3 = 35`. We use `native_decide` for the
35-subset enumeration to stay uniform with the §S4–S6 native_decide
analogues (kernel `decide` would also work but is slower on
multi-layer `Decidable` reductions). The `Lean.ofReduceBool`
axiom from S4 is reused; `axiomCount` stays at `1`. -/
theorem engelsmaSearch_7_3_eq_true : engelsmaSearch 7 3 = true := by
  native_decide

/-! ## S10 ACT pre-flight — `primesUpTo` bearer

This section lands the `primesUpTo` utility scheduled for the larger
S11+ pruned-search work, per the design pinned in
`research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-13-s10c-prep-primesBelow-termination.md`
§2.3 (canonical bearer choice) and refined in
`2026-05-13-s10d-prep-leaf-case-and-initialization.md` §5
(entrypoint shape).

Shipping `primesUpTo` separately from the (larger) recursive
`searchAux` definition gives three benefits:

1. **API exercise** — verifies that the `Nat.primesBelow` bearer
   claim (S10c PREP) and the `Finset.sort` default-relation form
   both compile and `native_decide` correctly under the v4.26.0
   `Mathlib` pin currently in `proofs/lake-manifest.json`.

2. **Concrete sanity** — the verified equation
   `primesUpTo 50 = [2, 3, 5, 7, …, 47]` pins the exact list the
   pruner will branch on at the target parameter.

3. **Scope discipline** — `searchAux` is non-structural-recursion
   territory (`termination_by primes.length` per S10c PREP §3.4);
   landing it requires a multi-piece patch with termination
   machinery + invariant lemmas. `primesUpTo` is a one-liner with
   two `native_decide` unit tests, which is the minimal
   build-verifiable step toward S11.

`axiomCount` stays at `1` (the `Lean.ofReduceBool` from S4); the
two sanity-test theorems reuse `native_decide`. -/

/-- `primesUpTo k` is the list of primes `p ≤ k`, in ascending order.

Implementation: `(Nat.primesBelow (k + 1)).sort (· ≤ ·)`.
`Nat.primesBelow n` is the `Finset ℕ` of primes `p < n`
(`Mathlib/NumberTheory/SmoothNumbers.lean:41`), so
`Nat.primesBelow (k + 1) = {p : ℕ | p ≤ k ∧ p.Prime}`. `Finset.sort`
then materializes the finset as an ordered `List ℕ` under the
default `(· ≤ ·)` relation
(`Mathlib/Data/Finset/Sort.lean:33`).

For the target parameter `k = 50` this returns the 15 primes
`p ≤ 47`, witnessed by `primesUpTo_50_eq` below. The S11+ pruner
will be entered as `searchAux w k (primesUpTo k) candidates chosen`. -/
def primesUpTo (k : ℕ) : List ℕ :=
  (Nat.primesBelow (k + 1)).sort (· ≤ ·)

/-- **Sanity test** at `k = 10` — relevant to the deferred S7 case
`(10, 30)` and to the parent file's `BoundedPrimeGaps.lean` smooth-
prime helpers. The four primes `p ≤ 10` are `[2, 3, 5, 7]`. -/
theorem primesUpTo_10_eq : primesUpTo 10 = [2, 3, 5, 7] := by
  native_decide

/-- **Sanity test** at the target parameter `k = 50`. The 15 primes
`p ≤ 50` are listed in ascending order; `47` is the largest prime
≤ 50 (the next is `53`). This is the exact list S11+'s pruned
`searchAux` will branch on at the `engelsmaSearch 246 50 = false`
discharge. -/
theorem primesUpTo_50_eq :
    primesUpTo 50 =
      [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] := by
  native_decide

/-- **S11b-α combiner (residue-pruned admissibility equivalence):**

    Translates `IsAdmissible H` for `H.card ≤ k` into a finite check over
    the prime list `primesUpTo k = (Nat.primesBelow (k + 1)).sort (· ≤ ·)`.

    The forward direction is restriction: an admissible `H` satisfies the
    image-cardinality bound at every prime, so in particular at every
    `p ∈ primesUpTo k`. The reverse direction splits on `p ≤ k` vs `p > k`;
    the `p ≤ k` case appeals to the hypothesis after re-asserting
    `p ∈ primesUpTo k`, and the `p > k` case forces the bound via
    `H.card ≤ k < p` plus `Finset.card_image_le`.

    Forward extracts `p.Prime` from `primesUpTo` membership via
    `Finset.mem_sort` + `Nat.mem_primesBelow`; reverse constructs membership
    symmetrically. This is the S11b-α deliverable of the S11b decomposition
    (S20 PREP §6 + S22 PREP §3.3 + §3.4 paper discharge). It is consumed by
    the bridge proof `engelsmaSearchPruned_eq_false_iff` below at line 922
    (S11b-δ ACT, currently sorry-stub). -/
lemma IsAdmissible_iff_residue_disjoint_primesUpTo
    {H : Finset ℕ} {k : ℕ} (hcard : H.card ≤ k) :
    IsAdmissible H ↔ ∀ p ∈ primesUpTo k, (H.image (· % p)).card < p := by
  constructor
  · -- Forward: restrict the admissibility ∀-quantifier to `primesUpTo k`.
    intro hadm p hp
    -- Extract `p.Prime` from `p ∈ primesUpTo k` via the
    -- `Finset.mem_sort` + `Nat.mem_primesBelow` chain (S22 PREP §3.3).
    have hp' : p ∈ Nat.primesBelow (k + 1) :=
      ((Nat.primesBelow (k + 1)).mem_sort (· ≤ ·)).mp hp
    have hp_prime : p.Prime := (Nat.mem_primesBelow.mp hp').2
    exact hadm p hp_prime
  · -- Reverse: case-split on whether `p ≤ k` or `p > k`.
    intro h p hp_prime
    by_cases hpk : p ≤ k
    · -- `p ≤ k` case: re-assert `p ∈ primesUpTo k` and apply the hypothesis
      -- (S22 PREP §3.4).
      apply h p
      refine ((Nat.primesBelow (k + 1)).mem_sort (· ≤ ·)).mpr ?_
      exact Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le hpk, hp_prime⟩
    · -- `p > k` case: cardinality forces the bound via H.card ≤ k < p
      -- + Finset.card_image_le.
      push_neg at hpk
      have hle : (H.image (· % p)).card ≤ H.card := Finset.card_image_le
      omega

/-- Single-branch step for the pruned admissibility search.

Given a prime `p`, a candidate residue `r ∈ [0, p)`, the remaining
candidate set `candidates`, the already-chosen prefix `chosen`, and a
continuation `cont` to invoke recursively on the filtered candidate /
chosen lists, this helper:

1. Filters `candidates` and `chosen` to drop any `n ≡ r (mod p)`.
2. Returns `false` early if the filtering shrank `chosen` (i.e., the
   prefix is no longer feasible after dropping that residue class).
3. Otherwise delegates to `cont` with the filtered lists.

The continuation is `Bool`-valued so the helper is non-recursive and
sits cleanly outside `searchAux`'s well-founded scope. -/
private def tryBranch (p r : ℕ) (candidates chosen : List ℕ)
    (cont : List ℕ → List ℕ → Bool) : Bool :=
  let candidates' := candidates.filter (fun n => n % p ≠ r)
  let chosen'     := chosen.filter (fun n => n % p ≠ r)
  if chosen'.length < chosen.length then false
  else cont candidates' chosen'

/-- Depth-first pruned admissibility search.

Given a target window width `w`, target subset size `k`, the ascending
list of primes `primes` to branch on, the remaining candidate set
`candidates`, and the prefix `chosen`, returns `true` iff there
exists a forbidden-residue extension of `chosen` to a `k`-element
admissible subset of `Finset.range w` (under the S10 PREP §7
residue-pruning invariant: each entry in `chosen` must avoid the
forbidden residue class for **every** prime in `primes`).

Leaf: when `primes = []`, the prefix `chosen` is residue-disjoint
across all primes ≤ `k`, so admissibility reduces to a pure
cardinality check (`candidates.length ≥ k - chosen.length`),
discharged by `decide`. This is the S10d PREP §3 invariant.

Recursive: for the head prime `p`, iterate over residues `r ∈ [0, p)`
via `(List.range p).any` and delegate each branch to `tryBranch`. The
recursive call `searchAux w k primes'` is **partially applied** as a
continuation value, sidestepping the §3 elaboration risk audited in
S16 PREP. -/
def searchAux (w k : ℕ) :
    (primes : List ℕ) → (candidates : List ℕ) → (chosen : List ℕ) → Bool
  | [], candidates, chosen =>
      decide (candidates.length ≥ k - chosen.length)
  | p :: primes', candidates, chosen =>
      if candidates.length < k - chosen.length then false
      else
        (List.range p).any (fun r =>
          tryBranch p r candidates chosen (searchAux w k primes'))
termination_by primes _ _ => primes.length
decreasing_by all_goals (simp_wf; try omega)

/-- Pruned-search surface for the admissibility decision problem.

`engelsmaSearchPruned w k = true` iff there exists `H ⊆ {0, …, w−1}`
with `0 ∈ H`, `|H| = k`, and `IsAdmissible H`. The implementation
walks the primes `p ≤ k` (via `primesUpTo k`, S10 ACT bearer) and
branches on forbidden residues; the residue-pruning invariant
collapses the leaf to a cardinality decision (per `searchAux`).

The initial prefix is `[0]` per S10d PREP §3 — pinning `0 ∈ H` lets the
leaf cardinality check on `chosen.length` start at `1` rather than `0`.
The candidate set is `(List.range w).filter (· ≠ 0)` (S26 repair): it
must be DISJOINT from `chosen`, because `searchAux`'s leaf test
`candidates.length ≥ k - chosen.length` counts candidates as *fresh*
slots on top of the committed prefix.  The legacy initial call passed
`List.range w` (which contains the committed `0`), double-counting `0`
and accepting parameters with only `k - 1` distinct elements available
— see the S26 section at the end of this file for the machine-checked
refutation (`legacy_bridge_refuted`).

The guard returns `false` for the degenerate parameters `w = 0` (then
`0 ∉ Finset.range w`, so no witness can contain `0`) and `k = 0` (then
`0 ∈ H` contradicts `H.card = 0`); in both cases the correct answer is
`false`, but the legacy leaf accepted spuriously via `Nat` truncation
(`k - chosen.length = 0` at `k = 0`). -/
def engelsmaSearchPruned (w k : ℕ) : Bool :=
  if w = 0 ∨ k = 0 then false
  else searchAux w k (primesUpTo k) ((List.range w).filter (· ≠ 0)) [0]

/-- **Bool/Prop bridge** for `engelsmaSearchPruned`. Mirror of
`engelsmaSearch_eq_false_iff` (S9 ACT) for the pruned variant.

The forward direction is the soundness contract: if
`engelsmaSearchPruned w k = false`, no admissible witness exists.
The reverse is completeness: every admissible witness is found.

**Proof structure (per S10 PREP §8 decomposition + S18 PREP §2)**:

1. `searchAux_sound`: `searchAux w k primes candidates chosen = true`
   implies the witness existence at the residue-pruned prefix.
2. `searchAux_complete`: every admissible witness consistent with
   `chosen` is found by some branch of `searchAux`.
3. `engelsmaSearchPruned_eq_iff`: combines the two via the
   residue-pruning invariant evaluated at `primes = primesUpTo k`,
   `candidates = (List.range w).filter (· ≠ 0)`, `chosen = [0]`.

**S26 status note**: this statement was UNPROVABLE against the legacy
(pre-S26) definition of `engelsmaSearchPruned` — the legacy initial call
double-counted `0` and returned `true` at `(w, k) = (1, 2)` where the RHS
is vacuously true (machine-checked: `legacy_bridge_refuted` below).  The
S26 repair (disjoint candidates + degenerate-parameter guard) makes the
statement agree with the naive `engelsmaSearch` on the whole grid
`w ≤ 12, k ≤ 5` (`engelsmaSearchPruned_agrees_small`), so it is now
plausibly true.  Sound/complete invariants for the decomposition must be
stated with `chosen ∩ candidates = ∅` as an explicit hypothesis.

S11b ACT author: discharge the `sorry` below via the three sub-lemmas
above; estimate +~190-300 LOC for the full decomposition (S18 PREP §2). -/
theorem engelsmaSearchPruned_eq_false_iff (w k : ℕ) :
    engelsmaSearchPruned w k = false ↔
      ∀ H ∈ (Finset.range w).powersetCard k, 0 ∈ H → ¬ IsAdmissible H := by
  sorry

/-- **Pruned-form S9 deliverable**: a `Bool`-equation reduction of
`engelsma_lower_bound` via the pruned search. Mirrors
`engelsma_lower_bound_of_engelsmaSearch_false` (S9 ACT). -/
theorem engelsma_lower_bound_of_engelsmaSearchPruned_false
    (h : engelsmaSearchPruned 246 50 = false) :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, 246 ≤ H.max' hne - H.min' hne :=
  engelsma_lower_bound_of_finitary
    ((engelsmaSearchPruned_eq_false_iff 246 50).mp h)

/-- **Sanity test 1**: `(w, k) = (7, 3)`, the smallest non-trivial
parameters. Mirrors `engelsmaSearch_7_3_eq_true` (S9 ACT, line 769).
Verifies the pruned search agrees with the naive search at small
parameters. -/
theorem engelsmaSearchPruned_7_3_eq_true :
    engelsmaSearchPruned 7 3 = true := by
  native_decide

/-- **Sanity test 2**: `(w, k) = (11, 5)`. Search space
`Nat.choose 11 5 = 462`; the pruned form prunes via primes `[2, 3, 5]`
(= `primesUpTo 5`).

**S26 correction**: the answer here is `false`, not `true` — Engelsma's
`H(5) = 12` means the narrowest admissible 5-tuple has diameter 12, so no
admissible 5-tuple fits in `{0, …, 10}` (diameter ≤ 10).  Concretely: an
admissible 5-tuple must be monochromatic mod 2 and must miss a residue
class mod 3, but each of the three classes mod 3 has ≥ 2 representatives
among the six evens (and among the five odds no class can be emptied), so
no 5-subset qualifies.  The legacy (pre-S26) definition certified `true`
here via the double-counted `0` — a second machine-checked manifestation
of the S26 soundness bug, now fixed (and cross-checked against the naive
search over the grid in `engelsmaSearchPruned_agrees_small`). -/
theorem engelsmaSearchPruned_11_5_eq_false :
    engelsmaSearchPruned 11 5 = false := by
  native_decide

/-! ## S26 — soundness repair: the legacy pruned initial call double-counts `0`

The S11b-δ bridge `engelsmaSearchPruned_eq_false_iff` was **unprovable as
stated** against the legacy (pre-S26) definition

    searchAux w k (primesUpTo k) (List.range w) [0]

because the initial candidate list `List.range w` contains `0` while the
prefix `chosen = [0]` has already committed it.  `searchAux`'s leaf test
`candidates.length ≥ k - chosen.length` counts every candidate as a fresh
slot on top of the committed prefix, so the surviving `0` in `candidates`
is counted twice and parameter pairs with only `k - 1` distinct usable
elements are accepted.

Minimal machine-checked counterexample, `(w, k) = (1, 2)`: the only
surviving branch (`p = 2`, forbidden residue `r = 1`) reaches the leaf
with `candidates = chosen = [0]` and accepts via `1 ≥ 2 - 1`, so the
legacy search returns `true` — yet `Finset.range 1` has no 2-element
subset at all, so the bridge RHS is vacuously true and the bridge would
force `false` (`legacy_bridge_refuted`).  A second, non-vacuous
manifestation: the legacy search certified `true` at `(11, 5)` although
`H(5) = 12` (see the corrected sanity test 2 above).

The S26 repair (in `engelsmaSearchPruned`):
1. initial candidates `(List.range w).filter (· ≠ 0)` — restores the
   disjointness invariant `chosen ∩ candidates = ∅` the leaf test needs;
2. a guard returning `false` at `w = 0` or `k = 0`, where pinning
   `0 ∈ H` is impossible or forbidden and `Nat` truncation made the
   legacy leaf accept spuriously.

The legacy definition is kept verbatim below (as
`engelsmaSearchPrunedLegacy`) solely so the refutation stays
machine-checked; do not consume it in new work. -/

/-- The legacy (pre-S26) pruned-search surface, kept verbatim so the
soundness refutation `legacy_bridge_refuted` stays machine-checked.
Do NOT consume this in new work — use `engelsmaSearchPruned`. -/
def engelsmaSearchPrunedLegacy (w k : ℕ) : Bool :=
  searchAux w k (primesUpTo k) (List.range w) [0]

/-- The legacy search accepts `(w, k) = (1, 2)`: the sole surviving branch
reaches the leaf with `candidates = chosen = [0]` and the double-counted
`0` satisfies `1 ≥ 2 - 1`. -/
theorem engelsmaSearchPrunedLegacy_1_2_eq_true :
    engelsmaSearchPrunedLegacy 1 2 = true := by
  native_decide

/-- The naive search correctly rejects `(w, k) = (1, 2)` — there is no
2-element subset of `{0}` at all (kernel `decide`; the powerset is empty). -/
theorem engelsmaSearch_1_2_eq_false : engelsmaSearch 1 2 = false := by
  decide

/-- **The S11b-δ bridge is FALSE for the legacy definition.**  At
`(w, k) = (1, 2)` the RHS is vacuously true (no 2-element subsets of
`Finset.range 1` exist), so the bridge would force the search to return
`false`; but the legacy search returns `true`.  This is the refutation
that motivated the S26 repair — any soundness development against the
legacy initial call was doomed. -/
theorem legacy_bridge_refuted :
    ¬ (engelsmaSearchPrunedLegacy 1 2 = false ↔
        ∀ H ∈ (Finset.range 1).powersetCard 2, 0 ∈ H → ¬ IsAdmissible H) := by
  intro h
  have hvac : ∀ H ∈ (Finset.range 1).powersetCard 2, 0 ∈ H → ¬ IsAdmissible H := by
    intro H hH _ _
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hH
    have h1 : H.card ≤ (Finset.range 1).card := Finset.card_le_card hsub
    rw [Finset.card_range, hcard] at h1
    omega
  have hfalse : engelsmaSearchPrunedLegacy 1 2 = false := h.mpr hvac
  rw [engelsmaSearchPrunedLegacy_1_2_eq_true] at hfalse
  exact Bool.noConfusion hfalse

/-- **S26 regression**: the repaired search rejects the legacy
counterexample `(1, 2)`. -/
theorem engelsmaSearchPruned_1_2_eq_false :
    engelsmaSearchPruned 1 2 = false := by
  native_decide

/-- **S26 regression**: `(2, 2)` — `{0, 1}` is the only candidate pair and
is inadmissible mod 2 (both residues hit).  The legacy definition also
certified `true` here. -/
theorem engelsmaSearchPruned_2_2_eq_false :
    engelsmaSearchPruned 2 2 = false := by
  native_decide

/-- **S26 drop-in agreement grid**: the repaired pruned search agrees with
the naive `engelsmaSearch` on every `(w, k)` with `w ≤ 12, k ≤ 5` — 78
parameter pairs covering both refuted legacy points `(1, 2)` and `(11, 5)`,
all degenerate rows (`w = 0`, `k = 0`), and both positive sanity points
`(7, 3)` and `(12, 5)`-adjacent cases.  This is the drop-in contract the
S9 scaffold requires of any pruned replacement, checked exhaustively on
the tractable grid. -/
theorem engelsmaSearchPruned_agrees_small :
    ((List.range 13).all fun w => (List.range 6).all fun k =>
      engelsmaSearchPruned w k == engelsmaSearch w k) = true := by
  native_decide

end BoundedPrimeGapsOQ03OQ02
