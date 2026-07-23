# Knowledge Base: erdos-70-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session (researcher-1, 2026-07-20) — countable-ordinal closure + conjecture specializations (axiom-free)

Created `proofs/Proofs/Erdos70WIP01.lean` (5 theorems, 0 sorry, 0 axiom;
host-verified `bin/lake env lean` exit 0, `#print axioms` = `[propext,
Classical.choice, Quot.sound]` on all). Generalizes the parent's specific
countability facts and connects the open conjecture to its special cases.

- `IsCountableOrdinal.of_le` — downward closure (`Ordinal.card_le_card`).
- `isCountableOrdinal_add` — closed under `+` (`Ordinal.card_add`,
  `Cardinal.add_le_aleph0`).
- `isCountableOrdinal_mul` — closed under `*` (`Ordinal.card_mul`, `mul_le_mul'`,
  `Cardinal.aleph0_mul_aleph0`).
- `erdos_70_conjecture_imp_omega` / `_imp_omega_squared` — specialize the open
  conjecture to `conjecture_omega` / `conjecture_omega_squared` via the parent
  witnesses `omega0_countable` / `omega0_squared_countable`.

### Verification
Parent `Erdos70Problem.lean` fresh-built to olean host-side (Mathlib-only, v4.31,
docker-free), child compiled against it. Exit 0.

### Next Steps
- `isCountableOrdinal_opow` for `ω^ω` (`conjecture_omega_tower` witness) — needs
  the `Ordinal.card` behaviour of `opow`, less directly available in Mathlib.
- Derive `omega0_plus_n_countable` / `omega0_squared_countable` as one-line
  corollaries of the new closure lemmas (dedup the parent).

---

## Session 2026-07-20 (researcher-1): closure toolkit + conjecture specializations

Batch 2 of axiom-free lemmas in `Proofs/Erdos70Problem.lean` (theorem count
9 → 18, still 0 axioms, 0 sorries). Host-verified with `lake env lean` (imports
`Mathlib`); `#print axioms` on all six new theorems yields only
`[propext, Classical.choice, Quot.sound]`.

- **Countability closure toolkit**: `zero_countable`, `one_countable`,
  `IsCountableOrdinal.mono` (β ≤ α), `IsCountableOrdinal.add`,
  `IsCountableOrdinal.mul`. The existing `omega0_plus_n_countable` /
  `omega0_squared_countable` are now instances of this general principle
  (`Ordinal.card_add/_mul` + `Cardinal.aleph0_add_aleph0/_mul_aleph0`).
- **Conjecture ⇒ specialization theorems**: `erdos_70_conjecture_omega`,
  `erdos_70_conjecture_omega_squared` derive the β=ω and β=ω·ω named cases
  (previously only `def`s) from `erdos_70_conjecture` via countability of the
  ordinal + `2 ≤ n`.
- **PartitionArrow boundary cases**: `partition_arrow_ordinal_zero` (α=0, empty
  set vacuously homogeneous with order type ≥ 0) and `partition_arrow_size_zero`
  (m=0, empty finset).

### Next targets
- Countability of `ω^ω` (`Ordinal.omega0 ^ Ordinal.omega0`), referenced by
  `conjecture_omega_tower` but not yet proven countable — needs a countable-sup
  argument (no direct `Ordinal.card_opow` in Mathlib), left as follow-up.
- Erdős Problem 70 itself (general countable β) is OPEN; the Erdős–Rado positive
  result 𝔠 → (ω+n, 4)₂³ needs partition-calculus machinery absent from Mathlib.

## Session 2026-07-20 (researcher-1): closure under finite exponentiation

Added 2 axiom-free theorems to `Proofs/Erdos70WIP01.lean` (theoremCount 5→7,
0 axioms, 0 sorries; `#print axioms` = propext/Classical.choice/Quot.sound only,
host-verified via parent-olean + `lake env lean`):

- **`isCountableOrdinal_opow_nat`** — the countable ordinals are closed under
  exponentiation by a natural number: `IsCountableOrdinal α → IsCountableOrdinal (α ^ (n:ℕ))`.
  Induction on `n`: base `α^0 = 1` (`one_countable`); step `α^(n+1) = α^n · α`
  via `Ordinal.opow_add`/`opow_one`, countable by `IsCountableOrdinal.mul`.
- **`omega0_opow_nat_countable`** — every finite power `ω^n` is countable,
  generalizing the parent's `omega0_squared_countable` (`ω·ω = ω^2`).

### Gotcha
`Ordinal.opow_succ` is stated as `a ^ Order.succ b`, so `rw [Ordinal.opow_succ]`
fails against a `α ^ (↑n + 1)` goal. Route the successor step through
`Nat.cast_add, Nat.cast_one, Ordinal.opow_add, Ordinal.opow_one` instead.

### Next target
Countability of the limit power `ω ^ ω` (`Ordinal.omega0 ^ Ordinal.omega0`),
referenced by `conjecture_omega_tower` — needs a countable-sup argument
(`ω^ω = ⨆ n, ω^n`); no direct `Ordinal.card_opow` exists in Mathlib v4.31.

## Session 2026-07-20 (researcher-1, session 3): ω^ω countable — the limit-exponent step

Picked up the session-1 "Next Steps" flag (`isCountableOrdinal_opow` for `ω^ω`). The
finite-power closure `isCountableOrdinal_opow_nat` handles `ω^n` (n:ℕ) but not the
*limit* exponent `ω^ω`. Added 3 axiom-free theorems to `Proofs/Erdos70WIP01.lean`
(host-verified: parent `Erdos70Problem.lean` fresh-built to olean, child `lake env lean`
exit 0; `#print axioms` = `[propext, Classical.choice, Quot.sound]` on all three).

- **`isCountableOrdinal_iff_lt_omega_one`** — bridge `IsCountableOrdinal α ↔ α < ω₁`
  (`card α ≤ ℵ₀ ↔ α < ω₁`), via `Cardinal.lt_omega_iff_card_lt` (`x < ω_ o ↔ x.card < ℵ_ o`)
  and `Cardinal.lt_aleph_one_iff` (`c < ℵ₁ ↔ c ≤ ℵ₀`).

- **`omega0_opow_omega0_countable`** — `ω^ω` is countable. Since `ω` is a successor-limit,
  `Ordinal.opow_le_of_isSuccLimit` gives `ω^ω ≤ c ↔ ∀ β<ω, ω^β ≤ c`; each `β<ω` is a finite
  `k` (`Ordinal.lt_omega0`), so `ω^β = ω^k ≤ ⨆ n:ℕ, ω^n` (`Ordinal.le_iSup`). That ℕ-indexed
  supremum of the countable ordinals `ω^n` (`omega0_opow_nat_countable`) is `< ω₁` by
  **`Ordinal.iSup_lt_omega_one`** (a countable sup of countable ordinals is countable —
  regularity of ℵ₁). Hence `ω^ω ≤ (⨆ n, ω^n) < ω₁`, so `ω^ω` is countable.

- **`erdos_70_conjecture_imp_omega_tower`** — specializes the open conjecture to
  `conjecture_omega_tower` (β=ω^ω), completing the ω / ω² / ω^ω trio of flagship cases.

### Gotcha
Universe must be pinned to `Ordinal.{0}` (write `Ordinal.omega0.{0}`) so the theorem
matches the parent's `conjecture_omega_tower`, which lives in `Ordinal.{0}`. Without the
pin the auto-generalized universe metavariable clashes (`LE.le.{u_1+1}` vs `.{1}`).
Also `Cardinal.lt_omega_iff_card_lt` is in the **`Cardinal`** namespace (not `Ordinal`).

### Next Steps
- General closure `isCountableOrdinal_opow` (α, β countable ⟹ α^β countable) by transfinite
  induction on β using `opow_limit` + `iSup_lt_omega_one` at each limit stage.
- Towers `ω^(ω^ω)` etc. up to `ε₀`; all countable, each a `le_iSup`-over-ℕ argument.

## Session 2026-07-21 (researcher-1): general closure under ordinal exponentiation

Extended `Proofs/Erdos70WIP01.lean` with the **general** exponentiation-closure
theorem (theoremCount 10→13, still 0 axioms, 0 sorries; host-verified: fresh
parent olean + `lake env lean`, `#print axioms` = propext/Classical.choice/Quot.sound).

- **`isCountableOrdinal_opow {α β} (hα : IsCountableOrdinal α) : IsCountableOrdinal β →
  IsCountableOrdinal (α ^ β)`** — the capstone the prior sessions were building toward.
  Subsumes both `isCountableOrdinal_opow_nat` (only `ω^n`, n:ℕ) and the bespoke
  `omega0_opow_omega0_countable` (only `ω^ω`). Transfinite induction on the exponent
  (`Ordinal.limitRecOn`):
  - `β=0`: `α^0=1` (`one_countable`).
  - `β=o+1`: `α^(o+1)=α^o·α` (`opow_add_one`), mul-closure.
  - `β` succ-limit, `α≠0`: `α^β = ⨆_{x:Iio β} α^x` (`opow_limit`); `Iio β` is a
    *countable* index type (`Cardinal.mk_Iio_ordinal` + `Cardinal.lift_le_aleph0`),
    each `α^x` countable by IH, so `⨆ < ω₁` via `Ordinal.iSup_lt_omega_one`
    (regularity of ℵ₁). `α=0`: `0^β=0` (`zero_opow`, limit exponent ≠ 0).
- **`omega0_opow_omega0_opow_omega0_countable`** — `ω^(ω^ω)` (2nd tower level),
  now a two-line corollary `isCountableOrdinal_opow omega0_countable (isCountableOrdinal_opow …)`.
- **`erdos_70_conjecture_imp_omega_tower_two`** — conjecture specialized to `β = ω^(ω^ω)`.

### Consequence
The whole exponential tower `ω, ω^ω, ω^(ω^ω), …` below `ε₀` is countable, and the
countable-ordinal class is now proved closed under all three ordinal operations
(`+`, `·`, `^`). Every further tower level is a one-liner.

### Gotchas (v4.31)
- `limitRecOn`'s successor case is stated with `o + 1` (not `Order.succ o`), so use
  `Ordinal.opow_add_one` (`a^(b+1)=a^b*a`) and `self_le_add_right o 1` for `o ≤ o+1`.
- `opow_limit` indexes the sup by `Set.Iio b` (a subtype in `Type 1` for `Ordinal.{0}`);
  `Cardinal.mk_Iio_ordinal` gives `#(Iio b) = lift b.card`, and `Cardinal.lift_le_aleph0`
  clears the universe lift so `Countable (Iio b)` follows from `IsCountableOrdinal b`.
- `IsSuccLimit.ne_bot` gives `o ≠ ⊥`; convert to `o ≠ 0` via `Ordinal.bot_eq_zero`.

### Frontier (UNCHANGED)
Erdős #70 itself (positive partition relation for general countable β) remains OPEN —
the Erdős–Rado result `𝔠 → (ω+n, 4)₂³` needs partition-calculus machinery absent from
Mathlib v4.31. The ordinal-arithmetic countability toolkit is now complete.

## Session 2026-07-21 (researcher-1): reduction to infinite Ramsey (the converse direction)

Every prior session ran `erdos_70_conjecture → special case β` (assume the
conjecture, specialize the exponent up to ε₀). This session adds the **converse
ingredient direction**: isolates the single fact that would prove the whole
formalized conjecture uniformly in β, and proves the reduction. Added to
`Proofs/Erdos70WIP01.lean` (theoremCount 16→18 incl. 1 new `def`; still 0 axioms,
0 sorries; host-verified fresh-parent-olean + `lake env lean` exit 0; `#print axioms`
= `[propext, Classical.choice, Quot.sound]` on both new theorems).

- **`InfiniteRamsey3` (def)** — the infinite Ramsey theorem for 2-colourings of
  3-element subsets of a continuum-sized `S`: some colour class has an *infinite*
  homogeneous set. Classical, but **absent from Mathlib v4.31** (no infinite
  Ramsey / hypergraph-partition dev; `Mathlib.Combinatorics` stops at
  Hales–Jewett, Hindman, finite pigeonhole). Carried as a named hypothesis, NOT
  an `axiom`, so the reduction stays assumption-free.
- **`infiniteRamsey3_imp_conjecture`** — `InfiniteRamsey3 → erdos_70_conjecture`,
  uniformly in every countable β and 2 ≤ n. Colour 0: the infinite homogeneous
  set meets the (cardinality-surrogate) order-type side via `β.card ≤ ℵ₀ ≤ #H`
  (`Cardinal.aleph0_le_mk_iff` + `Set.infinite_coe_iff`). Colour 1: any n-subset
  (`Set.Infinite.exists_subset_card_eq`) meets the size side, homogeneous because
  subsets of an `IsHomogeneous` set are homogeneous.
- **`counterexample_imp_not_infiniteRamsey3`** — contrapositive packaging via the
  parent's `conjecture_xor_counterexample`.

### KEY FAITHFULNESS FINDING (auditor-relevant)
The parent's `HasOrderTypeAtLeast S H α := α.card ≤ #H` is the **cardinality
surrogate** (parent labels it a "simplified version"), so the colour-0 disjunct
is satisfied by ANY set of cardinality ≥ ℵ₀. Under this surrogate the *formalized*
`erdos_70_conjecture` is **strictly weaker** than the genuine order-type partition
relation `𝔠 → (β, n)₂³` of Erdős #70, and is in fact a **theorem modulo infinite
Ramsey** (this reduction proves it). The genuine open content of Erdős #70 lives
entirely in the gap between the cardinality surrogate and TRUE order type β — a
homogeneous set of size ℵ₀ need not have order type ω², ω^ω, …. The tower-closure
development (ω…ε₀) specializes the *surrogate* statement only.

### Next Steps
- To formalize the REAL problem, strengthen `HasOrderTypeAtLeast` to genuine order
  type (there is a well-order on H of type ≥ α), then the reduction breaks and the
  true partition calculus (Erdős–Rado) is required — genuinely open/blocked.
- Building `InfiniteRamsey3` itself (infinite Ramsey for 3-uniform 2-colourings)
  from Mathlib's infinite pigeonhole is a self-contained ~200–400 line project
  and would discharge the surrogate conjecture outright. Blocked route until then.

## Session 2026-07-22 (researcher-1): InfiniteRamsey3 PROVED — surrogate conjecture is a theorem

**Mode**: BUILD (the "self-contained ~200–400 line project" flagged last session; landed at ~370 lines, 0 axioms, 0 sorries.)

### What was proved (all in `Erdos70WIP01.lean`, final section `RamseyProof`)
- **`majColor` / `majColor_mem`** — the `U`-majority colour of an `ℕ → Fin 2`
  function, attained on a `U`-large set, `U := Filter.hyperfilter ℕ` (the
  ultrafilter extending cofinite; `Ultrafilter.compl_mem_iff_notMem` + a
  `decide` over `Fin 2` handle the else-branch).
- **Iterated majorities** `pairMaj` / `pointMaj` / `topMaj` — the classical
  ultrafilter limit colours of a triple colouring, three levels deep.
- **`goodSet` / `goodSet_mem`** — the set of viable next elements after a finite
  prefix `L`; each clause is `U`-large given the invariant, via
  `list_forall_large` (finite-intersection helper by list induction) and
  `Nat.hyperfilter_le_atTop` for the tail clause.
- **`ramseyPrefix` / `ramseySeq` / `ramsey_invariant`** — the recursion-with-
  invariant pattern WITHOUT dependent-choice plumbing: define the sequence
  totally by structural recursion with `sInf`, then prove by induction that each
  term lies in its good set (`Nat.sInf_mem` + `Ultrafilter.nonempty_of_mem`).
- **`ramsey3_nat`** — infinite Ramsey for 2-colourings of 3-subsets of `ℕ`:
  the range of `ramseySeq` is infinite and homogeneous with colour `topMaj`.
- **`infiniteRamsey3_holds`** — transfer to any continuum-sized `S` via
  `Infinite.natEmbedding` (pull the colouring back along `Finset.map`, push the
  homogeneous set forward).
- **`erdos_70_formalized_conjecture_holds`** — `erdos_70_conjecture` is now an
  UNCONDITIONAL theorem via last session's reduction; also
  `no_erdos_70_counterexample`, `conjecture_omega_holds`,
  `conjecture_omega_squared_holds`, `epsilon0_partitionArrow_holds`.

### Key technique notes (reusable)
- Ordering every good-set clause smaller-point-first (`b < a → tripleColor b a m`)
  means NO symmetry lemmas for the unordered triple colour are ever needed — the
  final homogeneity argument sorts the 3-subset (`exists_sorted_triple`, 6-case
  `lt_of_le_of_ne` + `ext/simp/tauto`) and `StrictMono.lt_iff_lt` transports the
  value order back to index order.
- `tripleColor` totalizes the subtype colouring with junk value 0 for collided
  points; `tripleColor_eval` (via `dif_pos`) is the only bridge ever needed.

### Standing caveat (unchanged, auditor-relevant)
`HasOrderTypeAtLeast` is the parent's cardinality surrogate; the now-proved
`erdos_70_conjecture` is strictly weaker than genuine Erdős #70 (true order
type), which REMAINS OPEN and is the sole content of the remaining blocked route.

## Session 2026-07-23 (researcher-1) — faithful order-type arrow at β = ω

The prior session's optional follow-up ("faithful order-type arrow for β = ω —
provable from InfiniteRamsey3 since any infinite subset of a well-ordered set
contains an ω-chain") is DONE in new file `Erdos70WIP01Faithful.lean` (6 decls,
0 ax, 0 sorry). Key content and Lean specifics:

- **Key fact** `omega0_le_type_subrel_of_infinite {S} (r) [IsWellOrder S r]
  {H : Set S} (hH : H.Infinite) : ω ≤ type (Subrel r (· ∈ H))`. Proof: by_contra
  + `Ordinal.lt_omega0` gives type = n; `congrArg Ordinal.card` +
  `Ordinal.card_type` + `Ordinal.card_nat` force #↥H = n < ℵ₀ vs
  `Cardinal.aleph0_le_mk_iff.mpr (Set.infinite_coe_iff.mpr hH)`.
  Defeq note: `Set.Elem H` vs `Subtype (· ∈ H)` mismatches are handled by
  `have h' : mk ↥H = (n : Cardinal) := hcard` (exact accepts defeq; rw does not).
- `FaithfulArrowOmega κ m` quantifies over ALL well-orderings r of S
  ([IsWellOrder S r] instance gives `IsWellOrder _ (Subrel r p)` automatically,
  Mathlib Order/RelIso/Set.lean:115).
- Unconditional at 𝔠: `faithful_omega_arrow_holds` via `infiniteRamsey3_holds`.
- **Equivalence at ω**: `faithfulArrowOmega_iff_partitionArrow_omega` — the
  cardinality surrogate (`HasOrderTypeAtLeast = card ≤`) loses NOTHING at β = ω.
  Forward: well-order the bare S by `WellOrderingRel` (instance
  `WellOrderingRel.isWellOrder`, Mathlib SetTheory/Cardinal/Order.lean:542);
  `Ordinal.card_le_card` + `card_omega0` recover ℵ₀ ≤ #H. Backward: the key fact.
  This CERTIFIES the WIP file's `erdos_70_formalized_conjecture_holds` is
  faithful at its ω instance; divergence begins at ω² (ω-type subset of ω² is
  infinite with suborder type only ω).

Remaining (unchanged): genuine arrow for β ≥ ω² through ε₀ needs Erdős–Rado
order-type-preserving homogeneous-set machinery (structured blocker); the true
Erdős #70 remains open. No further elementary rungs visible on this node.
