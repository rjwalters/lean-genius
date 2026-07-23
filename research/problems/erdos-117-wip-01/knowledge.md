# Knowledge Base: erdos-117-wip-01

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

## Session 2026-07-20 (researcher-1) — n-commuting foundations for the def-only stub

**Mode**: FRESH (knowledge score 0). **Outcome**: progress — 7 axiom-free lemmas,
**host-verified v4.31** (`lake env lean`, exit 0; `#print axioms` spot-check clean).

Erdős Problem 117 (OPEN): `h(n)` = min # abelian subgroups covering any group whose
every size-`>n` subset has a commuting pair; `h(n)` is exponential (Pyber 1987).
`Erdos117Problem.lean` held only `HasNCommutingProperty`, `IsAbelianSubgroup`,
`abelianCoverNumber`. Added:

- **commute_of_hasNCommutingProperty_one** (headline) — `HasNCommutingProperty G 1`
  ⇒ every pair commutes. For distinct `x,y`, the subset `{x,y}` has card `2 > 1`, so its
  only distinct pair must commute; a 4-way `rcases` on membership closes it. This
  formalises the file's "Trivial Case n = 1 ⇒ G Abelian, h(1)=1" note.
- **hasNCommutingProperty_mono** — monotone in `n` (larger threshold = weaker):
  `n ≤ m` and the `n`-property give the `m`-property via `lt_of_le_of_lt`.
- **commGroup_hasNCommutingProperty_one** — abelian ⇒ 1-commuting (`Finset.one_lt_card`).
- **isAbelianSubgroup_bot / _top_of_commGroup / _mono** — closure of the abelian-subgroup
  predicate (trivial subgroup; whole group when abelian; downward under `≤`).
- **isAbelianSubgroup_iff_isMulCommutative** — the local `IsAbelianSubgroup G H` predicate
  is equivalent to Mathlib's `IsMulCommutative H`.

### v4.31 gotchas
- `Subgroup.IsCommutative` and `mul_comm_of_mem_isCommutative` are GONE. Use the class
  `IsMulCommutative H` (field `is_comm : Std.Commutative (·*·)`), the helper
  `isMulCommutative_iff`, and `setLike_mul_comm (ha : a∈H) (hb : b∈H)` (needs the instance
  in scope — `haveI := h`).
- `Finset.card_pair (h : a ≠ b) : ({a,b}).card = 2`; construction of `{x,y}` needs
  `DecidableEq G`, obtained via `classical`.

### Still open
`abelianCoverNumber` / `h(n)` and Pyber's exponential bounds `c₁^n < h(n) < c₂^n` (exact
base open) are deep and unformalized — this session builds only elementary scaffolding.

---

## Session 2026-07-22 (researcher-1-3) — h(1)=1 + n-commuting foundations (0-axiom)

**Mode**: FRESH (WEAK → ACT) · **Outcome**: progress — formalized the elementary
base-case facts the parent `Erdos117Problem.lean` left in prose, as 3 axiom-free
theorems in a new companion `proofs/Proofs/Erdos117WIP01.lean` (Docker-verified
v4.31.0; `#print axioms` on all three = `[propext, Classical.choice, Quot.sound]`).

- `not_hasNCommutingProperty_zero` — no group has the `0`-commuting property (the
  singleton `{1}` has card `1 > 0` but no distinct pair). The property is vacuous
  below `n = 1`.
- `commGroup_hasNCommutingProperty {n} (hn : 1 ≤ n)` — every commutative group has
  the `n`-commuting property for all `n ≥ 1` (via `hasNCommutingProperty_mono` on
  the parent's `n = 1` case).
- `abelianCoverNumber_one : abelianCoverNumber 1 = 1` — **the flagship `h(1) = 1`**,
  exactly the trivial case the problem requests. `1 ∈` set via the single abelian
  subgroup `⊤` (the group is abelian by `commute_of_hasNCommutingProperty_one`);
  `0 ∉` set since an empty `Fin 0 → Subgroup PUnit` family can't cover `1`.
  `le_antisymm (Nat.sInf_le …) (Nat.one_le_iff_ne_zero.mpr …)` with
  `Nat.sInf_eq_zero`.

**★GOTCHA (universe)**: `abelianCoverNumber` is **universe-polymorphic** — its body
quantifies `∀ (G : Type*)`, so `abelianCoverNumber.{u} 1`. Membership witnesses
must be built **inline** at the set's fixed universe `u`; a factored
`have hcover : ∀ (G : Type*) …` introduces a **second** universe `u_2` that does
NOT unify with the set's `u_1` (`Application type mismatch` at the `Nat.sInf_le`
site + `constant has level params [u_1, u_2] but expected [u_1]`). `PUnit` is
universe-polymorphic so `PUnit : Type u` supplies the witness group in any `u`.
`push_neg` rewrites `s ≠ ∅` directly to `s.Nonempty` (no `Set.nonempty_iff_ne_empty`).

**STILL OPEN / out of scope**: Pyber's exponential bounds `c₁ⁿ < h(n) < c₂ⁿ`
(deep) and the OPEN exact base of the growth stay unformalized. `h(n)`
well-definedness for general `n` (nonemptiness of the `sInf` argument) needs a
uniform cover bound = the Pyber upper bound, so it is NOT elementary.

## Session 2026-07-23 (researcher-1) — h(3) = 3 EXACT, unconditional (docker-VERIFIED, 8582 jobs; #print axioms = propext/Classical.choice/Quot.sound)

**Mode**: REVISIT. **Outcome**: the "classification-strength" assessment of `h(3) ≤ 3`
(in `Erdos117WIP01Three.lean`'s header) was an OVERESTIMATE — the uniform 3-cover is
elementary. New file `Erdos117WIP01Exact.lean` proves **h(3) = 3**, the first
nontrivial exact value on the Erdős #117 ladder, and discharges the well-definedness
hypothesis (`∃ k, CoversWithAbelian k 3`) that every prior h(3) statement carried.

### The mechanism (no classification, no Pyber, no symplectic forms)
1. **Covering**: a ≁ b ⟹ {a, b, ab} pairwise non-commuting ⟹ every g commutes with
   one of a, b, ab (else {a,b,ab,g} is a forbidden 4-set) ⟹ G = C(a) ∪ C(b) ∪ C(ab).
2. **Centralizers abelian**: u,v ∈ C(a) non-commuting ⟹ case-split on which of
   u, v, uv the witness b commutes with; each of the 5 cases yields an explicit
   pairwise non-commuting 4-set:
   (b~u,b~v) → {au, av, b, a(uv)}; (b~u,¬b~v) → {au, b, v, uv} (+ mirror);
   (¬,¬,b~uv) → {b, u, v, a(uv)}; (¬,¬,¬) → {b, u, v, uv}.
   Distinctness is FREE: non-commuting elements are automatically distinct, so
   `no_four_clique` needs only the 6 edges — this collapsed what looked like a
   distinctness-bookkeeping nightmare.
3. Combined: `CoversWithAbelian 3 3` (works for ALL groups, finiteness unused) ⟹
   `h(3) ≤ 3` via `Nat.sInf_le`; with Q₈'s `three_le_abelianCoverNumber_three`
   (hypothesis now discharged) ⟹ **h(3) = 3**. Ladder exactly: 0, 1, 1, 3, …

### Lean technique notes (v4.31)
- Commutation kit: 7 cancellation micro-lemmas (`comm_mul_of_comm`,
  `comm_ab_of_comm_mul`, `comm_of_mul_mul`, `comm_of_self_mul_left/right`,
  `comm_of_mul_left_right`, `comm_of_left_mul`, `comm_right_of_comm_mul`) — all
  pure `calc` + `mul_assoc` + `mul_left/right_cancel`; each clique edge becomes a
  one-liner `fun h => hX (kit ... h)`.
- `no_four_clique`: Finset `{w,x,y,z}` card-4 via chained
  `Finset.card_insert_of_not_mem` (distinctness derived from non-commutation);
  the 16-way `rcases ... <;> rcases ... <;> first | exact ...` dispatch handles
  both orientations of the commuting pair via `hcomm`/`hcomm.symm`.
- `Subgroup.mem_centralizer_singleton_iff : k ∈ centralizer {g} ↔ k * g = g * k`
  (member on the LEFT) — orientation matters; `.symm` where needed.
- Mirror case (¬b~u, b~v) = apply the (b~u, ¬b~v) lemma with u↔v swapped and
  `fun h => huv h.symm` — no duplicate proof.
- `![C₁, C₂, C₃] i` after `fin_cases i` / `⟨0, show g ∈ …⟩` reduces definitionally;
  `show` makes the defeq explicit and robust.

### Still open / out of scope
- h(4): S₃ has the 4-commuting property (ω(S₃) = 4) and needs 4 abelian subgroups —
  h(4) ≥ 4 is a plausible next rung (needs `not_coversWithAbelian_three` via S₃);
  well-definedness of h(4) (uniform bound for ω ≤ 4 groups) is genuinely harder —
  the centralizer-cover trick gives a cover by 4 CENTRALIZERS of a max clique, but
  their abelianness FAILS in general at ω = 4 (S₃: C((12)) = {e,(12)} abelian ✓, but
  the general argument breaks — the 5-case analysis is specific to ω = 3).
- Pyber's exponential bounds c₁ⁿ < h(n) < c₂ⁿ: DEEP, untouched (the open problem).

## Session 2026-07-23 (researcher-1, session 2) — h(4) rung: budget 3 fails at n >= 4 (S₃ pigeonhole)

**Mode**: REVISIT (executing the "next rung" identified this morning). New file
`Erdos117WIP01Four.lean` (0 ax, 0 sorry, kernel decide only).

- `not_abelian_three_cover_of_four_clique` — GENERIC pigeonhole: four pairwise
  non-commuting elements t₁,t₂,t₃,c defeat any abelian 3-cover (the member holding
  c excludes every tᵢ; three tᵢ into two remaining members collide). Works in any
  group; Fin-3 index pigeonhole via `.val` + `omega` (convert `Fin` ≠ to `.val` ≠
  with `Fin.ext`, feed `isLt` bounds).
- `s3_hasNCommutingProperty_four` — S₃ has the 4-commuting property (`decide`,
  2⁶ subsets, maxRecDepth 8192); `s3_not_hasNCommutingProperty_three` — SHARP:
  the 4-clique {swap 0 1, swap 0 2, swap 1 2, 3-cycle} shows S₃ enters exactly
  at threshold 4.
- `not_coversWithAbelian_three` (n ≥ 4) — ULift transport exactly as Three.lean
  (property along `MulEquiv.ulift.symm`, non-commutation descends via
  `congrArg ULift.down`).
- `four_le_abelianCoverNumber` / `_four` — h(n) ≥ 4 for n ≥ 4 (conditional on
  well-definedness, honest hne hypothesis); `abelianCoverNumber_three_lt_four`
  (h(3)=3 < h(4), conditional); `abelianCoverNumber_four_eq_zero_or_four_le`
  (unconditional dichotomy).

Ladder: **0, 1, 1, 3 (exact), ≥4, …** — strictly increasing again at n = 4.
Well-definedness of h(4) does NOT follow from the ω=3 centralizer trick
(blocked route; reopen = Neumann-type |G:Z| ≤ f(n) or materially new mechanism).
