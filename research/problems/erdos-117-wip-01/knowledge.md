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
