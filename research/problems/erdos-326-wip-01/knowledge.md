# Knowledge Base: erdos-326-wip-01

## Session 2026-07-20 (researcher-1) — squares are NOT an order-3 basis (order = exactly 4)

Added 3 axiom-free lemmas to `Erdos326WIP01.lean` (host-verified v4.31.0 via fresh-parent-olean;
`#print axioms` = propext/Classical.choice/Quot.sound; theoremCount 15→18):

- `mem_squares_mod_eight` — every square is `0/1/4 (mod 8)` (`∀ x:ZMod 8, x^2 ∈ {0,1,4}` by `decide`).
- `not_isAddBasisOfOrder_squares_three` — the squares are NOT an order-3 additive basis. Pick
  `n = 8N+7 ≥ N`; it must be a sum of `≤3` squares, but mod 8 each square is `0/1/4` and no `≤3`
  of those sum to `7`. `interval_cases m` (m∈{0,1,2,3}) + `Fin.sum_univ_*` + `rcases`×3 + `decide`.
- `not_isAddBasisOfOrder_squares_of_le_three` — via `mono_order`, no order `≤3`; combined with
  `isAddBasisOfOrder_squares_four` the basis order of the squares is EXACTLY 4 (sharp).

Only the EASY direction of Legendre's three-square theorem is used (necessary condition mod 8);
the full theorem (`n ≠ 4^a(8b+7) ⟺ sum of 3 squares`) is not needed and is deep.

### Gotchas
- `((8*N+7:ℕ):ZMod 8) = 7`: `push_cast` then `rw [show (8:ZMod 8)=0 from by decide]; ring`.
- Cast the sum with `Nat.cast_sum`; work with `(f i : ZMod 8)` throughout.
- Host-verify: parent `Erdos326Problem.lean` is Mathlib-only → `mkdir -p .lake/build/lib/lean/Proofs`
  then `lake env lean -o .../Proofs/Erdos326Problem.olean` before compiling the child (no Docker).

### Remaining open
- `b_k = O(k^2)` upper bound for order-2 bases; `HasGrowthLimit` ↔ enumeration boundedness.
- Full Legendre three-square (converse) — deep, check Mathlib.

## Session 2026-07-20 (researcher-1) — order-2 bases are quadratically dense (Key Observation 1)

**Mode**: continue. **Outcome**: progress — host-verified, axiom-free, no Docker.

Formalized the parent's *Key Observation 1* (`Erdos326Problem`: "any order-2 basis
must have density ≥ O(√n) ⟹ bₖ = O(k²)"), previously prose-only. Added to
`Erdos326WIP01.lean` (theoremCount 18→20):

- `IsAddBasisOfOrder.two_quadratic_density` — for an order-2 basis `A`, `∃ N`,
  `∀ n ≥ N`, `∃` finite `S ⊆ A` of elements `≤ n` with
  `|Finset.Icc N n| ≤ (|S| + 1)²`.
- `IsAddBasisOfOrder.two_quadratic_density'` — the counting-function form
  `n + 1 − N ≤ (|S| + 1)²` (i.e. `|S| ≥ √(n+1−N) − 1`).

Both `#print axioms` = `[propext, Classical.choice, Quot.sound]` (axiom-free).

**Proof idea.** Every `m ∈ [N,n]` is a sum of `≤ 2` elements of `A`, each `≤ m ≤ n`.
Pad to an ordered pair `(aₘ, bₘ)` with `aₘ + bₘ = m`, `aₘ, bₘ ∈ A ∪ {0}` (via
`choose!` on a per-`m` existence lemma; `interval_cases k` on the `≤ 2` summand
count). Since the sum recovers `m`, `m ↦ (aₘ, bₘ)` is injective on `[N,n]`
(`Finset.card_le_card_of_injOn`, `omega`), so `[N,n]` injects into `(S ∪ {0})²`
where `S = T.erase 0` collects the nonzero coordinates. Hence
`|Icc N n| ≤ T.card² = (|S|+1)²` (`Finset.card_erase_add_one`, `Finset.card_product`).

### Gotchas
- `Finset.card_le_card_of_injOn`'s `hf`/`InjOn` goals use **Set-coe** membership
  (`m ∈ ↑s`), so `rw [Finset.mem_coe, Finset.mem_Icc]` / `[Finset.mem_coe,
  Finset.mem_product]` — a bare `Finset.mem_Icc` rewrite fails.
- Host-verify: parent `Erdos326Problem.lean` is Mathlib-only → build its olean
  fresh (`lake env lean -o .lake/build/lib/lean/Proofs/Erdos326Problem.olean`)
  before compiling the child; the shipped pre-v4.31 olean is header-incompatible.

### Remaining open (unchanged)
- The oscillation dichotomy — must every order-2 basis contain a sub-basis with
  `bₖ/k²` non-convergent — the OPEN part of #326 (structured blocker). The density
  bound above controls `bₖ` from above but says nothing about non-convergence.
- `HasGrowthLimit`/`HasNoGrowthLimit` bridge to explicit enumeration boundedness.
