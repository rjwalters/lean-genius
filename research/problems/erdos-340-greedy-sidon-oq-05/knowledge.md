# Erdős #340 OQ-05: B_h Sequences

**Open question (generalization) from gallery proof `erdos-340-greedy-sidon`.**

The parent entry develops the theory of Sidon sets (= B_2 sequences: all pairwise
sums distinct) and proves the upper bound `|A| = O(√N)` for `A ⊆ {1,…,N}`. OQ-05
asks whether this extends to **B_h sequences**: sets in which all `h`-fold sums
(with repetition) are distinct.

## Summary

`Erdos340GreedySidonOQ05.lean` formalizes the foundational B_h theory and the sharp
B_h analogue of the Sidon upper bound, fully verified (0 sorries, 0 axioms beyond
`propext`/`Classical.choice`/`Quot.sound`).

| Result | Statement |
|--------|-----------|
| `IsBh h A` | `A` is B_h: the multiset-sum map is injective on `A.sym h` |
| `IsBh.subset` | B_h is inherited by subsets |
| `isBh_one` | every finite set is B_1 |
| `IsBh.of_succ` | downward closure: `B_{h+1}` ⟹ `B_h` |
| `IsBh.of_le` | downward closure (general): `k ≤ h`, `B_h` ⟹ `B_k` |
| `IsBh.sum_injOn_powersetCard` | the `h`-element **subsets** of a B_h set have distinct sums |
| `IsBh.choose_card_le` | **main:** `A ⊆ [1,N]`, B_h, `h ≥ 1` ⟹ `Nat.choose |A| h ≤ h·N` |
| `IsBh.two_card_mul_pred_le` | Sidon recovery: `|A|·(|A|-1) ≤ 4N` (i.e. `|A| = O(√N)`) |

The bound `Nat.choose |A| h ≤ h·N` gives `|A| = O(N^{1/h})`, the trivial B_h
ceiling that Bose–Chowla constructions meet to within `(1-o(1))`.

## Sessions

### Session 2026-06-27 (Session 1) — FRESH

**Mode**: FRESH · **Outcome**: progress (verified increment)

#### What I Did
- Defined `IsBh h A` as injectivity of the multiset-sum map `s ↦ (s : Multiset ℕ).sum`
  on the finset `A.sym h` of `h`-element multisets — the clean generalization of the
  parent `IsSidon` (B_2).
- Proved the structural lemmas `IsBh.subset` and `isBh_one`.
- Proved `IsBh.sum_injOn_powersetCard`: the `h`-element subsets of a B_h set have
  pairwise distinct sums (a subset is a repetition-free multiset, so distinctness is
  inherited from the B_h injectivity).
- Proved the **main theorem** `IsBh.choose_card_le`: `Nat.choose |A| h ≤ h·N` for a
  B_h set `A ⊆ {1,…,N}` with `h ≥ 1`, by injecting the `choose(|A|,h)` distinct
  subset-sums into the interval `[1, h·N]`.
- Proved `IsBh.two_card_mul_pred_le`, the explicit `h = 2` specialization, recovering
  the classical Sidon bound.

#### Key Findings
- **Route through `h`-subsets, not all `h`-multisets.** `Finset.sym s n` has no direct
  multichoose cardinality lemma in Mathlib (only the Fintype-level
  `Sym.card_sym_eq_choose`). Using `Finset.powersetCard` (with `Finset.card_powersetCard
  = Nat.choose`) for the counting, while keeping `A.sym h` only for the *definition*,
  makes the bound clean: `card_image_of_injOn` + `Nat.card_Icc` finish it.
- **Evenness needed at `h = 2`.** From `choose(k,2) = k(k-1)/2 ≤ 2N`, deriving
  `k(k-1) ≤ 4N` needs `2 ∣ k(k-1)` (`(Nat.even_mul_pred_self k).two_dvd`); without it
  `omega` finds the spurious counterexample `k(k-1) = 4N+1`.
- **Build infra gotcha.** The host disk was at 100% with ~10 concurrent Docker Lean
  builds thrashing the shared mathlib build dir (disk-I/O / permission-denied errors).
  The worktree's `.lake/packages` is an absolute symlink that breaks inside the
  container. Verified instead by invoking the host `v4.26.0` toolchain `lean` directly
  on the single file with a hand-built `LEAN_PATH` over the existing package oleans —
  no mathlib rebuild, low memory. `#print axioms` confirms 0-axiom.

#### Files Modified
- `proofs/Proofs/Erdos340GreedySidonOQ05.lean` (new, 206 lines, verified)
- `src/data/research/problems/erdos-340-greedy-sidon-oq-05.json` (new)

#### Next Steps
- B_h greedy extension + the `N^{1/(2h-1)}` greedy lower bound — the genuine open
  direction, matching the still-open parent #340.
- Optional exact bridge `IsBh 2 A ↔ Erdos340.IsSidon A`.

### Session 2026-06-27 (Session 2, researcher-10) — downward closure

**Mode**: ACT · **Outcome**: progress (verified increment, 0 sorries / 0 axioms).

#### What I Did
- Closed the first listed next-step: the **downward closure** in `h`.
  - `IsBh.of_succ`: `B_{h+1} ⟹ B_h`. Append a fixed `a ∈ A` to two `h`-multisets
    with equal sums; the consed `(h+1)`-multisets land in `A.sym (h+1)` with equal
    sums (each is the common sum plus `a`), so `B_{h+1}` injectivity gives
    `a ::ₛ s = a ::ₛ t`, and `Sym.cons_inj_right` cancels the head. The `A = ∅` case
    is degenerate (`∅.sym 0` is a `Unique` subsingleton; `∅.sym (k+1) = ∅`).
  - `IsBh.of_le`: `k ≤ h ⟹ B_h ⟹ B_k`, iterating `of_succ` via `Nat.le_induction`
    (revert the `B_h` hypothesis so the motive stays type-correct).

#### Key Findings / gotchas
- `hsum : (fun s => (↑s).sum) s = …` arrives as an un-beta-reduced lambda app; bind
  it to an explicitly-typed `have hsum0 : (s:Multiset).sum = (t:Multiset).sum := hsum`
  (defeq) before `rw`, else `rw [hsum]` fails to find the pattern.
- `Finset.not_mem_empty` is deprecated → `Finset.notMem_empty`.
- API used: `Sym.cons` (`::ₛ`), `Sym.coe_cons`, `Multiset.sum_cons`,
  `Sym.cons_inj_right`, `Sym.mem_cons`, `Finset.mem_sym_iff`, `Finset.sym_empty`,
  `Sym.uniqueZero`/`Subsingleton.elim`.

#### Verification
`lake env lean Proofs/Erdos340GreedySidonOQ05.lean` → exit 0, no warnings (Docker
host has a v4.26.0 lean image but per-file `lake env lean` over the symlinked main
`.lake` cache is faster/safer). `#print axioms` on `of_succ`/`of_le` = only the 3
foundational. lineCount 206 → 258, theoremCount 6 → 8.

### Session 2026-06-27 (Session 3, researcher-10) — exact Sidon bridge

**Mode**: ACT · **Outcome**: progress (verified increment, 0 sorries / 0 axioms).

#### What I Did
- Closed the second listed next-step: the **exact bridge** `IsBh 2 A ↔ Erdos340.IsSidon A`
  (theorem `isBh_two_iff_isSidon`), linking the new multiset-sum `B_h` definition to the
  parent gallery's classical Sidon definition. Added `import Proofs.Erdos340GreedySidon`.
  - `IsBh.isSidon` (forward): given `a≤b, c≤d ∈ A` with `a+b=c+d`, package the unordered
    pairs as `symPair a b, symPair c d ∈ A.sym 2`; equal multiset-sums + `B_2` injectivity
    give `{a,b}={c,d}` as multisets, so `a ∈ {c,d}`, `b ∈ {c,d}`, and `omega` (with the
    orderings) pins `a=c, b=d`.
  - `IsSidon.isBh_two` (reverse): each `Sym ℕ 2` element is `{a,b}` via
    `Multiset.card_eq_two`; the helper `pair_eq_of_sidon` feeds the correctly-ordered
    quadruple to `IsSidon` over the four `le_total` cases, yielding `{a,b}={c,d}` (using
    `Multiset.pair_comm` for the swapped branches), hence `s=t` by `Sym.coe_injective`.
  - Helper `symPair a b := ⟨{a,b}, by simp⟩ : Sym ℕ 2` with `@[simp] symPair_coe`
    (`= {a,b}`, rfl), `symPair_sum` (`= a+b`), `symPair_mem_sym`.

#### Key Findings / gotchas
- `IsBh`'s domain is `↑(A.sym 2)` (Finset coerced to a `Set` for `InjOn`); to use
  `Finset.mem_sym_iff` on the hypotheses first `rw [Finset.mem_coe, Finset.mem_sym_iff]`.
- Applying `hA : InjOn …` leaves the equality goal with an **un-beta-reduced lambda**
  `(fun s => (↑s).sum) (symPair a b) = …`; `rw [symPair_sum]` fails to match — use
  `simp only [symPair_sum]` (simp beta-reduces) then `exact hsum`.
- `Multiset.card_eq_two : card s = 2 ↔ ∃ x y, s = {x, y}`; `Multiset.pair_comm`,
  `Sym.coe_injective`, `Sym.mem_coe` are the load-bearing pair/Sym lemmas.

#### Verification
Docker host still down (containerd `meta.db` I/O error). Verified via host `v4.26.0`
`lean`: compiled the `import`ed `Proofs.Erdos340GreedySidon` to a temp olean, prepended
it to the `lake env` `LEAN_PATH`, then compiled `Erdos340GreedySidonOQ05.lean` → exit 0,
no warnings. `#print axioms isBh_two_iff_isSidon / IsBh.isSidon / IsSidon.isBh_two` =
only `propext / Classical.choice / Quot.sound` (0-axiom). lineCount 258 → 346,
theorems 8 → 14 (incl. 3 private helpers + `pair_eq_of_sidon`).

#### Next Steps
- The genuine open direction: greedy `B_h` extension + `N^{1/(2h-1)}` lower bound.
- Transport a concrete gallery Sidon result through `isBh_two_iff_isSidon` as a corollary.

### Session 2026-06-27 (Session 4, researcher-2) — greedy B_h extension

**Mode**: ACT · **Outcome**: progress (verified increment, 0 sorries / 0 axioms).

#### What I Did
- Closed the first listed next-step's *constructive seed*: the **greedy B_h
  extension**, the B_h analogue of the parent's `sidon_insert_of_large` /
  `sidon_exists_extension`.
  - `IsBh.insert_of_large`: if `A` is B_h and `m > h·(A.sup id)` then `insert m A`
    is B_h. (No `h ≥ 1` needed — `h = 0` is the trivial singleton-domain case.)
  - `IsBh.exists_insert`: every B_h set has *some* extension `m ∉ A` keeping it B_h;
    explicit witness `m = h·(A.sup id) + 1`. Iterating ⟹ B_h sets of unbounded size.
  - Private engine `bh_split`: any `h`-multiset `s` over `insert m A` decomposes as
    `j•{m} + s_A` where `j = (s:Multiset).count m` and `s_A = filter (·≠m)` lies in
    `A`; records `card s_A = h-j`, `j ≤ h`, and `sum s = j·m + sum s_A`.

#### Proof idea
Two colliding multisets give `j·m + Σs_A = k·m + Σt_A`. Each A-part sum is
`≤ (h-j)·(max A) ≤ h·(max A) < m`, so a strict `j ≠ k` forces one side to exceed
the other by `≥ m` — contradiction; hence `j = k`, then `Σs_A = Σt_A`, and the
`(h-j)`-multiset A-parts coincide by downward closure (`of_le` to `B_{h-j}`),
giving `s = t`.

#### Key Findings / gotchas
- `Multiset.filter_add_not` has `p` as the FIRST explicit arg (re-`variable (p)`
  before it in Mathlib): call `Multiset.filter_add_not (· = m) (s : Multiset ℕ)`.
- `Multiset.filter_eq' s b : s.filter (· = b) = replicate (count b s) b` (the primed
  version uses `(· = b)`; unprimed uses `(b = ·)`). `filter (·≠m)` is defeq to
  `filter (fun a => ¬ (·=m) a)`, so `rw` closes the split by `rfl` despite the
  un-beta-reduced form.
- For `x ∈ filter p s`, use `Multiset.mem_filter.mp hx` (gives `⟨x∈s, p x⟩`) — the
  bare `Multiset.of_mem_filter`/`mem_of_mem_filter` mis-unified the predicate here.
- `mul_le_mul_right'` is deprecated → replaced monotonicity steps with `gcongr`
  (discharges the `a ≤ b` side goal from a local `have`).
- The nonlinear `j*m` vs `k*m` comparison is fed to `omega` as atoms: supply
  `hexp : (j+1)*m = j*m + m` (by `ring`) and `hkm : (j+1)*m ≤ k*m` (by `gcongr`),
  then `omega` treats `j*m, k*m` as opaque and finishes linearly.
- Sum bound via `Multiset.sum_le_card_nsmul s (A.sup id) (…) : s.sum ≤ card s • sup`
  + `smul_eq_mul`; per-element `x ≤ A.sup id` from `Finset.le_sup (f := id)`.

#### Verification
Docker host build path unavailable; built the imported `Proofs.Erdos340GreedySidon`
to its olean (`lake env lean -o`), then `lake env lean Proofs/Erdos340GreedySidonOQ05.lean`
→ exit 0, no warnings. `#print axioms IsBh.insert_of_large / IsBh.exists_insert`
= only `propext / Classical.choice / Quot.sound` (0-axiom). 422 → 558 lines,
14 → 19 theorems (incl. private `bh_split`), 1 → 2 defs (counting `symPair`).

#### Next Steps
- Turn extendability into a *rate*: bound the FORBIDDEN set (values in `[1,N]` whose
  insertion breaks B_h) by `O(|A|^{2h-1})`, giving the greedy `N^{1/(2h-1)}` lower
  bound — the remaining open core, matching the still-open parent #340.
- Iterate `exists_insert` into an explicit greedy B_h sequence à la `greedySidonSeq`.

### Session 2026-06-27 (Session 4 cont., researcher-2) — explicit greedy B_h family

**Mode**: ACT · **Outcome**: progress (verified increment, 0 sorries / 0 axioms).
Added to the same PR (#30985) as the greedy extension.

#### What I Did
- Iterated `IsBh.exists_insert` into an **explicit greedy family** realizing the
  qualitative payoff of extendability:
  - `isBh_empty`: `∅` is B_h (h=0 domain `∅.sym 0` is a `Sym`-subsingleton; h≥1
    domain `∅.sym (k+1) = ∅`).
  - `greedyBhAux h hh : (n:ℕ) → {A : Finset ℕ // IsBh h A ∧ A.card = n}` — a
    subtype-bundled structural recursion that carries the B_h proof *alongside* the
    set, so `exists_insert`'s `IsBh` hypothesis is available at each step. Witness via
    `Classical.choose (prev.2.1.exists_insert hh)`; `choose_spec` gives
    `m∉prev ∧ B_h (insert m prev)`. card step: `Finset.card_insert_of_notMem`.
  - Projections `greedyBhSet` / `greedyBhSet_isBh` / `greedyBhSet_card`.
  - `exists_isBh_card`: for every h≥1 and n, a B_h set of cardinality exactly n exists.

#### Why it matters
SEPARATES the open question cleanly: a B_h set's *count* is unbounded for free
(this result); the genuinely open core is how small the *largest element* can be —
the N^{1/(2h-1)} greedy lower bound inside {1,…,N}.

#### Gotchas
- Bundle the invariant in a subtype and recurse on it — you cannot define the set by
  plain `Nat.rec` and prove B_h separately, because the next witness *depends on* the
  current B_h proof. The `{A // IsBh h A ∧ A.card = n}` carrier solves this.
- `Finset.card_insert_of_not_mem` is deprecated → `Finset.card_insert_of_notMem`.
- `noncomputable` required (Classical.choose). #print axioms = propext /
  Classical.choice / Quot.sound only (0-axiom in the policy sense).

#### Verification
`lake env lean` exit 0, no warnings. `#print axioms exists_isBh_card / greedyBhSet_card`
= 3 foundational only. 558 → 610 lines, 19 → 24 theorems, 2 → 4 defs.

### Session 2026-06-27 (Session 6, researcher-2) — dilation + affine invariance (rebased onto greedy main)

**Mode**: ACT · **Outcome**: progress (verified increment, 0 sorries / 0 axioms).

#### What I Did
- Added **Part 6: dilation + affine invariance**, completing the affine-symmetry picture
  of `B_h` (the natural complement to the existing translation invariance `map_add_right`).
  - `IsBh.map_mul_right` (`0 < c`): `A.image (· * c)` is `B_h`. Each `h`-fold sum scales
    by the common factor `c`. Proof mirrors `map_add_right`: pull each dilated `h`-multiset
    back into `A` by dividing entries by `c` (`Nat.mul_div_cancel _ hc`), recover via
    `Sym.map_map`/`Sym.map_congr`/`Sym.map_id'`, relate sums with the induction helper
    `sum_map_mul_const : (m.map (· * c)).sum = m.sum * c`, cancel `c > 0` via
    `Nat.eq_of_mul_eq_mul_right`, finish with `B_h` injectivity. `c = 0` is sharp (collapses
    the set to `{0}`), so `0 < c` is necessary, not cosmetic.
  - `IsBh.map_affine` (`0 < c`): `A.image (fun x => c*x + d)` is `B_h` = dilation then
    translation, `rw [hfun, ← Finset.image_image]` then `(hA.map_mul_right hc).map_add_right`.

#### Concurrency note (IMPORTANT)
- This work was first done as PR #31009 against main @3ef2b85 (the 509-line, pre-greedy
  file). While it was in flight the **greedy-extension** PR merged to main (file → 610
  lines, `insert_of_large`/`exists_insert`/`greedyBhSet`/`exists_isBh_card`), so #31009
  went `CONFLICTING`. I **rebased**: reset to new origin/main, re-applied the self-contained
  Part-6 affine code on top of the greedy version, merged the affine entries into the
  greedy JSON/knowledge, re-verified, and force-pushed `feature/researcher-2` to update
  #31009 (now mergeable, contains greedy + affine). The affine Lean code is unchanged from
  the original verification.

#### Key Findings / gotchas
- Two uses of `Nat.mul_div_cancel _ hc`: membership (`(x*c)/c = x ∈ A`) and round-trip
  recovery (`(y*c)/c * c = y*c`). First underscore is the dividend.
- `map_affine` slope orientation: affine written `c*x + d` but the dilation helper uses
  `· * c` (`x*c`); bridge with `funext x; simp [Nat.mul_comm]`. `Finset.image_image :
  (s.image f).image g = s.image (g ∘ f)`, so `←` un-composes.
- `Nat.eq_of_mul_eq_mul_right : 0 < c → a*c = b*c → a = b` is the multiplicative analogue
  of the additive `omega` cancellation in `map_add_right`.

#### Verification
Docker host unreliable. Verified via host `v4.26.0` `lake env lean`: compiled imported
`Proofs.Erdos340GreedySidon` to a temp olean (`/tmp/oq05build`), prepended to `LEAN_PATH`,
compiled `Erdos340GreedySidonOQ05.lean` → exit 0, no warnings. `#print axioms
IsBh.map_mul_right / IsBh.map_affine` = `[propext, Classical.choice, Quot.sound]` (0-axiom).
704 lines, 27 theorems.

#### Next Steps
- Unchanged open core: the forbidden-set counting for the `N^{1/(2h-1)}` greedy lower
  bound. `map_affine` now lets one normalise a `B_h` set (least element 0) as a first step.

### Session 2026-06-27 (researcher-3) — counting the forbidden values

**Mode**: CONTINUE (RICH) · **Outcome**: progress (verified increment)

Added `IsBh.card_forbidden_le` (Part 7): the §5b counting milestone made explicit.
For a `B_h` set `A`, the number of values `m ≤ h·max A` whose insertion breaks `B_h`
is `≤ h · T²`, where `T = #{multisets over A of size ≤ h}` (`= ∑_{i≤h} multichoose(|A|,i)`,
polynomial in `|A|` of degree `h`).

**Proof idea.** `exists_diff_eq_of_not_insert` gives each forbidden `m` a triple
`(d, sA, tA)` with `1 ≤ d ≤ h`, `sA,tA` multisets over `A` of size `≤ h`, and
`d·m + sA.sum = tA.sum`. Since `d ≥ 1`, the triple *determines* `m = (tA.sum−sA.sum)/d`.
So the forbidden set is a *subset of the image* of the finite triple-set
`Icc 1 h ×ˢ T ×ˢ T` under `(d,sA,tA) ↦ (tA.sum−sA.sum)/d` — no choice function needed,
just `card_le_card` + `card_image_le` + `card_product`.

**Key API.** `Finset.mem_sym_iff` (Sym carries card in its type → membership is just the
`∀x∈u, x∈A` condition); short multiset `u` over `A` lands in
`T := (range (h+1)).biUnion (i ↦ (A.sym i).image Subtype.val)` at index `card u`.
`Nat.mul_div_cancel_left m (0<d) : d*m/d = m`. `Nat.card_Icc : #(Icc a b)=b+1-a`.

**Honest scope.** The bound `h·T²` is degree `2h` in `|A|`, giving the *trivial*
`N^{1/2h}` greedy rate. The sharp `N^{1/(2h-1)}` needs the finer count exploiting the
orientation of the `d·m` block (the `d` and `(sA,tA)` are not independent). Still open.
Verified 0-axiom (`lake env lean`, exit 0; `#print axioms` = propext/Classical.choice/Quot.sound).

### Session 2026-06-27 (researcher-3, Session 8) — orientation bound ⇒ sharp count

**Mode**: CONTINUE (RICH) · **Outcome**: progress (verified increment, 0 sorries / 0 axioms).

Closed the explicitly-flagged "remaining open core": the **degree-`2h-1`** forbidden-set
count, realising the sharp `N^{1/(2h-1)}` greedy rate.  Two changes:

1. **Strengthened `IsBh.exists_diff_eq_of_not_insert`** with the *orientation bound*
   `Multiset.card sA + Multiset.card tA + d ≤ 2 * h`.  The multiplicity gap
   `d = |j − k|` is paid out of the `2h` total slots of the two colliding `h`-multisets,
   so the `A`-parts together carry `≤ 2h − d ≤ 2h − 1` elements.  Both `refine` branches
   discharge it by `omega` from `hcardS : card sA = h − j`, `hcardT : card tA = h − k`
   (combined `+ d = 2h − 2·min(j,k) ≤ 2h`).

2. **Added `IsBh.card_forbidden_le'`**: the forbidden set below `h·max A` has size
   `≤ 2 · h · T₋ · T₊`, where `T₋ = #{multisets over A of size < h}` (degree `h−1`) and
   `T₊ = #{size ≤ h}` (degree `h`).  Total degree `1 + (h−1) + h = 2h − 1` in `|A|` —
   one below the prior trivial `T²` (`card_forbidden_le`, degree `2h`).

#### Why it matters
The trivial `T²` count gives only `N^{1/2h}`; the sharp `B_h` greedy lower bound is
`N^{1/(2h-1)}`.  The whole gap is exactly the orientation observation that the gap `d`
consumes slots, dropping the combined `A`-part size from `2h` to `2h − 1`.  This is the
quantitative open core of #340's `B_h` generalisation, now formalised.

#### Proof technique (no bijection needed)
The combined size `≤ 2h − 1` with each part `≤ h` forces **at least one** of `sA`, `tA`
to have size `< h` (else combined `≥ 2h`; `omega`).  So the pair `(sA, tA)` lies in
`(T₋ ×ˢ T₊) ∪ (T₊ ×ˢ T₋)` — a clean case-split, *not* a parity/tagging bijection over
`A ⊎ A`.  Then forbidden ⊆ image of `Icc 1 h ×ˢ ((T₋ ×ˢ T₊) ∪ (T₊ ×ˢ T₋))` under the
determining map `(d, sA, tA) ↦ (tA.sum − sA.sum)/d`; `card_le_card`, `card_image_le`,
`card_union_le`, `card_product`, `Nat.card_Icc` finish.

#### Gotchas
- Use `range h` (not `range ((h−1)+1)`) for the size-`<h` pool `T₋` to dodge `ℕ`
  truncation of `h − 1`; membership is `card u < h → card u ∈ range h`.
- The "at least one side short" disjunction is proved by `omega` *as a goal* — omega
  closes `card sA < h ∨ card tA < h` directly from `hcsA, hctA ≤ h` and the new
  combined bound (`+ d ≤ 2h`, `d ≥ 1`).
- `Nat.mul_le_mul_left` to pull `h ·` through the `X.card ≤ 2·T₋·T₊` step; the union
  bound is `Finset.card_union_le _ _` then `card_product` + `ring`.

#### Verification
`~/.elan/toolchains/leanprover--lean4---v4.26.0/bin/lake env lean
Proofs/Erdos340GreedySidonOQ05.lean` → exit 0, no warnings (single-file over the
worktree's symlinked main `.lake`; `Erdos340GreedySidon.olean` prebuilt).  `#print
axioms IsBh.exists_diff_eq_of_not_insert / IsBh.card_forbidden_le'` =
`[propext, Classical.choice, Quot.sound]` (0-axiom).  835 → 923 lines, 28 → 30 theorems.

#### Next Steps
- Pin `T₋, T₊` to closed `∑ multichoose(|A|, i)` polynomials (`card_biUnion_le` +
  `Finset.card_sym`), making the degree-`2h−1` explicit as a polynomial in `|A|`.
- Combine with a `[1,N]`-bounded greedy iteration to formalise `|A| ≥ c·N^{1/(2h-1)}`
  end-to-end (forbidden count `< N` ⟹ an extension exists).

### Session 2026-06-27 (researcher-3) — explicit closed-form forbidden polynomial

**Mode**: CONTINUE (RICH) · **Outcome**: progress (verified increment, 0 sorries / 0 axioms).

Delivered the prior session's first listed next-step: pinning the abstract multiset
pools `T₋, T₊` of `card_forbidden_le'` to an explicit `|A|`-polynomial, turning the
"degree `2h−1`" claim into a concrete closed form (Part 8, 4 new theorems).

#### What I Did
- `card_sym_le_pow (A) (n) : (A.sym n).card ≤ A.card ^ n` — the **`Finset.sym`
  cardinality bound** that Mathlib lacks (it only has the Fintype-level exact
  `Sym.card_sym_eq_multichoose`). Induction on `n` via `sym_succ` +
  `sup_eq_biUnion` + `card_biUnion_le`: `|A.sym (n+1)| ≤ ∑_{a∈A} |A.sym n| =
  |A|·|A|^n`. (Each size-`(n+1)` multiset is `Sym.cons a` of a size-`n` one.)
- `geom_sum_le_pow (n) (k) : ∑_{i≤k} n^i ≤ (n+1)^k` — short induction:
  `(n+1)^{k+1} = (n+1)^k + n·(n+1)^k ≥ (n+1)^k + n^{k+1}` (each binomial summand of
  `(n+1)^k` dominates the bare `n^i`; avoids `add_pow` entirely).
- `card_pool_le (A) (k) : |pool of multisets over A of size ≤ k| ≤ (|A|+1)^k`,
  chaining `card_biUnion_le` → `card_image_le` → `card_sym_le_pow` → `geom_sum_le_pow`.
- **`IsBh.card_forbidden_poly` (h ≥ 1):** `#forbidden ≤ 2·h·(|A|+1)^{2h−1}` — the
  headline explicit degree-`(2h−1)` polynomial in `|A|`. Splits `h = h'+1`, bounds
  `T₋ ≤ (|A|+1)^{h'}` and `T₊ ≤ (|A|+1)^{h'+1}` via `card_pool_le`, then
  `(|A|+1)^{h'}·(|A|+1)^{h'+1} = (|A|+1)^{2h−1}` by `pow_add` (`h'+(h'+1) = 2(h'+1)−1`).

#### Why it matters
This is the form the greedy lower bound consumes directly: a `B_h` set inside
`{1,…,N}` admits a fresh small element whenever `2·h·(|A|+1)^{2h−1} < N`, giving the
sharp-exponent `|A| = Ω(N^{1/(2h−1)})` rate. The remaining open core is purely the
`[1,N]`-bounded greedy *iteration* + the real-power inequality — no more counting.
`card_sym_le_pow` is independently reusable (genuine Mathlib gap).

#### Key Findings / gotchas
- `Finset.sym_succ : s.sym (n+1) = s.sup (fun a => (s.sym n).image (Sym.cons a))`; the
  `sup` is the lattice (union) sup — convert to `biUnion` with `Finset.sup_eq_biUnion`
  before `Finset.card_biUnion_le`.
- State `geom_sum_le_pow` over `range (k+1)` (not `range k`) to dodge `k−1` subtraction;
  for `T₋ = range h` apply it at `k := h−1` after `obtain ⟨h', rfl⟩ : ∃ h', h = h'+1`.
- Final exponent merge: `mul_assoc (2*(h'+1))` then `← pow_add` then rewrite
  `h' + (h'+1) = 2*(h'+1) − 1` (`by omega`); `gcongr` discharges the two pool bounds.
- `ring` proves `(n+1)^(k+1) = (n+1)^k + n*(n+1)^k` on ℕ (it knows `pow_succ`).

#### Verification
Docker host down (`docker info` hangs). Verified via host `v4.26.0`
`lake env lean Proofs/Erdos340GreedySidonOQ05.lean` (dependency olean
`Proofs.Erdos340GreedySidon` already on `LEAN_PATH`) → exit 0, no warnings.
`#print axioms IsBh.card_forbidden_poly / card_sym_le_pow / geom_sum_le_pow /
card_pool_le` = `[propext, Classical.choice, Quot.sound]` (0-axiom). 923 → 1022 lines.

#### Next Steps
- The end-to-end greedy lower bound `∃ A ⊆ [1,N], IsBh h A ∧ |A| ≥ c·N^{1/(2h−1)}`:
  iterate "forbidden count `< N` ⟹ a small extension exists" inside `{1,…,N}`, then the
  real-power inequality `2h(k+1)^{2h−1} < N` ⟹ `k ≥ (N/(2h))^{1/(2h−1)} − 1`. Only
  remaining open piece; no further counting needed.

### Session 2026-06-27 (researcher-4) — end-to-end greedy lower bound inside [1,N]

**Mode**: CONTINUE (RICH) · **Outcome**: progress (verified increment, 0 sorries / 0 axioms).

Closed the single explicitly-flagged "only remaining open piece": the `[1,N]`-bounded
greedy *iteration*. The forbidden-count chain (Parts 5b–8) had reduced the problem to a
counting bound; Part 9 now runs the greedy algorithm to completion inside `{1,…,N}`.

#### What I Did (Part 9, 3 new theorems)
- **`IsBh.exists_insert_le`** (the bounded greedy step): a `B_h` set `A` with room
  `|A| + 2·h·(|A|+1)^{2h-1} < N` admits a *fresh element of `{1,…,N}`* — some
  `m ∈ {1,…,N}`, `m ∉ A`, with `insert m A` still `B_h`. The blocked values are
  `A ∪ F` where `F = {m ∈ [1,N] : ¬IsBh (insert m A)}`; each forbidden `m` satisfies
  `m ≤ h·max A` (else `insert_of_large` applies), so `F ⊆` the range counted by
  `card_forbidden_poly`, giving `|F| ≤ 2h(|A|+1)^{2h-1}`. Then
  `|A ∪ F| ≤ |A| + |F| < N = |[1,N]|`, so an unblocked `m` exists.
- **`exists_isBh_Icc_card`** (cumulative iteration): if `∀ j < k`, the per-step room
  `j + 2h(j+1)^{2h-1} < N` holds, then a `B_h` set `⊆ {1,…,N}` of card `k` exists.
  Induction on `k` from `∅` (`isBh_empty`), each step `exists_insert_le` +
  `Finset.insert_subset_iff` + `card_insert_of_notMem`.
- **`exists_isBh_Icc_card_of_le`** (closed-form): `k + 2h(k+1)^{2h-1} ≤ N` ⟹ a `B_h`
  set `⊆ {1,…,N}` of card exactly `k` exists. The single hypothesis dominates every
  intermediate room condition because `j ↦ j + 2h(j+1)^{2h-1}` is monotone
  (`gcongr` + `add_lt_add_of_lt_of_le`).

#### Why it matters
This is the form the asymptotic rate consumes directly: solving `2h(k+1)^{2h-1} ≈ N`
for `k` gives `k = Ω(N^{1/(2h-1)})`. The greedy *combinatorics* are now fully formal
end-to-end; the **only** gap left is the purely real-analytic fractional-power
conversion (`Real.rpow` bookkeeping), which uses no `B_h` structure.

#### Key Findings / gotchas
- `IsBh.exists_insert_le` needs **no** `A ⊆ {1,…,N}` hypothesis: an `m ∈ [1,N]` outside
  `A ∪ F` automatically avoids `A`. Dropping it keeps the lemma maximally reusable; the
  caller rebuilds `insert m A ⊆ [1,N]` from `m ∈ [1,N]` and its own subset fact.
- `Finset.card_sdiff` in this Mathlib (v4.26.0) is the **unconditional** intersection
  form `#(t\s) = #t − #(s ∩ t)` (no subset arg) — applying it to a `⊆` proof fails.
  Use `Finset.exists_mem_notMem_of_card_lt_card : #s < #t → ∃ e, e ∈ t ∧ e ∉ s` to grab
  the available element directly.
- `(Finset.Icc 1 N).card = N` via `Nat.card_Icc` (`N + 1 − 1`) then `omega`.
- `gcongr` fully discharges `2h(j+1)^{2h-1} ≤ 2h(k+1)^{2h-1}` from `j < k` (its
  discharger closes the `j+1 ≤ k+1` side goal — a trailing `omega` errors "no goals").
- `omega` treats `2*h*(A.card+1)^(2*h-1)` as one opaque atom; keeping the expression
  byte-identical in `card_forbidden_poly`, `hFcard`, and `hroom` lets `omega` chain the
  blocked-count bound `< N` without unfolding the power.

#### Verification
Docker host down (`docker info` times out). Verified via host `v4.26.0`
`lake env lean Proofs/Erdos340GreedySidonOQ05.lean` over the worktree's symlinked main
`.lake` (dependency `Proofs.Erdos340GreedySidon.olean` prebuilt) → exit 0, no warnings.
`#print axioms IsBh.exists_insert_le / exists_isBh_Icc_card / exists_isBh_Icc_card_of_le`
= `[propext, Classical.choice, Quot.sound]` (0-axiom). 1022 → 1124 lines, +3 theorems.

#### Next Steps
- The real-analytic step: from `exists_isBh_Icc_card_of_le`, pick
  `k ≈ (N/(4h))^{1/(2h-1)}` to obtain the explicit `|A| ≥ c·N^{1/(2h-1)}` bound.
  Pure `Real.rpow`/`Nat.pow` monotonicity — no further `B_h` work.
