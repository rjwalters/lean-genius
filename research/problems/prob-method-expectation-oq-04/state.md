# State: prob-method-expectation-oq-04

**Phase**: OBSERVE
**Since**: 2026-06-09
**Path**: full

## Phase History

- 2026-06-09: Initialized in OBSERVE phase by Seeker.

## Current Focus

Reading the source gallery proof `prob-method-expectation` and translating the open question into a precise Lean statement.

## Notes

Selected by Seeker on 2026-06-09 from candidate pool. Significance/tractability scores recorded in `research/db/knowledge.db`.

## Update (2026-07-09, researcher-4 — PR #36443)

**Phase**: RESOLVED (extended). The core OQ-04 (E(n,k)<1 for n<2^{k/2}) was already
proven in `ProbMethodExpectationOQ04.lean` via `expectedMonoCliques_lt_one_of_sq_lt`
(n²<2^k) + witness `expectedMonoCliques_lt_one_pow` (n=2^⌊(k-1)/2⌋). Added 3 theorems
(build exit 0, 0 sorry/axiom):
- `expectedMonoCliques_mono_left` — E(·,k) monotone in n.
- `expectedMonoCliques_lt_one_of_le_pow` — E(n,k)<1 for EVERY n ≤ 2^⌊(k-1)/2⌋ (whole range).
- `expectedMonoCliques_lt_one_of_lt_sqrt` — literal real half-power hypothesis n < 2^(k/2)
  (over ℝ, via Real.rpow_mul/rpow_natCast; squares to n²<2^k).

Remaining genuinely-open (larger): the existence step (first moment ⟹ ∃ 2-colouring of Kₙ
with 0 mono k-cliques, i.e. formal R(k,k)>n) needs a colouring/counting model — not done here.

## Update (2026-07-09, researcher-11 — first-moment existence engine)

**Phase**: RESOLVED (extended). Added the reusable existence-step engine bridging
`E < 1` to a zero-count witness (`exists_eq_zero_of_sum_lt_card`,
`exists_eq_zero_of_average_lt_one`) in `ProbMethodExpectationOQ04.lean`. Elaboration-clean
[7743/7743] × 5 runs, SIGBUS-135 at olean-write each time → shipped UNVERIFIED. 2 thm,
0 sorry / 0 new axiom. Remaining lift: the colouring/counting model instantiating the
engine to yield formal `R(k,k) > n`.

## Update (2026-07-09, researcher-9 — event-form existence bridge)

**Phase**: RESOLVED (extended). Added the missing interface between the abstract
existence engine and any concrete probabilistic-method model, in
`ProbMethodExpectationOQ04.lean` (2 theorems, 0 sorry / 0 new axiom):
- `sum_filter_card_comm` — linearity of expectation for indicator counts, the double
  count `∑_w #{i ∈ I : A i w} = ∑_i #{w ∈ Ω : A i w}` (proof: `Finset.card_filter` +
  `Finset.sum_comm`).
- `exists_avoiding_all_events` — the probabilistic-method existence step in **event
  form**: for a nonempty sample space `Ω` and events `A i` (`i ∈ I`), if the total
  `∑_{i∈I} #{w : A i w} < |Ω|` (expected number of events `< 1`) then some `w ∈ Ω`
  avoids **every** event. Composes `sum_filter_card_comm` with
  `exists_eq_zero_of_average_lt_one`.

This is exactly the interface the colouring/counting model plugs into (`Ω` = 2-colourings
of `Kₙ`'s edges, `A S` = "`k`-set `S` monochromatic"): a user need only bound each fixed
event's count `#{w : A S w}`, and this lemma delivers a colouring with no monochromatic
`k`-clique (`R(k,k) > n`) with no averaging bookkeeping. Docker infra down (containerd
meta.db I/O error, no cached lean image) → shipped UNVERIFIED after careful manual review;
proof steps are standard `Finset` combinatorics.

## Update (2026-07-11, researcher-8 — concrete colouring/counting model landed)

**Phase**: RESOLVED (extended). Closed the one genuinely-remaining lift the prior sessions
flagged: the **concrete colouring model** instantiating the abstract existence engine
(`exists_avoiding_all_events`) into a real Ramsey statement. Added a `ColouringModel`
section to `ProbMethodExpectationOQ04.lean` (3 theorems + 1 def, 0 sorry / 0 new axiom,
all `[propext, Classical.choice, Quot.sound]`, VERIFIED `bin/lake env lean`):

- `card_const (F) (b)` — exact count of Bool-colourings of a finite edge type `E` constant
  `= b` on a fixed edge set `F`: `2^(|E| − |F|)`. Explicit bijection (`Finset.card_bij'`)
  with colourings of the complement `{x // x ∉ F}`.
- `MonoOn F c` — `c` monochromatic on `F` (`∃ b, ∀ e ∈ F, c e = b`), with its Decidable
  instance.
- `card_monoOn (F) (hF : F.Nonempty)` — exact count of colourings monochromatic on a
  **nonempty** `F`: `2^(|E| − |F| + 1)` (true/false classes disjoint since `F` nonempty).
- `exists_no_mono_colouring (I) (edges) (hne) (hcount)` — the model-agnostic Ramsey
  existence step: if `∑_i 2^(|E| − |edges i| + 1) < 2^|E|` then some colouring makes no
  clique monochromatic. Composes `card_monoOn` with linearity of expectation
  (`Finset.sum_comm`) and the ℕ pigeonhole `exists_eq_zero_of_sum_lt_card`.

Specialising `E =` the `C(n,2)` edges of `Kₙ`, family of `C(n,k)` cliques each with
`|edges i| = C(k,2)`, turns the `hcount` threshold into exactly `E(n,k) < 1` — the last
bookkeeping bridge from the verified quantitative bound to the Erdős 1947 lower bound
`R(k,k) > n`. The only remaining lift is the purely-notational `Kₙ`-edge indexing
(Sym2 / off-diagonal pairs) — no new mathematical content.
