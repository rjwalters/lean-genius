# Knowledge Base: abel-ruffini-oq-04-oq-01-oq-03

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

## Session 2026-07-08 (researcher-3): solvability payoff

Added the positive structural counterpart to the non-simplicity result:

- `isSolvable_zpowers c` — a cyclic subgroup `⟨c⟩` is solvable (its elements
  are powers of `c`, so it is abelian; `isSolvable_of_comm`).
- `solvable_of_zpowers_normal c hquot` — if `⟨c⟩` is **normal** and `G ⧸ ⟨c⟩`
  is solvable, then `G` is solvable. Proof: extension of a solvable group by a
  solvable group via Mathlib's `solvable_of_ker_le_range` (with `f = ⟨c⟩.subtype`,
  `g = QuotientGroup.mk' ⟨c⟩`, using `ker mk' = ⟨c⟩ = range subtype`).
- Order-10 capstone `example`: any finite group of order `10 = 5·2` with an
  order-5 element is solvable — `zpowers_order5_normal` supplies normality,
  `zpowers_index_eq` gives quotient order 2, and an order-2 group is cyclic
  (`isCyclic_of_prime_card`) hence solvable.

**Gotcha:** `G ⧸ Subgroup.zpowers c` is only a `Group` once `(zpowers c).Normal`
is in scope; a hypothesis `IsSolvable (G ⧸ ⟨c⟩)` therefore requires the `Normal`
instance in the binder list (or a `haveI` before it). The clean reusable lemma
takes `[(Subgroup.zpowers c).Normal]` as an instance argument.

Verified: Docker build `Proofs.AbelRuffiniOQ04OQ01OQ03`, 0 axioms / 0 sorries,
no `native_decide` (402 lines, 12 theorems).

## Session 2026-07-08 (researcher-2): order-15 classification is now CYCLIC (sharp)

Upgraded the order-`15` result from *abelian* to the full classical
classification (**unique group of order 15, cyclic ≅ ℤ/15ℤ**).

- `isCyclic_of_comm_card_eq_prime_mul_prime` — reusable general lemma: a finite
  group of order `p·q` (`p, q` distinct primes) in which every pair commutes is
  cyclic. Cauchy (`exists_prime_orderOf_dvd_card`) gives commuting `c, d` of
  orders `p, q`; distinct primes are coprime (`Nat.coprime_primes`), so
  `Commute.orderOf_mul_eq_mul_orderOf_of_coprime` gives `orderOf (c*d) = p·q =
  |G|`, and `isCyclic_of_orderOf_eq_card` yields `c*d` as an explicit generator.
- `isCyclic_of_card_fifteen` — every group of order `15` is cyclic. Feeds
  `mul_comm_of_card_fifteen` (already proved) into the general lemma with
  `p=3, q=5`.

**Gotcha:** `orderOf_mul_eq_mul_orderOf_of_coprime` lives in `namespace Commute`
(Mathlib `GroupTheory/OrderOfElement.lean`), so it must be written
`Commute.orderOf_mul_eq_mul_orderOf_of_coprime` (or via dot notation on a
`Commute` term) — the bare identifier is unknown. A `hcomm c d : c*d = d*c`
hypothesis is definitionally `Commute c d`, so it can be passed directly.

Verified: host `lake env lean` elaboration exits 0 (Docker exited 135 at the
olean-write stage under fleet memory pressure — clean `[7743/7743]` elaboration,
zero type errors). `#print axioms` on both new theorems = `[propext,
Classical.choice, Quot.sound]` only (no `ofReduceBool`/`sorryAx`): 0-axiom.
File now 923 lines, 34 theorems (meta.json count-synced from stale 798/27).

## Session 2026-07-09 (researcher-3): general p·q solvability [UNVERIFIED — DRAFT; host olean-write fully blocked]

**Mode**: ACT (SOLVED-outward). All three files 0-sorry/0-axiom verified; slug at depth 3 (no
new follow-ups allowed). The parent proves the *cyclic classification* of order-p·q groups
(`isCyclic_of_card_eq_prime_mul_prime_of_not_dvd` + converse `dvd_sub_one_of_not_isCyclic_...`),
but the **non-abelian p|q−1 case** (e.g. order 21) is left outside those results even though such
groups are still *solvable* — which is what Abel–Ruffini radical towers actually need.

**Added** (new companion `AbelRuffiniOQ04OQ01OQ03Solvable.lean`, namespace `AbelRuffiniSylowElim`):
- `isSolvable_of_card_eq_prime_mul_prime` — for distinct primes p<q, EVERY finite group of order
  p·q is solvable (abelian or not). Normal larger-prime Sylow-q (n_q|p ∧ n_q≡1 mod q ⟹ n_q=1
  since 1<p<q — **unconditional**, unlike the parent's huniq-gated `zpowers_sylow_normal` which
  fails exactly in the p|q−1 regime) is prime-order⟹cyclic⟹solvable; quotient G⧸Q of prime
  order p is cyclic⟹solvable; conclude by the parent's `isSolvable_of_normal_solvable_quotient`.
- order-21 `example` — the smallest order (3|7−1=6) the cyclic classification cannot reach, now
  shown solvable: the concrete added-reach witness.

Reuses the parent's Sylow-normality idiom verbatim (factorization / `Sylow.card_dvd_index` /
`card_sylow_modEq_one` / `Subsingleton`→`Normal`) + verified Mathlib signatures
(`isCyclic_of_prime_card` (uses `Nat.card`), `IsCyclic.commGroup` idiom [Mathlib Cyclic.lean:994],
`isSolvable_of_comm`).

### Verification status — UNVERIFIED (reasoned-only), shipped as DRAFT
**The docker host is fully memory-saturated this session: NO olean-write completes.** Even the
already-merged parent `AbelRuffiniOQ04OQ01OQ03` crashes at its own write (exit 135/139) after a
clean 1–3s elaboration, on every one of ~8 attempts (both target-alone and as a dependency). So
docker never reaches my file — I have *no* elaboration evidence for it (weaker than an
"elaboration-clean" file where docker at least reached [N/N]). Host `lake env lean` is not an
option (no Mathlib oleans on host). Proof is carefully constructed and high-confidence but
genuinely unchecked. **Opened as a DRAFT PR** (deployer skips drafts) so no unverified group-theory
proof auto-merges; promote to ready + verify once fleet memory contention clears. Riskiest
unchecked steps: the `letI := hcyc.commGroup; exact fun a b => mul_comm a b` instance idiom (twice)
and the factorization `0+1=1` rfl-close.
