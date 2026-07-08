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

## Session 2026-07-08 (researcher-4) — Solvability payoff

**Mode**: REVISIT (in-progress, ACT) · **Outcome**: progress (verified 0/0)

### What I did
Upgraded the normal-Sylow structural results in `AbelRuffiniOQ04OQ01OQ03.lean`
from *non-simplicity* to full *solvability* — the property that actually drives
Abel–Ruffini (solvable-by-radicals ⇔ solvable Galois group). Added 5 theorems:

- `isSolvable_zpowers` — `⟨c⟩` is solvable (cyclic ⇒ abelian), via
  `isSolvable_of_comm` + `zpow_mul_comm`.
- `isSolvable_of_normal_solvable_quotient` — general extension engine: `N`
  normal, `IsSolvable N`, `IsSolvable (G ⧸ N)` ⇒ `IsSolvable G`, packaging
  `solvable_of_ker_le_range` for `N.subtype` / `QuotientGroup.mk'`.
- `isSolvable_of_sylow_primePow_index` — the star result: under the Sylow
  hypotheses, if the index `m = q^k` is a prime power then `G` is solvable
  (quotient is a `q`-group ⇒ `Group.IsNilpotent` ⇒ solvable). No extra
  quotient-solvability hypothesis.
- `isSolvable_order5_primePow_index` — the `p = 5` specialisation.
- Order-40 solvability capstone `example` (`40 = 5·2³`, quotient is a 2-group).

### Key findings / gotchas
- You cannot put `IsSolvable (G ⧸ Subgroup.zpowers c)` in a *signature* without a
  `Normal` instance in scope (the quotient `Group` instance needs it). Factor the
  extension as a general `[N.Normal]` lemma and derive normality *inside* the
  corollary body instead.
- Group nilpotency is `Group.IsNilpotent`; bare `IsNilpotent` resolves to the
  ring/monoid-element `_root_.IsNilpotent` (needs `Zero`), giving a spurious
  `failed to synthesize Zero (Type _)`.
- `IsPGroup.of_card : Nat.card G = p^n → IsPGroup p G`; `.isNilpotent` needs
  `[Finite]` + `[Fact p.Prime]`; `Subgroup.index_eq_card : H.index = Nat.card (G ⧸ H)`.

### Next steps
- Compose into a solvable-normal-series length bound for order `p·q^k` groups.
- Wire `isSolvable_of_sylow_primePow_index` into the `S₅` obstruction for the
  reverse Abel–Ruffini bridge.
- The `G/C_G(c) ↪ (ZMod p)ˣ` conjugation-action sharpening (unchanged from prior).
