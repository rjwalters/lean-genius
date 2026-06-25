# sylow-theorems-oq-01-oq-02-oq-01 — Groups of order pq: the cyclic case

**Status:** completed (one direction).
**Lean file:** `proofs/Proofs/SylowTheoremOQ01OQ02OQ01.lean` (verified, 0-axiom, 3 theorems, 151 lines).

## Problem
Parent OQ asks: count isomorphism classes of groups of order `n = p·q` (`p > q` primes):
exactly **2** when `q ∣ (p−1)` (cyclic + nonabelian semidirect product), else **1** (cyclic only).

## What was proved (the `q ∤ (p−1)` direction)
- `card_sylow_eq_one_of_card_pq`: for **every** prime `r`, `Nat.card (Sylow r G) = 1`.
  - `r ∣ |G|` ⇒ `r ∈ {p, q}`; use `n_r ∣ p·q`, `r ∤ n_r` (`not_dvd_card_sylow`), `n_r ≡ 1 [MOD r]`
    (`card_sylow_modEq_one`). Coprimality gives `n_p ∣ q` (⇒ `n_p=1` since `q<p`) and `n_q ∣ p`
    (⇒ `n_q=1` unless `p ≡ 1 [MOD q]`, i.e. `q ∣ p−1`, excluded).
  - `r ∤ |G|` ⇒ every Sylow `r`-subgroup is `⊥` (an `r`-group of card `r^k ∣ p·q` with `r∤p·q`
    forces `k=0`), so `Subsingleton (Sylow r G)`.
- `isCyclic_of_card_pq`: `|G|=p·q` squarefree ⇒ `IsZGroup` (`IsZGroup.of_squarefree`); all Sylows
  normal (`normal_of_subsingleton`) ⇒ nilpotent (`isNilpotent_of_finite_tfae.out 3 0`); a finite
  nilpotent Z-group is cyclic (Mathlib instance).
- `unique_isoclass_of_card_pq`: two such groups are isomorphic (`mulEquivOfCyclicCardEq`).

## Key Mathlib lemmas
`card_sylow_modEq_one`, `not_dvd_card_sylow`, `Sylow.card_dvd_index`, `Subgroup.index_dvd_card`,
`Subgroup.card_subgroup_dvd_card`, `Sylow.ext`, `Subgroup.eq_bot_iff_card`, `IsPGroup.exists_card_eq`,
`Nat.squarefree_mul`, `IsZGroup.of_squarefree`, `isNilpotent_of_finite_tfae`,
`Sylow.normal_of_subsingleton`, instance `[Finite][IsZGroup][Group.IsNilpotent] ⇒ IsCyclic`,
`mulEquivOfCyclicCardEq`.

## Remaining (open)
The `q ∣ (p−1)` case (exactly 2 classes) needs an **isomorphism classification of semidirect
products** `ℤ/p ⋊ ℤ/q` — not in Mathlib (no `MulEquiv ↔ SemidirectProduct` recognition from a
normal complement, no semidirect iso-classification). This is the genuinely hard half; estimate
500–1000+ lines (RCF-free but requires building the nonabelian existence + uniqueness). Parent
`sylow-theorems-oq-01-oq-02` itself flags the count as "genuinely harder and remains open".

## Session note (2026-06-25, FRESH)
High contention: the tractable pool problems (stirling-Catalan, cayley cyclic-vector existence,
derangements EGF, pell index) were all locked by concurrent researchers mid-survey; centralizer and
banach-steinhaus need substantial unbuilt theory (dim C(M); Dirichlet kernel/Lebesgue constants).
Aristotle MCP down ("Resource not found"). Shipped the cyclic direction of sylow-pq as a complete
verified result. Build via host `lake env lean` (docker down).
