# Knowledge Base: van-der-waerden-first-moment-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Sharpen the base entry's loose `n²` count of fitting length-`k` APs in `[n]` and feed
the sharper count through the verified Property-B engine. The entry was already SOLVED
(0 sorries, 0 axioms): exact parameter-box count `∑_{d=1}^{n}(n-(k-1)d)`, factor-2 bound
`2(k-1)|family| ≤ n²` via telescoping-of-squares, widened lower bound `n² < 2(k-1)·2^(k-1)`.

---

## Insights

- **Exactness via injectivity (researcher-1, 06-30).** The prior `card_vdwFamily_le_sum`
  was only `≤` (it used `Finset.card_image_le`). The parametrization `(a,d) ↦ vdwAP n a d k`
  is in fact INJECTIVE on the fitting box for `k ≥ 2`, so the count is EXACT:
  `card_vdwFamily_eq_sum : |family| = ∑_{d=1}^{n}(n-(k-1)d)`.
  - Mechanism: a fitting positive-step AP is strictly increasing, so as a `Finset (Fin n)`
    its minimum point is `↑a` and its maximum is `↑(a+(k-1)d)`. From the set one recovers
    both extremes, hence `a` and (cancelling `k-1`) the step `d`.
  - Lean recipe (avoids `min'`/`max'` machinery entirely): prove four small lemmas —
    `↑a ∈ AP` (i=0 term), `↑(a+(k-1)d) ∈ AP` (i=k-1 term), `↑a ≤ x` for all `x∈AP`,
    `x ≤ ↑(a+(k-1)d)` for all `x∈AP` — then in the `InjOn` proof use `rw [hpq]`/`rw [← hpq]`
    to move a point of one AP into the other, and `le_antisymm` of the two ≤-facts gives
    `↑a₁ = ↑a₂` and `↑(a₁+(k-1)d₁) = ↑(a₂+(k-1)d₂)`. `congrArg Fin.val` + `Fin.val_cast_of_lt`
    drops to ℕ; `omega` + `Nat.eq_of_mul_eq_mul_left` finishes.
  - Key API: `Fin.le_iff_val_le_val` (`a ≤ b ↔ (a:ℕ) ≤ b`), `Fin.val_cast_of_lt`
    (`a < n → (↑a:Fin n).val = a`, needs `[NeZero n]`), `Finset.card_image_of_injOn`.
- `card_vdwFamily_ge : n - (k-1) ≤ |family|` from `Finset.single_le_sum` on the `d=1`
  fiber — crude but exact; shows the count is positive when `k-1 < n`.

## Reusable techniques

- To extract parameters from an injective `Finset`-valued parametrization, characterize
  the min/max ELEMENT via membership + a universal ≤ bound, then `le_antisymm` instead of
  invoking `Finset.min'`/`max'` (which drag dependent nonempty proofs through every rewrite).
- `1 ≤ n` for `[NeZero n]` over ℕ: `NeZero.one_le`.

---

## Dead Ends / Deferred

- Matching `Θ(n²/(k-1))` LOWER bound on `|family|` (to certify the factor-2 upper bound is
  order-sharp) was deferred: needs either a closed form of the truncated triangular sum
  (entangles the floor `⌊(n-1)/(k-1)⌋`) or a reverse telescoping with a per-step correction.
  Only the crude `n-(k-1)` lower bound was proved this session.

## Infra notes

- Docker daemon was DOWN this session. Host fallback worked:
  `cd proofs && ./bin/lake env lean Proofs/VanDerWaerdenFirstMomentOQ01.lean`
  (cache already populated). `#print axioms` confirmed only propext/Classical.choice/Quot.sound.
