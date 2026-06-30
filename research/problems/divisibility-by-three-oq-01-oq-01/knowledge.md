# Knowledge Base: divisibility-by-three-oq-01-oq-01

Insights accumulated during research on this problem.

**OQ**: "Extend to an automated *tactic* that generates and verifies divisibility
rules for arbitrary input divisors `d` coprime to a given base `b`."

Source: gallery entry `divisibility-by-three-oq-01` (general last-k-digits / digital
root theory). Significance 6, tractability 6.

---

## Problem Understanding

A "divisibility rule for `d` in base `b`" (with `gcd(b,d)=1`) is one of two classical
forms, both of which reduce an arbitrary `n` to a much smaller test quantity:

1. **Osculator / truncation rule.** Writing `n = b·q + r` with `q = n / b`,
   `r = n % b`, pick an osculator `c` with `b·c ≡ 1 (mod d)`. Then
   `d ∣ n ↔ d ∣ (q + c·r)`. The "subtract" variant uses `c'` with `b·c' ≡ -1`,
   i.e. `d ∣ n ↔ d ∣ (q − c'·r)`; this is the same theorem with osculator `−c'`.
   Examples (base 10): d=7 → c=−2, d=11 → c=−1, d=13 → c=4, d=17 → c=−5, d=19 → c=2.

2. **Digit-block (digit-sum) rule.** Let `k = ord_d(b)` be the multiplicative order
   of `b` mod `d` (smallest `k>0` with `b^k ≡ 1 (mod d)`). Then
   `d ∣ n ↔ d ∣ (digits (b^k) n).sum` — group the base-`b` digits into blocks of
   length `k` and sum the blocks. The familiar digit-sum rule for 3 and 9 is the
   `b=10, d∈{3,9}, k=1` case (since `10 ≡ 1`); casting-out-elevens is `d=11, k=2`.

The OQ asks to turn this classical recipe into a Lean **tactic** that, given `b` and
`d`, *generates* the appropriate rule (computes `c` or `k`) and *verifies* it
(produces a checked proof term).

---

## Insights

### The underlying mathematics is ALREADY formalized in the gallery

This is the central finding of the survey. The OQ is mostly already done at the
theorem level; what is missing is (A) one mechanical generalization and (B) the
metaprogramming layer.

**Osculator family — proven, base 10 only**
(`proofs/Proofs/DivisibilityTruncationGeneralOQ01.lean`):

```lean
theorem unified_osculator (d : ℕ) (c : ℤ) (n : ℕ)
    (hcop : IsCoprime (d : ℤ) 10) (hc : (d : ℤ) ∣ 10 * c - 1) :
    (d : ℤ) ∣ n ↔ (d : ℤ) ∣ (↑(n / 10) + c * ↑(n % 10))
```

plus `neg_osculator_from_unified` (negative osculator as the `−c` special case) and
the per-prime instances `seven_unified`, `eleven_unified`, `thirteen_unified`,
`seventeen_unified`, `nineteen_unified`. The proof is the single algebraic identity
`10·(n/10 + c·(n%10)) = n + (10c − 1)·(n%10)`, transferred through coprimality.

**Digit-block family — proven, ARBITRARY base b**
(`proofs/Proofs/DivisibilityRulesOQ01OQ01OQ01.lean`, Part V):

```lean
theorem digit_block_rule_base_b (b d : ℕ) (hd : 1 < d) (hcop : Nat.Coprime d b)
    (k : ℕ) (hk : orderOf (b : ZMod d) ∣ k) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits (b ^ k) n).sum
```

plus `period_iff_orderOf_dvd_base_b`, `orderOf_base_b_is_minimal_period`,
`orderOf_pos_of_coprime` (Euler's theorem gives finite positive order). So the
digit-block half of the OQ is *fully general in the base already*.

Note: the existing `src/data` `leanFiles`/`relatedProofs` for this slug point only at
the `DivisibilityByThreeOQ01*` parent. The load-bearing prior art is actually in
`DivisibilityTruncationGeneral*.lean` and `DivisibilityRulesOQ01OQ01OQ01.lean`.

### Gap A — base-`b` osculator (mechanical port, ~15 lines)

The osculator theorem is the only rule family still hard-coded to base 10. The
general statement is a verbatim port:

```lean
theorem unified_osculator_base_b (b d : ℕ) (c : ℤ) (n : ℕ)
    (hcop : IsCoprime (d : ℤ) (b : ℤ)) (hc : (d : ℤ) ∣ (b : ℤ) * c - 1) :
    (d : ℤ) ∣ n ↔ (d : ℤ) ∣ (↑(n / b) + c * ↑(n % b))
```

Proof is identical to `unified_osculator` with the key identity
`b·(n/b + c·(n%b)) = n + (b·c − 1)·(n%b)`, obtained from `Nat.div_add_mod n b` cast to
ℤ (the base-10 file's `div_mod_cast` helper, generalized). Needs `0 < b` only so that
`n/b`, `n%b` behave; for `b ≥ 2` (the only interesting case) it is automatic.

### Gap B — the tactic itself (the actual OQ ask)

No tactic/metaprogram exists; every instance above is hand-instantiated with `c` (or
`k`) supplied by the author and the side conditions closed by `decide`/`native_decide`.
A tactic `divisibility_rule b d` (an `elab`/macro) closes the OQ by automating:

1. Check `Nat.Coprime d b` (decidable) → discharge by `decide`; fail with a clear
   message otherwise.
2. **Choose the rule and compute its parameter, externally (in meta code):**
   - If `b % d = 1` (order 1): pure digit-sum rule.
   - Osculator route: compute `c = b⁻¹ mod d` via extended Euclid (`Nat.gcdA b d`),
     then pick the signed representative of smaller magnitude (`c` vs `c − d`) to get
     the prettier "+" or "−" rule. Emit `unified_osculator_base_b b d c n …`.
   - Digit-block route: search the least `k > 0` with `b^k % d = 1` (the period). Emit
     `digit_block_rule_base_b b d _ _ k _ n`.
3. Discharge the numeric side goals — `(d:ℤ) ∣ b*c − 1`, `b^k % d = 1`,
   `Nat.Coprime d b`, `1 < d` — by `decide` / `native_decide` / `norm_num`.

In Lean the produced proof term **is** the verification, so "generate" and "verify"
are one step: the tactic builds the term; the kernel checks it.

### KEY subtlety — `orderOf` is noncomputable

`orderOf (b : ZMod d)` cannot be evaluated by `decide`/`native_decide` (explicit file
comment at `DivisibilityRulesOQ01OQ01OQ01.lean:146`). Consequently the tactic must NOT
try to compute the order symbolically. Instead it:
  (i)  searches in meta code for the least `k>0` with `b^k % d = 1` (plain `Nat`
       arithmetic, fast), then
  (ii) supplies that `k` explicitly and discharges the hypothesis
       `orderOf (b : ZMod d) ∣ k` *indirectly* via
       `(period_iff_orderOf_dvd_base_b b d (by norm_num) k).mp (by native_decide)`,
       where the `native_decide` proves the computable fact `b^k % d = 1`.

This "search for the witness period externally, then verify it computationally and
convert to the order statement" pattern is exactly what the manual examples at
`DivisibilityRulesOQ01OQ01OQ01.lean:150–165` already do by hand; the tactic just
automates the witness search and term assembly. This is the one genuinely non-obvious
piece of the design.

---

## Dead Ends

- **Evaluating `orderOf` directly inside the rule / making the period computable.**
  Blocked by the noncomputability of `orderOf` (Mathlib). The witness-and-verify route
  above (least-`k` search + `native_decide` on `b^k % d = 1` + `period_iff_orderOf_dvd_base_b`)
  is the correct workaround and is already used manually in the gallery.

- **Treating "automated tactic" as new mathematics.** It is not: both rule theorems
  exist (digit-block already base-general; osculator a one-port-away from base-general).
  The OQ's remaining content is engineering — a base-`b` port plus an elaboration-layer
  decision/term-construction tactic — not a new theorem. (Same shape as the
  "no Big-O cost model in Mathlib" judgement recorded for the Garner / binary-GCD OQs:
  identify which half of the question is genuine new math and which is tooling.)

---

## Status

SURVEY complete (OBSERVE → ORIENT). Resolution is fully specified on paper:
- Gap A: `unified_osculator_base_b` — mechanical port of the existing base-10 theorem.
- Gap B: `divisibility_rule` tactic — extended-Euclid osculator + least-period search,
  side goals via `native_decide`, period hypothesis via `period_iff_orderOf_dvd_base_b`.

ACT (writing + building the Lean) is **build-gated**: needs a Docker `lake build` to
confirm the new theorem and the `elab`/macro compile. Deferred during the 2026-06-13
verification blackout (Docker daemon down — `docker info` exit 124; Aristotle backend
404 — both confirmed live this session). No Lean committed.
