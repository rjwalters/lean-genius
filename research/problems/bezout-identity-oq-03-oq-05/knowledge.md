# Knowledge Base: bezout-identity-oq-03-oq-05

Garner's mixed-radix CRT reconstruction — formalize as an executable extension of
the gallery's two-modulus `crtInt` and prove it equals the CRT solution.

---

## Session 2026-06-15 (S1) — FRESH ORIENT (build-free; Docker + Aristotle blackout)

**Mode**: FRESH · **Outcome**: ORIENT — pinned the exact recurrence, the reduction
route to `crtInt`, the Mathlib/in-repo bearer map, and a Lean ACT skeleton. Validated
the whole construction with an exact-arithmetic certificate (`verify_garner.py`,
**81,774 checks PASS**). No Lean file written (cannot build-verify under blackout;
writing blind unverifiable Lean would be false progress).

### The object to formalize (pinned recurrence)

Pairwise-coprime moduli `m_1..m_k`, residues `r_1..r_k`. Garner builds the unique
`x ∈ [0, ∏ m_i)` in **mixed-radix** form:

    x = v_1 + v_2·m_1 + v_3·m_1 m_2 + ... + v_k·m_1···m_{k-1}

with the **sequential** coefficient recurrence (certified exact in `verify_garner.py`):

    v_1 = r_1                                    mod m_1
    v_j = (r_j - x_{j-1}) · (P_{j-1})^{-1}        mod m_j

where `x_{j-1} = v_1 + ... + v_{j-1}·m_1···m_{j-2}` is the partial reconstruction and
`P_{j-1} = m_1···m_{j-1}` the partial product. Crucially `(r_j - x_{j-1})·P_{j-1}^{-1}`
is taken **mod m_j**, and the inverse is `(P_{j-1} mod m_j)^{-1}` which exists because
`m_j` is coprime to every earlier modulus ⟹ coprime to their product `P_{j-1}`.

### The clean Lean shape: a `List.foldl` carrying `(x, P)`

Each step needs only the running value `x` and running product `P`; the digit is
`v = (r - x) · P⁻¹ mod m`, then `x := x + v·P`, `P := P·m`. This is a single left fold
over `List (ℤ × ℤ)` of `(modulus, residue)` pairs — no recursion bookkeeping beyond the
accumulator, and termination is free (`foldl` over a finite list).

### The REDUCTION route for the correctness proof (do NOT re-derive from scratch)

The Garner fold is **provably equal** to iterating the gallery's two-modulus
`crtInt` (BezoutIdentityOQ03.lean:232):

    crtInt m n a b := a·n·Int.gcdB m n + b·m·Int.gcdA m n
    crtInt_mod_left  : Int.gcd m n = 1 → crtInt m n a b ≡ a [ZMOD m]   (line 236)
    crtInt_mod_right : Int.gcd m n = 1 → crtInt m n a b ≡ b [ZMOD n]   (line 248)

Define `crtFold` = foldl combining the running solution `x` (mod running product `P`)
with the next `(m_j, r_j)` via `crtInt P m_j x r_j`. The certificate confirms
**Garner x == crtFold x == direct CRT** on all 81,774 systems. So the correctness
theorem decomposes as:

  (T1) `garner pairs ≡ r_i [ZMOD m_i]` for each i, and `0 ≤ garner pairs < ∏ m_i`.
  (T2) `garner pairs = crtFold pairs`  (induction on the list; the mixed-radix digit
       `v_j·P_{j-1}` equals the crtInt lift increment).
  (T3) `crtFold` congruences come directly from `crtInt_mod_left/right` by induction,
       reusing the proven two-modulus lemmas — this is where the existing gallery work
       is leveraged and almost no new arithmetic is needed.

Easiest Lean path: prove (T1) **directly** for the foldl (each step fixes residue mod
`m_j` and preserves earlier residues because the increment `v·P` is `≡ 0` mod every
earlier modulus — `P = m_1···m_{j-1}` is divisible by each), then (T2)/(T3) optional
for the "matches crtInt" clause the OQ asks for.

### Bearer map (pin @ current Mathlib in repo)

| Need | Bearer |
|------|--------|
| two-modulus CRT value + congruences | in-repo `crtInt`, `crtInt_mod_left`, `crtInt_mod_right` (BezoutIdentityOQ03.lean) |
| Bézout coefficients (for modular inverse) | `Int.gcdA`, `Int.gcdB`, `Int.gcd_eq_gcd_ab` |
| modular inverse over ℤ/ZMod | `ZMod.inv`, or `Int.gcdA m_j P` reduced mod `m_j` |
| `x + v·P ≡ x [ZMOD m_i]` for `i<j` | `m_i ∣ P` ⟹ `Int.ModEq` via `Int.modEq_iff_dvd` + `dvd_mul` |
| coprimality of `P_{j-1}` to `m_j` | `Nat.Coprime.prod_left` / `IsCoprime.prod_left` over the list |
| existential CRT cross-check | `ZMod.chineseRemainder`, `Nat.chineseRemainder` |

### Certificate (`verify_garner.py`, stdlib, exact integers — 81,774 PASS)

- **[A]** 76,274 exhaustive/sampled small systems (k=2,3), with independent brute-force
  uniqueness search over `[0,P)` for `P ≤ 600`.
- **[B]** 4,000 randomized large pairwise-coprime systems (k up to 7; primes & prime
  powers up to 83).
- **[C]** 1,000 order-independence checks (Garner's `x` is invariant under permuting the
  modulus list — a sanity invariant the Lean statement should reflect: the result depends
  on the *set* of congruences, not the fold order).
- **[D]** 500 exact mixed-radix expansion identity checks (`x = Σ v_j·∏_{<j} m_i`).
- All assert **Garner == crtInt-fold == direct CRT**, congruences hold, digits in range
  `0 ≤ v_j < m_j`, value in `[0, ∏ m_i)`.

### Decision / next action (ACT, once Docker returns)

Write `BezoutIdentityOQ03OQ05.lean`:
1. `def garner : List (ℤ × ℤ) → ℤ` as the `(x,P)` foldl above (returns `x`).
2. `theorem garner_modEq (pairs) (hcop : pairwise coprime moduli) (hpos) :
    ∀ (m,r) ∈ pairs, garner pairs ≡ r [ZMOD m]` — induction on list, using `m_i ∣ P_{j}`.
3. `theorem garner_lt_prod` : `0 ≤ garner pairs < ∏ moduli` (reduce final fold mod P).
4. (optional, satisfies the OQ's "matches crtInt" clause) `theorem garner_eq_crtFold`.
Reuse `crtInt_mod_left/right` for the two-modulus engine; no new heavy arithmetic.

**Risk note**: the fiddly part is the pairwise-coprimality bookkeeping for partial
products (`IsCoprime.prod_left`) and the `ℤ`/`ZMod` inverse plumbing — exactly the kind
of thing that must be build-checked, hence deferred to an ACT session with Docker up.

---

## Dead Ends

- None yet. (Avoid: re-proving CRT from scratch — the gallery's `crtInt` two-modulus
  lemmas already discharge the congruence core; Garner is a fold on top of them.)
