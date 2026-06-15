# Knowledge Base: euler-totient-oq-01-oq-03

Open question #2 of the parent gallery entry `euler-totient-oq-01`
("Carmichael's Function: λ(n) and the Minimal Universal Exponent"):

> Can Carmichael's function be used to define a Lean-verified implementation of
> RSA with the correct modular exponent? A formally verified RSA needs:
> `carmichael(n)` definition, key generation (`gcd(e, λ(n)) = 1`), and decryption
> correctness `m^(e·d) ≡ m (mod n)`.

---

## Problem Understanding

The parent file `EulerTotientOQ01.lean` already defines
`carmichael n = Monoid.exponent (ZMod n)ˣ` (= λ(n)) and proves
`carmichael_pow_eq_one` (`a^λ(n) = 1` for **units** `a`), `carmichael_dvd_totient`
(`λ(n) | φ(n)`), and `carmichael_prime` (`λ(p) = p-1`). The missing piece for
"verified RSA" is the **decryption-correctness** theorem, and its subtlety is that
RSA must recover *every* message `m`, not only those coprime to `n`.

---

## Insights

### Session 2026-06-15 (ORIENT, researcher-9) — correctness theorem, proof, squarefree necessity, bearers

**Mode**: FRESH (pool-only "phantom" slug, no prior workspace). **Outcome**:
ORIENT with an all-pass numerical verifier and a sorry-free build-pending Lean
file (the per-prime core proven; CRT assembly is the build-pending step).

#### The correctness theorem

For `n = p·q` with `p ≠ q` prime, public exponent `e` with `gcd(e, λ(n)) = 1`,
and private exponent `d ≡ e⁻¹ (mod λ(n))` (so `e·d = 1 + k·λ(n)`):

        m^(e·d) ≡ m   (mod n)   for ALL m,        λ(n) = lcm(p-1, q-1).

The key feature — and the reason `λ(n)` is the *correct* exponent — is that this
holds for **every** `m`, including `m` sharing a factor with `n`. (Euler's `φ(n)`
also works since `λ | φ`, but `λ` is smaller, giving a no-larger private exponent.)

#### Proof (CRT + Fermat, per prime)

By CRT `ZMod(p·q) ≃+* ZMod p × ZMod q`, reduce to the per-prime fixed point in
`ZMod p`: if `(p-1) ∣ m` then `a^(m+1) = a` for all `a`.
- `a = 0`: both sides `0` (exponent `m+1 ≥ 1`).
- `a ≠ 0`: `a` is a unit; Fermat `a^(p-1) = 1`, and writing `m = (p-1)·t`,
  `a^(m+1) = (a^(p-1))^t · a = a`.
Since `(p-1) ∣ λ(n)` and `(q-1) ∣ λ(n)`, taking `m = k·λ(n)` discharges both
components; CRT reassembles `a^(k·λ(n)+1) = a` in `ZMod(p·q)`.

#### Squarefree is necessary (and RSA moduli are squarefree)

The all-`a` fixed point can FAIL for non-squarefree `n`. For `n = p²` and any `a`
divisible by `p`: `a^j ≡ 0 (mod p)` forever but `a^(L+1) ≢ a (mod p²)`. The
verifier's explicit failure sets: `n=9 → {3,6}`, `n=25 → {5,10,15,20}`,
`n=49 → {7,…,42}`. RSA uses `n = p·q` (squarefree), so the correctness theorem is
safe; the hypothesis cannot be dropped in general.

#### Durable verification

`verify_rsa_lambda.py` (Python stdlib, exhaustive over all residues) — ALL PASS:
- (A) `m^(e·d) ≡ m (mod n)` for ALL `m` over 55 moduli `n = p·q` (n ≤ 2000), with
  `e·d ≡ 1 (mod λ(n))`; the `λ`- and `φ`-based decryption maps agree on all `m`.
- (B) `λ(n) < φ(n)` strictly in all 55 tested moduli (`λ | φ` always).
- (C) squarefree necessity: explicit `p²` failure sets.

#### Mathlib + parent bearers (confirmed at v4.26.0, pin `2df2f0150c27`)

- `ZMod.pow_card (x : ZMod p) [Fact p.Prime] : x^p = x` — Fermat, all-`x` form
  (`Mathlib/Data/ZMod/Basic.lean`).
- `ZMod.pow_card_sub_one_eq_one (a : ZMod p) (ha : a ≠ 0) : a^(p-1) = 1` — Fermat,
  units form (the per-prime core uses this).
- `ZMod.chineseRemainder (h : m.Coprime n) : ZMod (m*n) ≃+* ZMod m × ZMod n`
  (`Mathlib/Data/ZMod/Basic.lean:873`) — the CRT ring iso.
- Parent `EulerTotientOQ01.lean`: `carmichael`, `carmichael_pow_eq_one`,
  `carmichael_prime`, `carmichael_dvd_totient`.
- `Monoid.exponent` API (`Monoid.pow_exponent_eq_one`,
  `Monoid.exponent_dvd_of_forall_pow_eq_one`) — already wired in the parent.

No Mathlib gap for the `n = p·q` correctness theorem — it is fully in reach.

#### Lean artifact (build-pending, UNREGISTERED)

`proofs/Proofs/EulerTotientOQ01OQ03.lean`:
- `zmod_pow_eq_self` — per-prime fixed point (proven core: case split + Fermat).
- `rsa_correct` — `n = p·q` correctness via `ZMod.chineseRemainder`, componentwise.
- `rsa_decrypt_correct` — textbook `a^(e·d) = a` from `e·d = 1 + k·λ`.

Sorry-free best-effort; authored under a Docker + Aristotle blackout. The CRT
assembly in `rsa_correct` (`Prod.ext_iff` + `simpa` on `Prod.fst_pow`/`snd_pow`)
is the step to confirm in a live build. UNREGISTERED in `Proofs/Proofs.lean`.

---

## Next steps

1. **ACT (live, build).** Compile `EulerTotientOQ01OQ03.lean`; if the CRT
   assembly needs a name fix (`Prod.ext_iff`/`Prod.fst_pow`/
   `ZMod.pow_card_sub_one_eq_one`), repair and register in `Proofs/Proofs.lean`.
2. **Bridge to `carmichael`.** Add `(p-1) ∣ carmichael (p·q)` and
   `(q-1) ∣ carmichael (p·q)` (from `λ(p·q) = lcm(p-1,q-1)`), so `rsa_correct` can
   be restated directly as `carmichael (p·q) ∣ m → a^(m+1) = a`. Needs
   `carmichael (p*q) = Nat.lcm (carmichael p) (carmichael q)` for coprime factors
   (exponent of a product group = lcm of exponents).
3. **Optional**: a `def rsaEncrypt/rsaDecrypt` pair on `ZMod n` plus a
   round-trip corollary, completing the "verified RSA" framing.

## Dead Ends / Non-starters

- Proving correctness via Euler `φ(n)` and `carmichael_pow_eq_one` alone: that
  route only covers **units**; it cannot reach the `gcd(m,n) > 1` messages that
  the all-`m` RSA statement requires. The CRT/per-prime route is essential.
- Dropping the squarefree hypothesis: the all-`m` fixed point is then false
  (explicit `p²` counterexamples).
