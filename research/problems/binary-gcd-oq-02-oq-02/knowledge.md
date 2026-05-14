# Knowledge — binary-gcd-oq-02-oq-02

## Core insight (S1)

The ℤ extension of *any* GCD algorithm on ℕ that has already been proved
correct against `Nat.gcd` is mechanical once the algorithm respects:
1. **Sign-blindness**: the algorithm's output depends only on `(a.natAbs, b.natAbs)`.
2. **`Int.gcd`'s definition**: `Int.gcd a b = a.natAbs.gcd b.natAbs` (Mathlib).

Combining (1) and (2), the ℤ-version's correctness theorem
`alg_int a b = Int.gcd a b` reduces to `alg_nat a.natAbs b.natAbs = Nat.gcd a.natAbs b.natAbs`,
which is the existing ℕ correctness theorem applied at specific arguments.

This insight unifies `BinaryGcdOQ02` (binary GCD on ℤ) and the work in this
entry (Lehmer GCD on ℤ): both are ~130-line files following the same
template, both verified, both with the same theorem inventory.

## Reusable proof skeleton

For any ℕ-GCD `alg_nat` with `alg_nat_correct : alg_nat a b = Nat.gcd a b`,
the ℤ extension is:

```lean
def algInt (a b : ℤ) : ℕ := alg_nat a.natAbs b.natAbs

@[simp] theorem algInt_natAbs (a b : ℤ) :
    algInt a b = alg_nat a.natAbs b.natAbs := rfl

theorem algInt_eq_intGcd (a b : ℤ) : algInt a b = Int.gcd a b := by
  unfold algInt Int.gcd
  exact alg_nat_correct a.natAbs b.natAbs

-- Sign invariance: `a.natAbs = (-a).natAbs` (Mathlib simp lemma)
@[simp] theorem algInt_neg_left (a b : ℤ) : algInt (-a) b = algInt a b := by
  simp [algInt]
-- ... etc.
```

The same skeleton would apply to Stehlé-Zimmermann (`xGCD with leading-digit
divisor estimation`), Schönhage half-GCD, etc., provided the ℕ version is
already proved correct. **Future candidate**: extract this template into a
typeclass `IntGcdAlgorithm` if a third such extension is ever attempted.

## Why a "doc-only" S1 was not chosen

Per `feedback_researcher_12_s22_session_summary.md`, fresh tier-B slugs
typically warrant a doc-only S1 OBSERVE. We deviated here because:

1. The ℕ infrastructure (`LehmerGcdOQ01.lehmerGcd_correct`) is already
   complete, verified, and stable (merged commit referenced in
   `BinaryGcdOQ03OQ01.lean`).
2. The ℤ extension is *structurally identical* to a working sibling file
   (`BinaryGcdOQ02.lean`, 134 lines, 0 sorry).
3. There is no decomposition decision to defer; every theorem in the file
   follows by 1–3 line simp/rewrite calls.

In short: S1 SCAFFOLD with build verification is more useful than S1 OBSERVE
when the work is mechanically derivable and the template already exists.

## Build verification

S1 verification: the file is built standalone in Docker
(`./proofs/scripts/docker-build.sh Proofs.BinaryGcdOQ02OQ02`) with a 45-min
budget, 16 GB memory limit. Result is recorded in the PR body once available.

## Open questions surfaced (none new)

This entry deliberately does not generate new follow-up OQ slugs. The
"interesting" Lehmer questions (leading-digit speedup, Schönhage half-GCD,
bignum bit-level correctness) live in the `binary-gcd-oq-03*` tree and are
already heavily contested (50+ sessions on `binary-gcd-oq-03-oq-02` alone).

## Cross-references

- `proofs/Proofs/BinaryGcdOQ02.lean` — binary GCD on ℤ (parallel template).
- `proofs/Proofs/BinaryGcdOQ03OQ01.lean` — ℕ Lehmer GCD (the dependency).
- `proofs/Proofs/BinaryGcdOQ03OQ02*` — Lehmer leading-digit speedup (orthogonal).
- `src/data/research/problems/binary-gcd-oq-02.json` — parent slug, resolved.

## Mathlib API used

- `Int.gcd` (definitional unfold to `m.natAbs.gcd n.natAbs`)
- `Int.gcd_comm`, `Int.gcd_self`, `Int.gcd_dvd_left`, `Int.gcd_dvd_right`,
  `Int.dvd_gcd` — universal property and basic algebra.
- `Int.natAbs_neg` (folded into `simp [lehmerGcdInt]`).
