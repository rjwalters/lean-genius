# Problem: Burnside Counting — Prove rotatedIndex_add Composition Law

**ID**: burnside-counting-oq-01
**Category**: extension
**Tractability**: challenging
**Source Proof**: burnside-counting (Burnside's Lemma and Necklace Counting)
**Tags**: combinatorics, group-theory, counting, orbits, necklaces, group-actions, polya-enumeration

## Problem Statement

Prove the `rotatedIndex_add` composition law in Lean 4:

```
(a + n - b) % n
```

This is the modular arithmetic identity that underlies the rotation group action in Burnside's Lemma for necklace counting. Specifically:

**Goal**: Formalize that rotation by `a` followed by rotation by `b` (in a necklace of `n` beads) equals rotation by `(a + n - b) % n`, as a Lean theorem about `rotatedIndex`.

## Formal Statement Target

```lean
theorem rotatedIndex_add (n a b : ℕ) (hn : 0 < n) :
    rotatedIndex n a (rotatedIndex n b k) = rotatedIndex n ((a + b) % n) k
-- or the inverse composition variant:
theorem rotatedIndex_neg (n a b : ℕ) (hn : 0 < n) :
    rotatedIndex n ((a + n - b) % n) k = ...
```

## Context

Source proof: `burnside-counting` (Burnside's Lemma and Necklace Counting)

In the gallery proof of Burnside's Lemma for necklace counting, the key group action is rotation of a necklace of `n` beads. The `rotatedIndex` function maps bead position `k` under rotation by `a` positions: `rotatedIndex n a k = (k + a) % n`.

The composition law `(a + n - b) % n` appears in the group structure of the rotation action: it captures the inverse/composition in the cyclic group ℤ/nℤ.

## Why This Matters

1. **Concrete gap**: The gallery proof of Burnside's lemma may have this as a `sorry` or as an axiom — formalizing it would reduce the axiom count.
2. **Modular arithmetic infrastructure**: The proof would exercise Mathlib's `Nat.add_mod`, `Nat.sub_mod`, and cyclic group lemmas.
3. **Group action structure**: Formalizing this unlocks the full machine-checked proof of Burnside's lemma.

## Mathematical Analysis

The key identity: if `rotatedIndex n a k = (k + a) % n`, then:
- `rotatedIndex n a (rotatedIndex n b k) = ((k + b) % n + a) % n = (k + a + b) % n`
- The "inverse" rotation by `(n - b) % n` gives: `rotatedIndex n (n - b) (rotatedIndex n b k) = k`

The `(a + n - b) % n` formula computes the rotation that "undoes" rotation by `b` then applies rotation by `a`. In ℤ/nℤ terms: `a - b ≡ a + n - b (mod n)`.

## Mathlib Resources

- `Nat.add_mod`, `Nat.mod_mod_of_dvd`: modular arithmetic
- `ZMod n` or `Fin n`: the cyclic group ℤ/nℤ structure
- `Nat.sub_mod`: modular subtraction
- `Finset.sum_mod`: for the Burnside orbit counting

## Research Phase

OBSERVE

## Suggested First Steps

1. Read `src/data/proofs/burnside-counting/` to see the existing proof structure
2. Find `rotatedIndex` definition in the Lean source
3. Check if the composition law is currently axiomatized or has a `sorry`
4. Try `omega` or `ring` after unfolding modular arithmetic definitions
5. Look for analogous cyclic group lemmas in Mathlib (`ZMod`, `Fin.cyclic`)
