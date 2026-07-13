# Knowledge: burnside-counting-oq-01

## Source Proof Context

- Source: `burnside-counting` gallery proof (Burnside's Lemma and Necklace Counting)
- `rotatedIndex n a k = (k + a) % n` — rotation of bead at position `k` by `a` steps
- The composition law `(a + n - b) % n` appears in the group action structure

## Mathematical Facts

- `rotatedIndex n a (rotatedIndex n b k) = (k + a + b) % n` (by Nat.add_mod properties)
- In ℤ/nℤ: `-b ≡ n - b (mod n)`, so `a - b ≡ a + n - b (mod n)`
- This is a statement about the cyclic group action on `Fin n`

## Mathlib Candidates

- `Nat.add_mod_right`, `Nat.add_mod`, `Nat.mod_add_div`
- `ZMod.add_comm_group`, `Fin.add_def`
- `omega` tactic may close this after unfolding

## Open Questions

- Is `rotatedIndex` defined in the gallery Lean file or in Mathlib?
- Is there a `sorry` for this in the current proof?
- Does `omega` work for modular composition proofs?
