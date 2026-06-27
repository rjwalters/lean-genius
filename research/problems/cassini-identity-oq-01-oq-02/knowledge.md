# Knowledge Base: cassini-identity-oq-01-oq-02

Fibonacci addition formula from the Q-matrix factorisation `Q^{m+n} = Q^m Q^n`.

---

## Problem Understanding

Parent `cassini-identity-oq-01` (`Proofs/CassiniIdentityOQ01.lean`, verified) proves
Cassini's identity from `det(Q^{n+1}) = (det Q)^{n+1}` with `Q = !![1,1;1,0]`. Its second
open question: can the **addition formula** be read off directly from the entries of
`Q^{m+n} = Q^m Q^n` (associativity of matrix multiplication), packaging several Fibonacci
identities as corollaries of one factorisation, with no separate induction per identity?

---

## Session 2026-06-27 (researcher-9) — SOLVED the OQ [VERIFIED, 0-axiom]

**Outcome**: BUILD + new gallery entry. The open question is answered: the addition
formula is literally an entry of `Q^{(m+1)+(n+1)} = Q^{m+1} Q^{n+1}`.

### Built `Proofs/CassiniIdentityOQ01OQ02.lean` (121 LOC, 1 def + 5 theorems)
- `Q : Matrix (Fin 2) (Fin 2) ℤ := !![1,1;1,0]`.
- `Q_pow_succ (n) : Q^(n+1) = !![F(n+2),F(n+1);F(n+1),F(n)]` — **the only induction**.
  Shifted exponent `n+1` avoids the `F(-1)` index. Succ step: `rw [pow_succ, ih,
  show Q = !![(1:ℤ),1;1,0] from rfl, Matrix.mul_fin_two]`, then per-entry
  `simp only [cons_val', cons_val_fin_one, of_apply, empty_val',
  show k+1+2 = k+3 from rfl, show k+1+1 = k+2 from rfl] <;> push_cast <;>
  simp only [F2, F3, mul_one, mul_zero, add_zero] <;> ring`, where `F2,F3` are the cast
  recurrences `(F(k+2):ℤ)=F k+F(k+1)` (`exact_mod_cast Nat.fib_add_two`) and
  `(F(k+3):ℤ)=F(k+1)+F(k+2)` (`exact_mod_cast (Nat.fib_add_two (n:=k+1))`).
- `Q_factor (m n)` (private): closed-form of `pow_add` — `!![F(m+n+3),..]= !![F(m+2),..]*
  !![F(n+2),..]`. Built by `rw [← hexp, ← pow_add]` (hexp: (m+1)+(n+1)=(m+n+1)+1 by ring),
  `rw [Q_pow_succ, Q_pow_succ, Q_pow_succ]`, then `simpa only [show ...=... from rfl]`
  normalising the LHS indices.
- `fib_add_matrix (m n) : F(m+n+1) = F(m+1)F(n+1) + F(m)F(n)` — the `(2,2)` entry
  (recovers Mathlib `Nat.fib_add`). `congrFun (congrFun (Q_factor m n) 1) 1`, then
  `simp only [cons_val', cons_val_zero, cons_val_one, cons_val_fin_one, of_apply,
  empty_val', mul_apply, Fin.sum_univ_two] at h; exact_mod_cast h`.
- `fib_add_offdiag (m n) : F(m+n+2) = F(m+2)F(n+1) + F(m+1)F(n)` — the `(1,2)` entry
  (the problem's addition formula). Same recipe at index `(0,1)`.
- `cassini_matrix (n) : (F(n+2):ℤ)*F(n) - (F(n+1):ℤ)^2 = (-1)^(n+1)` — `Matrix.det_pow`
  + `det_fin_two_of` on `Q^(n+1)` and on `Q`; `rw [sq, hdet]; norm_num`.

### Verification
`lake env lean` (worktree proofs dir): EXIT 0, no warnings. `#print axioms` on all four
public theorems = `[propext, Classical.choice, Quot.sound]` only — 0 counting-axioms, no
`sorryAx`/`Lean.ofReduceBool`. Gallery `meta.json` + `annotations.json` created (status
verified, badge original, axiomCount 0). meta/annotations JSON validated.

### GOTCHAs
- Build in the **worktree** proofs dir (`.loom/worktrees/researcher-9/proofs`), NOT the
  main repo `proofs/` — concurrent agents edit there and clobber. Worktree `proofs/.lake`
  symlinks to main's olean cache so `lake env lean` resolves Mathlib fine.
- `rw [Q]` does NOT work for a plain `def`; use `rw [show Q = !![(1:ℤ),1;1,0] from rfl]`.
- `Proofs.lean` is **auto-generated** (`.lean/scripts/generate-proofs-imports.sh`,
  "do not edit manually") — ~495 proof files are unregistered; the generator picks up new
  files. Do not hand-edit it (also avoids merge conflicts).
- Index normalisation: `Nat.fib_add_two` matches `fib (?+2)` syntactically, so `fib(k+3)`
  (numeral 3) is NOT rewritten by it — supply explicit cast `have`s (F2/F3) and normalise
  `k+1+1→k+2`, `k+1+2→k+3` via `show ... from rfl` (they are defeq).
- `congrFun (congrFun matEq i) j` reads off a matrix-equation entry (Matrix is a function
  type synonym), then simp evaluates `!![..] i j`.

### Files
- `proofs/Proofs/CassiniIdentityOQ01OQ02.lean` (new, verified 0-axiom)
- `src/data/proofs/cassini-identity-oq-01-oq-02/{meta.json,annotations.json}` (new entry)

### Next Steps
- d'Ocagne `F_m F_{n+1} - F_{m+1}F_n = (-1)^n F_{m-n}` from off-diagonal entries of a
  product (needs `Q^{-n}` or a det-of-product argument).
- Catalan identity via `det(Q^{n-r} Q^{2r})`.
