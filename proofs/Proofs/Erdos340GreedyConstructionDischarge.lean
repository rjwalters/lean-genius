/-
# Erdős #340 — Greedy (Mian–Chowla) Sidon construction: axiom discharge

This file constructs the greedy Sidon sequence *explicitly* and proves it strictly
increasing with every initial segment Sidon. It thereby discharges the three
`greedySidonSeq*` existence axioms currently declared in `Erdos340GreedySidon.lean`:

* `axiom greedySidonSeq : ℕ → ℕ`
* `axiom greedySidonSeq_strictMono : StrictMono greedySidonSeq`
* `axiom greedySidonSeq_isSidon (n) : IsSidon (image greedySidonSeq (range (n+1)))`

The construction reuses the already-verified extension lemmas
`sidon_insert_of_large` and `sidon_exists_extension` from `Erdos340GreedyExtension.lean`
(merged in PR #25087). The well-definedness obligation — that a finite Sidon set can
always be extended by a strictly larger element while staying Sidon — is exactly
`sidon_exists_extension`, so the greedy rule never gets stuck.

## Status

This is an UNREGISTERED orphan companion file (not in `Proofs.lean`). It carries zero
gallery-build risk: nothing imports it. Once verified with the Docker build wrapper, the
construction below should be inlined into `Erdos340GreedySidon.lean`, replacing the three
`greedySidonSeq*` axioms with these theorems (set `def greedySidonSeq := greedySeq`).

The open growth conjecture `|A ∩ [1,N]| ≫ N^{1/2−ε}` (Erdős #340) is untouched.
-/

import Proofs.Erdos340GreedyExtension

namespace Erdos340

/-- `IsSidon` is decidable for a finite set: the four quantifiers are effectively bounded
by membership in `A`. The bounded form matches `IsSidon` after reordering the binders. -/
instance instDecidableIsSidon (A : Finset ℕ) : Decidable (IsSidon A) :=
  decidable_of_iff
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d)
    ⟨fun h a b c d ha hb hc hd => h a ha b hb c hc d hd,
     fun h a ha b hb c hc d hd => h a b c d ha hb hc hd⟩

open Classical in
/-- The next greedy term after a set `S` with strict lower bound `b`: the smallest `m > b`
that keeps the set Sidon. (Junk value `b + 1` if none exists; `nextSidon_spec` shows that
case never arises when `S` is Sidon.) -/
noncomputable def nextSidon (S : Finset ℕ) (b : ℕ) : ℕ :=
  if h : ∃ m, b < m ∧ IsSidon (insert m S) then Nat.find h else b + 1

/-- When `S` is Sidon, the next greedy term is strictly above `b` and keeps the set Sidon. -/
theorem nextSidon_spec {S : Finset ℕ} (hS : IsSidon S) (b : ℕ) :
    b < nextSidon S b ∧ IsSidon (insert (nextSidon S b) S) := by
  classical
  have hex : ∃ m, b < m ∧ IsSidon (insert m S) := by
    obtain ⟨m, hb, _, hm⟩ := sidon_exists_extension S hS b
    exact ⟨m, hb, hm⟩
  have hval : nextSidon S b = Nat.find hex := by
    unfold nextSidon; exact dif_pos hex
  rw [hval]
  exact Nat.find_spec hex

/-- Greedy construction as pairs `(aₙ, {a₀, …, aₙ})`, starting from `a₀ = 1`. -/
noncomputable def greedyPair : ℕ → ℕ × Finset ℕ
  | 0 => (1, {1})
  | (n + 1) =>
      (nextSidon (greedyPair n).2 (greedyPair n).1,
       insert (nextSidon (greedyPair n).2 (greedyPair n).1) (greedyPair n).2)

/-- The greedy Sidon sequence: `aₙ`. -/
noncomputable def greedySeq (n : ℕ) : ℕ := (greedyPair n).1

/-- The first `n + 1` greedy terms `{a₀, …, aₙ}` as a finite set. -/
noncomputable def greedySeqSet (n : ℕ) : Finset ℕ := (greedyPair n).2

/-- Every initial segment of the greedy construction is a Sidon set. -/
theorem greedySeqSet_isSidon : ∀ n, IsSidon (greedySeqSet n)
  | 0 => isSidon_singleton 1
  | (n + 1) => (nextSidon_spec (greedySeqSet_isSidon n) (greedySeq n)).2

/-- Each greedy term is strictly larger than its predecessor. -/
theorem greedySeq_lt_succ (n : ℕ) : greedySeq n < greedySeq (n + 1) :=
  (nextSidon_spec (greedySeqSet_isSidon n) (greedySeq n)).1

/-- The greedy sequence is strictly increasing. -/
theorem greedySeq_strictMono : StrictMono greedySeq :=
  strictMono_nat_of_lt_succ greedySeq_lt_succ

/-- The greedy set after `n` steps is the image of the first `n + 1` terms. -/
theorem greedySeqSet_eq_image (n : ℕ) :
    greedySeqSet n = Finset.image greedySeq (Finset.range (n + 1)) := by
  induction n with
  | zero => simp [greedySeqSet, greedySeq, greedyPair]
  | succ n ih =>
      have hrec : greedySeqSet (n + 1)
          = insert (greedySeq (n + 1)) (greedySeqSet n) := rfl
      have himg : Finset.image greedySeq (Finset.range (n + 1 + 1))
          = insert (greedySeq (n + 1)) (Finset.image greedySeq (Finset.range (n + 1))) := by
        rw [Finset.range_succ, Finset.image_insert]
      rw [hrec, ih, himg]

/-! ### Discharge of the three `greedySidonSeq*` axioms

With `greedySidonSeq := greedySeq`, the following theorems are exactly the statements of
the three axioms in `Erdos340GreedySidon.lean`, now proved. -/

/-- Discharge of `axiom greedySidonSeq_strictMono`: the explicit greedy sequence is
strictly increasing. -/
theorem greedySidonSeq_strictMono_discharge : StrictMono greedySeq :=
  greedySeq_strictMono

/-- Discharge of `axiom greedySidonSeq_isSidon`: the set of the first `n + 1` greedy terms
is always Sidon. -/
theorem greedySidonSeq_isSidon_discharge (n : ℕ) :
    IsSidon (Finset.image greedySeq (Finset.range (n + 1))) := by
  rw [← greedySeqSet_eq_image]
  exact greedySeqSet_isSidon n

end Erdos340
