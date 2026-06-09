/-
  Aristotle targets for Fermat Defect-One Conjecture
  Bounded-search lemmas for automated proof search.
  See FermatDefectOne.lean for the main formalization and the open headline
  conjecture `fermat_defect_one_exists`.

  These targets are scoped to small bounds that Aristotle can realistically
  chip at. None of them is the headline conjecture; the headline stays a
  sorry in the main file and is registered as a Tier-3 open-conjecture target
  in research/open-conjectures.json.

  Three bounded-search targets:

    witness_n_eq_4_bounded_50    -- "Does n=4 admit a witness with c ≤ 50?"
    witness_n_eq_5_bounded_50    -- "Does n=5 admit a witness with c ≤ 50?"
    no_witness_n_eq_4_below_20   -- "Bounded-nonexistence at n=4, c ≤ 20."

  Each is a theorem sorry (NOT an axiom). Aristotle can attempt these
  immediately; any one that succeeds ships as a verified `native_decide`
  witness lemma. The bounded-nonexistence target is a `decide`-style "no
  small witness" lower bound on M(n).

  These statements are intentionally narrow so the MCTS search can succeed
  on at least the no-witness target via `decide` / `native_decide`. If a
  bounded witness exists, the existence statement may also be decidable
  via the same tactic.
-/
import Mathlib
import Proofs.FermatDefectOne

namespace FermatDefectOne

/-! ## Bounded-witness existence targets

These are *existence* statements with explicit bounds on `c`. If a primitive
witness exists at the given `(n, bound)`, Aristotle should produce it; if no
such witness exists, the statement is false (and the target is dropped from
the registry — see `research/SORRY-CLASSIFICATION.md` Tier-3 policy).

Both `n = 4` and `n = 5` bounded-witness targets are *open* — no small witness
is known and we are explicitly attempting them.
-/

/-- Bounded witness at $n = 4$, $c \le 50$. Open: no primitive nontrivial
witness at $n = 4$ is currently known at any bound. -/
theorem witness_n_eq_4_bounded_50 :
    ∃ a b c : Nat, c ≤ 50 ∧ FermatDefectWitness 4 a b c := by
  sorry

/-- Bounded witness at $n = 5$, $c \le 50$. Open: no primitive nontrivial
witness at $n = 5$ is currently known at any bound. -/
theorem witness_n_eq_5_bounded_50 :
    ∃ a b c : Nat, c ≤ 50 ∧ FermatDefectWitness 5 a b c := by
  sorry

/-! ## Bounded-nonexistence targets

A bounded-nonexistence statement at $(n, N)$ asserts that no primitive
nontrivial defect-one witness exists with $c \le N$. This is a `decide`-style
claim with a finite search space.

A successful proof at $(4, 20)$ would push the minimal-witness function
$M(4) \ge 21$ (if it is finite), and the same template generalizes to other
$(n, N)$ pairs.
-/

/-- Bounded nonexistence at $n = 4$, $c \le 20$: no primitive nontrivial
defect-one witness exists with $c$ at most 20. Discharge candidate:
`decide` / `native_decide` over the finite search space. -/
theorem no_witness_n_eq_4_below_20 :
    ∀ a b c : Nat,
      2 ≤ a → a ≤ b → b < c → c ≤ 20 →
      ¬ FermatDefectWitness 4 a b c := by
  sorry

end FermatDefectOne
