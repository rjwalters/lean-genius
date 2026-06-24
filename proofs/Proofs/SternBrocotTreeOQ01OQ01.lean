import Mathlib
import Proofs.SternBrocotTreeOQ01

/-!
# Stern–Brocot run-lengths are the continued-fraction partial quotients
(`stern-brocot-tree-oq-01-oq-01`)

The parent entry (`stern-brocot-tree-oq-01`, `Proofs/SternBrocotTreeOQ01.lean`) builds
the Stern–Brocot tree from scratch over `ℤ` and proves the headline bijection: a path
`p : List Bool` of left/right moves (`false = L`, `true = R`) labels the reduced positive
rational `sbNum p / sbDen p`, and this sets up a bijection with reduced positive rationals.

Reading a path as a sequence of **runs** of consecutive equal moves
`R^{q₀} L^{q₁} R^{q₂} L^{q₃} …`, the classical theorem says the run-lengths `q₀, q₁, q₂, …`
are exactly the **partial quotients of the continued fraction** of the labelled rational:

  `sbNum p / sbDen p = q₀ + 1/(q₁ + 1/(q₂ + ⋯))`.

Mathlib has **no** Stern–Brocot development at all (the parent verified this against the
v4.26 checkout), so nothing here is a re-export.

## What is proved here (self-contained, pure arithmetic, `0` sorries, `0` axioms)

* **Run-transfer lemmas** `sbNum_replicate_true`, `sbDen_replicate_true`,
  `sbNum_replicate_false`, `sbDen_replicate_false` — prepending a run of `n` identical
  moves applies one affine step `n` times:
  `R`-run: `(num, den) ↦ (num + n·den, den)`; `L`-run: `(num, den) ↦ (num, den + n·num)`.
  These iterate the parent's single-step transfer lemmas.

* `runsToPathFrom` / `runsToPath` — assemble the run-structured path from a list of
  run-lengths (alternating moves, starting with an `R`-run).

* `cfValFrom` — the continued-fraction *convergent* of a run-length list, computed over
  `ℤ × ℤ` by the same affine steps (the `2×2` matrix model of continued fractions).

* `sb_runs_eq_cfVal` (**main theorem**) — the Stern–Brocot label of a run-structured path
  is exactly this convergent: `(sbNum (runsToPath qs), sbDen (runsToPath qs)) = cfValFrom true qs`.
  Equivalently `sbNum_runs` / `sbDen_runs` componentwise.

* `cfQFrom_true_cons`, `cfQFrom_false_cons`, `cfQFrom_two_cons` — the **continued-fraction
  recurrence** over `ℚ`: peeling the leading run-length off the list reproduces the regular
  continued fraction `q₀ + 1/(q₁ + 1/(q₂ + ⋯))`. This is the precise sense in which the
  run-lengths *are* the partial quotients.

* `runs_singleton` — a single `R`-run of length `n` labels the integer `n+1` (continued
  fraction `[n+1]`); `cfVal_fib` — the all-ones run-lengths give consecutive Fibonacci
  ratios (`[1,1,1] ↦ 5/3`), the slowest continued fraction.
-/

namespace SternBrocot

/-! ## Part I: Run-transfer lemmas (iterating the parent's single-step transfers) -/

/-- Prepending a run of `n` `R`-moves leaves the denominator unchanged. -/
theorem sbDen_replicate_true (n : ℕ) (q : List Bool) :
    sbDen (List.replicate n true ++ q) = sbDen q := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, sbDen_true_cons, ih]

/-- Prepending a run of `n` `R`-moves adds `n·den` to the numerator. -/
theorem sbNum_replicate_true (n : ℕ) (q : List Bool) :
    sbNum (List.replicate n true ++ q) = sbNum q + (n : ℤ) * sbDen q := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, sbNum_true_cons,
        sbDen_replicate_true k q, ih]
    push_cast; ring

/-- Prepending a run of `n` `L`-moves leaves the numerator unchanged. -/
theorem sbNum_replicate_false (n : ℕ) (q : List Bool) :
    sbNum (List.replicate n false ++ q) = sbNum q := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, sbNum_false_cons, ih]

/-- Prepending a run of `n` `L`-moves adds `n·num` to the denominator. -/
theorem sbDen_replicate_false (n : ℕ) (q : List Bool) :
    sbDen (List.replicate n false ++ q) = sbDen q + (n : ℤ) * sbNum q := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, sbDen_false_cons,
        sbNum_replicate_false k q, ih]
    push_cast; ring

/-! ## Part II: Run-structured paths and the continued-fraction convergent -/

/-- Build a Stern–Brocot path from a list of run-lengths, alternating moves and starting
with move `b` (`true = R`, `false = L`). -/
def runsToPathFrom : Bool → List ℕ → List Bool
  | _, [] => []
  | b, n :: ns => List.replicate n b ++ runsToPathFrom (!b) ns

/-- The run-structured path beginning with an `R`-run. -/
def runsToPath (qs : List ℕ) : List Bool := runsToPathFrom true qs

/-- The continued-fraction convergent `(num, den)` of a run-length list, built by the same
affine steps as the path (the `2×2` matrix model). Starting move `b` alternates. -/
def cfValFrom : Bool → List ℕ → ℤ × ℤ
  | _, [] => (1, 1)
  | true, n :: ns =>
      ((cfValFrom false ns).1 + (n : ℤ) * (cfValFrom false ns).2, (cfValFrom false ns).2)
  | false, n :: ns =>
      ((cfValFrom true ns).1, (cfValFrom true ns).2 + (n : ℤ) * (cfValFrom true ns).1)

/-- **Main theorem.** The Stern–Brocot label of a run-structured path equals the
continued-fraction convergent of its run-lengths. -/
theorem sb_runs_eq_cfVal (b : Bool) (qs : List ℕ) :
    (sbNum (runsToPathFrom b qs), sbDen (runsToPathFrom b qs)) = cfValFrom b qs := by
  induction qs generalizing b with
  | nil =>
    obtain ⟨h1, h2⟩ := sb_root
    simp [runsToPathFrom, cfValFrom, h1, h2]
  | cons n ns ih =>
    cases b with
    | true =>
      have hn : sbNum (runsToPathFrom false ns) = (cfValFrom false ns).1 :=
        congrArg Prod.fst (ih false)
      have hd : sbDen (runsToPathFrom false ns) = (cfValFrom false ns).2 :=
        congrArg Prod.snd (ih false)
      simp only [runsToPathFrom, Bool.not_true, cfValFrom]
      rw [sbNum_replicate_true, sbDen_replicate_true, hn, hd]
    | false =>
      have hn : sbNum (runsToPathFrom true ns) = (cfValFrom true ns).1 :=
        congrArg Prod.fst (ih true)
      have hd : sbDen (runsToPathFrom true ns) = (cfValFrom true ns).2 :=
        congrArg Prod.snd (ih true)
      simp only [runsToPathFrom, Bool.not_false, cfValFrom]
      rw [sbNum_replicate_false, sbDen_replicate_false, hn, hd]

/-- Componentwise form of the main theorem (numerator). -/
theorem sbNum_runs (b : Bool) (qs : List ℕ) :
    sbNum (runsToPathFrom b qs) = (cfValFrom b qs).1 :=
  congrArg Prod.fst (sb_runs_eq_cfVal b qs)

/-- Componentwise form of the main theorem (denominator). -/
theorem sbDen_runs (b : Bool) (qs : List ℕ) :
    sbDen (runsToPathFrom b qs) = (cfValFrom b qs).2 :=
  congrArg Prod.snd (sb_runs_eq_cfVal b qs)

/-! ## Part III: Positivity of the convergent (inherited from the parent) -/

theorem cfVal_fst_pos (b : Bool) (qs : List ℕ) : 0 < (cfValFrom b qs).1 := by
  have h := sbNum_pos (runsToPathFrom b qs)
  rw [sbNum_runs] at h; linarith

theorem cfVal_snd_pos (b : Bool) (qs : List ℕ) : 0 < (cfValFrom b qs).2 := by
  have h := sbDen_pos (runsToPathFrom b qs)
  rw [sbDen_runs] at h; linarith

/-! ## Part IV: The continued-fraction recurrence over `ℚ` -/

/-- The rational value of a run-length list: the labelled positive rational. -/
def cfQFrom (b : Bool) (qs : List ℕ) : ℚ :=
  ((cfValFrom b qs).1 : ℚ) / ((cfValFrom b qs).2 : ℚ)

theorem cfQFrom_pos (b : Bool) (qs : List ℕ) : 0 < cfQFrom b qs :=
  div_pos (by exact_mod_cast cfVal_fst_pos b qs) (by exact_mod_cast cfVal_snd_pos b qs)

/-- Peeling an `R`-run of length `n` exposes the integer part: `q₀ + (tail value)`. -/
theorem cfQFrom_true_cons (n : ℕ) (ns : List ℕ) :
    cfQFrom true (n :: ns) = (n : ℚ) + cfQFrom false ns := by
  have hq : ((cfValFrom false ns).2 : ℚ) ≠ 0 := by
    exact_mod_cast (cfVal_snd_pos false ns).ne'
  unfold cfQFrom
  simp only [cfValFrom]
  push_cast
  field_simp
  ring

/-- Peeling an `L`-run of length `n` exposes a reciprocal: `1/(n + 1/(tail value))`. -/
theorem cfQFrom_false_cons (n : ℕ) (ns : List ℕ) :
    cfQFrom false (n :: ns) = 1 / ((n : ℚ) + 1 / cfQFrom true ns) := by
  have hP : (0 : ℚ) < ((cfValFrom true ns).1 : ℚ) := by exact_mod_cast cfVal_fst_pos true ns
  unfold cfQFrom
  simp only [cfValFrom]
  push_cast
  rw [one_div_div, add_div' _ _ _ hP.ne', one_div_div]
  ring

/-- **Continued-fraction recurrence.** Two leading run-lengths unfold into the regular
continued fraction `q₀ + 1/(q₁ + 1/(rest))`: the run-lengths are the partial quotients. -/
theorem cfQFrom_two_cons (a₀ a₁ : ℕ) (rest : List ℕ) :
    cfQFrom true (a₀ :: a₁ :: rest) = (a₀ : ℚ) + 1 / ((a₁ : ℚ) + 1 / cfQFrom true rest) := by
  rw [cfQFrom_true_cons, cfQFrom_false_cons]

/-! ## Part V: Concrete instances -/

/-- A single `R`-run of length `n` labels the integer `n + 1` (continued fraction `[n+1]`). -/
theorem runs_singleton (n : ℕ) :
    sbNum (runsToPath [n]) = (n : ℤ) + 1 ∧ sbDen (runsToPath [n]) = 1 := by
  have h : cfValFrom true [n] = (1 + (n : ℤ) * 1, 1) := rfl
  refine ⟨?_, ?_⟩
  · rw [runsToPath, sbNum_runs, h]; show 1 + (n : ℤ) * 1 = (n : ℤ) + 1; ring
  · rw [runsToPath, sbDen_runs, h]

/-- The all-ones run-lengths give consecutive Fibonacci ratios — the slowest continued
fraction. Here `[1,1,1] ↦ 5/3` (convergent to the golden ratio). -/
theorem cfVal_fib : cfValFrom true [1, 1, 1] = (5, 3) := by decide

/-- Correspondingly, the rational value of `[1,1,1]` is `5/3`. -/
theorem cfQ_fib : cfQFrom true [1, 1, 1] = 5 / 3 := by
  rw [cfQFrom, cfVal_fib]; norm_num

end SternBrocot
