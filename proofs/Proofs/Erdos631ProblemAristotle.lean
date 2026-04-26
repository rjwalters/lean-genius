/-
  Aristotle targets for Erdos631Problem
  Routine supporting lemmas for automated proof search.
  See Erdos631Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT list_chromatic_ge_chromatic: depends on def-sorry listChromaticNumber
  - NOT planar_5_choosable: requires connection between listChromaticNumber (def-sorry)
      and IsKChoosable; not accessible without that definition
  - NOT outerplanar_is_planar: IsOuterplanar is a def-sorry
  - NOT choosable_implies_colorable: already proved by Aristotle in main file
  - choosable_monotone: purely from IsKChoosable definition via le_trans; provable

  Included targets (1):
  - choosable_monotone_ari: k-choosable implies (k+1)-choosable

  Proof sketch for choosable_monotone:
  Given any (k+1)-list assignment L with |L v| ≥ k+1 for all v,
  note |L v| ≥ k+1 ≥ k, so apply the k-choosability hypothesis with L directly.

  NOT included:
  - list_chromatic_ge_chromatic: listChromaticNumber is defined as sorry
  - planar_5_choosable: IsPlanar is def-sorry; thomassen_five_list_theorem uses
      listChromaticNumber (def-sorry) so the connection to IsKChoosable is broken
  - outerplanar_is_planar: IsOuterplanar is def-sorry
-/
import Mathlib
import Proofs.GraphCore
import Proofs.Erdos631Problem

namespace Erdos631Aristotle

open Finset Function Nat GraphCore
open SimpleGraph hiding chromaticNumber

/-
## Section: Monotonicity of k-Choosability

A k-choosable graph is also (k+1)-choosable:
any list assignment with lists of size ≥ k+1 also satisfies ≥ k.

Key Mathlib lemmas:
- Nat.le_of_succ_le: k + 1 ≤ n → k ≤ n
- le_trans: transitivity of ≤
-/

/-- k-choosability is monotone: if G is k-choosable then G is (k+1)-choosable.
    The proof is immediate: any (k+1)-list also satisfies the k-list size requirement. -/
theorem choosable_monotone_ari {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) :
    Erdos631.IsKChoosable G k → Erdos631.IsKChoosable G (k + 1) := by
  intro h C _ L hL
  exact h L (fun v => Nat.le_of_succ_le (hL v))

end Erdos631Aristotle
