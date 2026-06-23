/-
# Rogers-Ramanujan Identities: Computational Verification for Small n

The parent file (OQ-01) states the Rogers-Ramanujan first identity (RR1),
second identity (RR2), and Schur's partition identity as axioms. This file
provides computational verification of RR1 and RR2 for n = 0, 1, ..., 8
using `native_decide`.

**Rogers-Ramanujan First Identity (RR1)**: The number of partitions of n where
consecutive parts differ by ≥ 2 equals the number of partitions of n where all
parts are ≡ 1 or 4 (mod 5).

**Rogers-Ramanujan Second Identity (RR2)**: As above with smallest part ≥ 2,
equal to parts ≡ 2 or 3 (mod 5).

**Significance**: These identities hold for all n (Rogers 1894, Ramanujan 1913),
but their proofs require generating functions or bijective arguments. The
computational verification here provides concrete evidence at small values
and confirms the definitions are consistent with the classical results.
-/

import Proofs.PartitionTheoremOQ01
import Mathlib.Tactic

namespace PartitionTheoremOQ01OQ01

open RogersRamanujan

/-! ## Verification of Rogers-Ramanujan First Identity (n ≤ 8) -/

theorem rr1_n0 : (rr1GapPartitions 0).card = (rr1Mod5Partitions 0).card := by native_decide
theorem rr1_n1 : (rr1GapPartitions 1).card = (rr1Mod5Partitions 1).card := by native_decide
theorem rr1_n2 : (rr1GapPartitions 2).card = (rr1Mod5Partitions 2).card := by native_decide
theorem rr1_n3 : (rr1GapPartitions 3).card = (rr1Mod5Partitions 3).card := by native_decide
theorem rr1_n4 : (rr1GapPartitions 4).card = (rr1Mod5Partitions 4).card := by native_decide
theorem rr1_n5 : (rr1GapPartitions 5).card = (rr1Mod5Partitions 5).card := by native_decide
theorem rr1_n6 : (rr1GapPartitions 6).card = (rr1Mod5Partitions 6).card := by native_decide
theorem rr1_n7 : (rr1GapPartitions 7).card = (rr1Mod5Partitions 7).card := by native_decide
theorem rr1_n8 : (rr1GapPartitions 8).card = (rr1Mod5Partitions 8).card := by native_decide

/-! ## Verification of Rogers-Ramanujan Second Identity (n ≤ 8) -/

theorem rr2_n0 : (rr2GapPartitions 0).card = (rr2Mod5Partitions 0).card := by native_decide
theorem rr2_n1 : (rr2GapPartitions 1).card = (rr2Mod5Partitions 1).card := by native_decide
theorem rr2_n2 : (rr2GapPartitions 2).card = (rr2Mod5Partitions 2).card := by native_decide
theorem rr2_n3 : (rr2GapPartitions 3).card = (rr2Mod5Partitions 3).card := by native_decide
theorem rr2_n4 : (rr2GapPartitions 4).card = (rr2Mod5Partitions 4).card := by native_decide
theorem rr2_n5 : (rr2GapPartitions 5).card = (rr2Mod5Partitions 5).card := by native_decide
theorem rr2_n6 : (rr2GapPartitions 6).card = (rr2Mod5Partitions 6).card := by native_decide
theorem rr2_n7 : (rr2GapPartitions 7).card = (rr2Mod5Partitions 7).card := by native_decide
theorem rr2_n8 : (rr2GapPartitions 8).card = (rr2Mod5Partitions 8).card := by native_decide

/-! ## Combined Verification Theorem -/

/-- Both Rogers-Ramanujan identities hold computationally for all n ≤ 8. -/
theorem rr_both_verified_through_8 :
    ∀ n ≤ 8,
      (rr1GapPartitions n).card = (rr1Mod5Partitions n).card ∧
      (rr2GapPartitions n).card = (rr2Mod5Partitions n).card := by
  intro n hn
  interval_cases n <;> exact ⟨by native_decide, by native_decide⟩

/-! ## The Axioms Are Consistent with Small Values

The computational checks above demonstrate that the axioms in OQ-01
(`rogers_ramanujan_first` and `rogers_ramanujan_second`) are consistent
with computed values for n ≤ 8. The general identities require the
Rogers-Ramanujan generating function machinery (q-series identity).
-/

end PartitionTheoremOQ01OQ01
