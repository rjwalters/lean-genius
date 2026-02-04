/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 45b2cd95-41b7-4099-9f37-82ac2fef6ab5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem sum_multiplicities (P : PointConfig) :
    (distanceSet P).sum (unorderedMultiplicity P) = P.card.choose 2
-/

/-
  Erdős Problem #94: Distance Multiplicities in Convex Polygons

  Source: https://erdosproblems.com/94
  Status: SOLVED (Fishburn; strengthened by Lefmann-Theile 1995)
  Prize: $44

  Statement:
  Suppose n points in ℝ² form the vertices of a convex polygon. Let {u₁, ..., u_t}
  be the set of distinct distances between points, and let f(u_i) count how many
  pairs of points are at distance u_i. Then:
    ∑_i f(u_i)² ≪ n³

  Note: Trivially ∑ f(u_i) = C(n,2) = n(n-1)/2 (total number of pairs).

  Key Results:
  - Fishburn proved the n³ bound for convex polygons
  - Lefmann-Theile (1995) strengthened this to "no three collinear" condition
  - Erdős-Fishburn conjecture: regular n-gon maximizes ∑ f(u_i)²

  Tags: geometry, convex, distances, combinatorics
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic


namespace Erdos94

open Finset Real

/- ## Part I: Point Configurations -/

/-- A point in the Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A finite point configuration. -/
def PointConfig := Finset Point

/-- The distance between two points. -/
noncomputable def dist' (p q : Point) : ℝ := dist p q

/-- The set of all pairwise distances in a configuration. -/
noncomputable def distanceSet (P : PointConfig) : Finset ℝ :=
  (P.product P).image (fun pq => dist' pq.1 pq.2) |>.filter (· > 0)

/-- The multiset of distances (with repetition). -/
noncomputable def distanceMultiset (P : PointConfig) : Multiset ℝ :=
  (P.product P).val.map (fun pq => dist' pq.1 pq.2) |>.filter (· > 0)

/- ## Part II: Distance Multiplicity -/

/-- f(u) = number of ordered pairs at distance u. -/
noncomputable def distanceMultiplicity (P : PointConfig) (u : ℝ) : ℕ :=
  ((P.product P).filter fun pq => dist' pq.1 pq.2 = u ∧ pq.1 ≠ pq.2).card

/-- f(u) for unordered pairs (half of ordered). -/
noncomputable def unorderedMultiplicity (P : PointConfig) (u : ℝ) : ℕ :=
  distanceMultiplicity P u / 2

/-- The sum ∑ f(u_i) equals the total number of pairs. -/
theorem sum_multiplicities (P : PointConfig) :
    (distanceSet P).sum (unorderedMultiplicity P) = P.card.choose 2 := by
  -- By definition of $f(u)$, we know that $\sum_{u \in d(P)} f(u) = \binom{n}{2}$.
  have h_sum_f : (Erdos94.distanceSet P).sum (fun u => Erdos94.distanceMultiplicity P u) = P.card * (P.card - 1) := by
    -- Each pair of distinct points contributes exactly once to the sum of the multiplicities.
    have h_sum_pairs : ∑ u ∈ Erdos94.distanceSet P, (Erdos94.distanceMultiplicity P u) = ∑ p ∈ P, ∑ q ∈ P, if p ≠ q then 1 else 0 := by
      unfold Erdos94.distanceMultiplicity;
      rw [ show Erdos94.distanceSet P = Finset.image ( fun pq : Point × Point => Erdos94.dist' pq.1 pq.2 ) ( Finset.filter ( fun pq : Point × Point => pq.1 ≠ pq.2 ) ( Finset.product P P ) ) from ?_ ];
      · rw [ Finset.sum_image' ];
        rotate_left;
        use fun pq => 1;
        · simp +contextual [ Finset.filter_filter ];
          exact fun a b ha hb hab => by congr; ext; aesop;
        · erw [ Finset.sum_filter, Finset.sum_product ];
      · -- By definition of distanceSet, we have that every element in the distanceSet is a positive distance between two distinct points in P.
        ext; simp [Erdos94.distanceSet];
        constructor <;> intro h;
        · rcases h with ⟨ ⟨ a, b, ⟨ ha, hb ⟩, rfl ⟩, h ⟩ ; exact ⟨ a, b, ⟨ ⟨ ha, hb ⟩, by rintro rfl; exact h.ne' <| by unfold Erdos94.dist'; norm_num ⟩, rfl ⟩;
        · exact ⟨ by obtain ⟨ a, b, h, rfl ⟩ := h; exact ⟨ a, b, h.1, rfl ⟩, by obtain ⟨ a, b, h, rfl ⟩ := h; exact dist_pos.mpr h.2 ⟩;
    simp_all +decide [ Finset.sum_ite, Finset.filter_ne ];
  convert congr_arg ( fun x : ℕ => x / 2 ) h_sum_f using 1;
  · rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ];
    rw [ Finset.sum_mul _ _ _ ];
    refine' Finset.sum_congr rfl fun u hu => _;
    unfold Erdos94.unorderedMultiplicity;
    rw [ Nat.div_mul_cancel ];
    -- By definition of $f(u)$, we know that $f(u)$ is even.
    have h_even : ∀ u ∈ Erdos94.distanceSet P, Even (Erdos94.distanceMultiplicity P u) := by
      intro u hu
      have h_even : ∃ S : Finset (Point × Point), S = (P.product P).filter (fun pq => dist' pq.1 pq.2 = u ∧ pq.1 ≠ pq.2) ∧ (∀ pq ∈ S, (pq.2, pq.1) ∈ S) ∧ (∀ pq ∈ S, pq ≠ (pq.2, pq.1)) := by
        refine' ⟨ _, rfl, _, _ ⟩ <;> simp +contextual [ Erdos94.dist' ];
        exact fun a b ha hb hab hne => ⟨ by rwa [ dist_comm ], Ne.symm hne ⟩;
      obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := h_even;
      -- Since $S$ is a finite set of pairs, we can partition it into pairs of the form $(pq, (pq.2, pq.1))$.
      have h_partition : ∃ T : Finset (Finset (Point × Point)), (∀ t ∈ T, t.card = 2) ∧ (∀ t ∈ T, ∀ pq ∈ t, pq ∈ S) ∧ (∀ pq ∈ S, ∃ t ∈ T, pq ∈ t) ∧ (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint t₁ t₂) := by
        use Finset.image (fun pq => {pq, (pq.2, pq.1)}) S;
        simp +zetaDelta at *;
        refine' ⟨ _, _, _, _ ⟩;
        · rintro t x y hx rfl; rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; simp +decide [ hx, hS₃ x y hx ] ;
          exact hS₃ x y hx;
        · rintro t x y hx rfl a b hab; rw [ Finset.mem_insert, Finset.mem_singleton ] at hab; aesop;
        · exact fun a b hab => ⟨ _, ⟨ a, b, hab, rfl ⟩, Finset.mem_insert_self _ _ ⟩;
        · rintro t₁ x y hx rfl t₂ z w hz rfl hne; simp_all +decide [ Finset.disjoint_left ] ;
          grind;
      obtain ⟨ T, hT₁, hT₂, hT₃, hT₄ ⟩ := h_partition;
      have h_card_S : S.card = Finset.sum T (fun t => t.card) := by
        rw [ ← Finset.card_biUnion ];
        · congr with pq ; simp +decide [ hT₃ ];
          exact ⟨ hT₃ pq, fun ⟨ t, ht₁, ht₂ ⟩ => hT₂ t ht₁ pq ht₂ ⟩;
        · exact fun t₁ ht₁ t₂ ht₂ h => hT₄ t₁ ht₁ t₂ ht₂ h;
      simp_all +decide [ Erdos94.distanceMultiplicity ];
    exact even_iff_two_dvd.mp ( h_even u hu );
  · rw [ Nat.choose_two_right ]

/- ## Part III: Sum of Squared Multiplicities -/

/-- The key quantity: ∑ f(u_i)². -/
noncomputable def sumSquaredMultiplicities (P : PointConfig) : ℕ :=
  (distanceSet P).sum fun u => (unorderedMultiplicity P u) ^ 2

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Type mismatch
  {x ∈ (Finset.product P P).product (Finset.product P P) | ?m.9}
has type
  Finset ((Erdos94.Point × Erdos94.Point) × Erdos94.Point × Erdos94.Point)
but is expected to have type
  ℕ
Invalid field notation: Type is not of the form `C ...` where C is a constant
  p ≠ q ∧ r ≠ s ∧ Erdos94.dist' p q = Erdos94.dist' r s
has type
  Prop-/
/-- Alternative: count quadruples (p,q,r,s) with d(p,q) = d(r,s). -/
noncomputable def countEqualDistancePairs (P : PointConfig) : ℕ :=
  ((P.product P).product (P.product P)).filter fun ((p,q), (r,s)) =>
    p ≠ q ∧ r ≠ s ∧ dist' p q = dist' r s |>.card

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  countEqualDistancePairs
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  P-/
/-- The two formulations are related. -/
theorem squared_sum_eq_count (P : PointConfig) :
    4 * sumSquaredMultiplicities P = countEqualDistancePairs P := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Membership ?m.1 Erdos94.PointConfig

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/- ## Part IV: Convex Position -/

/-- Points are in convex position if they form the vertices of a convex polygon. -/
def InConvexPosition (P : PointConfig) : Prop :=
  ∀ p ∈ P, p ∈ convexHull ℝ (P.erase p : Set Point) → False

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Membership Erdos94.Point Erdos94.PointConfig

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Membership Erdos94.Point Erdos94.PointConfig

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Membership Erdos94.Point Erdos94.PointConfig

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Unknown identifier `Collinear`-/
/-- No three points are collinear. -/
def NoThreeCollinear (P : PointConfig) : Prop :=
  ∀ p q r : Point, p ∈ P → q ∈ P → r ∈ P →
    p ≠ q → q ≠ r → p ≠ r →
    ¬Collinear ℝ ({p, q, r} : Set Point)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  InConvexPosition
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  P
Function expected at
  NoThreeCollinear
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  P-/
/-- Convex position implies no three collinear. -/
theorem convex_implies_no_collinear (P : PointConfig) :
    InConvexPosition P → NoThreeCollinear P := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  InConvexPosition
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  P-/
/- ## Part V: The Main Theorem (Fishburn) -/

/-- Fishburn's theorem: For convex polygons, ∑ f(u)² = O(n³). -/
theorem fishburn_theorem :
    ∃ C : ℝ, C > 0 ∧ ∀ P : PointConfig, InConvexPosition P →
      (sumSquaredMultiplicities P : ℝ) ≤ C * (P.card : ℝ) ^ 3 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  InConvexPosition
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  P-/
/-- The constant C can be taken to be 1 (asymptotically). -/
theorem fishburn_asymptotic :
    ∀ ε > 0, ∃ N : ℕ, ∀ P : PointConfig, InConvexPosition P → P.card ≥ N →
      (sumSquaredMultiplicities P : ℝ) ≤ (1 + ε) * (P.card : ℝ) ^ 3 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  NoThreeCollinear
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  P-/
/- ## Part VI: Lefmann-Theile Strengthening (1995) -/

/-- Lefmann-Theile: The bound holds under "no three collinear" (weaker than convex). -/
theorem lefmann_theile_theorem :
    ∃ C : ℝ, C > 0 ∧ ∀ P : PointConfig, NoThreeCollinear P →
      (sumSquaredMultiplicities P : ℝ) ≤ C * (P.card : ℝ) ^ 3 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  EmptyCollection Erdos94.PointConfig

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Application type mismatch: The argument
  Finset.range n
has type
  Finset ℕ
but is expected to have type
  Finset ℝ
in the application
  Finset.image (fun (k : ℝ) => ![Real.cos (2 * π * k / (↑n : ℝ)), Real.sin (2 * π * k / (↑n : ℝ))]) (Finset.range n)-/
/- ## Part VII: Lower Bounds and Extremal Configurations -/

/-- The regular n-gon configuration. -/
noncomputable def regularNGon (n : ℕ) : PointConfig :=
  if n < 3 then ∅ else
    (Finset.range n).image fun k =>
      ![Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)]

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  InConvexPosition
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (regularNGon n)-/
/-- Regular n-gon is in convex position. -/
theorem regular_ngon_convex (n : ℕ) (hn : n ≥ 3) :
    InConvexPosition (regularNGon n) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `regularNGon`-/
/-- Compute ∑ f(u)² for the regular n-gon. -/
noncomputable def regularNGonSum (n : ℕ) : ℕ :=
  sumSquaredMultiplicities (regularNGon n)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  regularNGonSum
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  regularNGonSum
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n-/
/-- The regular n-gon achieves Θ(n³). -/
theorem regular_ngon_cubic :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      c₁ * n ^ 3 ≤ (regularNGonSum n : ℝ) ∧ (regularNGonSum n : ℝ) ≤ c₂ * n ^ 3 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `InConvexPosition`
Unknown identifier `regularNGonSum`-/
/- ## Part VIII: Erdős-Fishburn Conjecture -/

/-- Erdős-Fishburn conjecture: The regular n-gon maximizes ∑ f(u)². -/
def ErdosFishburnConjecture : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∀ P : PointConfig, InConvexPosition P → P.card = n →
    sumSquaredMultiplicities P ≤ regularNGonSum n

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  InConvexPosition
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  P
Function expected at
  regularNGonSum
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  n-/
/-- The conjecture holds for small n (verified computationally). -/
theorem conjecture_small_cases : ∀ n : ℕ, 3 ≤ n ∧ n ≤ 10 →
    ∀ P : PointConfig, InConvexPosition P → P.card = n →
      sumSquaredMultiplicities P ≤ regularNGonSum n := by
  sorry

/- ## Part IX: Related Quantities -/

/-- The number of distinct distances. -/
noncomputable def numDistinctDistances (P : PointConfig) : ℕ :=
  (distanceSet P).card

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  InConvexPosition
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  P-/
/-- For convex n-gon, number of distinct distances is ⌊n/2⌋. -/
theorem convex_distinct_distances (P : PointConfig) (hP : InConvexPosition P) :
    numDistinctDistances P ≤ P.card / 2 + 1 := by
  sorry

/- Aristotle failed to find a proof. -/
/-- The maximum multiplicity of any single distance. -/
noncomputable def maxMultiplicity (P : PointConfig) : ℕ :=
  (distanceSet P).sup' (by sorry) (unorderedMultiplicity P)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  InConvexPosition
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  P-/
/-- For convex position, max multiplicity is O(n). -/
theorem convex_max_multiplicity (P : PointConfig) (hP : InConvexPosition P) :
    (maxMultiplicity P : ℝ) ≤ 2 * P.card := by
  sorry

/- ## Part X: Connections to Other Problems -/

/-- The unit distance problem: how many pairs at distance exactly 1? -/
noncomputable def unitDistanceCount (P : PointConfig) : ℕ :=
  unorderedMultiplicity P 1

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  InConvexPosition
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  P-/
/-- Erdős unit distance conjecture bound for convex position. -/
theorem convex_unit_distance (P : PointConfig) (hP : InConvexPosition P) :
    (unitDistanceCount P : ℝ) ≤ 2 * P.card - 2 := by
  sorry

end Erdos94