import Proofs.Erdos85SequentialCounter

/-!
# Reverse semantics of the Knuth sequential counter

Unlike the canonical-witness lemmas, these schemas constrain arbitrary
auxiliary propositions. They provide the semantic converse needed by CNF
coverage arguments. A concrete DIMACS containment proof remains separate.
-/

namespace Erdos85

/-- The four nontrivial counter schemas, interpreted as implications under
an arbitrary valuation of inputs and auxiliaries. -/
structure SeqCounterReverseSchemas (n t : Nat) (x : Nat → Prop)
    (s : Nat → Nat → Prop) : Prop where
  base : ∀ j, j < n - t → x j → s 0 j
  horizontal : ∀ k j, k < t → j + 1 < n - t → s k j → s k (j + 1)
  diagonal : ∀ k j, k + 1 < t → j < n - t →
    x (j + k + 1) → s k j → s (k + 1) j
  overflow : ∀ j, j < n - t → x (j + t) → s (t - 1) j → False

/-- There cannot be `t+1` strictly increasing true input positions. -/
theorem seqCounterReverse_no_chain {n t : Nat} {x : Nat → Prop}
    {s : Nat → Nat → Prop} (h : SeqCounterReverseSchemas n t x s)
    (ht : 0 < t) (p : Nat → Nat)
    (hinc : ∀ k, k < t → p k < p (k + 1))
    (hlast : p t < n) (hx : ∀ k, k ≤ t → x (p k)) : False := by
  have gap (a : Nat) : ∀ d, a + d ≤ t → p a + d ≤ p (a + d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
        intro had
        have hi := ih (by omega)
        have hs := hinc (a + d) (by omega)
        have he : a + (d + 1) = a + d + 1 := by omega
        rw [he]
        omega
  have lower (k : Nat) (hk : k ≤ t) : k ≤ p k := by
    have hg := gap 0 k (by omega)
    simp only [Nat.zero_add] at hg
    omega
  let q : Nat → Nat := fun k => p k - k
  have qb (k : Nat) (hk : k ≤ t) : q k < n - t := by
    have hg := gap k (t - k) (by omega)
    have he : k + (t - k) = t := by omega
    rw [he] at hg
    have hl := lower k hk
    dsimp [q]
    omega
  have qm (k : Nat) (hk : k < t) : q k ≤ q (k + 1) := by
    have hi := hinc k hk
    have hl := lower k (by omega)
    have hl' := lower (k + 1) (by omega)
    dsimp [q]
    omega
  have grow (k a : Nat) (hk : k < t) :
      ∀ d, a + d < n - t → s k a → s k (a + d) := by
    intro d
    induction d with
    | zero => intro _ hs; simpa using hs
    | succ d ih =>
        intro hb hs
        have hp := ih (by omega) hs
        simpa [Nat.add_assoc] using h.horizontal k (a + d) hk (by omega) hp
  have transport (k a b : Nat) (hk : k < t) (hab : a ≤ b)
      (hb : b < n - t) (ha : s k a) : s k b := by
    have he : a + (b - a) = b := by omega
    have hg := grow k a hk (b - a) (by omega) ha
    simpa [he] using hg
  have force : ∀ k, k < t → s k (q k) := by
    intro k
    induction k with
    | zero =>
        intro _
        apply h.base (q 0) (qb 0 (by omega))
        simpa [q] using hx 0 (by omega)
    | succ k ih =>
        intro hk
        have hs := transport k (q k) (q (k + 1)) (by omega)
          (qm k (by omega)) (qb (k + 1) (by omega)) (ih (by omega))
        have hl := lower (k + 1) (by omega)
        have he : q (k + 1) + k + 1 = p (k + 1) := by dsimp [q]; omega
        apply h.diagonal k (q (k + 1)) (by omega) (qb (k + 1) (by omega))
        · rw [he]
          exact hx (k + 1) (by omega)
        · exact hs
  have hqm : q (t - 1) ≤ q t := by
    have hm := qm (t - 1) (by omega)
    have he : t - 1 + 1 = t := by omega
    simpa [he] using hm
  have hs := transport (t - 1) (q (t - 1)) (q t) (by omega)
    hqm (qb t le_rfl) (force (t - 1) (by omega))
  have hl := lower t le_rfl
  have he : q t + t = p t := by dsimp [q]; omega
  apply h.overflow (q t) (qb t le_rfl)
  · rw [he]
    exact hx t le_rfl
  · exact hs

/-- Arbitrary satisfying auxiliary values enforce the cardinality bound. -/
theorem seqCounterReverse_card_le {n t : Nat} {x : Nat → Prop}
    [DecidablePred x] {s : Nat → Nat → Prop}
    (h : SeqCounterReverseSchemas n t x s) (ht : 0 < t) :
    ((Finset.range n).filter x).card ≤ t := by
  classical
  by_contra hnot
  have hcard : t + 1 ≤ ((Finset.range n).filter x).card := by omega
  obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq hcard
  let e := u.orderEmbOfFin hucard
  let p : Nat → Nat := fun k => if hk : k < t + 1 then e ⟨k, hk⟩ else 0
  have pmem (k : Nat) (hk : k < t + 1) : p k ∈ u := by
    simp only [p, dif_pos hk]
    exact u.orderEmbOfFin_mem hucard ⟨k, hk⟩
  have hbound (k : Nat) (hk : k ≤ t) : p k < n := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp (hu (pmem k (by omega)))).1
  have htrue (k : Nat) (hk : k ≤ t) : x (p k) := by
    exact (Finset.mem_filter.mp (hu (pmem k (by omega)))).2
  have hinc (k : Nat) (hk : k < t) : p k < p (k + 1) := by
    have hi := e.strictMono
      (show (⟨k, by omega⟩ : Fin (t + 1)) < ⟨k + 1, by omega⟩ from by simp)
    simpa only [p, dif_pos (show k < t + 1 by omega),
      dif_pos (show k + 1 < t + 1 by omega)] using hi
  exact seqCounterReverse_no_chain h ht p hinc (hbound t le_rfl) htrue

/-- Bridge to the existing Boolean prefix-count semantics. -/
theorem seqCounterReverse_seqPrefixTrue_le {n t : Nat} (x : Fin n → Bool)
    {s : Nat → Nat → Prop}
    (h : SeqCounterReverseSchemas n t
      (fun i => if hi : i < n then x ⟨i, hi⟩ = true else False) s)
    (ht : 0 < t) : seqPrefixTrue x n ≤ t := by
  have he : seqPrefixTrue x n =
      ((Finset.range n).filter
        (fun i => if hi : i < n then x ⟨i, hi⟩ = true else False)).card := by
    unfold seqPrefixTrue
    congr 1
    ext i
    by_cases hi : i < n <;> simp [hi]
  rw [he]
  exact seqCounterReverse_card_le h ht

/-- Applying the reverse counter to negated inputs gives the lower bound
used by the one-high CNF's exact-degree encoding. -/
theorem seqCounterReverse_complement_lower_bound {n t : Nat} (x : Fin n → Bool)
    {s : Nat → Nat → Prop}
    (h : SeqCounterReverseSchemas n t
      (fun i => if hi : i < n then seqNeg x ⟨i, hi⟩ = true else False) s)
    (ht : 0 < t) : n - t ≤ seqPrefixTrue x n := by
  have hb := seqCounterReverse_seqPrefixTrue_le (seqNeg x) h ht
  have hc := seqPrefixTrue_neg_add x
  omega

end Erdos85
