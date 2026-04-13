/-
  Aristotle targets for CantorDiagonalizationOQ02OQ03OQ02 (Fodor's Pressing-Down Lemma)
  Routine supporting lemmas for automated proof search.
  See CantorDiagonalizationOQ02OQ03OQ02.lean for the main formalization.

  Status: 1 sorry remaining — diagInter_isUnbounded (needs isClub_bInter)
  Progress: isClub_inter PROVED; diagInter_isUnbounded_ari SORRY (needs isClub_bInter)

  Key blocker: isClub_bInter requires transfinite induction over < κ-many clubs.
  The finite intersection case (isClub_inter) is proved below via ping-pong sequences.

  Proof of isClub_inter:
    Unbounded half: Given α₀ < κ.ord, ping-pong between C₁ and C₂:
      seqA 0 ∈ C₁ with α₀ < seqA 0
      seqB n ∈ C₂ with seqA n < seqB n
      seqA (n+1) ∈ C₁ with seqB n < seqA (n+1)
    Let γ = iSup seqB. Then:
      γ < κ.ord: ℕ-indexed, each seqB n < κ.ord, κ regular → iSup_lt_ord
      γ is a limit ordinal: iSup of strictly monotone ω-sequence
      γ ∈ C₁ ∩ C₂: each is closed; seqA n+1 cofinal in C₁, seqB n cofinal in C₂
    Closed half: project intersection membership to each component.

  Helper lemmas:
  1. iSup_strictMono_isSuccLimit: iSup of strictly monotone ω-sequence is limit
  2. isClub_inter: finite intersection of two clubs is a club (PROVED)
  3. isClub_bInter: bounded intersection of clubs is a club (SORRY — needs transfinite induction)
  4. diagInter_isUnbounded_ari: the main sorry (exposed for Aristotle)
-/
import Mathlib
import Proofs.CantorDiagonalizationOQ02OQ03OQ02

namespace FodorLemmaAristotle

open FodorLemma Cardinal Ordinal

/-- The supremum of a strictly monotone ω-sequence is a limit ordinal. -/
private lemma iSup_strictMono_isSuccLimit {seq : ℕ → Ordinal}
    (hmono : StrictMono seq) (hbdd : BddAbove (Set.range seq)) :
    IsSuccLimit (iSup seq) := by
  have hlt : ∀ n, seq n < iSup seq := fun n =>
    (hmono (Nat.lt_succ_self n)).trans_le (le_ciSup hbdd (n + 1))
  exact (isLUB_ciSup hbdd).isSuccLimit_of_notMem
    ⟨seq 0, Set.mem_range_self 0⟩
    (fun ⟨n, hn⟩ => absurd (hn ▸ hlt n) (lt_irrefl _))

/-- The intersection of two clubs below κ.ord is itself a club.
    Both components (unbounded and closed) pass to the intersection. -/
lemma isClub_inter {κ : Cardinal} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {C₁ C₂ : Set Ordinal}
    (hC₁ : IsClub κ C₁) (hC₂ : IsClub κ C₂) :
    IsClub κ (C₁ ∩ C₂) := by
  constructor
  · -- Unbounded: ping-pong between C₁ and C₂
    intro α₀ hα₀
    -- Pack the alternating sequence as a sigma type for transparency
    let T := {q : Ordinal × Ordinal // q.1 ∈ C₁ ∧ q.2 ∈ C₂ ∧ q.1 < q.2 ∧ q.2 < κ.ord}
    let packBase : T :=
      let ⟨a₀, ha₀_mem, hα₀_lt, ha₀_bound⟩ := hC₁.1 α₀ hα₀
      let ⟨b₀, hb₀_mem, ha₀_lt, hb₀_bound⟩ := hC₂.1 a₀ ha₀_bound
      ⟨(a₀, b₀), ha₀_mem, hb₀_mem, ha₀_lt, hb₀_bound⟩
    let packStep : T → T := fun prev =>
      let ⟨a', ha'_mem, _, ha'_lt, ha'_bound⟩ := hC₁.1 prev.1.2 prev.2.2.2.2
      let ⟨b', hb'_mem, ha'_lt_b', hb'_bound⟩ := hC₂.1 a' ha'_bound
      ⟨(a', b'), ha'_mem, hb'_mem, ha'_lt_b', hb'_bound⟩
    let pack : ℕ → T := fun n => Nat.rec packBase (fun _ prev => packStep prev) n
    let seqA : ℕ → Ordinal := fun n => (pack n).1.1
    let seqB : ℕ → Ordinal := fun n => (pack n).1.2
    have hA_mem : ∀ n, seqA n ∈ C₁ := fun n => (pack n).2.1
    have hB_mem : ∀ n, seqB n ∈ C₂ := fun n => (pack n).2.2.1
    have hAB : ∀ n, seqA n < seqB n := fun n => (pack n).2.2.2.1
    have hB_lt : ∀ n, seqB n < κ.ord := fun n => (pack n).2.2.2.2
    have hBA : ∀ n, seqB n < seqA (n + 1) := fun n =>
      (hC₁.1 (pack n).1.2 (pack n).2.2.2.2).choose_spec.2.1
    have hB_succ : ∀ n, seqB n < seqB (n + 1) := fun n =>
      (hBA n).trans (hAB (n + 1))
    have hB_strict : StrictMono seqB :=
      strictMono_nat_of_lt_succ hB_succ
    have hbdd : BddAbove (Set.range seqB) :=
      ⟨κ.ord, fun x ⟨n, hn⟩ => hn ▸ le_of_lt (hB_lt n)⟩
    let γ := iSup seqB
    have hγ_lt : γ < κ.ord :=
      Ordinal.iSup_lt_ord (by rw [hκ.cof_eq, Cardinal.mk_nat]; exact hκ_unc) hB_lt
    have hγ_limit : γ.IsSuccLimit :=
      iSup_strictMono_isSuccLimit hB_strict hbdd
    have hlt : ∀ n, seqB n < γ := fun n =>
      (hB_succ n).trans_le (le_ciSup hbdd (n + 1))
    have hC₁_cof : ∀ p, p < γ → ∃ δ ∈ C₁, p < δ ∧ δ < γ := fun p hp => by
      obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hp
      exact ⟨seqA (n + 1), hA_mem (n + 1),
             hn.trans (hBA n),
             (hAB (n + 1)).trans_le (le_ciSup hbdd (n + 1))⟩
    have hC₂_cof : ∀ p, p < γ → ∃ δ ∈ C₂, p < δ ∧ δ < γ := fun p hp => by
      obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hp
      exact ⟨seqB n, hB_mem n, hn, hlt n⟩
    have hγ_C₁ : γ ∈ C₁ := hC₁.2 γ hγ_lt hγ_limit hC₁_cof
    have hγ_C₂ : γ ∈ C₂ := hC₂.2 γ hγ_lt hγ_limit hC₂_cof
    have hα₀_lt_γ : α₀ < γ := by
      have h₁ : α₀ < seqA 0 := (hC₁.1 α₀ hα₀).choose_spec.2.1
      exact (h₁.trans (hAB 0)).trans_le (le_ciSup hbdd 0)
    exact ⟨γ, ⟨hγ_C₁, hγ_C₂⟩, hα₀_lt_γ, hγ_lt⟩
  · -- Closed: project cofinal sequences to each component
    intro γ hγκ hγlim hcof
    constructor
    · apply hC₁.2 γ hγκ hγlim
      intro α hα
      obtain ⟨δ, ⟨hδ₁, _⟩, hlt, hδγ⟩ := hcof α hα
      exact ⟨δ, hδ₁, hlt, hδγ⟩
    · apply hC₂.2 γ hγκ hγlim
      intro α hα
      obtain ⟨δ, ⟨_, hδ₂⟩, hlt, hδγ⟩ := hcof α hα
      exact ⟨δ, hδ₂, hlt, hδγ⟩

/-- The intersection of a < κ-sized family of clubs is a club.
    SORRY: Requires transfinite induction over < κ-many clubs.
    This is the key missing ingredient for diagInter_isUnbounded. -/
lemma isClub_bInter {κ : Cardinal} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {I : Type*} (hI : #I < κ) {f : I → Set Ordinal}
    (hf : ∀ i, IsClub κ (f i)) :
    IsClub κ (⋂ i, f i) := by sorry

/-- The diagonal intersection of a κ-indexed family of clubs is unbounded
    below κ.ord. This is the main sorry in the parent file.
    SORRY: Requires isClub_bInter for the finite intersection step. -/
lemma diagInter_isUnbounded_ari {κ : Cardinal} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {f : Ordinal → Set Ordinal} (hf : ∀ β, β < κ.ord → IsClub κ (f β)) :
    IsUnboundedBelow κ (diagInter f) := by
  sorry

end FodorLemmaAristotle
