import Proofs.Erdos85FiniteRowDFS

namespace Erdos85

/-- Every branch contains one subtree per domain entry, in the same order. -/
inductive FiniteRowCoverCertificate (Cut Leaf : Type) where
  | cut (reason : Cut)
  | leaf (entry : Leaf)
  | branch (children : List (FiniteRowCoverCertificate Cut Leaf))

def finiteRowChildrenCheck {α β : Type} (check : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a::as, b::bs => check a b && finiteRowChildrenCheck check as bs
  | _, _ => false

theorem finiteRowChildrenCheck_cover {α β : Type} (check : α → β → Bool)
    (as : List α) (bs : List β) (hc : finiteRowChildrenCheck check as bs = true) :
    ∀ a ∈ as, ∃ b ∈ bs, check a b = true := by
  induction as generalizing bs with
  | nil => simp
  | cons x xs ih =>
    cases bs with
    | nil => cases hc
    | cons y ys =>
      simp only [finiteRowChildrenCheck,Bool.and_eq_true] at hc
      intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · subst a
        exact ⟨y,List.mem_cons_self,hc.1⟩
      · obtain ⟨b,hb,hcheck⟩ := ih ys hc.2 a ha
        exact ⟨b,List.mem_cons_of_mem y hb,hcheck⟩

/-- Local rejection reasons replace repeated full-prefix tests. A leaf is
accepted only after all rows have been assigned. -/
def finiteRowCoverCheck {m : Nat} {α Cut Leaf : Type}
    (domain : Fin m → List α) (reject : Nat → (Fin m → α) → Cut → Bool)
    (accept : (Fin m → α) → Leaf → Bool) :
    Nat → Nat → (Fin m → α) → FiniteRowCoverCertificate Cut Leaf → Bool
  | _, k, rows, .cut reason => reject k rows reason
  | 0, _, rows, .leaf entry => accept rows entry
  | fuel+1, k, rows, .branch children =>
    if h : k < m then
      finiteRowChildrenCheck (fun row child =>
        finiteRowCoverCheck domain reject accept fuel (k+1)
          (Function.update rows ⟨k,h⟩ row) child) (domain ⟨k,h⟩) children
    else false
  | _, _, _, _ => false

private theorem prefix_update {m : Nat} {α : Type} (base target : Fin m → α)
    (k : Nat) (hk : k < m) :
    Function.update (finiteRowPrefix base target k) ⟨k,hk⟩ (target ⟨k,hk⟩) =
      finiteRowPrefix base target (k+1) := by
  funext i
  by_cases hi : i = ⟨k,hk⟩
  · subst i
    simp [finiteRowPrefix]
  · have hne : i.val ≠ k := fun h => hi (Fin.ext h)
    have he : (i.val < k+1) ↔ i.val < k := by omega
    simp [Function.update_of_ne hi,finiteRowPrefix,he]

/-- Any target whose rows belong to their domains and cannot satisfy a cut
reason reaches a checked terminal entry. No completeness of the cut reasons
is required. -/
theorem finiteRowCoverCheck_cover {m : Nat} {α Cut Leaf : Type}
    (domain : Fin m → List α) (reject : Nat → (Fin m → α) → Cut → Bool)
    (accept : (Fin m → α) → Leaf → Bool) (base target : Fin m → α)
    (hdom : ∀ i, target i ∈ domain i)
    (hreject : ∀ k, k ≤ m → ∀ reason,
      reject k (finiteRowPrefix base target k) reason = false)
    (cert : FiniteRowCoverCertificate Cut Leaf)
    (hc : finiteRowCoverCheck domain reject accept m 0 base cert = true) :
    ∃ entry, accept target entry = true := by
  have aux : ∀ fuel k, k+fuel=m → ∀ cert,
      finiteRowCoverCheck domain reject accept fuel k (finiteRowPrefix base target k) cert = true →
      ∃ entry, accept target entry = true := by
    intro fuel
    induction fuel with
    | zero =>
      intro k hk cert hcheck
      have hkm : k=m := by omega
      subst k
      cases cert with
      | cut reason =>
        have hr := hreject m (by omega) reason
        simp only [finiteRowCoverCheck,hr] at hcheck
        cases hcheck
      | leaf entry =>
        have he : finiteRowPrefix base target m = target := by
          funext i
          exact if_pos i.isLt
        exact ⟨entry,by simpa only [finiteRowCoverCheck,he] using hcheck⟩
      | branch children => cases hcheck
    | succ fuel ih =>
      intro k hk cert hcheck
      cases cert with
      | cut reason =>
        have hr := hreject k (by omega) reason
        simp only [finiteRowCoverCheck,hr] at hcheck
        cases hcheck
      | leaf entry => cases hcheck
      | branch children =>
        have hkm : k < m := by omega
        simp only [finiteRowCoverCheck,dif_pos hkm] at hcheck
        obtain ⟨child,_,hchild⟩ := finiteRowChildrenCheck_cover _ _ _ hcheck
          (target ⟨k,hkm⟩) (hdom _)
        rw [prefix_update] at hchild
        exact ih (k+1) (by omega) child hchild
  have he : finiteRowPrefix base target 0 = base := by
    funext i
    simp only [finiteRowPrefix,Nat.not_lt_zero,if_false]
  apply aux m 0 (by omega) cert
  simpa only [he] using hc

end Erdos85
#print axioms Erdos85.finiteRowChildrenCheck_cover
#print axioms Erdos85.finiteRowCoverCheck_cover
