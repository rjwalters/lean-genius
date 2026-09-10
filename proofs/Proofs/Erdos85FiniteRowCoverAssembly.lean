import Proofs.Erdos85FiniteRowCoverCertificate

namespace Erdos85

/-- Assemble positional checks from proof terms, without evaluating the children again. -/
theorem finiteRowChildrenCheck_of_forall₂ {α β : Type} (check : α → β → Bool)
    {rows : List α} {children : List β}
    (h : List.Forall₂ (fun row child => check row child = true) rows children) :
    finiteRowChildrenCheck check rows children = true := by
  induction h with
  | nil => rfl
  | cons hhead _ ih =>
    simp only [finiteRowChildrenCheck, hhead, ih, Bool.and_self]

/-- A branch can reuse independently checked subtree theorems. -/
theorem finiteRowCoverCheck_branch {m : Nat} {α Cut Leaf : Type}
    (domain : Fin m → List α) (reject : Nat → (Fin m → α) → Cut → Bool)
    (accept : (Fin m → α) → Leaf → Bool) (fuel k : Nat) (hk : k < m)
    (rows : Fin m → α) (children : List (FiniteRowCoverCertificate Cut Leaf))
    (hchildren : List.Forall₂ (fun row child =>
      finiteRowCoverCheck domain reject accept fuel (k+1)
        (Function.update rows ⟨k,hk⟩ row) child = true) (domain ⟨k,hk⟩) children) :
    finiteRowCoverCheck domain reject accept (fuel+1) k rows (.branch children) = true := by
  rw [finiteRowCoverCheck, dif_pos hk]
  exact finiteRowChildrenCheck_of_forall₂ _ hchildren

/-- Indexed assembly is convenient when the subtree theorems are generated as shards. -/
theorem finiteRowCoverCheck_branch_of_get {m : Nat} {α Cut Leaf : Type}
    (domain : Fin m → List α) (reject : Nat → (Fin m → α) → Cut → Bool)
    (accept : (Fin m → α) → Leaf → Bool) (fuel k : Nat) (hk : k < m)
    (rows : Fin m → α) (children : List (FiniteRowCoverCertificate Cut Leaf))
    (hlen : (domain ⟨k,hk⟩).length = children.length)
    (hchildren : ∀ i hi hj,
      finiteRowCoverCheck domain reject accept fuel (k+1)
        (Function.update rows ⟨k,hk⟩ ((domain ⟨k,hk⟩).get ⟨i,hi⟩))
        (children.get ⟨i,hj⟩) = true) :
    finiteRowCoverCheck domain reject accept (fuel+1) k rows (.branch children) = true := by
  apply finiteRowCoverCheck_branch domain reject accept fuel k hk rows children
  exact List.forall₂_iff_get.mpr ⟨hlen,hchildren⟩

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

/-- A checked suffix covers every admissible target extending its starting prefix.
Only the remaining row domains and cut reasons on later prefixes are needed. -/
theorem finiteRowCoverCheck_cover_from {m : Nat} {α Cut Leaf : Type}
    (domain : Fin m → List α) (reject : Nat → (Fin m → α) → Cut → Bool)
    (accept : (Fin m → α) → Leaf → Bool) (base target : Fin m → α)
    (fuel k : Nat) (hsize : k+fuel=m)
    (hdom : ∀ i, k ≤ i.val → target i ∈ domain i)
    (hreject : ∀ j, k ≤ j → j ≤ m → ∀ reason,
      reject j (finiteRowPrefix base target j) reason = false)
    (cert : FiniteRowCoverCertificate Cut Leaf)
    (hc : finiteRowCoverCheck domain reject accept fuel k
      (finiteRowPrefix base target k) cert = true) :
    ∃ entry, accept target entry = true := by
  induction fuel generalizing k cert with
  | zero =>
    have hkm : k=m := by omega
    subst k
    cases cert with
    | cut reason =>
      have hr := hreject m (by omega) (by omega) reason
      simp only [finiteRowCoverCheck,hr] at hc
      cases hc
    | leaf entry =>
      have he : finiteRowPrefix base target m = target := by
        funext i
        exact if_pos i.isLt
      exact ⟨entry,by simpa only [finiteRowCoverCheck,he] using hc⟩
    | branch children => cases hc
  | succ fuel ih =>
    cases cert with
    | cut reason =>
      have hr := hreject k (by omega) (by omega) reason
      simp only [finiteRowCoverCheck,hr] at hc
      cases hc
    | leaf entry => cases hc
    | branch children =>
      have hkm : k < m := by omega
      simp only [finiteRowCoverCheck,dif_pos hkm] at hc
      obtain ⟨child,_,hchild⟩ := finiteRowChildrenCheck_cover _ _ _ hc
        (target ⟨k,hkm⟩) (hdom ⟨k,hkm⟩ (Nat.le_refl k))
      rw [prefix_update] at hchild
      exact ih (k+1) (by omega) (fun i hi => hdom i (by omega))
        (fun j hj hm reason => hreject j (by omega) hm reason) child hchild

end Erdos85
#print axioms Erdos85.finiteRowChildrenCheck_of_forall₂
#print axioms Erdos85.finiteRowCoverCheck_branch
#print axioms Erdos85.finiteRowCoverCheck_branch_of_get
#print axioms Erdos85.finiteRowCoverCheck_cover_from
