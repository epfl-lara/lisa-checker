import Lisa.Syntax
import Lisa.Standard
import Lisa.Weakened

open Lisa
open Expr

@[simp]
private theorem isSame_refl {leq : Order} (href : Reflexive leq) (α : Expr) :
    isSame leq α α := by
  exact ⟨href α, href α⟩

@[simp]
private theorem ordContains_refl {leq : Order} (href : Reflexive leq) (α : Expr) (Γ : Finset Expr) :
    ordContains leq α (insert α Γ) := by
  exact ⟨α, by simp, isSame_refl href α⟩

@[simp]
private theorem setLeq_refl {leq : Order} (href : Reflexive leq) (Γ : Finset Expr) :
    setLeq leq Γ Γ := by
  intro φ hφ
  exact ⟨φ, hφ, isSame_refl href φ⟩

@[simp]
private theorem sequentLeq_refl {leq : Order} (href : Reflexive leq) (Γ Δ : Finset Expr) :
    sequentLeq leq Γ Δ Γ Δ := by
  unfold sequentLeq
  exact setLeq_refl href _

@[simp]
private theorem isSame_symm {leq : Order} {α β : Expr} (h : isSame leq α β) :
    isSame leq β α := by
  exact ⟨h.2, h.1⟩

private theorem setLeq_empty {leq : Order} (Γ : Finset Expr) :
    setLeq leq ∅ Γ := by
  intro φ hφ
  simp at hφ

private theorem setLeq_of_subset {leq : Order} (href : Reflexive leq)
    {Γ Ω : Finset Expr} (hsub : Γ ⊆ Ω) :
    setLeq leq Γ Ω := by
  intro φ hφ
  exact ⟨φ, hsub hφ, isSame_refl href φ⟩

private theorem setLeq_to_insert_of_sdiff {leq : Order} (href : Reflexive leq)
    {Γ Ω : Finset Expr} {α : Expr}
    (hrem : ∀ φ ∈ (Γ \ Ω), isSame leq α φ) :
    setLeq leq Γ (insert α Ω) := by
  intro φ hφ
  by_cases hΩ : φ ∈ Ω
  · exact ⟨φ, by simp [hΩ], isSame_refl href φ⟩
  · have hsdiff : φ ∈ Γ \ Ω := by
      simp [hφ, hΩ]
    exact ⟨α, by simp, isSame_symm (hrem φ hsdiff)⟩

private theorem setLeq_to_insert₂_of_sdiff {leq : Order} (href : Reflexive leq)
    {Γ Ω : Finset Expr} {α β : Expr}
    (hrem : ∀ φ ∈ (Γ \ Ω), isSame leq α φ ∨ isSame leq β φ) :
    setLeq leq Γ (insert α (insert β Ω)) := by
  intro φ hφ
  by_cases hΩ : φ ∈ Ω
  · exact ⟨φ, by simp [hΩ], isSame_refl href φ⟩
  · have hsdiff : φ ∈ Γ \ Ω := by
      simp [hφ, hΩ]
    rcases hrem φ hsdiff with hα | hβ
    · exact ⟨α, by simp, isSame_symm hα⟩
    · exact ⟨β, by simp, isSame_symm hβ⟩

private theorem setLeq_insert_of_ordContains {leq : Order} (href : Reflexive leq)
    {Γ : Finset Expr} {α : Expr}
    (hα : ordContains leq α Γ) :
    setLeq leq (insert α Γ) Γ := by
  intro φ hφ
  simp only [Finset.mem_insert] at hφ
  rcases hφ with rfl | hφ
  · exact hα
  · exact ⟨φ, hφ, isSame_refl href φ⟩

private theorem setLeq_singleton_of_ordContains {leq : Order}
    {Γ : Finset Expr} {α : Expr}
    (hα : ordContains leq α Γ) :
    setLeq leq {α} Γ := by
  intro φ hφ
  simp only [Finset.mem_singleton] at hφ
  subst φ
  exact hα

private theorem sequentLeq_of_setLeq {leq : Order} (hneg : NegInvariant leq)
    {Γ Δ Γ' Δ' : Finset Expr}
    (hΓ : setLeq leq Γ Γ') (hΔ : setLeq leq Δ Δ') :
    sequentLeq leq Γ Δ Γ' Δ' := by
  dsimp [sequentLeq, setLeq] at hΓ hΔ ⊢
  intro φ hφ
  rw [Finset.mem_union] at hφ
  rcases hφ with hφ | hφ
  · simp only [Finset.mem_image] at hφ
    rcases hφ with ⟨ψ, hψ, rfl⟩
    rcases hΓ ψ hψ with ⟨χ, hχ, hsame⟩
    exact ⟨neg χ, by
      simp only [Finset.mem_union, Finset.mem_image]
      exact Or.inl ⟨χ, hχ, rfl⟩, hneg hsame⟩
  · rcases hΔ φ hφ with ⟨χ, hχ, hsame⟩
    exact ⟨χ, by simp [hχ], hsame⟩

private theorem setLeq_union_self {leq : Order} (href : Reflexive leq)
    (Γ : Finset Expr) :
    setLeq leq (Γ ∪ Γ) Γ := by
  apply setLeq_of_subset href
  intro φ hφ
  simp only [Finset.mem_union] at hφ
  exact hφ.elim id id

private theorem setLeq_insert_union_self_to_insert {leq : Order}
    (href : Reflexive leq) (Γ : Finset Expr) (α : Expr) :
    setLeq leq (insert α (Γ ∪ Γ)) (insert α Γ) := by
  apply setLeq_of_subset href
  intro φ hφ
  simp only [Finset.mem_insert, Finset.mem_union] at hφ ⊢
  rcases hφ with rfl | hφ
  · exact Or.inl rfl
  · exact Or.inr (hφ.elim id id)

private theorem setLeq_insert_union_self_of_ordContains {leq : Order}
    (href : Reflexive leq) {Γ : Finset Expr} {α : Expr}
    (hα : ordContains leq α Γ) :
    setLeq leq (insert α (Γ ∪ Γ)) Γ := by
  intro φ hφ
  simp only [Finset.mem_insert, Finset.mem_union] at hφ
  rcases hφ with rfl | hφ
  · exact hα
  · rcases hφ with hφ | hφ
    · exact ⟨φ, hφ, isSame_refl href φ⟩
    · exact ⟨φ, hφ, isSame_refl href φ⟩

private theorem not_free_exists_insert_union {x : SVar} {α : Expr}
    {Γ Δ : Finset Expr}
    (hfree : x ∉ freeVars (Γ ∪ Δ)) :
    x ∉ freeVars (insert (exists_ x α) Γ ∪ Δ) := by
  change x ∉ (insert (exists_ x α) Γ ∪ Δ).biUnion (fun e : Expr => Expr.freeVars e)
  change x ∉ (Γ ∪ Δ).biUnion (fun e : Expr => Expr.freeVars e) at hfree
  simpa [Expr.exists_, Finset.biUnion_insert, Finset.union_assoc,
    Finset.union_left_comm, Finset.union_comm] using hfree

private theorem not_free_forall_insert_union {x : SVar} {α : Expr}
    {Γ Δ : Finset Expr}
    (hfree : x ∉ freeVars (Γ ∪ Δ)) :
    x ∉ freeVars (insert (forall_ x α) Γ ∪ Δ) := by
  change x ∉ (insert (forall_ x α) Γ ∪ Δ).biUnion (fun e : Expr => Expr.freeVars e)
  change x ∉ (Γ ∪ Δ).biUnion (fun e : Expr => Expr.freeVars e) at hfree
  simpa [Expr.forall_, Finset.biUnion_insert, Finset.union_assoc,
    Finset.union_left_comm, Finset.union_comm] using hfree

@[simp]
private theorem isFSet_insert {Γ : Finset Expr} {φ : Expr} (hφ : isFormula φ) (hΓ : isFSet Γ) :
    isFSet (insert φ Γ) := by
  intro ψ hψ
  simp only [Finset.mem_insert] at hψ
  rcases hψ with rfl | hψ
  · exact hφ
  · exact hΓ ψ hψ

@[simp]
private theorem isFSet_empty :
    isFSet (∅ : Finset Expr) := by
  intro φ hφ
  simp at hφ

@[simp]
private theorem isFSet_union {Γ Δ : Finset Expr} (hΓ : isFSet Γ) (hΔ : isFSet Δ) :
    isFSet (Γ ∪ Δ) := by
  intro φ hφ
  simp only [Finset.mem_union] at hφ
  rcases hφ with hφ | hφ
  · exact hΓ φ hφ
  · exact hΔ φ hφ

@[simp]
private theorem isFormula_and {α β : Expr} (hα : isFormula α) (hβ : isFormula β) :
    isFormula (and α β) := by
  dsimp [isFormula, hasSort] at hα hβ ⊢
  simp [Expr.and, hα, hβ]

@[simp]
private theorem isFormula_imp {α β : Expr} (hα : isFormula α) (hβ : isFormula β) :
    isFormula (imp α β) := by
  dsimp [isFormula, hasSort] at hα hβ ⊢
  simp [Expr.imp, hα, hβ]

@[simp]
private theorem isFormula_iff {α β : Expr} (hα : isFormula α) (hβ : isFormula β) :
    isFormula (iff α β) := by
  dsimp [isFormula, hasSort] at hα hβ ⊢
  simp [Expr.iff, hα, hβ]

@[simp]
private theorem isFormula_neg {α : Expr} (hα : isFormula α) :
    isFormula (neg α) := by
  dsimp [isFormula, hasSort] at hα ⊢
  simp [Expr.neg, hα]

@[simp]
private theorem isFormula_or {α β : Expr} (hα : isFormula α) (hβ : isFormula β) :
    isFormula (or α β) := by
  dsimp [isFormula, hasSort] at hα hβ ⊢
  simp [Expr.or, hα, hβ]

@[simp]
private theorem isFormula_forall {x : SVar} {α : Expr} (hx : x.sort = ind) (hα : isFormula α) :
    isFormula (forall_ x α) := by
  dsimp [isFormula, hasSort] at hα ⊢
  simp [Expr.forall_, hx, hα]

@[simp]
private theorem isFormula_exists {x : SVar} {α : Expr} (hx : x.sort = ind) (hα : isFormula α) :
    isFormula (exists_ x α) := by
  dsimp [isFormula, hasSort] at hα ⊢
  simp [Expr.exists_, hx, hα]

@[simp]
private theorem isTerm_epsilon {x : SVar} {α : Expr} (hx : x.sort = ind) (hα : isFormula α) :
    isTerm (epsilon_ (.lam x α)) := by
  dsimp [isTerm, hasSort, isFormula] at hα ⊢
  simp [Expr.epsilon_, hx, hα]

@[simp]
private theorem isFormula_substOne {x : SVar} {t α : Expr}
    (hx : x.sort = ind) (ht : isTerm t) (hα : isFormula α) :
    isFormula (substOne x t α) := by
  unfold Expr.substOne Expr.subst
  apply Subst.subst_preserves_hasSort
  · apply Subst.wellSorted_insert
    · simp
    · rwa [hx]
  · exact hα

@[simp]
private theorem isFormula_eq {s t : Expr} (hs : isTerm s) (ht : isTerm t) :
    isFormula (eq s t) := by
  dsimp [isFormula, hasSort, isTerm] at hs ht ⊢
  simp [Expr.eq, hs, ht]

def fwdEmbed {leq Γ Δ} (href : Reflexive leq) :
    Standard.ProofTree leq Γ Δ ->
    Weakened.ProofTree leq Γ Δ
  | .restate hΓ hΔ hΓ' hΔ' pf hle₁ hle₂ =>
      .restate hΓ hΔ hΓ' hΔ' (fwdEmbed href pf) hle₁ hle₂
  | .weakening hΓ hΔ hΓ' hΔ' pf hle =>
      .weakening hΓ hΔ hΓ' hΔ' (fwdEmbed href pf) hle
  | .hypothesis φ hφ =>
      .hypothesis φ
        (isFSet_insert hφ (show isFSet (∅ : Finset Expr) from by
          intro ψ hψ
          simp at hψ))
        (isFSet_insert hφ (show isFSet (∅ : Finset Expr) from by
          intro ψ hψ
          simp at hψ))
        (hφ)
        (ordContains_refl href φ ∅)
        (ordContains_refl href φ ∅)
  | .cut φ hΓ hΔ hΩ hΞ hφ pf₁ pf₂ =>
      Weakened.ProofTree.cut φ
        hΓ (isFSet_insert hφ hΔ)
        (fwdEmbed href pf₁)
        (isFSet_insert hφ hΩ) hΞ
        (fwdEmbed href pf₂)
        (isFSet_union hΓ hΩ) (isFSet_union hΔ hΞ)
        hφ
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΔ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot (Or.inl hχΔ)))
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΩ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot (Or.inr hχΩ)))
  | .leftAnd φ ψ hΓ hΔ hφ hψ pf =>
      Weakened.ProofTree.leftAnd φ ψ
        (isFSet_insert hφ (isFSet_insert hψ hΓ)) hΔ
        (fwdEmbed href pf)
        (isFSet_insert (isFormula_and hφ hψ) hΓ) hΔ
        hφ hψ
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχrest
          · rw [hχφ]
            exact Or.inl (isSame_refl href φ)
          · rcases hχrest with hχψ | hχΓ
            · rw [hχψ]
              exact Or.inr (isSame_refl href ψ)
            · exact False.elim (hχnot (by simp [hχΓ])))
        (by
          exact ⟨and φ ψ, by simp, isSame_refl href (and φ ψ)⟩)
  | .leftOr (Γ := Γ₁) (Ω := Ω₁) (Δ := Δ₁) (Ξ := Ξ₁) φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      let prems : List (AnnotatedSequent Expr) :=
        [
          { pre := insert φ Γ₁, post := Δ₁, val := φ },
          { pre := insert ψ Ω₁, post := Ξ₁, val := ψ }
        ]
      Weakened.ProofTree.leftOr (prems := prems)
        (Ω₁ := insert (or φ ψ) (Γ₁ ∪ Ω₁)) (Ω₂ := Δ₁ ∪ Ξ₁)
        (by simp [prems])
        (isFSet_insert (isFormula_or hφ hψ) (isFSet_union hΓ hΩ))
        (isFSet_union hΔ hΞ)
        (by
          intro prem hprem
          simp [prems] at hprem
          rcases hprem with rfl | hprem
          · exact ⟨isFSet_insert hφ hΓ, hΔ, hφ⟩
          · rw [hprem]
            exact ⟨isFSet_insert hψ hΩ, hΞ, hψ⟩)
        (by
          intro prem hprem
          let p₁ : AnnotatedSequent Expr := { pre := insert φ Γ₁, post := Δ₁, val := φ }
          let p₂ : AnnotatedSequent Expr := { pre := insert ψ Ω₁, post := Ξ₁, val := ψ }
          by_cases hp₁ : prem = p₁
          · subst prem
            exact fwdEmbed href pf₁
          · have hp₂ : prem = p₂ := by
              simpa [prems, p₁, p₂, hp₁] using hprem
            subst prem
            exact fwdEmbed href pf₂)
        (by
          intro prem hprem
          simp [prems] at hprem
          rcases hprem with rfl | hprem
          · constructor
            · intro χ hχ
              simp [hχ]
            · intro χ hχ
              simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
              rcases hχ with ⟨hχleft, hχnot⟩
              rcases hχleft with hχφ | hχΓ
              · rw [hχφ]
                exact isSame_refl href φ
              · exact False.elim (hχnot (by simp [hχΓ]))
          · rw [hprem]
            constructor
            · intro χ hχ
              simp [hχ]
            · intro χ hχ
              simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
              rcases hχ with ⟨hχleft, hχnot⟩
              rcases hχleft with hχψ | hχΩ
              · rw [hχψ]
                exact isSame_refl href ψ
              · exact False.elim (hχnot (by simp [hχΩ])))
        (by
          exact ⟨or φ ψ, by simp, isSame_refl href (or φ ψ)⟩)
  | .leftImp φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Weakened.ProofTree.leftImp φ ψ
        hΓ (isFSet_insert hφ hΔ)
        (fwdEmbed href pf₁)
        (isFSet_insert hψ hΩ) hΞ
        (fwdEmbed href pf₂)
        (isFSet_insert (isFormula_imp hφ hψ) (isFSet_union hΓ hΩ)) (isFSet_union hΔ hΞ)
        hφ hψ
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΔ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot (Or.inl hχΔ)))
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχψ | hχΩ
          · rw [hχψ]
            exact isSame_refl href ψ
          · exact False.elim (hχnot (by simp [hχΩ])))
        (by
          exact ⟨imp φ ψ, by simp, isSame_refl href (imp φ ψ)⟩)
  | .leftIff φ ψ hΓ hΔ hφ hψ pf =>
      Weakened.ProofTree.leftIff φ ψ
        (isFSet_insert (isFormula_imp hφ hψ)
          (isFSet_insert (isFormula_imp hψ hφ) hΓ))
        hΔ
        (fwdEmbed href pf)
        (isFSet_insert (isFormula_iff hφ hψ) hΓ) hΔ
        hφ hψ
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχimp | hχrest
          · rw [hχimp]
            exact Or.inl (isSame_refl href (imp φ ψ))
          · rcases hχrest with hχimp | hχΓ
            · rw [hχimp]
              exact Or.inr (isSame_refl href (imp ψ φ))
            · exact False.elim (hχnot (by simp [hχΓ])))
        (by
          exact ⟨iff φ ψ, by simp, isSame_refl href (iff φ ψ)⟩)
  | .leftNot φ hΓ hΔ hφ pf =>
      Weakened.ProofTree.leftNot φ
        hΓ (isFSet_insert hφ hΔ)
        (fwdEmbed href pf)
        (isFSet_insert (isFormula_neg hφ) hΓ) hΔ
        hφ
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΔ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot hχΔ))
        (by
          exact ⟨neg φ, by simp, isSame_refl href (neg φ)⟩)
  | .leftForall x φ t hΓ hΔ hx hφ ht pf =>
      Weakened.ProofTree.leftForall x φ t
        (isFSet_insert (isFormula_substOne hx ht hφ) hΓ) hΔ
        (fwdEmbed href pf)
        (isFSet_insert (isFormula_forall hx hφ) hΓ) hΔ
        hx hφ ht
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχsubst | hχΓ
          · rw [hχsubst]
            exact isSame_refl href (substOne x t φ)
          · exact False.elim (hχnot (by simp [hχΓ])))
        (by
          exact ⟨forall_ x φ, by simp, isSame_refl href (forall_ x φ)⟩)
  | .leftExists x φ hΓ hΔ hx hφ pf hfree =>
      Weakened.ProofTree.leftExists x φ
        (isFSet_insert hφ hΓ) hΔ
        (fwdEmbed href pf)
        (isFSet_insert (isFormula_exists hx hφ) hΓ) hΔ
        hx hφ
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΓ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot (by simp [hχΓ])))
        (by
          exact ⟨exists_ x φ, by simp, isSame_refl href (exists_ x φ)⟩)
        hfree
  | .rightAnd (Γ := Γ₁) (Ω := Ω₁) (Δ := Δ₁) (Ξ := Ξ₁) φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      let prems : List (AnnotatedSequent Expr) :=
        [
          { pre := Γ₁, post := insert φ Δ₁, val := φ },
          { pre := Ω₁, post := insert ψ Ξ₁, val := ψ }
        ]
      Weakened.ProofTree.rightAnd (prems := prems)
        (Ω₁ := Γ₁ ∪ Ω₁) (Ω₂ := insert (and φ ψ) (Δ₁ ∪ Ξ₁))
        (by simp [prems])
        (isFSet_union hΓ hΩ)
        (isFSet_insert (isFormula_and hφ hψ) (isFSet_union hΔ hΞ))
        (by
          intro prem hprem
          simp [prems] at hprem
          rcases hprem with rfl | hprem
          · exact ⟨hΓ, isFSet_insert hφ hΔ, hφ⟩
          · rw [hprem]
            exact ⟨hΩ, isFSet_insert hψ hΞ, hψ⟩)
        (by
          intro prem hprem
          let p₁ : AnnotatedSequent Expr := { pre := Γ₁, post := insert φ Δ₁, val := φ }
          let p₂ : AnnotatedSequent Expr := { pre := Ω₁, post := insert ψ Ξ₁, val := ψ }
          by_cases hp₁ : prem = p₁
          · subst prem
            exact fwdEmbed href pf₁
          · have hp₂ : prem = p₂ := by
              simpa [prems, p₁, p₂, hp₁] using hprem
            subst prem
            exact fwdEmbed href pf₂)
        (by
          intro prem hprem
          simp [prems] at hprem
          rcases hprem with rfl | hprem
          · constructor
            · intro χ hχ
              simp [hχ]
            · intro χ hχ
              simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
              rcases hχ with ⟨hχleft, hχnot⟩
              rcases hχleft with hχφ | hχΔ
              · rw [hχφ]
                exact isSame_refl href φ
              · exact False.elim (hχnot (by simp [hχΔ]))
          · rw [hprem]
            constructor
            · intro χ hχ
              simp [hχ]
            · intro χ hχ
              simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
              rcases hχ with ⟨hχleft, hχnot⟩
              rcases hχleft with hχψ | hχΞ
              · rw [hχψ]
                exact isSame_refl href ψ
              · exact False.elim (hχnot (by simp [hχΞ])))
        (by
          exact ⟨and φ ψ, by simp, isSame_refl href (and φ ψ)⟩)
  | .rightOr φ ψ hΓ hΔ hφ hψ pf =>
      Weakened.ProofTree.rightOr φ ψ
        hΓ (isFSet_insert hφ (isFSet_insert hψ hΔ))
        (fwdEmbed href pf)
        hΓ (isFSet_insert (isFormula_or hφ hψ) hΔ)
        hφ hψ
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχrest
          · rw [hχφ]
            exact Or.inl (isSame_refl href φ)
          · rcases hχrest with hχψ | hχΔ
            · rw [hχψ]
              exact Or.inr (isSame_refl href ψ)
            · exact False.elim (hχnot (by simp [hχΔ])))
        (by
          exact ⟨or φ ψ, by simp, isSame_refl href (or φ ψ)⟩)
  | .rightImp φ ψ hΓ hΔ hφ hψ pf =>
      Weakened.ProofTree.rightImp φ ψ
        (isFSet_insert hφ hΓ) (isFSet_insert hψ hΔ)
        (fwdEmbed href pf)
        hΓ (isFSet_insert (isFormula_imp hφ hψ) hΔ)
        hφ hψ
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΓ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot hχΓ))
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχψ | hχΔ
          · rw [hχψ]
            exact isSame_refl href ψ
          · exact False.elim (hχnot (by simp [hχΔ])))
        (by
          exact ⟨imp φ ψ, by simp, isSame_refl href (imp φ ψ)⟩)
  | .rightIff φ ψ hΓ hΔ hΩ hΞ hφ hψ pf₁ pf₂ =>
      Weakened.ProofTree.rightIff φ ψ
        hΓ (isFSet_insert (isFormula_imp hφ hψ) hΔ)
        (fwdEmbed href pf₁)
        hΩ (isFSet_insert (isFormula_imp hψ hφ) hΞ)
        (fwdEmbed href pf₂)
        (isFSet_union hΓ hΩ) (isFSet_insert (isFormula_iff hφ hψ) (isFSet_union hΔ hΞ))
        hφ hψ
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχimp | hχΔ
          · rw [hχimp]
            exact isSame_refl href (imp φ ψ)
          · exact False.elim (hχnot (by simp [hχΔ])))
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχimp | hχΞ
          · rw [hχimp]
            exact isSame_refl href (imp ψ φ)
          · exact False.elim (hχnot (by simp [hχΞ])))
        (by
          exact ⟨iff φ ψ, by simp, isSame_refl href (iff φ ψ)⟩)
  | .rightNot φ hΓ hΔ hφ pf =>
      Weakened.ProofTree.rightNot φ
        (isFSet_insert hφ hΓ) hΔ
        (fwdEmbed href pf)
        hΓ (isFSet_insert (isFormula_neg hφ) hΔ)
        hφ
        (by
          intro χ hχ
          simp [hχ])
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΓ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot hχΓ))
        (by
          exact ⟨neg φ, by simp, isSame_refl href (neg φ)⟩)
  | .rightForall x φ hΓ hΔ hx hφ pf hfree =>
      Weakened.ProofTree.rightForall x φ
        hΓ (isFSet_insert hφ hΔ)
        (fwdEmbed href pf)
        hΓ (isFSet_insert (isFormula_forall hx hφ) hΔ)
        hx hφ
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχφ | hχΔ
          · rw [hχφ]
            exact isSame_refl href φ
          · exact False.elim (hχnot (by simp [hχΔ])))
        (by
          exact ⟨forall_ x φ, by simp, isSame_refl href (forall_ x φ)⟩)
        (by
          have hsets : insert (forall_ x φ) Γ ∪ Δ = Γ ∪ insert (forall_ x φ) Δ := by
            ext χ
            simp [or_assoc, or_comm]
          simpa [hsets] using hfree)
  | .rightExists x φ t hΓ hΔ hx hφ ht pf =>
      Weakened.ProofTree.rightExists x φ t
        hΓ (isFSet_insert (isFormula_substOne hx ht hφ) hΔ)
        (fwdEmbed href pf)
        hΓ (isFSet_insert (isFormula_exists hx hφ) hΔ)
        hx hφ ht
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχsubst | hχΔ
          · rw [hχsubst]
            exact isSame_refl href (substOne x t φ)
          · exact False.elim (hχnot (by simp [hχΔ])))
        (by
          exact ⟨exists_ x φ, by simp, isSame_refl href (exists_ x φ)⟩)
  | .rightEpsilon x φ t hΓ hΔ hx hφ ht pf =>
      Weakened.ProofTree.rightEpsilon x φ t
        hΓ (isFSet_insert (isFormula_substOne hx ht hφ) hΔ)
        (fwdEmbed href pf)
        hΓ (isFSet_insert (isFormula_substOne hx (isTerm_epsilon hx hφ) hφ) hΔ)
        hx hφ ht
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχsubst | hχΔ
          · rw [hχsubst]
            exact isSame_refl href (substOne x t φ)
          · exact False.elim (hχnot (by simp [hχΔ])))
        (by
          exact ⟨substOne x (epsilon_ (.lam x φ)) φ, by simp, isSame_refl href (substOne x (epsilon_ (.lam x φ)) φ)⟩)
  | .leftRefl t hΓ hΔ ht pf =>
      Weakened.ProofTree.leftRefl t
        (isFSet_insert (isFormula_eq ht ht) hΓ) hΔ
        (fwdEmbed href pf)
        hΓ hΔ
        ht
        (by
          intro χ hχ
          exact hχ)
        (by
          intro χ hχ
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hχ
          rcases hχ with ⟨hχleft, hχnot⟩
          rcases hχleft with hχeq | hχΓ
          · rw [hχeq]
            exact isSame_refl href (eq t t)
          · exact False.elim (hχnot hχΓ))
  | .rightRefl t ht =>
      Weakened.ProofTree.rightRefl t
        (show isFSet (∅ : Finset Expr) from by
          intro φ hφ
          simp at hφ)
        (isFSet_insert (isFormula_eq ht ht) (show isFSet (∅ : Finset Expr) from by
          intro φ hφ
          simp at hφ))
        ht
        (ordContains_refl href (eq t t) ∅)
  | .leftSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift pf =>
      Weakened.ProofTree.leftSubstEq eqs φ
        (isFSet_insert hφs hΓ) hΔ
        (fwdEmbed href pf)
        (isFSet_union hlift (isFSet_insert hφt hΓ)) hΔ
        heqs hφ hargs hφs hφt hlift
        (by
          dsimp
          intro χ hχ
          refine ⟨χ, ?_, isSame_refl href χ⟩
          simpa [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
            or_assoc, or_left_comm, or_comm] using hχ)
        (by
          intro χ hχ
          exact hχ)
  | .rightSubstEq eqs φ hΓ hΔ heqs hφ hargs hφs hφt hlift pf =>
      Weakened.ProofTree.rightSubstEq eqs φ
        hΓ (isFSet_insert hφs hΔ)
        (fwdEmbed href pf)
        (isFSet_union hlift hΓ) (isFSet_insert hφt hΔ)
        heqs hφ hargs hφs hφt hlift
        (by
          dsimp
          intro χ hχ
          refine ⟨χ, ?_, isSame_refl href χ⟩
          simpa [Finset.mem_union, or_assoc, or_left_comm, or_comm] using hχ)
        (by
          dsimp
          intro χ hχ
          refine ⟨χ, ?_, isSame_refl href χ⟩
          simpa [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
            or_assoc, or_left_comm, or_comm] using hχ)
  | .instSchema σ hΓ hΔ hσ pf =>
      Weakened.ProofTree.instSchema σ
        hΓ hΔ
        (fwdEmbed href pf)
        (by
          intro φ hφ
          simp only [Finset.mem_image] at hφ
          rcases hφ with ⟨ψ, hψ, rfl⟩
          exact Subst.subst_preserves_hasSort hσ (hΓ ψ hψ))
        (by
          intro φ hφ
          simp only [Finset.mem_image] at hφ
          rcases hφ with ⟨ψ, hψ, rfl⟩
          exact Subst.subst_preserves_hasSort hσ (hΔ ψ hψ))
        hσ
        (sequentLeq_refl href _ _)

def bwdEmbed  {leq Γ Δ} (href : Reflexive leq) (hneg : NegInvariant leq) :
    Weakened.ProofTree leq Γ Δ ->
    Standard.ProofTree leq Γ Δ
  | .restate hΓ hΔ hΓ' hΔ' pf hle₁ hle₂ =>
      Standard.ProofTree.restate hΓ hΔ hΓ' hΔ' (bwdEmbed href hneg pf) hle₁ hle₂
  | .weakening hΓ hΔ hΓ' hΔ' pf hle =>
      Standard.ProofTree.weakening hΓ hΔ hΓ' hΔ' (bwdEmbed href hneg pf) hle
  | .hypothesis α hΩ₁ hΩ₂ hα hleft hright =>
      Standard.ProofTree.weakening
        (isFSet_insert hα isFSet_empty)
        (isFSet_insert hα isFSet_empty)
        hΩ₁ hΩ₂
        (Standard.ProofTree.hypothesis α hα)
        (sequentLeq_of_setLeq hneg
          (setLeq_singleton_of_ordContains hleft)
          (setLeq_singleton_of_ordContains hright))
  | .cut (Ω₁ := Ω₁) (Ω₂ := Ω₂) α hΓ₁ hΓ₂ pf₁ hΔ₁ hΔ₂ pf₂ hΩ₁ hΩ₂ hα hsub₁ hsub₂ hrem₁ hrem₂ =>
      let pf₁' : Standard.ProofTree leq Ω₁ (insert α Ω₂) :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          hΩ₁ (isFSet_insert hα hΩ₂)
          (bwdEmbed href hneg pf₁)
          (sequentLeq_of_setLeq hneg
            (setLeq_of_subset href hsub₁)
            (setLeq_to_insert_of_sdiff href hrem₁))
      let pf₂' : Standard.ProofTree leq (insert α Ω₁) Ω₂ :=
        Standard.ProofTree.weakening
          hΔ₁ hΔ₂
          (isFSet_insert hα hΩ₁) hΩ₂
          (bwdEmbed href hneg pf₂)
          (sequentLeq_of_setLeq hneg
            (setLeq_to_insert_of_sdiff href hrem₂)
            (setLeq_of_subset href hsub₂))
      Standard.ProofTree.weakening
        (isFSet_union hΩ₁ hΩ₁) (isFSet_union hΩ₂ hΩ₂)
        hΩ₁ hΩ₂
        (Standard.ProofTree.cut α hΩ₁ hΩ₂ hΩ₁ hΩ₂ hα pf₁' pf₂')
        (sequentLeq_of_setLeq hneg
          (setLeq_union_self href Ω₁)
          (setLeq_union_self href Ω₂))
  | .leftAnd (Ω₁ := Ω₁) (Ω₂ := Ω₂) α β hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hα hβ hsub hrem hadd =>
      let pf' : Standard.ProofTree leq (insert α (insert β Ω₁)) Ω₂ :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          (isFSet_insert hα (isFSet_insert hβ hΩ₁)) hΩ₂
          (bwdEmbed href hneg pf)
          (sequentLeq_of_setLeq hneg
            (setLeq_to_insert₂_of_sdiff href hrem)
            (setLeq_of_subset href hsub))
      Standard.ProofTree.weakening
        (isFSet_insert (isFormula_and hα hβ) hΩ₁) hΩ₂
        hΩ₁ hΩ₂
        (Standard.ProofTree.leftAnd α β hΩ₁ hΩ₂ hα hβ pf')
        (sequentLeq_of_setLeq hneg
          (setLeq_insert_of_ordContains href hadd)
          (setLeq_refl href Ω₂))
  | .leftOr hne hΩ₁ hΩ₂ hsorted hprems hpreserved hadd =>
      sorry
  | .leftImp (Ω₁ := Ω₁) (Ω₂ := Ω₂) α β hΓ₁ hΓ₂ pf₁ hΔ₁ hΔ₂ pf₂ hΩ₁ hΩ₂ hα hβ hsub₁ hsub₂ hrem₁ hrem₂ hadd =>
      let pf₁' : Standard.ProofTree leq Ω₁ (insert α Ω₂) :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          hΩ₁ (isFSet_insert hα hΩ₂)
          (bwdEmbed href hneg pf₁)
          (sequentLeq_of_setLeq hneg
            (setLeq_of_subset href hsub₁)
            (setLeq_to_insert_of_sdiff href hrem₁))
      let pf₂' : Standard.ProofTree leq (insert β Ω₁) Ω₂ :=
        Standard.ProofTree.weakening
          hΔ₁ hΔ₂
          (isFSet_insert hβ hΩ₁) hΩ₂
          (bwdEmbed href hneg pf₂)
          (sequentLeq_of_setLeq hneg
            (setLeq_to_insert_of_sdiff href hrem₂)
            (setLeq_of_subset href hsub₂))
      Standard.ProofTree.weakening
        (isFSet_insert (isFormula_imp hα hβ) (isFSet_union hΩ₁ hΩ₁))
        (isFSet_union hΩ₂ hΩ₂)
        hΩ₁ hΩ₂
        (Standard.ProofTree.leftImp α β hΩ₁ hΩ₂ hΩ₁ hΩ₂ hα hβ pf₁' pf₂')
        (sequentLeq_of_setLeq hneg
          (setLeq_insert_union_self_of_ordContains href hadd)
          (setLeq_union_self href Ω₂))
  | .leftIff (Ω₁ := Ω₁) (Ω₂ := Ω₂) α β hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hα hβ hsub hrem hadd =>
      let pf' : Standard.ProofTree leq (insert (imp α β) (insert (imp β α) Ω₁)) Ω₂ :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          (isFSet_insert (isFormula_imp hα hβ)
            (isFSet_insert (isFormula_imp hβ hα) hΩ₁)) hΩ₂
          (bwdEmbed href hneg pf)
          (sequentLeq_of_setLeq hneg
            (setLeq_to_insert₂_of_sdiff href hrem)
            (setLeq_of_subset href hsub))
      Standard.ProofTree.weakening
        (isFSet_insert (isFormula_iff hα hβ) hΩ₁) hΩ₂
        hΩ₁ hΩ₂
        (Standard.ProofTree.leftIff α β hΩ₁ hΩ₂ hα hβ pf')
        (sequentLeq_of_setLeq hneg
          (setLeq_insert_of_ordContains href hadd)
          (setLeq_refl href Ω₂))
  | .leftNot (Ω₁ := Ω₁) (Ω₂ := Ω₂) α hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hα hsub hrem hadd =>
      let pf' : Standard.ProofTree leq Ω₁ (insert α Ω₂) :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          hΩ₁ (isFSet_insert hα hΩ₂)
          (bwdEmbed href hneg pf)
          (sequentLeq_of_setLeq hneg
            (setLeq_of_subset href hsub)
            (setLeq_to_insert_of_sdiff href hrem))
      Standard.ProofTree.weakening
        (isFSet_insert (isFormula_neg hα) hΩ₁) hΩ₂
        hΩ₁ hΩ₂
        (Standard.ProofTree.leftNot α hΩ₁ hΩ₂ hα pf')
        (sequentLeq_of_setLeq hneg
          (setLeq_insert_of_ordContains href hadd)
          (setLeq_refl href Ω₂))
  | .leftForall (Ω₁ := Ω₁) (Ω₂ := Ω₂) x α t hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hx hα ht hsub hrem hadd =>
      let pf' : Standard.ProofTree leq (insert (substOne x t α) Ω₁) Ω₂ :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          (isFSet_insert (isFormula_substOne hx ht hα) hΩ₁) hΩ₂
          (bwdEmbed href hneg pf)
          (sequentLeq_of_setLeq hneg
            (setLeq_to_insert_of_sdiff href hrem)
            (setLeq_of_subset href hsub))
      Standard.ProofTree.weakening
        (isFSet_insert (isFormula_forall hx hα) hΩ₁) hΩ₂
        hΩ₁ hΩ₂
        (Standard.ProofTree.leftForall x α t hΩ₁ hΩ₂ hx hα ht pf')
        (sequentLeq_of_setLeq hneg
          (setLeq_insert_of_ordContains href hadd)
          (setLeq_refl href Ω₂))
  | .leftExists (Ω₁ := Ω₁) (Ω₂ := Ω₂) x α hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hx hα hsub hrem hadd hfree =>
      let pf' : Standard.ProofTree leq (insert α Ω₁) Ω₂ :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          (isFSet_insert hα hΩ₁) hΩ₂
          (bwdEmbed href hneg pf)
          (sequentLeq_of_setLeq hneg
            (setLeq_to_insert_of_sdiff href hrem)
            (setLeq_of_subset href hsub))
      Standard.ProofTree.weakening
        (isFSet_insert (isFormula_exists hx hα) hΩ₁) hΩ₂
        hΩ₁ hΩ₂
        (Standard.ProofTree.leftExists x α hΩ₁ hΩ₂ hx hα pf'
          (not_free_exists_insert_union hfree))
        (sequentLeq_of_setLeq hneg
          (setLeq_insert_of_ordContains href hadd)
          (setLeq_refl href Ω₂))
  | .rightAnd hne hΩ₁ hΩ₂ hsorted hprems hpreserved hadd =>
      sorry
  | .rightOr (Ω₁ := Ω₁) (Ω₂ := Ω₂) α β hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hα hβ hsub hrem hadd =>
      let pf' : Standard.ProofTree leq Ω₁ (insert α (insert β Ω₂)) :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          hΩ₁ (isFSet_insert hα (isFSet_insert hβ hΩ₂))
          (bwdEmbed href hneg pf)
          (sequentLeq_of_setLeq hneg
            (setLeq_of_subset href hsub)
            (setLeq_to_insert₂_of_sdiff href hrem))
      Standard.ProofTree.weakening
        hΩ₁ (isFSet_insert (isFormula_or hα hβ) hΩ₂)
        hΩ₁ hΩ₂
        (Standard.ProofTree.rightOr α β hΩ₁ hΩ₂ hα hβ pf')
        (sequentLeq_of_setLeq hneg
          (setLeq_refl href Ω₁)
          (setLeq_insert_of_ordContains href hadd))
  | .rightImp (Ω₁ := Ω₁) (Ω₂ := Ω₂) α β hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hα hβ hrem₁ hrem₂ hadd =>
      let pf' : Standard.ProofTree leq (insert α Ω₁) (insert β Ω₂) :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          (isFSet_insert hα hΩ₁) (isFSet_insert hβ hΩ₂)
          (bwdEmbed href hneg pf)
          (sequentLeq_of_setLeq hneg
            (setLeq_to_insert_of_sdiff href hrem₁)
            (setLeq_to_insert_of_sdiff href hrem₂))
      Standard.ProofTree.weakening
        hΩ₁ (isFSet_insert (isFormula_imp hα hβ) hΩ₂)
        hΩ₁ hΩ₂
        (Standard.ProofTree.rightImp α β hΩ₁ hΩ₂ hα hβ pf')
        (sequentLeq_of_setLeq hneg
          (setLeq_refl href Ω₁)
          (setLeq_insert_of_ordContains href hadd))
  | .rightIff (Ω₁ := Ω₁) (Ω₂ := Ω₂) α β hΓ₁ hΓ₂ pf₁ hΔ₁ hΔ₂ pf₂ hΩ₁ hΩ₂ hα hβ hsub₁ hsub₂ hrem₁ hrem₂ hadd =>
      let pf₁' : Standard.ProofTree leq Ω₁ (insert (imp α β) Ω₂) :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          hΩ₁ (isFSet_insert (isFormula_imp hα hβ) hΩ₂)
          (bwdEmbed href hneg pf₁)
          (sequentLeq_of_setLeq hneg
            (setLeq_of_subset href hsub₁)
            (setLeq_to_insert_of_sdiff href hrem₁))
      let pf₂' : Standard.ProofTree leq Ω₁ (insert (imp β α) Ω₂) :=
        Standard.ProofTree.weakening
          hΔ₁ hΔ₂
          hΩ₁ (isFSet_insert (isFormula_imp hβ hα) hΩ₂)
          (bwdEmbed href hneg pf₂)
          (sequentLeq_of_setLeq hneg
            (setLeq_of_subset href hsub₂)
            (setLeq_to_insert_of_sdiff href hrem₂))
      Standard.ProofTree.weakening
        (isFSet_union hΩ₁ hΩ₁)
        (isFSet_insert (isFormula_iff hα hβ) (isFSet_union hΩ₂ hΩ₂))
        hΩ₁ hΩ₂
        (Standard.ProofTree.rightIff α β hΩ₁ hΩ₂ hΩ₁ hΩ₂ hα hβ pf₁' pf₂')
        (sequentLeq_of_setLeq hneg
          (setLeq_union_self href Ω₁)
          (setLeq_insert_union_self_of_ordContains href hadd))
  | .rightNot (Ω₁ := Ω₁) (Ω₂ := Ω₂) α hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hα hsub hrem hadd =>
      let pf' : Standard.ProofTree leq (insert α Ω₁) Ω₂ :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          (isFSet_insert hα hΩ₁) hΩ₂
          (bwdEmbed href hneg pf)
          (sequentLeq_of_setLeq hneg
            (setLeq_to_insert_of_sdiff href hrem)
            (setLeq_of_subset href hsub))
      Standard.ProofTree.weakening
        hΩ₁ (isFSet_insert (isFormula_neg hα) hΩ₂)
        hΩ₁ hΩ₂
        (Standard.ProofTree.rightNot α hΩ₁ hΩ₂ hα pf')
        (sequentLeq_of_setLeq hneg
          (setLeq_refl href Ω₁)
          (setLeq_insert_of_ordContains href hadd))
  | .rightForall (Ω₁ := Ω₁) (Ω₂ := Ω₂) x α hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hx hα hsub hrem hadd hfree =>
      let pf' : Standard.ProofTree leq Ω₁ (insert α Ω₂) :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          hΩ₁ (isFSet_insert hα hΩ₂)
          (bwdEmbed href hneg pf)
          (sequentLeq_of_setLeq hneg
            (setLeq_of_subset href hsub)
            (setLeq_to_insert_of_sdiff href hrem))
      Standard.ProofTree.weakening
        hΩ₁ (isFSet_insert (isFormula_forall hx hα) hΩ₂)
        hΩ₁ hΩ₂
        (Standard.ProofTree.rightForall x α hΩ₁ hΩ₂ hx hα pf'
          (not_free_forall_insert_union hfree))
        (sequentLeq_of_setLeq hneg
          (setLeq_refl href Ω₁)
          (setLeq_insert_of_ordContains href hadd))
  | .rightExists (Ω₁ := Ω₁) (Ω₂ := Ω₂) x α t hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hx hα ht hsub hrem hadd =>
      let pf' : Standard.ProofTree leq Ω₁ (insert (substOne x t α) Ω₂) :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          hΩ₁ (isFSet_insert (isFormula_substOne hx ht hα) hΩ₂)
          (bwdEmbed href hneg pf)
          (sequentLeq_of_setLeq hneg
            (setLeq_of_subset href hsub)
            (setLeq_to_insert_of_sdiff href hrem))
      Standard.ProofTree.weakening
        hΩ₁ (isFSet_insert (isFormula_exists hx hα) hΩ₂)
        hΩ₁ hΩ₂
        (Standard.ProofTree.rightExists x α t hΩ₁ hΩ₂ hx hα ht pf')
        (sequentLeq_of_setLeq hneg
          (setLeq_refl href Ω₁)
          (setLeq_insert_of_ordContains href hadd))
  | .rightEpsilon (Ω₁ := Ω₁) (Ω₂ := Ω₂) x α t hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hx hα ht hsub hrem hadd =>
      let pf' : Standard.ProofTree leq Ω₁ (insert (substOne x t α) Ω₂) :=
        Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          hΩ₁ (isFSet_insert (isFormula_substOne hx ht hα) hΩ₂)
          (bwdEmbed href hneg pf)
          (sequentLeq_of_setLeq hneg
            (setLeq_of_subset href hsub)
            (setLeq_to_insert_of_sdiff href hrem))
      Standard.ProofTree.weakening
        hΩ₁ (isFSet_insert (isFormula_substOne hx (isTerm_epsilon hx hα) hα) hΩ₂)
        hΩ₁ hΩ₂
        (Standard.ProofTree.rightEpsilon x α t hΩ₁ hΩ₂ hx hα ht pf')
        (sequentLeq_of_setLeq hneg
          (setLeq_refl href Ω₁)
          (setLeq_insert_of_ordContains href hadd))
  | .leftRefl t hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ ht hsub hrem =>
      Standard.ProofTree.leftRefl t hΩ₁ hΩ₂ ht
        (Standard.ProofTree.weakening
          hΓ₁ hΓ₂
          (isFSet_insert (isFormula_eq ht ht) hΩ₁) hΩ₂
          (bwdEmbed href hneg pf)
          (sequentLeq_of_setLeq hneg
            (setLeq_to_insert_of_sdiff href hrem)
            (setLeq_of_subset href hsub)))
  | .rightRefl (Ω₁ := Ω₁) t hΩ₁ hΩ₂ ht hadd =>
      Standard.ProofTree.weakening
        isFSet_empty
        (isFSet_insert (isFormula_eq ht ht) isFSet_empty)
        hΩ₁ hΩ₂
        (Standard.ProofTree.rightRefl t ht)
        (sequentLeq_of_setLeq hneg
          (setLeq_empty Ω₁)
          (setLeq_singleton_of_ordContains hadd))
  | .leftSubstEq eqs φ hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ heqs hφ hargs hφs hφt hlift hle hsub =>
      sorry
  | .rightSubstEq eqs φ hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ heqs hφ hargs hφs hφt hlift hleft hright =>
      sorry
  | .instSchema σ hΓ₁ hΓ₂ pf hΩ₁ hΩ₂ hσ hle =>
      Standard.ProofTree.weakening
        (by
          intro φ hφ
          simp only [Finset.mem_image] at hφ
          rcases hφ with ⟨ψ, hψ, rfl⟩
          exact Subst.subst_preserves_hasSort hσ (hΓ₁ ψ hψ))
        (by
          intro φ hφ
          simp only [Finset.mem_image] at hφ
          rcases hφ with ⟨ψ, hψ, rfl⟩
          exact Subst.subst_preserves_hasSort hσ (hΓ₂ ψ hψ))
        hΩ₁ hΩ₂
        (Standard.ProofTree.instSchema σ hΓ₁ hΓ₂ hσ (bwdEmbed href hneg pf))
        hle

theorem standard_eq_weakened (leq : Order) (Γ Δ : Finset Expr)
    (href : Reflexive leq) (hneg : NegInvariant leq) :
    Nonempty (Standard.ProofTree leq Γ Δ) ↔
    Nonempty (Weakened.ProofTree leq Γ Δ) := by
  constructor <;> intro ⟨pf⟩
  · exact ⟨fwdEmbed href pf⟩
  · exact ⟨bwdEmbed href hneg pf⟩
