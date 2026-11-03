import Lisa.LambdaFol.PureFol
import Lisa.LambdaFol.ToPureFol.PureFolSubstitution

/-! Small derivations used by the syntactic translation. Residual assumptions
and conclusions are retained throughout, including epsilon extensionality. -/
namespace Lisa.LambdaFol.PureFol
open FirstOrder
variable {L : Language.{0, 0}}
variable [DecidableEq (Formula L)]
variable {Γ Δ : Finset (Formula L)}

namespace ProofTree

def eq_refl (t : Term L) : ProofTree Γ (insert (.equal t t) Δ) :=
  (ProofTree.refl t).weakening (Finset.empty_subset _) (by simp)

/-- Turn a contextual implication into its formula. -/
def implies {p q : Formula L} (d : ProofTree (insert p Γ) (insert q Δ)) :
    ProofTree Γ (insert (.imp p q) Δ) := .rightImp p q d

def iff_of_mutual_entailment {p q : Formula L}
    (d : ProofTree (insert p Γ) (insert q Δ))
    (e : ProofTree (insert q Γ) (insert p Δ)) :
    ProofTree Γ (insert (.iff p q) Δ) := by
  simpa using ProofTree.rightIff p q d.implies e.implies

def iff_refl (p : Formula L) : ProofTree Γ (insert (.iff p p) Δ) :=
  iff_of_mutual_entailment (hypothesisIn p (by simp) (by simp)) (hypothesisIn p (by simp) (by simp))

end ProofTree
end Lisa.LambdaFol.PureFol

/-! Contextual logical congruence, derived from the first-order rules.
The antecedent and residual succedent are retained, including under binders. -/
namespace Lisa.LambdaFol.PureFol
open FirstOrder
variable {L : Language.{0, 0}} [DecidableEq (Formula L)]
variable {Γ Δ : Finset (Formula L)} {p q r p' q' : Formula L}
namespace ProofTree

def iff_forward (d : ProofTree Γ (insert (.iff p q) Δ)) :
    ProofTree (insert p Γ) (insert q Δ) := by
  have step : ProofTree (insert (.iff p q) {p}) {q} := by
    apply leftIff
    exact (ProofTree.leftImp (Γ := {p}) (Δ := ∅) (Θ := ∅) (Ξ := {q})
      p q (.hypothesis p) (.hypothesis q)).weakening (by simp) (by simp)
  simpa using ProofTree.cut (Θ := {p}) (Ξ := {q}) (.iff p q) d step

def iff_backward (d : ProofTree Γ (insert (.iff p q) Δ)) :
    ProofTree (insert q Γ) (insert p Δ) := by
  have step : ProofTree (insert (.iff p q) {q}) {p} := by
    apply leftIff
    exact (ProofTree.leftImp (Γ := {q}) (Δ := ∅) (Θ := ∅) (Ξ := {p})
      q p (.hypothesis q) (.hypothesis p)).weakening (by simp) (by simp)
  simpa using ProofTree.cut (Θ := {q}) (Ξ := {p}) (.iff p q) d step

def iff_symm (d : ProofTree Γ (insert (.iff p q) Δ)) :
    ProofTree Γ (insert (.iff q p) Δ) := iff_of_mutual_entailment d.iff_backward d.iff_forward

def entails_trans (d : ProofTree (insert p Γ) (insert q Δ))
    (e : ProofTree (insert q Γ) (insert r Δ)) :
    ProofTree (insert p Γ) (insert r Δ) := by
  simpa using ProofTree.cut q d e

def iff_trans (d : ProofTree Γ (insert (.iff p q) Δ))
    (e : ProofTree Γ (insert (.iff q r) Δ)) :
    ProofTree Γ (insert (.iff p r) Δ) :=
  iff_of_mutual_entailment (entails_trans d.iff_forward e.iff_forward)
    (entails_trans e.iff_backward d.iff_backward)

def and_mono (d : ProofTree (insert p Γ) (insert p' Δ))
    (e : ProofTree (insert q Γ) (insert q' Δ)) :
    ProofTree (insert (.and p q) Γ) (insert (.and p' q') Δ) := by
  apply leftAnd
  have d' := d.weakening (Γ' := insert p (insert q Γ)) (by simp) (Finset.Subset.refl _)
  have e' := e.weakening (Γ' := insert p (insert q Γ)) (by simp) (Finset.Subset.refl _)
  simpa using ProofTree.rightAnd p' q' d' e'

def and_congr (d : ProofTree Γ (insert (.iff p p') Δ))
    (e : ProofTree Γ (insert (.iff q q') Δ)) :
    ProofTree Γ (insert (.iff (.and p q) (.and p' q')) Δ) :=
  iff_of_mutual_entailment (and_mono d.iff_forward e.iff_forward) (and_mono d.iff_backward e.iff_backward)

def or_mono (d : ProofTree (insert p Γ) (insert p' Δ))
    (e : ProofTree (insert q Γ) (insert q' Δ)) :
    ProofTree (insert (.or p q) Γ) (insert (.or p' q') Δ) := by
  have d' : ProofTree (insert p Γ) (insert (.or p' q') Δ) :=
    .rightOr p' q' (d.weakening (Finset.Subset.refl _) (by simp))
  have e' : ProofTree (insert q Γ) (insert (.or p' q') Δ) :=
    .rightOr p' q' (e.weakening (Finset.Subset.refl _) (by simp))
  simpa using ProofTree.leftOr p q d' e'

def or_congr (d : ProofTree Γ (insert (.iff p p') Δ))
    (e : ProofTree Γ (insert (.iff q q') Δ)) :
    ProofTree Γ (insert (.iff (.or p q) (.or p' q')) Δ) :=
  iff_of_mutual_entailment (or_mono d.iff_forward e.iff_forward) (or_mono d.iff_backward e.iff_backward)

def not_mono (d : ProofTree (insert p Γ) (insert q Δ)) :
    ProofTree (insert (.not q) Γ) (insert (.not p) Δ) := by
  have e := ProofTree.leftNot q d
  simpa [Finset.insert_comm] using ProofTree.rightNot p
    (by simpa [Finset.insert_comm] using e)

def not_congr (d : ProofTree Γ (insert (.iff p q) Δ)) :
    ProofTree Γ (insert (.iff (.not p) (.not q)) Δ) :=
  iff_of_mutual_entailment (not_mono d.iff_backward) (not_mono d.iff_forward)

def imp_mono (d : ProofTree (insert p' Γ) (insert p Δ))
    (e : ProofTree (insert q Γ) (insert q' Δ)) :
    ProofTree (insert (.imp p q) Γ) (insert (.imp p' q') Δ) := by
  apply rightImp
  simpa [Finset.insert_comm] using ProofTree.leftImp p q d e

def imp_congr (d : ProofTree Γ (insert (.iff p p') Δ))
    (e : ProofTree Γ (insert (.iff q q') Δ)) :
    ProofTree Γ (insert (.iff (.imp p q) (.imp p' q')) Δ) :=
  iff_of_mutual_entailment (imp_mono d.iff_backward e.iff_forward) (imp_mono d.iff_forward e.iff_backward)

def forall_mono (x : Identifier) (hΓ : Fresh x Γ) (hΔ : Fresh x Δ)
    (d : ProofTree (insert p Γ) (insert q Δ)) :
    ProofTree (insert (forall_ x p) Γ) (insert (forall_ x q) Δ) := by
  have e := ProofTree.leftForall x p (.var (.inl x)) (by simpa using d)
  exact .rightForall x q e
    (by simpa [Fresh] using hΓ) hΔ

def forall_congr (x : Identifier) (hΓ : Fresh x Γ) (hΔ : Fresh x Δ)
    (d : ProofTree Γ (insert (.iff p q) Δ)) :
    ProofTree Γ (insert (.iff (forall_ x p) (forall_ x q)) Δ) :=
  iff_of_mutual_entailment (forall_mono x hΓ hΔ d.iff_forward) (forall_mono x hΓ hΔ d.iff_backward)

def exists_mono (x : Identifier) (hΓ : Fresh x Γ) (hΔ : Fresh x Δ)
    (d : ProofTree (insert p Γ) (insert q Δ)) :
    ProofTree (insert (exists_ x p) Γ) (insert (exists_ x q) Δ) := by
  have e := ProofTree.rightExists x q (.var (.inl x)) (by simpa using d)
  exact .leftExists x p e hΓ
    (by simpa [Fresh] using hΔ)

def exists_congr (x : Identifier) (hΓ : Fresh x Γ) (hΔ : Fresh x Δ)
    (d : ProofTree Γ (insert (.iff p q) Δ)) :
    ProofTree Γ (insert (.iff (exists_ x p) (exists_ x q)) Δ) :=
  iff_of_mutual_entailment (exists_mono x hΓ hΔ d.iff_forward) (exists_mono x hΓ hΔ d.iff_backward)

/-- Individual equality permits substitution in either direction, in any formula. -/
def subst_iff (x : Identifier) (p : Formula L) (t u : Term L)
    (d : ProofTree Γ (insert (.equal t u) Δ)) :
    ProofTree Γ (insert (.iff (substOne x t p) (substOne x u p)) Δ) := by
  apply iff_of_mutual_entailment
  · simpa using ProofTree.rightSubst (Γ := {substOne x t p}) (Δ := ∅) x p t u
      (.hypothesis _) d
  · simpa using ProofTree.leftSubst (Γ := ∅) (Δ := {substOne x t p}) x p t u
      (.hypothesis _) d

noncomputable def eq_symm {t u : Term L}
    (d : ProofTree Γ (insert (.equal t u) Δ)) :
    ProofTree Γ (insert (.equal u t) Δ) := by
  let x := Classical.choose t.freeVars.exists_notMem
  have hx : x ∉ t.freeVars := Classical.choose_spec t.freeVars.exists_notMem
  have ht := t.subst_single_fresh t hx
  have hu := t.subst_single_fresh u hx
  have initial : ProofTree ∅ {substOne x t (.equal (.var (.inl x)) t)} := by
    simpa [substOne, BoundedFormula.subst, BoundedTerm.subst, single, ht] using (ProofTree.refl t)
  simpa [substOne, BoundedFormula.subst, BoundedTerm.subst, single, hu] using
    ProofTree.rightSubst (Γ := ∅) (Δ := ∅) x (.equal (.var (.inl x)) t) t u initial d

noncomputable def eq_trans {t u v : Term L}
    (d : ProofTree Γ (insert (.equal t u) Δ))
    (e : ProofTree Γ (insert (.equal u v) Δ)) :
    ProofTree Γ (insert (.equal t v) Δ) := by
  let x := Classical.choose t.freeVars.exists_notMem
  have hx : x ∉ t.freeVars := Classical.choose_spec t.freeVars.exists_notMem
  have hu := t.subst_single_fresh u hx
  have hv := t.subst_single_fresh v hx
  have initial : ProofTree Γ (insert (substOne x u (.equal t (.var (.inl x)))) Δ) := by
    simpa [substOne, BoundedFormula.subst, BoundedTerm.subst, single, hu] using d
  simpa [substOne, BoundedFormula.subst, BoundedTerm.subst, single, hv] using
    ProofTree.rightSubst x (.equal t (.var (.inl x))) u v initial e

def iff_expand (p q : Formula L) :
    ProofTree Γ (insert (.iff (.iff p q) (.and (.imp p q) (.imp q p))) Δ) := by
  have hp : ProofTree (insert (.imp p q) (insert (.imp q p) Γ)) (insert (.imp p q) Δ) :=
    hypothesisIn (.imp p q) (by simp) (by simp)
  have hq : ProofTree (insert (.imp p q) (insert (.imp q p) Γ)) (insert (.imp q p) Δ) :=
    hypothesisIn (.imp q p) (by simp) (by simp)
  apply iff_of_mutual_entailment
  · apply leftIff
    simpa using ProofTree.rightAnd _ _ hp hq
  · apply leftAnd
    simpa using ProofTree.rightIff p q hp hq

def iff_congr (d : ProofTree Γ (insert (.iff p p') Δ))
    (e : ProofTree Γ (insert (.iff q q') Δ)) :
    ProofTree Γ (insert (.iff (.iff p q) (.iff p' q')) Δ) :=
  iff_trans (iff_expand p q) (iff_trans (and_congr (imp_congr d e) (imp_congr e d))
    (iff_expand p' q').iff_symm)

end ProofTree
end Lisa.LambdaFol.PureFol
