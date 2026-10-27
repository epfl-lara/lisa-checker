import Lisa.SCLambdaToPure.MathlibSyntax
import Lisa.SCLambdaToPure.PureEncodings

/-! Syntactic equivalence of the existing Mathlib-based FOL calculus and the
independent target in `.fol` mode. This preserves the earlier A/B reductions
while giving them the same target syntax as the epsilon reduction. -/
namespace Lisa.SCLambdaToPure.MathlibSyntax
open FirstOrder PureSyntax
variable {L : Language.{0, 0}}
noncomputable section
local instance : DecidableEq (Pure.Formula L) := Classical.decEq _
local instance : DecidableEq (PureSyntax.Formula L .fol) := Classical.decEq _

def ofContext (Γ : Pure.Context L) : PureSyntax.Context L .fol := Γ.image ofFormula
def toContext (Γ : PureSyntax.Context L .fol) : Pure.Context L := Γ.image toFormula

@[simp] theorem ofContext_empty : ofContext (L := L) ∅ = ∅ := Finset.image_empty _
@[simp] theorem ofContext_insert (p : Pure.Formula L) (Γ : Pure.Context L) :
    ofContext (insert p Γ) = insert (ofFormula p) (ofContext Γ) := Finset.image_insert _ _ _
@[simp] theorem ofContext_singleton (p : Pure.Formula L) : ofContext {p} = {ofFormula p} := Finset.image_singleton _ _
@[simp] theorem ofContext_union (Γ Δ : Pure.Context L) : ofContext (Γ ∪ Δ) = ofContext Γ ∪ ofContext Δ := Finset.image_union _ _
@[simp] theorem toContext_empty : toContext (L := L) ∅ = ∅ := Finset.image_empty _
@[simp] theorem toContext_insert (p : PureSyntax.Formula L .fol) (Γ : PureSyntax.Context L .fol) :
    toContext (insert p Γ) = insert (toFormula p) (toContext Γ) := Finset.image_insert _ _ _
@[simp] theorem toContext_singleton (p : PureSyntax.Formula L .fol) : toContext {p} = {toFormula p} := Finset.image_singleton _ _
@[simp] theorem toContext_union (Γ Δ : PureSyntax.Context L .fol) : toContext (Γ ∪ Δ) = toContext Γ ∪ toContext Δ := Finset.image_union _ _
@[simp] theorem context_roundtrip (Γ : Pure.Context L) : toContext (ofContext Γ) = Γ := by
  simp [toContext, ofContext, Finset.image_image, Function.comp_def]

@[simp] theorem ofFormula_not (p : Pure.Formula L) : ofFormula p.not = encodedNot (ofFormula p) := rfl
@[simp] theorem ofFormula_and (p q : Pure.Formula L) : ofFormula (p ⊓ q) = encodedAnd (ofFormula p) (ofFormula q) := rfl
@[simp] theorem ofFormula_or (p q : Pure.Formula L) : ofFormula (p ⊔ q) = encodedOr (ofFormula p) (ofFormula q) := rfl
@[simp] theorem ofFormula_imp (p q : Pure.Formula L) : ofFormula (p.imp q) = (ofFormula p).imp (ofFormula q) := rfl
@[simp] theorem ofFormula_top : ofFormula (⊤ : Pure.Formula L) = encodedNot .bot := rfl
@[simp] theorem ofFormula_bot : ofFormula (⊥ : Pure.Formula L) = .bot := rfl
@[simp] theorem ofFormula_equal (t u : Pure.Term L) : ofFormula (t.equal u) = .equal (ofFreeTerm t) (ofFreeTerm u) := rfl
@[simp] theorem ofFormula_forall (x : Nat) (p : Pure.Formula L) :
    ofFormula (Pure.forall_ x p) = PureSyntax.forall_ x (ofFormula p) := by
  change BFormula.all (ofFormula (Pure.bind x p)) = _
  rw [ofFormula_bind]
  rfl
@[simp] theorem ofFormula_exists (x : Nat) (p : Pure.Formula L) :
    ofFormula (Pure.exists_ x p) = encodedExists x (ofFormula p) := by
  change BFormula.imp (.all (.imp (ofFormula (Pure.bind x p)) .bot)) .bot = _
  rw [ofFormula_bind]
  rfl

theorem fresh_of {x : Nat} {Γ : Pure.Context L} (h : Pure.Fresh x Γ) : Fresh x (ofContext Γ) := by
  intro p hp
  obtain ⟨p, hp', rfl⟩ := Finset.mem_image.mp hp
  simpa only [ofFormula_freeVars] using h p hp'
theorem fresh_to {x : Nat} {Γ : PureSyntax.Context L .fol} (h : Fresh x Γ) : Pure.Fresh x (toContext Γ) := by
  intro p hp
  obtain ⟨p, hp', rfl⟩ := Finset.mem_image.mp hp
  simpa only [toFormula_freeVars] using h p hp'

def ofProof {Γ Δ : Pure.Context L} (d : Pure.ProofTree ∅ Γ Δ) :
    PureSyntax.ProofTree ∅ (ofContext Γ) (ofContext Δ) := by
  induction d with
  | hypothesis p => simpa using PureSyntax.ProofTree.hypothesis (T := ∅) (ofFormula p)
  | theoryAxiom h => exact False.elim h
  | weakening _ hΓ hΔ ih => exact ih.weakening (Finset.image_mono _ hΓ) (Finset.image_mono _ hΔ)
  | cut p _ _ ih ih' => simpa using PureSyntax.ProofTree.cut (ofFormula p) (by simpa using ih) (by simpa using ih')
  | leftFalse => simpa using PureSyntax.ProofTree.leftFalse (T := (∅ : PureSyntax.Theory L .fol))
  | rightTrue => simpa using PureSyntax.ProofTree.rightEncodedTrue (T := (∅ : PureSyntax.Theory L .fol))
  | leftAnd p q _ ih => simpa using PureSyntax.ProofTree.leftEncodedAnd (ofFormula p) (ofFormula q) (by simpa using ih)
  | rightAnd p q _ _ ih ih' => simpa using PureSyntax.ProofTree.rightEncodedAnd (ofFormula p) (ofFormula q) (by simpa using ih) (by simpa using ih')
  | leftOr p q _ _ ih ih' => simpa using PureSyntax.ProofTree.leftEncodedOr (ofFormula p) (ofFormula q) (by simpa using ih) (by simpa using ih')
  | rightOr p q _ ih => simpa using PureSyntax.ProofTree.rightEncodedOr (ofFormula p) (ofFormula q) (by simpa using ih)
  | leftImp p q _ _ ih ih' => simpa using PureSyntax.ProofTree.leftImp (ofFormula p) (ofFormula q) (by simpa using ih) (by simpa using ih')
  | rightImp p q _ ih => simpa using PureSyntax.ProofTree.rightImp (ofFormula p) (ofFormula q) (by simpa using ih)
  | leftNot p _ ih => simpa using PureSyntax.ProofTree.leftEncodedNot (ofFormula p) (by simpa using ih)
  | rightNot p _ ih => simpa using PureSyntax.ProofTree.rightEncodedNot (ofFormula p) (by simpa using ih)
  | leftForall x p t _ ih => simpa using PureSyntax.ProofTree.leftForall x (ofFormula p) (ofFreeTerm t) (by simpa using ih)
  | rightForall x p _ hΓ hΔ ih => simpa using PureSyntax.ProofTree.rightForall x (ofFormula p) (by simpa using ih) (fresh_of hΓ) (fresh_of hΔ)
  | leftExists x p _ hΓ hΔ ih => simpa using PureSyntax.ProofTree.leftEncodedExists x (ofFormula p) (by simpa using ih) (fresh_of hΓ) (fresh_of hΔ)
  | rightExists x p t _ ih => simpa using PureSyntax.ProofTree.rightEncodedExists x (ofFormula p) (ofFreeTerm t) (by simpa using ih)
  | refl t => simpa using PureSyntax.ProofTree.refl (T := ∅) (ofFreeTerm t)
  | leftSubst x p t u _ _ ih ih' => simpa using PureSyntax.ProofTree.leftSubst x (ofFormula p) (ofFreeTerm t) (ofFreeTerm u) (by simpa using ih) (by simpa using ih')
  | rightSubst x p t u _ _ ih ih' => simpa using PureSyntax.ProofTree.rightSubst x (ofFormula p) (ofFreeTerm t) (ofFreeTerm u) (by simpa using ih) (by simpa using ih')

@[simp] theorem toFormula_equal (t u : PureSyntax.Term L .fol) :
    toFormula (.equal t u) = (toFreeTerm t).equal (toFreeTerm u) := by
  have h (t : PureSyntax.Term L .fol) : (toFreeTerm t).relabel Sum.inl = toTerm t := by
    have hh := congrArg toTerm (ofFreeTerm_toFreeTerm t)
    simpa [ofFreeTerm] using hh
  change Language.BoundedFormula.equal (toTerm t) (toTerm u) = _
  rw [← h t, ← h u]
  rfl
@[simp] theorem toFormula_forall (x : Nat) (p : PureSyntax.Formula L .fol) :
    toFormula (PureSyntax.forall_ x p) = Pure.forall_ x (toFormula p) := by
  change (toFormula (PureSyntax.bind x p)).all = _
  rw [toFormula_bind]; rfl
@[simp] theorem toFormula_exists (x : Nat) (p : PureSyntax.Formula L .fol) :
    toFormula (PureSyntax.exists_ x p) = Pure.exists_ x (toFormula p) := by
  change (toFormula (PureSyntax.bind x p)).ex = _
  rw [toFormula_bind]; rfl

def toProof {Γ Δ : PureSyntax.Context L .fol} (d : PureSyntax.ProofTree ∅ Γ Δ) :
    Pure.ProofTree ∅ (toContext Γ) (toContext Δ) := by
  induction d with
  | hypothesis p => simpa using Pure.ProofTree.hypothesis (T := ∅) (toFormula p)
  | theoryAxiom h => exact False.elim h
  | weakening _ hΓ hΔ ih => exact ih.weakening (Finset.image_mono _ hΓ) (Finset.image_mono _ hΔ)
  | cut p _ _ ih ih' => simpa using Pure.ProofTree.cut (toFormula p) (by simpa using ih) (by simpa using ih')
  | leftFalse => simpa only [toContext_singleton, toContext_empty, toFormula] using Pure.ProofTree.leftFalse (T := (∅ : L.Theory))
  | rightTrue => simpa only [toContext_singleton, toContext_empty, toFormula] using Pure.ProofTree.rightTrue (T := (∅ : L.Theory))
  | leftAnd p q _ ih => simpa only [toContext_insert, toFormula] using Pure.ProofTree.leftAnd (toFormula p) (toFormula q) (by simpa using ih)
  | rightAnd p q _ _ ih ih' => simpa only [toContext_insert, toContext_union, toFormula] using Pure.ProofTree.rightAnd (toFormula p) (toFormula q) (by simpa using ih) (by simpa using ih')
  | leftOr p q _ _ ih ih' => simpa only [toContext_insert, toContext_union, toFormula] using Pure.ProofTree.leftOr (toFormula p) (toFormula q) (by simpa using ih) (by simpa using ih')
  | rightOr p q _ ih => simpa only [toContext_insert, toFormula] using Pure.ProofTree.rightOr (toFormula p) (toFormula q) (by simpa using ih)
  | leftImp p q _ _ ih ih' => simpa only [toContext_insert, toContext_union, toFormula] using Pure.ProofTree.leftImp (toFormula p) (toFormula q) (by simpa using ih) (by simpa using ih')
  | rightImp p q _ ih => simpa only [toContext_insert, toFormula] using Pure.ProofTree.rightImp (toFormula p) (toFormula q) (by simpa using ih)
  | leftIff p q _ ih =>
      simpa only [toContext_insert, toFormula] using Pure.ProofTree.leftAnd
        ((toFormula p).imp (toFormula q)) ((toFormula q).imp (toFormula p))
        (by simpa only [toContext_insert, toFormula] using ih)
  | rightIff p q _ _ ih ih' =>
      simpa only [toContext_insert, toContext_union, toFormula] using Pure.ProofTree.rightAnd
        ((toFormula p).imp (toFormula q)) ((toFormula q).imp (toFormula p))
        (by simpa only [toContext_insert, toFormula] using ih)
        (by simpa only [toContext_insert, toFormula] using ih')
  | leftNot p _ ih => simpa only [toContext_insert, toFormula] using Pure.ProofTree.leftNot (toFormula p) (by simpa using ih)
  | rightNot p _ ih => simpa only [toContext_insert, toFormula] using Pure.ProofTree.rightNot (toFormula p) (by simpa using ih)
  | leftForall x p t _ ih => simpa using Pure.ProofTree.leftForall x (toFormula p) (toFreeTerm t) (by simpa using ih)
  | rightForall x p _ hΓ hΔ ih => simpa using Pure.ProofTree.rightForall x (toFormula p) (by simpa using ih) (fresh_to hΓ) (fresh_to hΔ)
  | leftExists x p _ hΓ hΔ ih => simpa using Pure.ProofTree.leftExists x (toFormula p) (by simpa using ih) (fresh_to hΓ) (fresh_to hΔ)
  | rightExists x p t _ ih => simpa using Pure.ProofTree.rightExists x (toFormula p) (toFreeTerm t) (by simpa using ih)
  | refl t => simpa using Pure.ProofTree.refl (T := ∅) (toFreeTerm t)
  | leftSubst x p t u _ _ ih ih' => simpa using Pure.ProofTree.leftSubst x (toFormula p) (toFreeTerm t) (toFreeTerm u) (by simpa using ih) (by simpa using ih')
  | rightSubst x p t u _ _ ih ih' => simpa using Pure.ProofTree.rightSubst x (toFormula p) (toFreeTerm t) (toFreeTerm u) (by simpa using ih) (by simpa using ih')
  | epsilonWitness h => cases h
  | epsilonExt h => cases h

theorem provable_iff {Γ Δ : Pure.Context L} :
    Pure.Provable ∅ Γ Δ ↔ PureSyntax.Provable ∅ (ofContext Γ) (ofContext Δ) := by
  constructor
  · exact fun ⟨d⟩ => ⟨ofProof d⟩
  · intro ⟨d⟩
    exact ⟨by simpa using toProof d⟩

end
end Lisa.SCLambdaToPure.MathlibSyntax
