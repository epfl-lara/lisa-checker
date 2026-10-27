import Lisa.SCLambdaToPure.AToPure.PureOperations
import Lisa.SCLambdaToPure.AToPure.Syntax

/-! Embedding the independent first-order syntax, including epsilon, into
intrinsically sorted lambda terms. All target binders bind individuals.
The variable environment makes binding and renaming explicit and uniform. -/
namespace Lisa.SCLambdaToPure.PureEmbedding
open Lambda
open Pure (BTerm BFormula Renaming)
open Readback (language)
open Embedding (apps head)
open Signature (arity)
variable {α β : Type}

abbrev Variables (α : Type) (n : Nat) := α ⊕ Fin n → Lambda.Term ind

def lift (v : Variables α n) : Variables α (n + 1)
  | .inl x => (v (.inl x)).shift ind
  | .inr i => Fin.lastCases (.bound 0) (fun j => (v (.inr j)).shift ind) i

@[simp] theorem lift_free (v : Variables α n) (x : α) :
    lift v (.inl x) = (v (.inl x)).shift ind := rfl
@[simp] theorem lift_last (v : Variables α n) :
    lift v (.inr (Fin.last n)) = .bound 0 := by simp [lift]
@[simp] theorem lift_castSucc (v : Variables α n) (i : Fin n) :
    lift v (.inr i.castSucc) = (v (.inr i)).shift ind := by simp [lift]

theorem lift_shift (v : Variables α n) (x : α ⊕ Fin n) :
    lift v (Pure.shift x) = (v x).shift ind := by
  cases x <;> simp [Pure.shift]

theorem lift_precompose (v : Variables β m) (ρ : Renaming α n β m) :
    lift (v ∘ ρ) = lift v ∘ ρ.lift := by
  funext x
  cases x with
  | inl x => simp [Function.comp_def, lift_shift]
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Function.comp_def, lift_shift]

mutual
  def term {n : Nat} (v : Variables α n) : BTerm language α n → Lambda.Term ind
    | .var x => v x
    | .func (k := k) c ts => apps k (.const c.id) (fun i => term v (ts i))
    | .epsilon p => .app (.const ⟨"epsilon", 0⟩) (.lam ind (formula (lift v) p))
  def formula {n : Nat} (v : Variables α n) : BFormula language α n → Lambda.Term prop
    | .rel (k := k) c ts => apps k (head c (arity k prop)) (fun i => term v (ts i))
    | .equal t u => .app (.app (.const ⟨"eq", 0⟩) (term v t)) (term v u)
    | .top => .const ⟨"top", 0⟩
    | .bot => .const ⟨"bot", 0⟩
    | .not p => .app (.const ⟨"not", 0⟩) (formula v p)
    | .and p q => .app (.app (.const ⟨"and", 0⟩) (formula v p)) (formula v q)
    | .or p q => .app (.app (.const ⟨"or", 0⟩) (formula v p)) (formula v q)
    | .imp p q => .app (.app (.const ⟨"imp", 0⟩) (formula v p)) (formula v q)
    | .iff p q => .app (.app (.const ⟨"iff", 0⟩) (formula v p)) (formula v q)
    | .all p => .app (.const ⟨"forall", 0⟩) (.lam ind (formula (lift v) p))
    | .ex p => .app (.const ⟨"exists", 0⟩) (.lam ind (formula (lift v) p))
end

mutual
  theorem term_rename {n m : Nat} (v : Variables β m) :
      (t : BTerm language α n) → (ρ : Renaming α n β m) →
      term v (t.rename ρ) = term (v ∘ ρ) t
    | .var _, _ => rfl
    | .func c ts, ρ => by
        simp only [BTerm.rename, term]
        congr 1
        funext i
        exact term_rename v (ts i) ρ
    | .epsilon p, ρ => by
        simp only [BTerm.rename, term, formula_rename, ← lift_precompose]
  theorem formula_rename {n m : Nat} (v : Variables β m) :
      (p : BFormula language α n) → (ρ : Renaming α n β m) →
      formula v (p.rename ρ) = formula (v ∘ ρ) p
    | .rel c ts, ρ => by
        simp only [BFormula.rename, formula]
        congr 1
        funext i
        exact term_rename v (ts i) ρ
    | .equal t u, ρ => by
        simp only [BFormula.rename, formula, term_rename]
    | .top, _ => rfl
    | .bot, _ => rfl
    | .not p, ρ => by simp only [BFormula.rename, formula, formula_rename]
    | .and p q, ρ | .or p q, ρ | .imp p q, ρ | .iff p q, ρ => by simp only [BFormula.rename, formula, formula_rename]
    | .all p, ρ | .ex p, ρ => by simp only [BFormula.rename, formula, formula_rename, ← lift_precompose]
end

def environment (n : Nat) : Variables Identifier n
  | .inl x => .free x
  | .inr i => .bound (n - 1 - i.val)

theorem environment_lift (n : Nat) :
    lift (environment n) = environment (n + 1) := by
  funext x
  cases x with
  | inl x => rfl
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [environment]
      · simp only [lift_castSucc, environment, Term.shift, Term.rename, Ren.shift,
          ↓reduceIte, Fin.val_castSucc]
        congr 1
        omega

/-- Embed a Pure term with no ambient bound slots; free identifiers are retained. -/
def ofTerm (t : Pure.Term language) : Lambda.Term ind :=
  term (environment 0) t
/-- Embed a Pure formula with no ambient bound slots. -/
def ofFormula (p : Pure.Formula language) : Lambda.Term prop :=
  formula (environment 0) p

end Lisa.SCLambdaToPure.PureEmbedding

/-! Renaming and simultaneous substitution commute with the independent embedding,
including quantifier and epsilon bodies. -/
namespace Lisa.SCLambdaToPure.PureEmbedding
open Lambda
open Pure (BTerm BFormula Renaming Substitution)
open Readback (language)
open Embedding (apps head apps_replace)
variable {α β : Type}

private theorem preserves_lift_const (R : Replacement)
    (hc : ∀ s c, R.const s c = .const c) :
    ∀ s c, (R.lift ind).const s c = .const c := by
  intro s c
  simp [Replacement.lift, hc, Term.shift, Term.rename]

private theorem preserves_lift_free (R : Replacement)
    (hf : ∀ s, s ≠ ind → ∀ x, R.free s x = .free x) :
    ∀ s, s ≠ ind → ∀ x, (R.lift ind).free s x = .free x := by
  intro s hs x
  simp [Replacement.lift, hf s hs x, Term.shift, Term.rename]

theorem lift_replace (R : Replacement) (v : Variables α n) :
    (fun x => (R.lift ind).apply (lift v x)) = lift (fun x => R.apply (v x)) := by
  funext x
  cases x with
  | inl x => exact R.apply_shift (v (.inl x)) ind
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [Replacement.apply, Replacement.lift]
      · simp only [lift_castSucc]
        exact R.apply_shift (v (.inr j)) ind

private theorem head_replace (R : Replacement)
    (hc : ∀ s c, R.const s c = .const c)
    (hf : ∀ s, s ≠ ind → ∀ x, R.free s x = .free x)
    (c : Readback.Symbol) (k : Nat) :
    R.apply (head c (Signature.arity k prop)) = head c (Signature.arity k prop) := by
  have hs : Signature.arity k prop ≠ ind := by cases k <;> simp [Signature.arity]
  simp only [head]
  split
  · exact hf _ hs _
  · exact hc _ _

mutual
  theorem term_replace {n : Nat} (R : Replacement)
      (hc : ∀ s c, R.const s c = .const c)
      (hf : ∀ s, s ≠ ind → ∀ x, R.free s x = .free x)
      (v : Variables α n) : (t : BTerm language α n) →
      R.apply (term v t) = term (fun x => R.apply (v x)) t
    | .var _ => rfl
    | .func c ts => by
        simp only [term, apps_replace, Replacement.apply, hc]
        congr 1
        funext i
        exact term_replace R hc hf v (ts i)
    | .epsilon p => by
        simp only [term, Replacement.apply, hc,
          formula_replace (R.lift ind) (preserves_lift_const R hc) (preserves_lift_free R hf),
          lift_replace]
  theorem formula_replace {n : Nat} (R : Replacement)
      (hc : ∀ s c, R.const s c = .const c)
      (hf : ∀ s, s ≠ ind → ∀ x, R.free s x = .free x)
      (v : Variables α n) : (p : BFormula language α n) →
      R.apply (formula v p) = formula (fun x => R.apply (v x)) p
    | .rel c ts => by
        simp only [formula, apps_replace, head_replace R hc hf]
        congr 1
        funext i
        exact term_replace R hc hf v (ts i)
    | .equal t u => by simp only [formula, Replacement.apply, hc, term_replace R hc hf]
    | .top => hc _ _
    | .bot => hc _ _
    | .not p => by simp only [formula, Replacement.apply, hc, formula_replace R hc hf]
    | .and p q | .or p q | .imp p q | .iff p q => by simp only [formula, Replacement.apply, hc, formula_replace R hc hf]
    | .all p | .ex p => by
        simp only [formula, Replacement.apply, hc,
          formula_replace (R.lift ind) (preserves_lift_const R hc) (preserves_lift_free R hf),
          lift_replace]
end

theorem lift_rename (v : Variables α n) (ρ : Ren) :
    (fun x => (lift v x).rename (ρ.lift ind)) = lift (fun x => (v x).rename ρ) := by
  funext x
  cases x with
  | inl x => simp [Term.shift, Term.rename_comp, Ren.lift_shift]
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i <;>
        simp [Term.rename, Term.rename_comp, Ren.lift_shift]

theorem term_renameSource {n : Nat} (v : Variables α n) (ρ : Ren) :
    (t : BTerm language α n) →
    (term v t).rename ρ = term (fun x => (v x).rename ρ) t := by
  intro t
  simpa only [Replacement.apply_ofSub, Term.subst_ofRen] using
    term_replace (Replacement.ofSub (Sub.ofRen ρ)) (by intros; rfl) (by intros; rfl) v t

theorem formula_renameSource {n : Nat} (v : Variables α n) (ρ : Ren) :
    (p : BFormula language α n) →
    (formula v p).rename ρ = formula (fun x => (v x).rename ρ) p := by
  intro p
  simpa only [Replacement.apply_ofSub, Term.subst_ofRen] using
    formula_replace (Replacement.ofSub (Sub.ofRen ρ)) (by intros; rfl) (by intros; rfl) v p

theorem term_shift {n : Nat} (v : Variables α n) (t : BTerm language α n) :
    term (lift v) (t.rename Pure.shift) = (term v t).shift ind := by
  rw [term_rename, Term.shift, term_renameSource]
  congr 1
  funext x
  exact lift_shift v x

theorem lift_substitution (v : Variables β m) (σ : Substitution language α n β m) :
    (fun x => term (lift v) (σ.lift x)) = lift (fun x => term v (σ x)) := by
  funext x
  cases x with
  | inl x => simp [term_shift]
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [term, term_shift]

mutual
  theorem term_subst {n m : Nat} (v : Variables β m) :
      (t : BTerm language α n) → (σ : Substitution language α n β m) →
      term v (t.subst σ) = term (fun x => term v (σ x)) t
    | .var _, _ => rfl
    | .func c ts, σ => by
        simp only [BTerm.subst, term]
        congr 1
        funext i
        exact term_subst v (ts i) σ
    | .epsilon p, σ => by
        simp only [BTerm.subst, term, formula_subst, lift_substitution]
  theorem formula_subst {n m : Nat} (v : Variables β m) :
      (p : BFormula language α n) → (σ : Substitution language α n β m) →
      formula v (p.subst σ) = formula (fun x => term v (σ x)) p
    | .rel c ts, σ => by
        simp only [BFormula.subst, formula]
        congr 1
        funext i
        exact term_subst v (ts i) σ
    | .equal t u, σ => by simp only [BFormula.subst, formula, term_subst]
    | .top, _ => rfl
    | .bot, _ => rfl
    | .not p, σ => by simp only [BFormula.subst, formula, formula_subst]
    | .and p q, σ | .or p q, σ | .imp p q, σ | .iff p q, σ => by simp only [BFormula.subst, formula, formula_subst]
    | .all p, σ | .ex p, σ => by simp only [BFormula.subst, formula, formula_subst, lift_substitution]
end

end Lisa.SCLambdaToPure.PureEmbedding

/-! Individual replacement and binding commute with the embedding. Constants
remain constants; only free individual variables are substituted. -/
namespace Lisa.SCLambdaToPure.PureEmbedding
open Lambda
open Pure (BTerm BFormula)
open Readback (language)
open Embedding (apps head apps_replace)
variable {α : Type}

private theorem environment_subst (n : Nat) (σ : Sub)
    (hσ : ∀ i < n, σ ind i = .bound i) :
    (fun x => (Replacement.ofSub σ).apply (environment n x)) = environment n := by
  funext x
  cases x with
  | inl x => rfl
  | inr i =>
      simp only [Replacement.apply_ofSub, environment, Term.subst]
      exact hσ _ (by omega)

theorem term_scoped (t : BTerm language Identifier n) (σ : Sub)
    (hσ : ∀ i < n, σ ind i = .bound i) :
    (term (environment n) t).subst σ = term (environment n) t := by
  rw [← Replacement.apply_ofSub, term_replace _ (by intros; rfl) (by intros; rfl),
    environment_subst n σ hσ]

theorem formula_scoped (p : BFormula language Identifier n) (σ : Sub)
    (hσ : ∀ i < n, σ ind i = .bound i) :
    (formula (environment n) p).subst σ = formula (environment n) p := by
  rw [← Replacement.apply_ofSub, formula_replace _ (by intros; rfl) (by intros; rfl),
    environment_subst n σ hσ]

theorem ofTerm_subst_eq (t : Pure.Term language) (σ : Sub) :
    (ofTerm t).subst σ = ofTerm t := term_scoped t σ (by simp)

theorem ofFormula_subst_eq (p : Pure.Formula language) (σ : Sub) :
    (ofFormula p).subst σ = ofFormula p := formula_scoped p σ (by simp)

theorem formula_substOne
    (x : Identifier) (t : Pure.Term language) (p : Pure.Formula language) :
    ofFormula (Pure.substOne x t p) =
      (Replacement.single ⟨x, ind⟩ (ofTerm t)).apply (ofFormula p) := by
  let R := Replacement.single ⟨x, ind⟩ (ofTerm t)
  change formula _ (p.subst _) = R.apply (formula _ p)
  rw [formula_subst, formula_replace R (by intros; rfl) (Readback.single_heads _ _).free]
  congr 1
  funext z
  cases z with
  | inl y =>
      by_cases hy : y = x
      · subst y; simp [Pure.single, R, environment, Replacement.apply, Replacement.single]
        rfl
      · simp [Pure.single, hy, R, environment, Replacement.apply, Replacement.single, term]
  | inr i => exact Fin.elim0 i

theorem formula_bind
    (x : Identifier) (p : Pure.Formula language) :
    formula (environment 1) (Pure.bind x p) =
      (Replacement.abstract ⟨x, ind⟩).apply (ofFormula p) := by
  let R := Replacement.abstract ⟨x, ind⟩
  have hc : ∀ s c, R.const s c = .const c := by intros; rfl
  have hf : ∀ s, s ≠ ind → ∀ y, R.free s y = .free y := by
    intro s hs y
    simp [R, Replacement.abstract, Names.bind, Names.free, hs, Term.rename]
  change formula _ (p.rename _) = R.apply (formula _ p)
  rw [formula_rename, formula_replace R hc hf]
  congr 1
  funext z
  cases z with
  | inl y =>
      by_cases hy : y = x
      · subst y
        simp [Pure.close, environment, R, Replacement.abstract,
          Replacement.apply, Names.bind]
      · simp [Pure.close, hy, environment, R, Replacement.abstract,
          Replacement.apply, Names.bind, Names.free, Term.rename]
  | inr i => exact Fin.elim0 i

end Lisa.SCLambdaToPure.PureEmbedding
