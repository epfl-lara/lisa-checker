import Lisa.Syntax

/-! Describe capture-avoiding αβη conversion independently of propositional order. -/

namespace Lisa

/-- Erase binder names while retaining free identifiers, sorts, and binder depth. -/
inductive NamelessExpr where
  | free : SVar → NamelessExpr
  | bound : Nat → LSort → NamelessExpr
  | const : SConst → NamelessExpr
  | app : NamelessExpr → NamelessExpr → NamelessExpr
  | lam : LSort → NamelessExpr → NamelessExpr
  deriving DecidableEq, Repr

/-- Resolve the nearest binder first, including shadowed variable names. -/
def Expr.toNameless (bound : List SVar) : Expr → NamelessExpr
  | .var x => match bound.idxOf? x with
    | some index => .bound index x.sort
    | none => .free x
  | .const c => .const c
  | .app f a => .app (f.toNameless bound) (a.toNameless bound)
  | .lam x body => .lam x.sort (body.toNameless (x :: bound))

/-- Include the inferred sort so alpha comparison also covers malformed syntax safely. -/
def Expr.alphaKey (e : Expr) : NamelessExpr × Option LSort :=
  (e.toNameless [], e.sort)

/-- Compare binder structure without identifying distinct free variables. -/
def AlphaEq (p q : Expr) : Prop := p.alphaKey = q.alphaKey

instance : DecidableRel AlphaEq := fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- Close sort-compatible beta and eta equations under equivalence and expression contexts. -/
inductive Conversion : Expr → Expr → Prop
  | alpha {p q} : AlphaEq p q → Conversion p q
  | beta (x : SVar) (body arg : Expr) : arg.hasSort x.sort →
      Conversion (.app (.lam x body) arg) (Expr.substOne x arg body)
  | eta (x : SVar) (f : Expr) (s : LSort) :
      f.hasSort (x.sort >> s) → x ∉ f.freeVars →
      Conversion (.lam x (.app f (.var x))) f
  | symm {p q} : Conversion p q → Conversion q p
  | trans {p q r} : Conversion p q → Conversion q r → Conversion p r
  | app {f g a b} : Conversion f g → Conversion a b →
      Conversion (.app f a) (.app g b)
  | lam (x : SVar) {p q} : Conversion p q → Conversion (.lam x p) (.lam x q)

namespace Conversion

@[refl] theorem refl (e : Expr) : Conversion e e := .alpha rfl

/-- Preserve inferred sorts, even when an enclosing expression is malformed. -/
theorem preserves_sort {p q : Expr} (h : Conversion p q) : p.sort = q.sort := by
  induction h with
  | alpha h => exact congrArg Prod.snd h
  | beta x body arg ha =>
      have hs := Subst.subst_preserves_sort
        (Subst.wellSorted_insert (σ := ∅) (by trivial) ha) body
      change (.app (.lam x body) arg : Expr).sort = _
      rw [Expr.substOne, Expr.subst, hs]
      change arg.sort = some x.sort at ha
      cases hb : body.sort <;> simp [Expr.sort, hb, ha]
  | eta x f s hf _ =>
      change f.sort = some (x.sort >> s) at hf
      simp [Expr.sort, hf]
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | app _ _ ih₁ ih₂ => simp only [Expr.sort, ih₁, ih₂]
  | lam _ _ ih => simp only [Expr.sort, ih]

/-- Form alpha-beta-eta classes without changing the executable expression syntax. -/
def setoid : Setoid Expr where
  r := Conversion
  iseqv := ⟨refl, symm, trans⟩

abbrev Term := Quotient setoid

def term (e : Expr) : Term := Quotient.mk setoid e

@[simp] theorem term_eq {p q : Expr} : term p = term q ↔ Conversion p q :=
  Quotient.eq

/-- Recover a sort independently of the representative's binder names or reductions. -/
def termSort : Term → Option LSort :=
  Quotient.lift Expr.sort (fun _ _ h => preserves_sort h)

/-- Apply conversion classes using congruence of alpha-beta-eta equivalence. -/
def termApp : Term → Term → Term :=
  Quotient.lift₂ (fun f a => term (.app f a))
    (fun _ _ _ _ hf ha => Quotient.sound (.app hf ha))

def termLam (x : SVar) : Term → Term :=
  Quotient.lift (fun p => term (.lam x p))
    (fun _ _ h => Quotient.sound (.lam x h))

end Conversion

end Lisa
