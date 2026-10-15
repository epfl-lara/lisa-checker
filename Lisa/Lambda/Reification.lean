import Lisa.Lambda.NamedConversion

/-! Reconstruct named syntax without changing the original conversion relation. -/

namespace Lisa.Lambda

/-- Assign a free identifier to each variable in a typed context. -/
abbrev Context (Γ : List LSort) := ∀ {s}, Var Γ s → Identifier

namespace Context

def empty : Context [] := fun v => nomatch v

def extend (ρ : Context Γ) (x : Identifier) : Context (s :: Γ)
  | _, .here => x
  | _, .there v => ρ v

def vars : {Γ : List LSort} → Context Γ → Finset SVar
  | [], _ => ∅
  | s :: _, ρ => insert ⟨ρ .here, s⟩ (vars (fun v => ρ (.there v)))

theorem mem_vars (ρ : Context Γ) (v : Var Γ s) : (⟨ρ v, s⟩ : SVar) ∈ ρ.vars := by
  induction v with
  | here => simp [vars]
  | there v ih => exact Finset.mem_insert_of_mem (ih _)

@[simp] theorem vars_extend (ρ : Context Γ) (x : Identifier) :
    vars (extend (s := s) ρ x) = insert ⟨x, s⟩ ρ.vars := rfl

/-- Choose a binder outside the expression's free variables and the context names. -/
def fresh (ρ : Context Γ) (xs : Finset SVar) (s : LSort) : SVar :=
  ⟨freshId ((xs ∪ ρ.vars).image SVar.id) ⟨"x", 0⟩, s⟩

theorem fresh_not_mem (ρ : Context Γ) (xs : Finset SVar) (s : LSort) :
    ρ.fresh xs s ∉ xs ∪ ρ.vars := by
  intro h
  exact freshId_not_mem ((xs ∪ ρ.vars).image SVar.id) ⟨"x", 0⟩
    (Finset.mem_image.mpr ⟨ρ.fresh xs s, h, rfl⟩)

def toSub (ρ : Context Γ) : Sub Γ [] := fun v => .free (ρ v)

end Context

namespace Term

@[simp] def freeVars : Term Γ s → Finset SVar
  | .bound _ => ∅
  | .free (s := s) x => {⟨x, s⟩}
  | .const _ => ∅
  | .app f a => f.freeVars ∪ a.freeVars
  | .lam b => b.freeVars

@[simp] theorem freeVars_rename (e : Term Γ s) (ρ : Ren Γ Δ) :
    (e.rename ρ).freeVars = e.freeVars := by
  induction e generalizing Δ <;> simp_all [rename]

/-- Restore binder names, freshening each binder against its body and context. -/
def reify : (e : Term Γ s) → Context Γ → Expr
  | .bound (s := s) v, ρ => .var ⟨ρ v, s⟩
  | .free (s := s) x, _ => .var ⟨x, s⟩
  | .const (s := s) c, _ => .const ⟨c, s⟩
  | .app f a, ρ => .app (f.reify ρ) (a.reify ρ)
  | .lam (s := s) b, ρ =>
      let x := ρ.fresh b.freeVars s
      .lam x (b.reify (ρ.extend x.id))

@[simp] theorem reify_sort (e : Term Γ s) (ρ : Context Γ) :
    (e.reify ρ).sort = some s := by
  induction e with
  | lam b ih => simp [reify, ih, Context.fresh]
  | _ => simp_all [reify]

/-- Bound free variables of the reconstructed syntax by the source and context. -/
theorem reify_freeVars (e : Term Γ s) (ρ : Context Γ) :
    (e.reify ρ).freeVars ⊆ e.freeVars ∪ ρ.vars := by
  induction e with
  | bound v => simpa [reify] using ρ.mem_vars v
  | free => simp [reify]
  | const => simp [reify]
  | app f a ihf iha =>
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp (ihf ρ hx) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
        · exact Finset.mem_union_right _ h
      · rcases Finset.mem_union.mp (iha ρ hx) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
        · exact Finset.mem_union_right _ h
  | lam b ih =>
      intro y hy
      simp only [reify, Expr.freeVars, Finset.mem_sdiff, Finset.mem_singleton] at hy
      have hb := ih _ hy.1
      simp only [Context.vars_extend, Finset.mem_union, Finset.mem_insert] at hb
      rcases hb with hb | hb | hb
      · exact Finset.mem_union_left _ hb
      · exact False.elim (hy.2 hb)
      · exact Finset.mem_union_right _ hb

end Term

/-- Interpret reconstructed syntax by the original typed substitution. -/
theorem interpretNamed_reify (e : Term Γ s) (ρ : Context Γ) (η : Names Δ) (σ : Sub Γ Δ)
    (hfree : ∀ x ∈ e.freeVars, η x = .free x.id)
    (hbound : ∀ {t} (v : Var Γ t), η ⟨ρ v, t⟩ = σ v) :
    interpretNamed (e.reify ρ) η = some ⟨s, e.subst σ⟩ := by
  induction e generalizing Δ with
  | bound v => simp [Term.reify, interpretNamed, Term.subst, hbound]
  | @free Γ s x =>
      simpa [Term.reify, interpretNamed, Term.subst] using
        congrArg (fun e : Term Δ s => some (⟨s, e⟩ : Packed.Expr Δ))
          (hfree ⟨x, s⟩ (by simp))
  | const => rfl
  | app f a ihf iha =>
      have hf := ihf ρ η σ (fun x hx => hfree x (Finset.mem_union_left _ hx)) hbound
      have ha := iha ρ η σ (fun x hx => hfree x (Finset.mem_union_right _ hx)) hbound
      simp [Term.reify, interpretNamed, hf, ha, Packed.app, Term.subst]
  | @lam s Γ t b ih =>
      let x := ρ.fresh b.freeVars s
      have hx : x ∉ b.freeVars ∪ ρ.vars := ρ.fresh_not_mem _ _
      have hf : ∀ y ∈ b.freeVars, (η.bind x) y = .free y.id := by
        intro y hy
        have hyx : y ≠ x := fun h => hx (h ▸ Finset.mem_union_left _ hy)
        simp [Names.bind_other _ hyx, hfree y hy, Term.rename]
      have hb : ∀ {u} (v : Var (s :: Γ) u),
          (η.bind x) ⟨ρ.extend x.id v, u⟩ = Sub.lift σ v := by
        intro u v
        cases v with
        | here => exact Names.bind_self η x
        | there v =>
            have hvx : (⟨ρ v, u⟩ : SVar) ≠ x :=
              fun h => hx (h ▸ Finset.mem_union_right _ (ρ.mem_vars v))
            simpa [Context.extend, Names.bind_other _ hvx, Sub.lift] using
              congrArg (Term.rename Var.there) (hbound v)
      change (interpretNamed (b.reify (ρ.extend x.id)) (η.bind x)).map
        (Packed.lam s) = _
      rw [ih _ _ _ hf hb]
      rfl

@[simp] theorem interpretNamed_reify_free (e : Term Γ s) (ρ : Context Γ) :
    interpretNamed (e.reify ρ) Names.free = some ⟨s, e.subst ρ.toSub⟩ :=
  interpretNamed_reify e ρ Names.free ρ.toSub (by intros; rfl) (by intros; rfl)

end Lisa.Lambda
