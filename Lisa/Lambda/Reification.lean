import Lisa.Lambda.NamedAlphaBetaEta

namespace Lisa.Lambda
/-- A naming assignment with a finite range, sufficient for any finite set of
ambient variables. Reification performs this assignment; it is not injective. -/

structure Context where
  lookup : LSort → Nat → Identifier
  used : LSort → Finset Identifier
  lookup_mem : ∀ s n, lookup s n ∈ used s
namespace Context

def empty : Context := ⟨fun _ _ => ⟨"_ambient", 0⟩, fun _ => {⟨"_ambient", 0⟩}, by simp⟩

def extend (ρ : Context) (x : SVar) : Context where
  lookup s n := if s = x.sort then match n with | 0 => x.id | n+1 => ρ.lookup s n else ρ.lookup s n
  used s := if s = x.sort then insert x.id (ρ.used s) else ρ.used s
  lookup_mem s n := by
    by_cases h : s = x.sort <;> cases n <;> simp [h, ρ.lookup_mem]
variable {ρ : Context} {x : SVar}

@[simp] theorem extend_zero : (ρ.extend x).lookup x.sort 0 = x.id := by simp [extend]

@[simp] theorem extend_succ : (ρ.extend x).lookup x.sort (n+1) = ρ.lookup x.sort n := by simp [extend]

@[simp] theorem extend_other (h : s ≠ x.sort) : (ρ.extend x).lookup s n = ρ.lookup s n := by simp [extend, h]

def fresh (ρ : Context) (xs : Finset SVar) (s : LSort) : SVar :=
  ⟨freshId (xs.image SVar.id ∪ ρ.used s) ⟨"x", 0⟩, s⟩

@[simp] theorem fresh_sort (ρ : Context) (xs : Finset SVar) (s : LSort) : (ρ.fresh xs s).sort = s := rfl

theorem fresh_not_used (ρ : Context) (xs : Finset SVar) (s : LSort) : (ρ.fresh xs s).id ∉ ρ.used s :=
  fun h => freshId_not_mem _ _ (Finset.mem_union_right _ h)

theorem fresh_not_mem (ρ : Context) (xs : Finset SVar) (s : LSort) : ρ.fresh xs s ∉ xs :=
  fun h => freshId_not_mem (xs.image SVar.id ∪ ρ.used s) ⟨"x", 0⟩
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ρ.fresh xs s, h, rfl⟩))

theorem ne_lookup_of_unused (ρ : Context) (hx : x.id ∉ ρ.used x.sort) (s : LSort) (n : Nat) :
    (⟨ρ.lookup s n, s⟩ : SVar) ≠ x := by
  intro h
  have hs := congrArg SVar.sort h
  have hi := congrArg SVar.id h
  exact hx (by simpa only [← hs, ← hi] using ρ.lookup_mem s n)

def toSub (ρ : Context) : Sub := fun s n => .free (ρ.lookup s n)
end Context

namespace Term

@[simp] def freeVars : Term s → Finset SVar
  | .bound _ => ∅
  | .free x => {⟨x, s⟩}
  | .const _ => ∅
  | .app f a => f.freeVars ∪ a.freeVars
  | .lam _ b => b.freeVars

@[simp] theorem freeVars_rename (e : Term s) (ρ : Ren) : (e.rename ρ).freeVars = e.freeVars := by
  induction e generalizing ρ <;> simp_all [rename]

def reify : Term s → Context → Expr
  | .bound n, ρ => .var ⟨ρ.lookup s n, s⟩
  | .free x, _ => .var ⟨x, s⟩
  | .const c, _ => .const ⟨c, s⟩
  | .app f a, ρ => .app (f.reify ρ) (a.reify ρ)
  | .lam s b, ρ => let x := ρ.fresh b.freeVars s; .lam x (b.reify (ρ.extend x))

@[simp] theorem reify_sort (e : Term s) (ρ : Context) : (e.reify ρ).sort = some s := by
  induction e generalizing ρ with
  | lam b e ih => simp [reify, ih, Context.fresh]
  | _ => simp_all [reify]

theorem reify_freeVars (e : Term s) (ρ : Context) :
    ∀ y ∈ (e.reify ρ).freeVars, y ∈ e.freeVars ∨ y.id ∈ ρ.used y.sort := by
  induction e generalizing ρ with
  | bound n =>
      intro y hy
      simp only [reify, Expr.freeVars, Finset.mem_singleton] at hy
      subst y
      exact .inr (ρ.lookup_mem _ _)
  | free x => simp [reify]
  | const c => simp [reify]
  | app f a ihf iha =>
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact (ihf ρ y hy).imp (Finset.mem_union_left _) id
      · exact (iha ρ y hy).imp (Finset.mem_union_right _) id
  | lam b e ih =>
      intro y hy
      simp only [reify, Expr.freeVars, Finset.mem_sdiff, Finset.mem_singleton] at hy
      rcases ih _ y hy.1 with hf | hu
      · exact .inl hf
      · by_cases hs : y.sort = b
        · simp only [Context.extend, Context.fresh, hs, ↓reduceIte, Finset.mem_insert] at hu
          rcases hu with hu | hu
          · exact False.elim (hy.2 (by cases y; exact congrArg₂ SVar.mk hu hs))
          · exact .inr (by simpa only [hs] using hu)
        · exact .inr (by simpa only [Context.extend, Context.fresh, hs, ↓reduceIte] using hu)
end Term

theorem interpretNamed_reify (e : Term s) (ρ : Context) (η : Names) (σ : Sub)
    (hfree : ∀ x ∈ e.freeVars, η x = .free x.id)
    (hbound : ∀ t n, η ⟨ρ.lookup t n, t⟩ = σ t n) :
    interpretNamed (e.reify ρ) η = some ⟨s, e.subst σ⟩ := by
  induction e generalizing ρ η σ with
  | bound n => simp [Term.reify, interpretNamed, Term.subst, hbound]
  | @free s x =>
      simpa [Term.reify, interpretNamed, Term.subst] using
        congrArg (fun e : Term s => some (⟨s, e⟩ : Packed.Expr)) (hfree ⟨x, s⟩ (by simp))
  | const => rfl
  | app f a ihf iha =>
      simp [Term.reify, interpretNamed, ihf ρ η σ (fun x hx => hfree x (Finset.mem_union_left _ hx)) hbound,
        iha ρ η σ (fun x hx => hfree x (Finset.mem_union_right _ hx)) hbound, Packed.app, Term.subst]
  | lam b e ih =>
      let x := ρ.fresh e.freeVars b
      have hx : x ∉ e.freeVars := ρ.fresh_not_mem e.freeVars b
      have hu : x.id ∉ ρ.used x.sort := ρ.fresh_not_used e.freeVars b
      have hf : ∀ y ∈ e.freeVars, (η.bind x) y = .free y.id := by
        intro y hy
        simp [Names.bind_other _ (show y ≠ x from fun h => hx (h ▸ hy)), hfree y hy, Term.rename]
      have hb : ∀ t n, (η.bind x) ⟨(ρ.extend x).lookup t n, t⟩ = σ.lift x.sort t n := by
        intro t n; by_cases h : t = x.sort
        · subst t; cases n with
          | zero =>
              rw [Context.extend_zero, Sub.lift_zero]
              exact Names.bind_self η x
          | succ n =>
              rw [Context.extend_succ]
              simpa [Names.bind_other _ (ρ.ne_lookup_of_unused hu x.sort n), Sub.lift] using
                congrArg (Term.rename (Ren.shift x.sort)) (hbound x.sort n)
        · rw [Context.extend_other h]
          simpa [Names.bind_other _ (ρ.ne_lookup_of_unused hu t n), Sub.lift, h] using
            congrArg (Term.rename (Ren.shift x.sort)) (hbound t n)
      change (interpretNamed (e.reify (ρ.extend x)) (η.bind x)).map (Packed.lam b) = _
      rw [ih _ _ _ hf hb]; rfl

@[simp] theorem interpretNamed_reify_free (e : Term s) (ρ : Context) :
    interpretNamed (e.reify ρ) Names.free = some ⟨s, e.subst ρ.toSub⟩ :=
  interpretNamed_reify e ρ Names.free ρ.toSub (by intros; rfl) (by intros; rfl)
end Lisa.Lambda
