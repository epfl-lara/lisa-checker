import Lisa.Lambda.Syntax

namespace Lisa.Lambda

/-- Describe semantic values that can be renamed into larger binder contexts. -/
structure Family where
  Obj : List LSort → Type
  map : Ren Γ Δ → Obj Γ → Obj Δ
  map_id : ∀ (v : Obj Γ), map Ren.id v = v
  map_comp : ∀ (ρ : Ren Γ Δ) (τ : Ren Δ Θ) (v : Obj Γ),
    map τ (map ρ v) = map (Ren.comp ρ τ) v

namespace Family

attribute [simp] map_id map_comp

/-- Interpret ground sorts by syntax; reflection will supply neutral terms. -/
def ground (s : LSort) : Family where
  Obj Γ := Term Γ s
  map := Term.rename
  map_id := Term.rename_id
  map_comp ρ τ v := v.rename_comp ρ τ

/-- Require semantic functions to commute with every subsequent context renaming. -/
structure Fn (A B : Family) (Γ : List LSort) where
  run : ∀ {Δ}, Ren Γ Δ → A.Obj Δ → B.Obj Δ
  natural : ∀ (ρ : Ren Γ Δ) (τ : Ren Δ Θ) (v : A.Obj Δ),
    B.map τ (run ρ v) = run (Ren.comp ρ τ) (A.map τ v)

@[ext] theorem Fn.ext {A B : Family} {Γ} {f g : Fn A B Γ}
    (h : ∀ {Δ} (ρ : Ren Γ Δ) (a : A.Obj Δ), f.run ρ a = g.run ρ a) : f = g := by
  cases f
  cases g
  congr
  funext Δ ρ a
  exact h ρ a

def arrow (A B : Family) : Family where
  Obj Γ := Fn A B Γ
  map ρ f := ⟨fun τ => f.run (Ren.comp ρ τ), by
    intro Δ Θ τ υ v
    exact f.natural (Ren.comp ρ τ) υ v⟩
  map_id _ := Fn.ext (fun _ _ => rfl)
  map_comp _ _ _ := Fn.ext (fun _ _ => rfl)

@[simp] theorem arrow_map_run (A B : Family) (f : Fn A B Γ)
    (ρ : Ren Γ Δ) (τ : Ren Δ Θ) (a : A.Obj Θ) :
    ((arrow A B).map ρ f).run τ a = f.run (Ren.comp ρ τ) a := rfl

end Family

/-- Bundle readback and reflection with their renaming laws. -/
structure Model (s : LSort) where
  values : Family
  quote : values.Obj Γ → Term Γ s
  reflect : Term Γ s → values.Obj Γ
  quote_natural : ∀ (ρ : Ren Γ Δ) (v : values.Obj Γ),
    (quote v).rename ρ = quote (values.map ρ v)
  reflect_natural : ∀ (ρ : Ren Γ Δ) (e : Term Γ s),
    values.map ρ (reflect e) = reflect (e.rename ρ)

namespace Model

attribute [simp] quote_natural reflect_natural

def ground (s : LSort) : Model s where
  values := Family.ground s
  quote := fun e => e
  reflect := fun e => e
  quote_natural _ _ := rfl
  reflect_natural _ _ := rfl

/-- Reify functions by applying them to a fresh bound variable. -/
def arrow (A : Model s) (B : Model t) : Model (s >> t) where
  values := Family.arrow A.values B.values
  quote f := .lam (B.quote (f.run Var.there (A.reflect (.bound .here))))
  reflect e := ⟨fun ρ a => B.reflect (.app (e.rename ρ) (A.quote a)), by
    intro Δ Θ ρ τ a
    simp only [reflect_natural, Term.rename, Term.rename_comp, quote_natural]⟩
  quote_natural ρ f := by
    simp only [Term.rename]
    congr 1
    rw [B.quote_natural, f.natural, A.reflect_natural]
    rfl
  reflect_natural ρ e := by
    apply Family.Fn.ext
    intro Θ τ a
    simp only [Family.arrow_map_run, Term.rename_comp]

end Model

/-- Build a Kripke model structurally on the sort, without a reduction budget. -/
def model : (s : LSort) → Model s
  | .ind => Model.ground .ind
  | .prop => Model.ground .prop
  | .arrow s t => Model.arrow (model s) (model t)

abbrev Val (Γ : List LSort) (s : LSort) := (model s).values.Obj Γ
abbrev Env (Γ Δ : List LSort) := ∀ {s}, Var Γ s → Val Δ s

namespace Env

def rename (η : Env Γ Δ) (ρ : Ren Δ Θ) : Env Γ Θ :=
  fun {s} v => (model s).values.map ρ (η v)

def extend (η : Env Γ Δ) (a : Val Δ s) : Env (s :: Γ) Δ
  | _, .here => a
  | _, .there v => η v

@[simp] theorem rename_id (η : Env Γ Δ) : @rename Γ Δ Δ η Ren.id = @η := by
  funext s v
  exact (model s).values.map_id _

@[simp] theorem rename_comp (η : Env Γ Δ) (ρ : Ren Δ Θ) (τ : Ren Θ Ξ) :
    @rename Γ Θ Ξ (rename η ρ) τ = @rename Γ Δ Ξ η (Ren.comp ρ τ) := by
  funext s v
  exact (model s).values.map_comp _ _ _

@[simp] theorem rename_extend (η : Env Γ Δ) (a : Val Δ s) (ρ : Ren Δ Θ) :
    @rename (s :: Γ) Δ Θ (extend η a) ρ =
      @extend Γ Θ s (rename η ρ) ((model s).values.map ρ a) := by
  funext t v
  cases v <;> rfl

end Env

/-- Evaluate terms together with the proof that evaluation commutes with renaming. -/
def evaluation (e : Term Γ s) :
    {run : ∀ {Δ}, Env Γ Δ → Val Δ s //
      ∀ {Δ Θ} (η : Env Γ Δ) (ρ : Ren Δ Θ),
        (model s).values.map ρ (run η) = run (Env.rename η ρ)} :=
  match e with
  | .bound v => ⟨fun η => η v, fun _ _ => rfl⟩
  | .free (s := s) x => ⟨fun _ => (model s).reflect (.free x), by
      intro Δ Θ η ρ
      rw [Model.reflect_natural]
      rfl⟩
  | .const (s := s) c => ⟨fun _ => (model s).reflect (.const c), by
      intro Δ Θ η ρ
      rw [Model.reflect_natural]
      rfl⟩
  | .app f a =>
      let ef := evaluation f
      let ea := evaluation a
      ⟨fun η => (ef.val η).run Ren.id (ea.val η), by
        intro Δ Θ η ρ
        change _ = (ef.val (Env.rename η ρ)).run Ren.id (ea.val (Env.rename η ρ))
        rw [← ef.property η ρ, ← ea.property η ρ]
        exact (ef.val η).natural Ren.id ρ (ea.val η)⟩
  | .lam b =>
      let eb := evaluation b
      ⟨fun η => ⟨fun ρ a => eb.val (Env.extend (Env.rename η ρ) a), by
          intro Θ Ξ ρ τ a
          rw [eb.property, Env.rename_extend, Env.rename_comp]⟩, by
        intro Δ Θ η ρ
        apply Family.Fn.ext
        intro Ξ τ a
        change eb.val (Env.extend (Env.rename η (Ren.comp ρ τ)) a) =
          eb.val (Env.extend (Env.rename (Env.rename η ρ) τ) a)
        rw [Env.rename_comp]⟩

abbrev eval (e : Term Γ s) (η : Env Γ Δ) : Val Δ s := (evaluation e).val η

@[simp] theorem eval_natural (e : Term Γ s) (η : Env Γ Δ) (ρ : Ren Δ Θ) :
    (model s).values.map ρ (eval e η) = eval e (Env.rename η ρ) :=
  (evaluation e).property η ρ

/-- Reflect the context, evaluate, and read back an eta-long beta-normal candidate. -/
def normalize (e : Term Γ s) : Term Γ s :=
  (model s).quote (eval e (fun v => (model _).reflect (.bound v)))

end Lisa.Lambda
