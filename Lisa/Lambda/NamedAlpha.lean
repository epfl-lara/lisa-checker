import Lisa.Lambda.NamedEnvironment

namespace Lisa.Lambda

namespace Names

/-- Interpret the nearest occurrence of each name in a binder stack. -/
def resolve : (bound : List SVar) → Sub (bound.map SVar.sort) Γ → Names Γ → Names Γ
  | [], _, η => η
  | x :: bound, σ, η => fun y =>
      if h : y = x then h.symm ▸ σ .here
      else resolve bound (fun v => σ (.there v)) η y

theorem resolve_rename (bound : List SVar) (σ : Sub (bound.map SVar.sort) Γ)
    (η : Names Γ) (ρ : Ren Γ Δ) :
    resolve bound (fun v => (σ v).rename ρ) (η.rename ρ) =
      (resolve bound σ η).rename ρ := by
  induction bound with
  | nil => rfl
  | cons x bound ih =>
      funext y
      by_cases h : y = x
      · subst y; simp [resolve, rename]
      · simpa [resolve, rename, h] using congrFun (ih (fun v => σ (.there v))) y

theorem resolve_bind (bound : List SVar) (σ : Sub (bound.map SVar.sort) Γ)
    (η : Names Γ) (x : SVar) :
    resolve (x :: bound) (Sub.lift σ) (η.rename Var.there) =
      (resolve bound σ η).bind x := by
  funext y
  by_cases h : y = x
  · subst y; simp [resolve, bind]
  · simp only [resolve, h, ↓reduceDIte, Sub.lift_there, resolve_rename, bind_other _ h]
    rfl

theorem resolve_unbound (bound : List SVar) (σ : Sub (bound.map SVar.sort) Γ)
    (η : Names Γ) (h : bound.idxOf? x = none) : resolve bound σ η x = η x := by
  induction bound with
  | nil => rfl
  | cons y bound ih =>
      by_cases hxy : x = y
      · subst x; simp [List.idxOf?_cons] at h
      · simp [List.idxOf?_cons, Ne.symm hxy] at h
        simpa [resolve, hxy] using ih (fun v => σ (.there v)) (by simpa using h)

theorem resolve_bound (bound : List SVar) (σ : Sub (bound.map SVar.sort) Γ)
    (η : Names Γ) (h : bound.idxOf? x = some n) :
    ∃ v : Var (bound.map SVar.sort) x.sort,
      Var.lookup (bound.map SVar.sort) n = some ⟨x.sort, v⟩ ∧
      resolve bound σ η x = σ v := by
  induction bound generalizing n with
  | nil => simp at h
  | cons y bound ih =>
      by_cases hxy : x = y
      · subst x
        simp [List.idxOf?_cons] at h
        subst n
        exact ⟨.here, rfl, by simp [resolve]⟩
      · simp [List.idxOf?_cons, Ne.symm hxy] at h
        obtain ⟨i, hi, rfl⟩ := h
        obtain ⟨v, hv, he⟩ := ih (fun v => σ (.there v)) hi
        exact ⟨.there v, by simp [Var.lookup, hv], by simpa [resolve, hxy] using he⟩

end Names

/-- Interpret nameless syntax with explicit bound and free environments. -/
def interpretNameless (η : Names Δ) (σ : Sub Γ Δ) :
    NamelessExpr → Option (Packed.Expr Δ)
  | .free x => some ⟨x.sort, η x⟩
  | .const c => some ⟨c.sort, .const c.id⟩
  | .bound n s => do
      let ⟨t, v⟩ ← Var.lookup Γ n
      if h : s = t then some ⟨s, σ (h ▸ v)⟩ else none
  | .app f a => do
      let f' ← interpretNameless η σ f
      let a' ← interpretNameless η σ a
      Packed.app f' a'
  | .lam s b =>
      (interpretNameless (η.rename Var.there) (Sub.lift σ) b).map (Packed.lam s)

/-- Resolve names and erase them in either order without changing the result. -/
theorem interpretNamed_resolve (e : Expr) (bound : List SVar)
    (σ : Sub (bound.map SVar.sort) Γ) (η : Names Γ) :
    interpretNamed e (Names.resolve bound σ η) =
      interpretNameless η σ (e.toNameless bound) := by
  induction e generalizing Γ bound with
  | var x =>
      cases hi : bound.idxOf? x with
      | none => simp [interpretNamed, Expr.toNameless, hi, interpretNameless,
          Names.resolve_unbound bound σ η hi]
      | some n =>
          obtain ⟨v, hv, he⟩ := Names.resolve_bound bound σ η hi
          simp [interpretNamed, Expr.toNameless, hi, interpretNameless, hv, he]
  | const => rfl
  | app f a ihf iha => simp only [interpretNamed, Expr.toNameless, interpretNameless, ihf, iha]
  | lam x b ih =>
      simp only [interpretNamed, Expr.toNameless, interpretNameless, ← Names.resolve_bind, ih]
      rfl

/-- Preserve interpretation under alpha-equivalence in every sorted environment. -/
theorem interpretNamed_alpha {e f : Expr} (h : AlphaEq e f) (η : Names Γ) :
    interpretNamed e η = interpretNamed f η := by
  have hs := congrArg Prod.fst h
  rw [Expr.alphaKey, Expr.alphaKey] at hs
  have empty : Sub [] Γ := fun v => nomatch v
  simpa only [Names.resolve] using
    (interpretNamed_resolve e [] empty η).trans
      ((congrArg (interpretNameless η empty) hs).trans
        (interpretNamed_resolve f [] empty η).symm)

/-- Recover the original typed elaborator from the identity interpretation. -/
theorem interpretNameless_identity (e : NamelessExpr) (Γ : List LSort) :
    interpretNameless Names.free (Sub.id : Sub Γ Γ) e = elaborate Γ e := by
  induction e generalizing Γ with
  | free => rfl
  | const => rfl
  | bound n s =>
      cases hv : Var.lookup Γ n with
      | none => simp [interpretNameless, elaborate, hv]
      | some w =>
          rcases w with ⟨t, v⟩
          by_cases h : s = t <;> simp [interpretNameless, elaborate, hv, h, Sub.id]
  | lam s b ih =>
      simp only [interpretNameless, Sub.lift_id]
      change (interpretNameless Names.free Sub.id b).map (Packed.lam s) = _
      rw [ih]
      cases hb : elaborate (s :: Γ) b <;> simp [elaborate, hb, Packed.lam]
  | app f a ihf iha =>
      simp only [interpretNameless, ihf, iha, elaborate]
      cases hf : elaborate Γ f with
      | none => rfl
      | some w =>
          rcases w with ⟨s, f⟩
          cases ha : elaborate Γ a with
          | none => cases s <;> rfl
          | some w => cases s <;> rfl

/-- Use the existing name-erasing elaborator when free variables remain free. -/
theorem interpretNamed_free (e : Expr) :
    interpretNamed e (Names.free : Names []) = elaborate [] (e.toNameless []) := by
  exact (interpretNamed_resolve e [] Sub.id Names.free).trans
    (interpretNameless_identity _ [])

/-- Recover the named sort from the general interpretation and identity environment. -/
theorem elaborate_named_sort (e : Expr) (bound : List SVar) :
    (elaborate (bound.map SVar.sort) (e.toNameless bound)).map Sigma.fst = e.sort := by
  rw [← interpretNameless_identity, ← interpretNamed_resolve]
  exact interpretNamed_sort e (Names.resolve bound Sub.id Names.free)

/-- Elaborate every well-sorted named expression at its original sort. -/
theorem elaborate_named {e : Expr} (h : e.hasSort s) (bound : List SVar) :
    ∃ t : Term (bound.map SVar.sort) s,
      elaborate (bound.map SVar.sort) (e.toNameless bound) = some ⟨s, t⟩ := by
  have hs := (elaborate_named_sort e bound).trans h
  cases he : elaborate (bound.map SVar.sort) (e.toNameless bound) with
  | none => simp [he] at hs
  | some w =>
      rcases w with ⟨u, t⟩
      simp [he] at hs
      subst u
      exact ⟨t, rfl⟩

/-- Reject precisely the malformed named expressions at the typed boundary. -/
theorem elaborate_named_none (e : Expr) (bound : List SVar) :
    elaborate (bound.map SVar.sort) (e.toNameless bound) = none ↔ e.sort = none := by
  rw [← elaborate_named_sort e bound]
  exact Option.map_eq_none_iff.symm


/-- Characterize named alpha-equivalence by equality of successful typed interpretations. -/
theorem alpha_iff_interpretNamed_eq {p q : Expr} (hp : p.hasSort s) (hq : q.hasSort s) :
    AlphaEq p q ↔ interpretNamed p (Names.free : Names []) = interpretNamed q Names.free := by
  constructor
  · exact fun h => interpretNamed_alpha h Names.free
  · intro h
    rw [interpretNamed_free, interpretNamed_free] at h
    obtain ⟨a, ha⟩ := elaborate_named hp []
    simp only [List.map_nil] at ha
    have hb := h.symm.trans ha
    have hk := (elaborate_sound ha).symm.trans (elaborate_sound hb)
    exact Prod.ext hk (hp.trans hq.symm)

end Lisa.Lambda
