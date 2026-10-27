import Lisa.Lambda.NamedEnvironment

/-! Agreement with the shared alpha-equivalence specification. All-binders
indices appear only in the alpha-key proof helpers in this module. -/
namespace Lisa.Lambda
/- Helpers below connect the shared alpha key's all-binders indices with the
per-sort variables. They are proof infrastructure, not a second elaborator. -/
namespace AlphaKey

def lift (b : LSort) (ρ : Ren) : Ren := fun s n =>
  if s = b then match n with | 0 => 0 | n+1 => ρ s n + 1
  else ρ s n + 1

@[simp] theorem lift_zero : lift b ρ b 0 = 0 := by simp [lift]

theorem lift_shift (b : LSort) (ρ : Ren) (s : LSort) (n : Nat) :
    lift b ρ s (Ren.shift b s n) = ρ s n + 1 := by
  by_cases h : s = b <;> simp [lift, Ren.shift, h]

def erase (e : Term s) (ρ : Ren) : NamelessExpr := match e with
  | .bound n => .bound (ρ s n) s
  | .free x => .free ⟨x, s⟩
  | .const c => .const ⟨c, s⟩
  | .app f a => .app (erase f ρ) (erase a ρ)
  | .lam b e => .lam b (erase e (lift b ρ))

def liftSub (b : LSort) (σ : Sub) : Sub := fun s n => match n with
  | 0 => .bound 0
  | n+1 => (σ s n).shift b

def resolve : List SVar → Sub → Names → Names
  | [], _, η => η
  | x :: xs, σ, η => fun y =>
      if h : y = x then h.symm ▸ σ x.sort 0
      else resolve xs (fun s n => σ s (n+1)) η y

theorem resolve_rename (xs : List SVar) (σ : Sub) (η : Names) (ρ : Ren) :
    resolve xs (fun s n => (σ s n).rename ρ) (η.rename ρ) = (resolve xs σ η).rename ρ := by
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs ih =>
      funext y
      by_cases h : y = x
      · subst y; simp [resolve, Names.rename]
      · simpa [resolve, Names.rename, h] using congrFun (ih (fun s n => σ s (n+1))) y

theorem resolve_bind (xs : List SVar) (σ : Sub) (η : Names) (x : SVar) :
    resolve (x :: xs) (liftSub x.sort σ) (η.rename (Ren.shift x.sort)) = (resolve xs σ η).bind x := by
  funext y
  by_cases h : y = x
  · subst y; simp [resolve, Names.bind, liftSub]
  · simp only [resolve, h, ↓reduceDIte, liftSub, Names.bind_other _ h]
    exact congrFun (resolve_rename xs σ η (Ren.shift x.sort)) y

theorem resolve_unbound (xs : List SVar) (σ : Sub) (η : Names)
    (h : xs.idxOf? x = none) : resolve xs σ η x = η x := by
  induction xs generalizing σ with
  | nil => rfl
  | cons y xs ih =>
      by_cases hxy : x = y
      · subst x; simp [List.idxOf?_cons] at h
      · simp [List.idxOf?_cons, Ne.symm hxy] at h
        simpa [resolve, hxy] using ih (fun s n => σ s (n+1)) (by simpa using h)

theorem resolve_bound (xs : List SVar) (σ : Sub) (η : Names)
    (h : xs.idxOf? x = some n) : resolve xs σ η x = σ x.sort n := by
  induction xs generalizing σ n with
  | nil => simp at h
  | cons y xs ih =>
      by_cases hxy : x = y
      · subst x; simp [List.idxOf?_cons] at h; subst n; simp [resolve]
      · simp [List.idxOf?_cons, Ne.symm hxy] at h
        obtain ⟨i, hi, rfl⟩ := h
        simpa [resolve, hxy] using ih (fun s n => σ s (n+1)) hi

def interpret (η : Names) (σ : Sub) : NamelessExpr → Option Packed.Expr
  | .free x => some ⟨x.sort, η x⟩
  | .const c => some ⟨c.sort, .const c.id⟩
  | .bound n s => some ⟨s, σ s n⟩
  | .app f a => do let f ← interpret η σ f; let a ← interpret η σ a; Packed.app f a
  | .lam s b => (interpret (η.rename (Ren.shift s)) (liftSub s σ) b).map (Packed.lam s)

theorem interpret_resolve (e : Expr) (xs : List SVar) (σ : Sub) (η : Names) :
    interpretNamed e (resolve xs σ η) = interpret η σ (e.toNameless xs) := by
  induction e generalizing xs σ η with
  | var x =>
      cases hi : xs.idxOf? x with
      | none => simp [interpretNamed, Expr.toNameless, hi, interpret, resolve_unbound xs σ η hi]
      | some n => simp [interpretNamed, Expr.toNameless, hi, interpret, resolve_bound xs σ η hi]
  | const => rfl
  | app f a ihf iha => simp only [interpretNamed, Expr.toNameless, interpret, ihf, iha]
  | lam x b ih => simp only [interpretNamed, Expr.toNameless, interpret, ← resolve_bind, ih]

def KeyEnv (xs : List SVar) (η : Names) (ρ : Ren) : Prop := ∀ x,
  match xs.idxOf? x with
  | none => η x = .free x.id
  | some n => ∃ m, η x = .bound m ∧ ρ x.sort m = n

theorem KeyEnv.bind (h : KeyEnv xs η ρ) (x : SVar) :
    KeyEnv (x :: xs) (η.bind x) (lift x.sort ρ) := by
  intro y; by_cases hy : y = x
  · subst y
    simp only [List.idxOf?_cons, beq_self_eq_true, ↓reduceIte]
    exact ⟨0, Names.bind_self _ _, lift_zero⟩
  · simp only [List.idxOf?_cons, show (x == y) = false from beq_eq_false_iff_ne.mpr (Ne.symm hy)]
    have hh := h y
    cases hi : xs.idxOf? y with
    | none => simp only [hi] at hh ⊢; simp [Names.bind_other _ hy, hh, Term.rename]
    | some n =>
        simp only [hi] at hh ⊢
        obtain ⟨m, hm, hr⟩ := hh
        exact ⟨Ren.shift x.sort y.sort m, by simp [Names.bind_other _ hy, hm, Term.rename],
          by simpa only [lift_shift] using congrArg (· + 1) hr⟩

theorem erase_interpretNamed (p : Expr) (h : interpretNamed p η = some ⟨s, e⟩)
    (hk : KeyEnv xs η ρ) : erase e ρ = p.toNameless xs := by
  induction p generalizing s e η xs ρ with
  | var x =>
      cases h
      have hh := hk x
      cases hi : xs.idxOf? x with
      | none => simp only [hi] at hh; simp [hh, erase, Expr.toNameless, hi]
      | some n =>
          simp only [hi] at hh
          obtain ⟨m, hm, hr⟩ := hh
          simp [hm, erase, hr, Expr.toNameless, hi]
  | const c => cases h; rfl
  | lam x b ih =>
      cases hb : interpretNamed b (η.bind x) with
      | none => simp [interpretNamed, hb] at h
      | some w =>
          rcases w with ⟨t, b'⟩
          simp only [interpretNamed, hb, Option.map_some, Packed.lam, Option.some.injEq] at h
          cases h; exact congrArg (NamelessExpr.lam x.sort) (ih hb (hk.bind x))
  | app f a ihf iha =>
      cases hf : interpretNamed f η with
      | none => simp [interpretNamed, hf] at h
      | some w =>
          rcases w with ⟨fs, f'⟩
          cases fs with
          | ind => simp [interpretNamed, hf, Packed.app] at h
          | prop => simp [interpretNamed, hf, Packed.app] at h
          | arrow u t =>
              cases ha : interpretNamed a η with
              | none => simp [interpretNamed, hf, ha] at h
              | some w =>
                  rcases w with ⟨v, a'⟩
                  by_cases hv : v = u
                  · subst v
                    simp [interpretNamed, hf, ha, Packed.app] at h
                    obtain ⟨rfl, he⟩ := h; cases he
                    exact congrArg₂ NamelessExpr.app (ihf hf hk) (iha ha hk)
                  · simp [interpretNamed, hf, ha, Packed.app, hv] at h
end AlphaKey

theorem interpretNamed_alpha (h : AlphaEq p q) (η : Names) : interpretNamed p η = interpretNamed q η :=
  (AlphaKey.interpret_resolve p [] Sub.id η).trans
    ((congrArg (AlphaKey.interpret η Sub.id) (congrArg Prod.fst h)).trans
      (AlphaKey.interpret_resolve q [] Sub.id η).symm)

theorem alpha_iff_interpretNamed_eq (hp : p.hasSort s) (hq : q.hasSort s) :
    AlphaEq p q ↔ interpretNamed p Names.free = interpretNamed q Names.free := by
  constructor
  · exact fun h => interpretNamed_alpha h _
  · intro h
    obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
    have hf := h.symm.trans he
    have hk : AlphaKey.KeyEnv [] Names.free Ren.id := fun _ => rfl
    exact Prod.ext ((AlphaKey.erase_interpretNamed p he hk).symm.trans
      (AlphaKey.erase_interpretNamed q hf hk)) (hp.trans hq.symm)
end Lisa.Lambda
