import Lisa.AlphaBetaEtaNormalization.Internal.Normalization
import Lisa.AlphaBetaEtaNormalization.Internal.NamedReflection

/-! Normalization preserves scope: locally closed terms have no dangling bound indices.
The final section records the exact free names of named interpretation. -/

namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization.Algorithm

/-- Extending an environment preserves a property satisfied by all its values. -/
theorem env_extend {P : (s : LSort) → Val s → Prop} {η : Env} {a : Val s}
    (hη : ∀ t n, P t (η t n)) (ha : P s a) : ∀ t n, P t (η.extend a t n) := by
  intro t n
  by_cases h : t = s
  · subst t; cases n <;> simp only [Env.extend_zero, Env.extend_succ]
    · exact ha
    · exact hη _ _
  · simpa only [Env.extend_other h] using hη t n

private def defaultTerm : (s : LSort) → Term s
  | .ind => .const ⟨"_default", 0⟩
  | .prop => .const ⟨"top", 0⟩
  | .arrow s t => .lam s (defaultTerm t)

/-- Every bound index refers to one of the binders available at `d`. -/
def Scoped (d : Depth) : Term s → Prop
  | .bound n => n < d s
  | .free _ | .const _ => True
  | .app f a => Scoped d f ∧ Scoped d a
  | .lam b e => Scoped (d.inc b) e

private def ScopedValue : (s : LSort) → Depth → Val s → Prop
  | .ind, d, v => ∀ k, d.Extends k → Scoped k (v k)
  | .prop, d, v => ∀ k, d.Extends k → Scoped k (v k)
  | .arrow s t, d, f => ∀ k, d.Extends k → ∀ a, ScopedValue s k a → ScopedValue t k (f a)

private theorem ScopedValue.mono (h : ScopedValue s d v) (hdk : d.Extends k) : ScopedValue s k v := by
  cases s with
  | ind => exact fun l hkl => h l (hdk.trans hkl)
  | prop => exact fun l hkl => h l (hdk.trans hkl)
  | arrow s t => exact fun l hkl a ha => h l (hdk.trans hkl) a ha

private theorem quote_reflect_scoped (s : LSort) :
    (∀ d v, ScopedValue s d v → Scoped d (quote s d v)) ∧
    (∀ d r, (∀ k, d.Extends k → Scoped k (r k)) → ScopedValue s d (reflect s r)) := by
  induction s with
  | ind => exact ⟨fun d _ h => h d (Depth.extends_refl d), fun _ _ h => h⟩
  | prop => exact ⟨fun d _ h => h d (Depth.extends_refl d), fun _ _ h => h⟩
  | arrow s t ihs iht =>
      constructor
      · intro d f hf
        apply iht.1
        apply hf (d.inc s) (Depth.extends_inc d s)
        apply ihs.2
        intro k hk
        have hs := hk s
        simp only [Scoped, fresh, Depth.inc_self] at hs ⊢
        omega
      · intro d r hr k hk a ha
        apply iht.2
        intro l hl
        exact ⟨hr l (hk.trans hl), ihs.1 l a (ha.mono hl)⟩

private theorem eval_scopedValue (e : Term s) (d : Depth) (η : Env)
    (hη : ∀ t n, ScopedValue t d (η t n)) :
    ScopedValue s d (eval e η) := by
  induction e generalizing d η with
  | bound n => exact hη _ n
  | free x => exact (quote_reflect_scoped _).2 d _ (fun _ _ => True.intro)
  | const c => exact (quote_reflect_scoped _).2 d _ (fun _ _ => True.intro)
  | app f a ihf iha =>
      exact ihf d η hη d (Depth.extends_refl d) _ (iha d η hη)
  | lam b e ih =>
      exact fun k hk a ha => ih k (η.extend a) (env_extend (fun t n => (hη t n).mono hk) ha)

private theorem default_scopedValue (s : LSort) (d : Depth) (η : Env) :
    ScopedValue s d (eval (defaultTerm s) η) := by
  induction s generalizing d η with
  | ind => exact fun _ _ => True.intro
  | prop => exact fun _ _ => True.intro
  | arrow s t _ ih => exact fun k _ _ _ => ih k _

/-- Normalizing a term with no ambient indices leaves it locally closed. -/
theorem normalize_scoped (e : Term s) (hc : ∀ σ, e.subst σ = e) :
    Scoped Depth.zero (normalize e) := by
  apply (quote_reflect_scoped s).1
  rw [← hc (fun s _ => defaultTerm s), eval_subst]
  exact eval_scopedValue _ _ _ (fun t _ => default_scopedValue t _ _)

private def HasFreeVars (xs : Finset SVar) : Option Packed.Expr → Prop
  | none => True
  | some ⟨_, e⟩ => e.freeVars = xs

private theorem app_freeVars {f a : Option Packed.Expr}
    (hf : HasFreeVars xs f) (ha : HasFreeVars ys a) :
    HasFreeVars (xs ∪ ys) (f.bind fun f => a.bind (Packed.app f)) := by
  rcases f with _ | ⟨s, f⟩
  · trivial
  rcases a with _ | ⟨u, a⟩
  · trivial
  cases s with
  | ind | prop => trivial
  | arrow s t =>
      by_cases h : u = s
      · subst u
        simpa [Packed.app, HasFreeVars] using congrArg₂ (fun xs ys : Finset SVar => xs ∪ ys) hf ha
      · simp [Packed.app, h, HasFreeVars]

private theorem bind_freeVars (p : Expr) (η : Names) (x : SVar) :
    p.freeVars.biUnion (fun y => ((η.bind x) y).freeVars) =
      (p.freeVars \ {x}).biUnion (fun y => (η y).freeVars) := by
  ext z
  simp only [Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨y, hy, hz⟩
    by_cases h : y = x
    · subst y; simp at hz
    · exact ⟨y, ⟨hy, h⟩, by simpa [Names.bind_other _ h] using hz⟩
  · rintro ⟨y, ⟨hy, h⟩, hz⟩
    exact ⟨y, hy, by simpa [Names.bind_other _ h] using hz⟩

private theorem interpret_freeVars (p : Expr) (η : Names) :
    HasFreeVars (p.freeVars.biUnion (fun x => (η x).freeVars)) (interpretNamed p η) := by
  induction p generalizing η with
  | var x => simp [interpretNamed, HasFreeVars, Expr.freeVars]
  | const c => simp [interpretNamed, HasFreeVars, Expr.freeVars]
  | app f a ihf iha =>
      simpa [interpretNamed, Expr.freeVars, Finset.union_biUnion] using
        app_freeVars (ihf η) (iha η)
  | lam x b ih =>
      have hb := ih (η.bind x)
      rw [bind_freeVars] at hb
      cases he : interpretNamed b (η.bind x) with
      | none => simp [interpretNamed, he, HasFreeVars]
      | some v =>
          obtain ⟨s, t⟩ := v
          simpa [interpretNamed, he, Packed.lam, HasFreeVars, Expr.freeVars] using
            (show t.freeVars = _ by simpa [he, HasFreeVars] using hb)

theorem interpretNamed_freeVars_eq {p : Expr} {e : Term s}
    (he : interpretNamed p Names.free = some ⟨s, e⟩) : e.freeVars = p.freeVars := by
  have h := interpret_freeVars p Names.free
  simp only [he, HasFreeVars, Names.free, Term.freeVars] at h
  change e.freeVars = p.freeVars.biUnion (fun x => {x}) at h
  simpa only [Finset.biUnion_singleton_eq_self] using h

theorem interpretNamed_freeVars {p : Expr} {e : Term s}
    (he : interpretNamed p Names.free = some ⟨s, e⟩) : e.freeVars ⊆ p.freeVars :=
  (interpretNamed_freeVars_eq he).subset

end Lisa.LambdaFol
