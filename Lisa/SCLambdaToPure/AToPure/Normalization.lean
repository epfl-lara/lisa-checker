import Lisa.Lambda.Normalization
import Lisa.Lambda.NamedReflection

/-!
# The shape of canonical lambda expressions

Conversion correctness alone does not say that the output of normalization is
beta-normal and eta-long. These predicates and the readiness argument establish
that additional property for the existing evaluator, without changing it.
-/

namespace Lisa.SCLambdaToPure

open Lambda

mutual
  /-- A variable or constant applied to canonical arguments. -/
  inductive Neutral : {s : LSort} → Term s → Prop where
    | bound (n : Nat) : Neutral (.bound (s := s) n)
    | free (x : Identifier) : Neutral (.free (s := s) x)
    | const (c : Identifier) : Neutral (.const (s := s) c)
    | app {f : Term (s >> t)} {a : Term s} :
        Neutral f → Canonical a → Neutral (.app f a)

  /-- Eta-long normal forms: abstractions at arrow sorts, neutral terms at base sorts. -/
  inductive Canonical : {s : LSort} → Term s → Prop where
    | ind {e : Term ind} : Neutral e → Canonical e
    | prop {e : Term prop} : Neutral e → Canonical e
    | lam {e : Term t} : Canonical e → Canonical (.lam s e)
end

private def Ready : (s : LSort) → Val s → Prop
  | .ind, v => ∀ d, Canonical (v d)
  | .prop, v => ∀ d, Canonical (v d)
  | .arrow s t, f => ∀ a, Ready s a → Ready t (f a)

private theorem readback_ready (s : LSort) :
    (∀ v, Ready s v → ∀ d, Canonical (quote s d v)) ∧
    (∀ n : Residual s, (∀ d, Neutral (n d)) → Ready s (reflect s n)) := by
  induction s with
  | ind => exact ⟨fun _ h => h, fun _ h d => .ind (h d)⟩
  | prop => exact ⟨fun _ h => h, fun _ h d => .prop (h d)⟩
  | arrow s t ihs iht =>
      constructor
      · intro f hf d
        exact .lam (iht.1 _ (hf _ (ihs.2 _ (fun _ => .bound _))) _)
      · intro n hn a ha
        exact iht.2 _ (fun d => .app (hn d) (ihs.1 a ha d))

/-- Extending an environment preserves a property satisfied by all its values. -/
theorem env_extend {P : (s : LSort) → Val s → Prop} {η : Env} {a : Val s}
    (hη : ∀ t n, P t (η t n)) (ha : P s a) : ∀ t n, P t (η.extend a t n) := by
  intro t n
  by_cases h : t = s
  · subst t; cases n <;> simp only [Env.extend_zero, Env.extend_succ]
    · exact ha
    · exact hη _ _
  · simpa only [Env.extend_other h] using hη t n

private theorem eval_ready (e : Term s) (η : Env)
    (hη : ∀ t n, Ready t (η t n)) : Ready s (eval e η) := by
  induction e generalizing η with
  | bound n => exact hη _ n
  | free x => exact (readback_ready _).2 _ (fun _ => .free x)
  | const c => exact (readback_ready _).2 _ (fun _ => .const c)
  | app f a ihf iha => exact ihf η hη _ (iha η hη)
  | lam s b ih => exact fun a ha => ih _ (env_extend hη ha)

/-- The existing normalizer really produces beta-normal, eta-long syntax. -/
theorem normalize_canonical (e : Term s) : Canonical (normalize e) :=
  (readback_ready s).1 _
    (eval_ready e ambient (fun t _ =>
      (readback_ready t).2 _ (fun _ => .bound _))) _

/-- At a function sort a canonical expression starts with a lambda. -/
theorem Canonical.arrow {e : Term (s >> t)} (h : Canonical e) :
    ∃ b : Term t, e = .lam s b ∧ Canonical b := by
  cases h with
  | lam h => exact ⟨_, rfl, h⟩

/-- No canonical application has a lambda at its head. -/
theorem Neutral.not_lam {e : Term (s >> t)} (h : Neutral e) (b : Term t) :
    e ≠ .lam s b := by
  intro he
  subst e
  cases h

end Lisa.SCLambdaToPure

/-!
# Scope and free names of normalized expressions

Normalization's conversion theorem alone does not bound syntactic support:
beta expansion can introduce unused free variables. The argument here follows
evaluation and readback instead. It proves that the actual normalizer produces
no dangling indices and no new free names.
-/

namespace Lisa.SCLambdaToPure

open Lambda

private def defaultTerm : (s : LSort) → Term s
  | .ind => .const ⟨"_default", 0⟩
  | .prop => .const ⟨"top", 0⟩
  | .arrow s t => .lam s (defaultTerm t)

/-- All bound indices are available at `d`, and every free name belongs to `xs`. -/
def Supported (d : Depth) (xs : Finset SVar) : Term s → Prop
  | .bound n => n < d s
  | .free x => SVar.mk x s ∈ xs
  | .const _ => True
  | .app f a => Supported d xs f ∧ Supported d xs a
  | .lam b e => Supported (d.inc b) xs e

private def Safe (xs : Finset SVar) : (s : LSort) → Depth → Val s → Prop
  | .ind, d, v => ∀ k, d.Extends k → Supported k xs (v k)
  | .prop, d, v => ∀ k, d.Extends k → Supported k xs (v k)
  | .arrow s t, d, f => ∀ k, d.Extends k → ∀ a, Safe xs s k a → Safe xs t k (f a)

private theorem Safe.mono (h : Safe xs s d v) (hdk : d.Extends k) : Safe xs s k v := by
  cases s with
  | ind => exact fun l hkl => h l (hdk.trans hkl)
  | prop => exact fun l hkl => h l (hdk.trans hkl)
  | arrow s t => exact fun l hkl a ha => h l (hdk.trans hkl) a ha

private theorem readback_safe (xs : Finset SVar) (s : LSort) :
    (∀ d v, Safe xs s d v → Supported d xs (quote s d v)) ∧
    (∀ d r, (∀ k, d.Extends k → Supported k xs (r k)) → Safe xs s d (reflect s r)) := by
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
        simp only [Supported, fresh, Depth.inc_self] at hs ⊢
        omega
      · intro d r hr k hk a ha
        apply iht.2
        intro l hl
        exact ⟨hr l (hk.trans hl), ihs.1 l a (ha.mono hl)⟩

private theorem eval_safe (e : Term s) (d : Depth) (xs : Finset SVar) (η : Env)
    (he : e.freeVars ⊆ xs) (hη : ∀ t n, Safe xs t d (η t n)) :
    Safe xs s d (eval e η) := by
  induction e generalizing d η with
  | bound n => exact hη _ n
  | free x => exact (readback_safe xs _).2 d _ (fun _ _ => he (by simp))
  | const c => exact (readback_safe xs _).2 d _ (fun _ _ => True.intro)
  | app f a ihf iha =>
      exact ihf d η (Finset.Subset.trans Finset.subset_union_left he) hη
        d (Depth.extends_refl d) _
        (iha d η (Finset.Subset.trans Finset.subset_union_right he) hη)
  | lam b e ih =>
      exact fun k hk a ha => ih k (η.extend a) he (env_extend (fun t n => (hη t n).mono hk) ha)

private theorem default_safe (s : LSort) (d : Depth) (xs : Finset SVar) (η : Env) :
    Safe xs s d (eval (defaultTerm s) η) := by
  induction s generalizing d η with
  | ind => exact fun _ _ => True.intro
  | prop => exact fun _ _ => True.intro
  | arrow s t _ ih => exact fun k _ _ _ => ih k _

/-- Normalizing a complete term preserves both scope and its free-name bound. -/
theorem normalize_supported (e : Term s) (hc : ∀ σ, e.subst σ = e) :
    Supported Depth.zero e.freeVars (normalize e) := by
  apply (readback_safe e.freeVars s).1
  rw [← hc (fun s _ => defaultTerm s), eval_subst, hc]
  apply eval_safe _ _ _ _ (Finset.Subset.refl _)
  exact fun t _ => default_safe t _ _ _

theorem Supported.freeVars {e : Term s} (h : Supported d xs e) : e.freeVars ⊆ xs := by
  induction e generalizing d with
  | bound => simp
  | free => simpa [Term.freeVars, Finset.singleton_subset_iff] using h
  | const => simp
  | app _ _ ihf iha => exact Finset.union_subset (ihf h.1) (iha h.2)
  | lam _ _ ih => exact ih h

theorem normalize_freeVars_subset (e : Term s) (hc : ∀ σ, e.subst σ = e) :
    (normalize e).freeVars ⊆ e.freeVars := (normalize_supported e hc).freeVars

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

end Lisa.SCLambdaToPure
