import Lisa.SCLambdaToPure.AToPure.Syntax
import Lisa.SCLambdaToPure.AToPure.Normalization
import Lisa.Lambda.NamedReflection

/-!
# First-order shapes after lambda normalization

`Individual` and `Formula` are predicates on the existing typed lambda syntax,
not new expression types. Epsilon terms contain first-order formulas, so these
two shape predicates are mutually inductive. They include partially applied symbols.
At ground sorts, their grammar is precisely first-order syntax (with explicit
individual indices allowed for an ambient scope).

`InLanguage` permits arbitrary lambda binders and applications, but only the
first-order constants and ground free variables. Its normalization theorem is
the shape argument from `canonical_lamfol` in the paper.
-/

namespace Lisa.SCLambdaToPure.FirstOrderShape

open Lambda

export Signature (arity)

mutual
inductive Individual : {s : LSort} → Term s → Prop where
  | bound (n : Nat) : Individual (.bound (s := ind) n)
  | free (x : Identifier) : Individual (.free (s := ind) x)
  | symbol (n : Nat) (c : Identifier) : Individual (.const (s := arity n ind) c)
  | app {f : Term (ind >> s)} {a : Term ind} :
      Individual f → Individual a → Individual (.app f a)

  | epsilon {p : Term prop} : Formula p →
      Individual (.app (.const ⟨"epsilon", 0⟩) (.lam ind p) : Term ind)

inductive Formula : {s : LSort} → Term s → Prop where
  | free (x : Identifier) : Formula (.free (s := prop) x)
  | symbol (n : Nat) (c : Identifier) : Formula (.const (s := arity n prop) c)
  | app {f : Term (ind >> s)} {a : Term ind} :
      Formula f → Individual a → Formula (.app f a)
  | top : Formula (.const (s := prop) ⟨"top", 0⟩)
  | bot : Formula (.const (s := prop) ⟨"bot", 0⟩)
  | neg {p : Term prop} : Formula p → Formula (.app (.const ⟨"not", 0⟩) p : Term prop)
  | and {p q : Term prop} : Formula p → Formula q →
      Formula (.app (.app (.const ⟨"and", 0⟩) p) q : Term prop)
  | or {p q : Term prop} : Formula p → Formula q →
      Formula (.app (.app (.const ⟨"or", 0⟩) p) q : Term prop)
  | imp {p q : Term prop} : Formula p → Formula q →
      Formula (.app (.app (.const ⟨"imp", 0⟩) p) q : Term prop)
  | iff {p q : Term prop} : Formula p → Formula q →
      Formula (.app (.app (.const ⟨"iff", 0⟩) p) q : Term prop)
  | eq {t u : Term ind} : Individual t → Individual u →
      Formula (.app (.app (.const ⟨"eq", 0⟩) t) u : Term prop)
  | all {p : Term prop} : Formula p →
      Formula (.app (.const ⟨"forall", 0⟩) (.lam ind p) : Term prop)
  | ex {p : Term prop} : Formula p →
      Formula (.app (.const ⟨"exists", 0⟩) (.lam ind p) : Term prop)

end

/-- Exactly the constant sorts admitted in the first-order fragment with epsilon.
Symbols sharing a printed name at a different sort remain distinct.
-/
inductive Constant : LSort → Identifier → Prop where
  | function (n : Nat) (c : Identifier) : Constant (arity n ind) c
  | predicate (n : Nat) (c : Identifier) : Constant (arity n prop) c
  | top : Constant prop ⟨"top", 0⟩
  | bot : Constant prop ⟨"bot", 0⟩
  | neg : Constant (prop >> prop) ⟨"not", 0⟩
  | and : Constant (prop >> prop >> prop) ⟨"and", 0⟩
  | or : Constant (prop >> prop >> prop) ⟨"or", 0⟩
  | imp : Constant (prop >> prop >> prop) ⟨"imp", 0⟩
  | iff : Constant (prop >> prop >> prop) ⟨"iff", 0⟩
  | eq : Constant (ind >> ind >> prop) ⟨"eq", 0⟩
  | all : Constant ((ind >> prop) >> prop) ⟨"forall", 0⟩
  | ex : Constant ((ind >> prop) >> prop) ⟨"exists", 0⟩

  | epsilon : Constant ((ind >> prop) >> ind) ⟨"epsilon", 0⟩

/-- Higher-order bound variables are allowed; free variables are ground.
This does not assert that the input is already in first-order or normal form.
-/
inductive InLanguage : {s : LSort} → Term s → Prop where
  | bound (n : Nat) : InLanguage (.bound (s := s) n)
  | individual (x : Identifier) : InLanguage (.free (s := ind) x)
  | proposition (x : Identifier) : InLanguage (.free (s := prop) x)
  | const {c : Identifier} : Constant s c → InLanguage (.const (s := s) c)
  | app {f : Term (s >> t)} {a : Term s} :
      InLanguage f → InLanguage a → InLanguage (.app f a)
  | lam {b : Term t} : InLanguage b → InLanguage (.lam s b)

private def Good : (s : LSort) → Val s → Prop
  | .ind, v => ∀ d, Individual (v d)
  | .prop, v => ∀ d, Formula (v d)
  | .arrow s t, f => ∀ a, Good s a → Good t (f a)

private theorem reflect_function (n : Nat) (r : Residual (arity n ind))
    (h : ∀ d, Individual (r d)) : Good (arity n ind) (reflect (arity n ind) r) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro a ha
      apply ih
      intro d
      exact .app (h d) (ha d)

private theorem reflect_predicate (n : Nat) (r : Residual (arity n prop))
    (h : ∀ d, Formula (r d)) : Good (arity n prop) (reflect (arity n prop) r) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro a ha
      apply ih
      intro d
      exact .app (h d) (ha d)

private theorem constant_good (h : Constant s c) :
    Good s (reflect s (fun _ => .const c)) := by
  cases h with
  | function n c => exact reflect_function n _ (fun _ => .symbol n c)
  | predicate n c => exact reflect_predicate n _ (fun _ => .symbol n c)
  | top => exact fun _ => .top
  | bot => exact fun _ => .bot
  | neg => exact fun _ hp d => .neg (hp d)
  | and => exact fun _ hp _ hq d => .and (hp d) (hq d)
  | or => exact fun _ hp _ hq d => .or (hp d) (hq d)
  | imp => exact fun _ hp _ hq d => .imp (hp d) (hq d)
  | iff => exact fun _ hp _ hq d => .iff (hp d) (hq d)
  | eq => exact fun _ ht _ hu d => .eq (ht d) (hu d)
  | all => exact fun _ hf d => .all (hf _ (fun _ => .bound _) _)
  | ex => exact fun _ hf d => .ex (hf _ (fun _ => .bound _) _)
  | epsilon => exact fun _ hf d => .epsilon (hf _ (fun _ => .bound _) _)

private theorem eval_good {e : Term s} (h : InLanguage e) (η : Env)
    (hη : ∀ s n, Good s (η s n)) : Good s (eval e η) := by
  induction h generalizing η with
  | bound n => exact hη _ n
  | individual x => exact fun _ => .free x
  | proposition x => exact fun _ => .free x
  | const h => exact constant_good h
  | app _ _ ihf iha => exact ihf η hη _ (iha η hη)
  | @lam t s b _ ih => exact fun a ha => ih _ (env_extend hη ha)

private def defaultTerm : (s : LSort) → Term s
  | .ind => .free ⟨"_default", 0⟩
  | .prop => .const ⟨"top", 0⟩
  | .arrow s t => .lam s (defaultTerm t)

private theorem default_good (s : LSort) (η : Env) : Good s (eval (defaultTerm s) η) := by
  induction s generalizing η with
  | ind => exact fun _ => .free _
  | prop => exact fun _ => .top
  | arrow s t _ ih => exact fun _ _ => ih _

private theorem closed_eval_good {e : Term s} (h : InLanguage e) (hc : ∀ σ, e.subst σ = e) :
    Good s (eval e ambient) := by
  rw [← hc (fun s _ => defaultTerm s), eval_subst]
  exact eval_good h _ (fun t _ => default_good t _)

/-- The canonical form of a complete individual expression is a first-order term. -/
theorem normalize_individual {e : Term ind} (h : InLanguage e)
    (hc : ∀ σ, e.subst σ = e) : Individual (normalize e) :=
  closed_eval_good h hc Depth.zero

/-- The canonical form of a complete formula is a first-order formula.
The closure premise excludes ambient higher-order indices; named interpretation
supplies it automatically. Higher-order lambdas inside the input are unrestricted.
-/
theorem normalize_formula {e : Term prop} (h : InLanguage e)
    (hc : ∀ σ, e.subst σ = e) : Formula (normalize e) :=
  closed_eval_good h hc Depth.zero

theorem normalize_named_formula {p : Expr} {e : Term prop}
    (he : interpretNamed p Names.free = some ⟨prop, e⟩) (h : InLanguage e) :
    Formula (normalize e) :=
  normalize_formula h (subst_of_interpretNamed he)

theorem InLanguage.rename {e : Term s} (h : InLanguage e) (ρ : Ren) :
    InLanguage (e.rename ρ) := by
  induction h generalizing ρ with
  | bound => exact .bound _
  | individual => exact .individual _
  | proposition => exact .proposition _
  | const h => exact .const h
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam _ ih => exact .lam (ih _)

/-- The constant restriction, stated directly on Lisa's named expressions. -/
def ConstantsInLanguage : Expr → Prop
  | .var _ => True
  | .const c => Constant c.sort c.id
  | .app f a => ConstantsInLanguage f ∧ ConstantsInLanguage a
  | .lam _ b => ConstantsInLanguage b

private def resultInLanguage : Option Packed.Expr → Prop
  | none => True
  | some ⟨_, t⟩ => InLanguage t

private theorem resultInLanguage_app {f a : Option Packed.Expr}
    (hf : resultInLanguage f) (ha : resultInLanguage a) :
    resultInLanguage (f.bind fun f => a.bind (Packed.app f)) := by
  rcases f with _ | ⟨s, f⟩
  · trivial
  rcases a with _ | ⟨u, a⟩
  · trivial
  cases s with
  | ind => trivial
  | prop => trivial
  | arrow s t =>
      by_cases h : u = s
      · subst u; simpa [Packed.app, resultInLanguage] using (InLanguage.app hf ha)
      · simp [Packed.app, h, resultInLanguage]

private theorem interpret_inLanguage (e : Expr) (η : Names)
    (hc : ConstantsInLanguage e)
    (hv : ∀ x ∈ e.freeVars, InLanguage (η x)) : resultInLanguage (interpretNamed e η) := by
  induction e generalizing η with
  | var x => exact hv x (by simp)
  | const c => exact .const hc
  | app f a ihf iha =>
      exact resultInLanguage_app
        (ihf η hc.1 (fun x hx => hv x (by simp [hx])))
        (iha η hc.2 (fun x hx => hv x (by simp [hx])))
  | lam x b ih =>
      have hb : resultInLanguage (interpretNamed b (η.bind x)) := by
        apply ih _ hc
        intro y hy
        by_cases h : y = x
        · subst y; simp only [Names.bind_self]; exact .bound _
        · rw [Names.bind_other _ h]
          exact (hv y (by simp [hy, h])).rename _
      cases he : interpretNamed b (η.bind x) with
      | none => simp [interpretNamed, he, resultInLanguage]
      | some v =>
          obtain ⟨s, b⟩ := v
          simpa [interpretNamed, he, resultInLanguage, Packed.lam] using
            (InLanguage.lam (s := x.sort) (by simpa [he, resultInLanguage] using hb))

/-- Transfer the signature and free-sort restrictions across named interpretation. -/
theorem inLanguage_of_interpretNamed {p : Expr} {e : Term s}
    (he : interpretNamed p Names.free = some ⟨s, e⟩)
    (hc : ConstantsInLanguage p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop) : InLanguage e := by
  have h := interpret_inLanguage p Names.free hc (by
    intro x hx
    rcases hv x hx with hs | hs
    · obtain ⟨id, s⟩ := x; cases hs; exact .individual id
    · obtain ⟨id, s⟩ := x; cases hs; exact .proposition id)
  simpa [he, resultInLanguage] using h

/-- The paper's canonical-form shape theorem, with explicit signature and
free-variable hypotheses on the original named expression. Free propositions
remain schematic nullary predicates when read into first-order syntax.
-/
theorem canonical_lamfol {p : Expr} {e : Term prop}
    (he : interpretNamed p Names.free = some ⟨prop, e⟩)
    (hc : ConstantsInLanguage p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop) :
    Canonical (normalize e) ∧ Formula (normalize e) := by
  exact ⟨normalize_canonical e, normalize_named_formula he
    (inLanguage_of_interpretNamed he hc hv)⟩

end Lisa.SCLambdaToPure.FirstOrderShape

/-! Normalization fixes first-order expressions, including epsilon.
The mutual argument follows the first-order grammar. Epsilon bodies and
quantifier bodies use exactly the same binder calculation. -/
namespace Lisa.SCLambdaToPure.FirstOrderShape
open Lambda

private def Computes : (s : LSort) → Depth → Val s → Term s → Prop
  | .ind, d, v, e => v d = e
  | .prop, d, v, e => v d = e
  | .arrow s t, d, v, e => ∀ a, Computes t d (v a) (.app e (quote s d a))

private theorem reflect_computes (s : LSort) (d : Depth) (r : Residual s) :
    Computes s d (reflect s r) (r d) := by
  induction s with
  | ind | prop => rfl
  | arrow s t _ ih => intro a; exact ih _

private def Assigned (d : Depth) (η : Env) (σ : Sub) : Prop :=
  ∀ n k, d.Extends k → η ind n k = (σ ind n).rename (d.weaken k)

private theorem shift_weaken {d k : Depth} (h : (d.inc b).Extends k) :
    Ren.comp (Ren.shift b) ((d.inc b).weaken k) = d.weaken k := by
  funext s n
  have hs := h s
  by_cases he : s = b
  · subst s
    simp [Ren.comp, Ren.shift, Depth.weaken] at hs ⊢
    omega
  · simp [Ren.comp, Ren.shift, Depth.weaken, he]

private theorem Assigned.extend (h : Assigned d η σ) :
    Assigned (d.inc ind) (η.extend (b := ind) (fresh ind (d ind))) (σ.lift ind) := by
  intro n k hk
  cases n with
  | zero => simp [Env.extend, Sub.lift, fresh, Term.rename, Depth.weaken]
  | succ n =>
      simp only [Env.extend_succ, Sub.lift_succ, Term.rename_comp, shift_weaken hk]
      exact h n k ((Depth.extends_inc d ind).trans hk)

mutual
  private theorem individual_computes {e : Term s} (h : Individual e)
      (η : Env) (σ : Sub) (hη : Assigned d η σ) : Computes s d (eval e η) (e.subst σ) := by
    match h with
    | .bound n =>
        simpa only [Depth.weaken_self, Term.rename_id] using hη n d (Depth.extends_refl d)
    | .free x => rfl
    | .symbol n c => exact reflect_computes _ _ _
    | @Individual.app s f a hf ha =>
        have h := individual_computes hf η σ hη (eval a η)
        have he := individual_computes ha η σ hη
        change eval a η d = a.subst σ at he
        simpa only [quote, readback, he, Term.subst] using h
    | .epsilon hp =>
        change Term.app _ (.lam ind (eval (s := prop) _ (η.extend (b := ind) (fresh ind (d ind))) (d.inc ind))) = _
        rw [formula_computes hp _ _ hη.extend]
        rfl
  private theorem formula_computes {e : Term s} (h : Formula e)
      (η : Env) (σ : Sub) (hη : Assigned d η σ) : Computes s d (eval e η) (e.subst σ) := by
    match h with
    | .free x => rfl
    | .symbol n c => exact reflect_computes _ _ _
    | @Formula.app s f a hf ha =>
        have h := formula_computes hf η σ hη (eval a η)
        have he := individual_computes ha η σ hη
        change eval a η d = a.subst σ at he
        simpa only [quote, readback, he, Term.subst] using h
    | .top | .bot => rfl
    | .neg hp =>
        change Term.app _ (eval (s := prop) _ η d) = _
        rw [formula_computes hp η σ hη]
        rfl
    | .and hp hq | .or hp hq | .imp hp hq | .iff hp hq =>
        change Term.app (Term.app _ (eval (s := prop) _ η d)) (eval (s := prop) _ η d) = _
        rw [formula_computes hp η σ hη, formula_computes hq η σ hη]
        rfl
    | .eq ht hu =>
        change Term.app (Term.app _ (eval (s := ind) _ η d)) (eval (s := ind) _ η d) = _
        rw [individual_computes ht η σ hη, individual_computes hu η σ hη]
        rfl
    | .all hp | .ex hp =>
        change Term.app _ (.lam ind (eval (s := prop) _ (η.extend (b := ind) (fresh ind (d ind))) (d.inc ind))) = _
        rw [formula_computes hp _ _ hη.extend]
        rfl
end

private theorem ambient_assigned : Assigned Depth.zero ambient Sub.id := by
  intro n k hk
  simp [ambient, Sub.id, Term.rename, Depth.weaken, Depth.zero, Nat.add_comm, reflect, readback]

theorem normalize_individual_eq {e : Term ind} (h : Individual e) : normalize e = e := by
  exact (individual_computes h ambient Sub.id ambient_assigned).trans e.subst_id

theorem normalize_formula_eq {e : Term prop} (h : Formula e) : normalize e = e := by
  exact (formula_computes h ambient Sub.id ambient_assigned).trans e.subst_id

end Lisa.SCLambdaToPure.FirstOrderShape
