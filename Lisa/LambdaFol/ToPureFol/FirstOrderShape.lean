import Lisa.LambdaFol.FirstOrder
import Lisa.LambdaFol.ToPureFol.SignatureAndVariables
import Lisa.LambdaFol.ToPureFol.NormalizationScope
import Lisa.AlphaBetaEtaNormalization.Internal.NamedReflection

/-!
# First-order shapes after lambda normalization

`IsTermOrFunction` and `IsFormulaOrPredicate` are predicates on the existing typed lambda syntax,
not new expression types. Epsilon terms contain first-order formulas, so these
two shape predicates are mutually inductive. They include partially applied symbols.
At ground sorts, their grammar is precisely first-order syntax (with explicit
individual indices allowed for an ambient scope).

`Compatible` permits arbitrary lambda binders and applications, but only the
first-order constants and free individual/proposition variables. Its normalization theorem is
the canonical-form shape argument from the paper.
-/

namespace Lisa.LambdaFol.FirstOrderShape

open AlphaBetaEtaNormalization.Algorithm

mutual
inductive IsTermOrFunction : {s : LSort} → Term s → Prop where
  | bound (n : Nat) : IsTermOrFunction (.bound (s := ind) n)
  | free (x : Identifier) : IsTermOrFunction (.free (s := ind) x)
  | symbol (n : Nat) (c : Identifier) : IsTermOrFunction (.const (s := arity n ind) c)
  | app {f : Term (ind >> s)} {a : Term ind} :
      IsTermOrFunction f → IsTermOrFunction a → IsTermOrFunction (.app f a)

  | epsilon {p : Term prop} : IsFormulaOrPredicate p →
      IsTermOrFunction (.app (.const ⟨"epsilon", 0⟩) (.lam ind p) : Term ind)

inductive IsFormulaOrPredicate : {s : LSort} → Term s → Prop where
  | free (x : Identifier) : IsFormulaOrPredicate (.free (s := prop) x)
  | symbol (n : Nat) (c : Identifier) : IsFormulaOrPredicate (.const (s := arity n prop) c)
  | app {f : Term (ind >> s)} {a : Term ind} :
      IsFormulaOrPredicate f → IsTermOrFunction a → IsFormulaOrPredicate (.app f a)
  | neg {p : Term prop} : IsFormulaOrPredicate p → IsFormulaOrPredicate (.app (.const ⟨"not", 0⟩) p : Term prop)
  | and {p q : Term prop} : IsFormulaOrPredicate p → IsFormulaOrPredicate q →
      IsFormulaOrPredicate (.app (.app (.const ⟨"and", 0⟩) p) q : Term prop)
  | or {p q : Term prop} : IsFormulaOrPredicate p → IsFormulaOrPredicate q →
      IsFormulaOrPredicate (.app (.app (.const ⟨"or", 0⟩) p) q : Term prop)
  | imp {p q : Term prop} : IsFormulaOrPredicate p → IsFormulaOrPredicate q →
      IsFormulaOrPredicate (.app (.app (.const ⟨"imp", 0⟩) p) q : Term prop)
  | iff {p q : Term prop} : IsFormulaOrPredicate p → IsFormulaOrPredicate q →
      IsFormulaOrPredicate (.app (.app (.const ⟨"iff", 0⟩) p) q : Term prop)
  | all {p : Term prop} : IsFormulaOrPredicate p →
      IsFormulaOrPredicate (.app (.const ⟨"forall", 0⟩) (.lam ind p) : Term prop)
  | ex {p : Term prop} : IsFormulaOrPredicate p →
      IsFormulaOrPredicate (.app (.const ⟨"exists", 0⟩) (.lam ind p) : Term prop)

end

-- Truth, falsehood, and equality already have the shape of first-order
-- predicates. Keep convenient names without adding duplicate induction cases.
theorem IsFormulaOrPredicate.top : IsFormulaOrPredicate (.const (s := prop) ⟨"top", 0⟩) := .symbol 0 _
theorem IsFormulaOrPredicate.bot : IsFormulaOrPredicate (.const (s := prop) ⟨"bot", 0⟩) := .symbol 0 _
theorem IsFormulaOrPredicate.eq {t u : Term ind} (ht : IsTermOrFunction t) (hu : IsTermOrFunction u) :
    IsFormulaOrPredicate (.app (.app (.const ⟨"eq", 0⟩) t) u : Term prop) :=
  .app (.app (.symbol 2 _) ht) hu

theorem AllowedConstant.top : AllowedConstant prop ⟨"top", 0⟩ := .predicate 0 _
theorem AllowedConstant.bot : AllowedConstant prop ⟨"bot", 0⟩ := .predicate 0 _
theorem AllowedConstant.eq : AllowedConstant (ind >> ind >> prop) ⟨"eq", 0⟩ := .predicate 2 _

/-- Higher-order bound variables are allowed; free variables have individual or proposition sort.
This does not assert that the input is already in first-order or normal form.
-/
inductive Compatible : {s : LSort} → Term s → Prop where
  | bound (n : Nat) : Compatible (.bound (s := s) n)
  | individual (x : Identifier) : Compatible (.free (s := ind) x)
  | proposition (x : Identifier) : Compatible (.free (s := prop) x)
  | const {c : Identifier} : AllowedConstant s c → Compatible (.const (s := s) c)
  | app {f : Term (s >> t)} {a : Term s} :
      Compatible f → Compatible a → Compatible (.app f a)
  | lam {b : Term t} : Compatible b → Compatible (.lam s b)

private def FirstOrderValue : (s : LSort) → Val s → Prop
  | .ind, v => ∀ d, IsTermOrFunction (v d)
  | .prop, v => ∀ d, IsFormulaOrPredicate (v d)
  | .arrow s t, f => ∀ a, FirstOrderValue s a → FirstOrderValue t (f a)

private theorem reflect_function (n : Nat) (r : Residual (arity n ind))
    (h : ∀ d, IsTermOrFunction (r d)) : FirstOrderValue (arity n ind) (reflect (arity n ind) r) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro a ha
      apply ih
      intro d
      exact .app (h d) (ha d)

private theorem reflect_predicate (n : Nat) (r : Residual (arity n prop))
    (h : ∀ d, IsFormulaOrPredicate (r d)) : FirstOrderValue (arity n prop) (reflect (arity n prop) r) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro a ha
      apply ih
      intro d
      exact .app (h d) (ha d)

private theorem constant_firstOrderValue (h : AllowedConstant s c) :
    FirstOrderValue s (reflect s (fun _ => .const c)) := by
  cases h with
  | function n c => exact reflect_function n _ (fun _ => .symbol n c)
  | predicate n c => exact reflect_predicate n _ (fun _ => .symbol n c)
  | neg => exact fun _ hp d => .neg (hp d)
  | and => exact fun _ hp _ hq d => .and (hp d) (hq d)
  | or => exact fun _ hp _ hq d => .or (hp d) (hq d)
  | imp => exact fun _ hp _ hq d => .imp (hp d) (hq d)
  | iff => exact fun _ hp _ hq d => .iff (hp d) (hq d)
  | all => exact fun _ hf d => .all (hf _ (fun _ => .bound _) _)
  | ex => exact fun _ hf d => .ex (hf _ (fun _ => .bound _) _)
  | epsilon => exact fun _ hf d => .epsilon (hf _ (fun _ => .bound _) _)

private theorem eval_firstOrderValue {e : Term s} (h : Compatible e) (η : Env)
    (hη : ∀ s n, FirstOrderValue s (η s n)) : FirstOrderValue s (eval e η) := by
  induction h generalizing η with
  | bound n => exact hη _ n
  | individual x => exact fun _ => .free x
  | proposition x => exact fun _ => .free x
  | const h => exact constant_firstOrderValue h
  | app _ _ ihf iha => exact ihf η hη _ (iha η hη)
  | @lam t s b _ ih => exact fun a ha => ih _ (env_extend hη ha)

private def defaultTerm : (s : LSort) → Term s
  | .ind => .free ⟨"_default", 0⟩
  | .prop => .const ⟨"top", 0⟩
  | .arrow s t => .lam s (defaultTerm t)

private theorem default_firstOrderValue (s : LSort) (η : Env) : FirstOrderValue s (eval (defaultTerm s) η) := by
  induction s generalizing η with
  | ind => exact fun _ => .free _
  | prop => exact fun _ => .top
  | arrow s t _ ih => exact fun _ _ => ih _

private theorem locallyClosed_eval_firstOrderValue {e : Term s} (h : Compatible e) (hc : ∀ σ, e.subst σ = e) :
    FirstOrderValue s (eval e ambient) := by
  rw [← hc (fun s _ => defaultTerm s), eval_subst]
  exact eval_firstOrderValue h _ (fun t _ => default_firstOrderValue t _)

/-- The canonical form of a complete individual expression is a first-order term. -/
theorem normalize_individual {e : Term ind} (h : Compatible e)
    (hc : ∀ σ, e.subst σ = e) : IsTermOrFunction (normalize e) :=
  locallyClosed_eval_firstOrderValue h hc Depth.zero

/-- The canonical form of a complete formula is a first-order formula.
The closure premise excludes ambient higher-order indices; named interpretation
supplies it automatically. Higher-order lambdas inside the input are unrestricted.
-/
theorem normalize_formula {e : Term prop} (h : Compatible e)
    (hc : ∀ σ, e.subst σ = e) : IsFormulaOrPredicate (normalize e) :=
  locallyClosed_eval_firstOrderValue h hc Depth.zero

theorem Compatible.rename {e : Term s} (h : Compatible e) (ρ : Ren) :
    Compatible (e.rename ρ) := by
  induction h generalizing ρ with
  | bound => exact .bound _
  | individual => exact .individual _
  | proposition => exact .proposition _
  | const h => exact .const h
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam _ ih => exact .lam (ih _)

private def resultCompatible : Option Packed.Expr → Prop
  | none => True
  | some ⟨_, t⟩ => Compatible t

private theorem resultCompatible_app {f a : Option Packed.Expr}
    (hf : resultCompatible f) (ha : resultCompatible a) :
    resultCompatible (f.bind fun f => a.bind (Packed.app f)) := by
  rcases f with _ | ⟨s, f⟩
  · trivial
  rcases a with _ | ⟨u, a⟩
  · trivial
  cases s with
  | ind => trivial
  | prop => trivial
  | arrow s t =>
      by_cases h : u = s
      · subst u; simpa [Packed.app, resultCompatible] using (Compatible.app hf ha)
      · simp [Packed.app, h, resultCompatible]

private theorem interpret_inLanguage (e : Expr) (η : Names)
    (hc : AllowedConstants e)
    (hv : ∀ x ∈ e.freeVars, Compatible (η x)) : resultCompatible (interpretNamed e η) := by
  induction e generalizing η with
  | var x => exact hv x (by simp)
  | const c => exact .const hc
  | app f a ihf iha =>
      exact resultCompatible_app
        (ihf η hc.1 (fun x hx => hv x (by simp [hx])))
        (iha η hc.2 (fun x hx => hv x (by simp [hx])))
  | lam x b ih =>
      have hb : resultCompatible (interpretNamed b (η.bind x)) := by
        apply ih _ hc
        intro y hy
        by_cases h : y = x
        · subst y; simp only [Names.bind_self]; exact .bound _
        · rw [Names.bind_other _ h]
          exact (hv y (by simp [hy, h])).rename _
      cases he : interpretNamed b (η.bind x) with
      | none => simp [interpretNamed, he, resultCompatible]
      | some v =>
          obtain ⟨s, b⟩ := v
          simpa [interpretNamed, he, resultCompatible, Packed.lam] using
            (Compatible.lam (s := x.sort) (by simpa [he, resultCompatible] using hb))

/-- Transfer the signature and free-sort restrictions across named interpretation. -/
theorem compatible_of_interpretNamed {p : Expr} {e : Term s}
    (he : interpretNamed p Names.free = some ⟨s, e⟩)
    (hc : AllowedConstants p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop) : Compatible e := by
  have h := interpret_inLanguage p Names.free hc (by
    intro x hx
    rcases hv x hx with hs | hs
    · obtain ⟨id, s⟩ := x; cases hs; exact .individual id
    · obtain ⟨id, s⟩ := x; cases hs; exact .proposition id)
  simpa [he, resultCompatible] using h

/-- The paper's canonical-form shape theorem, with explicit signature and
free-variable hypotheses on the original named expression. Free propositions
remain schematic nullary predicates when read into first-order syntax.
-/
theorem normalForm_isFirstOrder {p : Expr} {e : Term prop}
    (he : interpretNamed p Names.free = some ⟨prop, e⟩)
    (hc : AllowedConstants p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop) :
    IsFormulaOrPredicate (normalize e) :=
  normalize_formula (compatible_of_interpretNamed he hc hv) (subst_of_interpretNamed he)

end Lisa.LambdaFol.FirstOrderShape

/-! Normalization fixes first-order expressions, including epsilon.
The mutual argument follows the first-order grammar. Epsilon bodies and
quantifier bodies use exactly the same binder calculation. -/
namespace Lisa.LambdaFol.FirstOrderShape
open AlphaBetaEtaNormalization.Algorithm

private def ValueRepresentsTerm : (s : LSort) → Depth → Val s → Term s → Prop
  | .ind, d, v, e => v d = e
  | .prop, d, v, e => v d = e
  | .arrow s t, d, v, e => ∀ a, ValueRepresentsTerm t d (v a) (.app e (quote s d a))

private theorem reflect_representsTerm (s : LSort) (d : Depth) (r : Residual s) :
    ValueRepresentsTerm s d (reflect s r) (r d) := by
  induction s with
  | ind | prop => rfl
  | arrow s t _ ih => intro a; exact ih _

private def EnvRepresentsSubstitution (d : Depth) (η : Env) (σ : Sub) : Prop :=
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

private theorem EnvRepresentsSubstitution.extend (h : EnvRepresentsSubstitution d η σ) :
    EnvRepresentsSubstitution (d.inc ind) (η.extend (b := ind) (fresh ind (d ind))) (σ.lift ind) := by
  intro n k hk
  cases n with
  | zero => simp [Env.extend, Sub.lift, fresh, Term.rename, Depth.weaken]
  | succ n =>
      simp only [Env.extend_succ, Sub.lift_succ, Term.rename_comp, shift_weaken hk]
      exact h n k ((Depth.extends_inc d ind).trans hk)

mutual
  private theorem individual_representsTerm {e : Term s} (h : IsTermOrFunction e)
      (η : Env) (σ : Sub) (hη : EnvRepresentsSubstitution d η σ) : ValueRepresentsTerm s d (eval e η) (e.subst σ) := by
    match h with
    | .bound n =>
        simpa only [Depth.weaken_self, Term.rename_id] using hη n d (Depth.extends_refl d)
    | .free x => rfl
    | .symbol n c => exact reflect_representsTerm _ _ _
    | @IsTermOrFunction.app s f a hf ha =>
        have h := individual_representsTerm hf η σ hη (eval a η)
        have he := individual_representsTerm ha η σ hη
        change eval a η d = a.subst σ at he
        simpa only [quote, readback, he, Term.subst] using h
    | .epsilon hp =>
        change Term.app _ (.lam ind (eval (s := prop) _ (η.extend (b := ind) (fresh ind (d ind))) (d.inc ind))) = _
        rw [formula_representsTerm hp _ _ hη.extend]
        rfl
  private theorem formula_representsTerm {e : Term s} (h : IsFormulaOrPredicate e)
      (η : Env) (σ : Sub) (hη : EnvRepresentsSubstitution d η σ) : ValueRepresentsTerm s d (eval e η) (e.subst σ) := by
    match h with
    | .free x => rfl
    | .symbol n c => exact reflect_representsTerm _ _ _
    | @IsFormulaOrPredicate.app s f a hf ha =>
        have h := formula_representsTerm hf η σ hη (eval a η)
        have he := individual_representsTerm ha η σ hη
        change eval a η d = a.subst σ at he
        simpa only [quote, readback, he, Term.subst] using h
    | .neg hp =>
        change Term.app _ (eval (s := prop) _ η d) = _
        rw [formula_representsTerm hp η σ hη]
        rfl
    | .and hp hq | .or hp hq | .imp hp hq | .iff hp hq =>
        change Term.app (Term.app _ (eval (s := prop) _ η d)) (eval (s := prop) _ η d) = _
        rw [formula_representsTerm hp η σ hη, formula_representsTerm hq η σ hη]
        rfl
    | .all hp | .ex hp =>
        change Term.app _ (.lam ind (eval (s := prop) _ (η.extend (b := ind) (fresh ind (d ind))) (d.inc ind))) = _
        rw [formula_representsTerm hp _ _ hη.extend]
        rfl
end

private theorem ambient_representsSubstitution : EnvRepresentsSubstitution Depth.zero ambient Sub.id := by
  intro n k hk
  simp [ambient, Sub.id, Term.rename, Depth.weaken, Depth.zero, Nat.add_comm, reflect, readback]

theorem normalize_individual_eq {e : Term ind} (h : IsTermOrFunction e) : normalize e = e := by
  exact (individual_representsTerm h ambient Sub.id ambient_representsSubstitution).trans e.subst_id

theorem normalize_formula_eq {e : Term prop} (h : IsFormulaOrPredicate e) : normalize e = e := by
  exact (formula_representsTerm h ambient Sub.id ambient_representsSubstitution).trans e.subst_id

end Lisa.LambdaFol.FirstOrderShape
