import Lisa.SCLambdaToPure.AToPure.Grounding
import Lisa.SCLambdaToPure.OrderedToA.Substitution

/-! Interpret the named source syntax by complete expressions. These operations
retain the source sorts and commute with conversion and simultaneous schematic
instantiation. They do not interpret formulas as truth values. -/
namespace Lisa.SCLambdaToPure.Syntactic
open Lambda

namespace Assignment

noncomputable def expression (R : Assignment) (e : Expr) (h : e.hasSort s) : ScopedExpr s :=
  R.apply (Classical.choose (interpretNamed_sorted h Names.free))

theorem expression_of_named (R : Assignment) (e : Expr) (h : e.hasSort s)
    {t : Term s} (ht : interpretNamed e Names.free = some ⟨s, t⟩) :
    R.expression e h = R.apply t := by
  have hh := Classical.choose_spec (interpretNamed_sorted h Names.free)
  have he : t = Classical.choose (interpretNamed_sorted h Names.free) := by
    simpa using ht.symm.trans hh
  simp only [expression, ← he]

theorem expression_support (R S : Assignment) (e : Expr) (h : e.hasSort s)
    (hc : R.const = S.const)
    (hf : ∀ x ∈ e.freeVars, R.free x.sort x.id = S.free x.sort x.id) :
    R.expression e h = S.expression e h := by
  obtain ⟨t, ht⟩ := interpretNamed_sorted h Names.free
  rw [R.expression_of_named e h ht, S.expression_of_named e h ht]
  apply ScopedExpr.ext
  let Q : Replacement := { S.replacement with bound := R.replacement.bound }
  have h₁ : R.replacement.apply t = Q.apply t := by
    refine Replacement.apply_congr t R.replacement Q rfl ?_ ?_
    · simp only [replacement, hc, Q]
    · intro u x hx
      exact congrArg ScopedExpr.term (hf ⟨x, u⟩ (interpretNamed_freeVars ht hx))
  exact h₁.trans (Replacement.apply_closed_congr t (subst_of_interpretNamed ht) Q S.replacement rfl rfl)

theorem expression_equiv (R : Assignment) {e f : Expr} (h : AlphaBetaEta e f)
    (he : e.hasSort s) (hf : f.hasSort s) :
    Equiv (R.expression e he).term (R.expression f hf).term := by
  obtain ⟨a, ha⟩ := interpretNamed_sorted he Names.free
  obtain ⟨b, hb⟩ := interpretNamed_sorted hf Names.free
  rw [R.expression_of_named e he ha, R.expression_of_named f hf hb]
  have hh := interpretNamed_alphaBetaEta h Names.free
  rw [ha, hb] at hh
  cases hh with
  | some hh => exact R.replacement.equiv hh

@[simp] theorem expression_var (R : Assignment) (x : SVar) :
    R.expression (.var x) rfl = R.free x.sort x.id :=
  R.expression_of_named (.var x) rfl (t := .free x.id) rfl

@[simp] theorem expression_const (R : Assignment) (c : SConst) :
    R.expression (.const c) rfl = R.const c.sort c.id :=
  R.expression_of_named (.const c) rfl (t := .const c.id) rfl

theorem expression_app (R : Assignment) {f a : Expr}
    (hf : f.hasSort (s >> t)) (ha : a.hasSort s) :
    R.expression (.app f a) (s := t) (by
      dsimp only [Expr.hasSort] at hf ha ⊢; simp [Expr.sort, hf, ha]) =
      (R.expression f hf).app (R.expression a ha) := by
  obtain ⟨f', hf'⟩ := interpretNamed_sorted hf Names.free
  obtain ⟨a', ha'⟩ := interpretNamed_sorted ha Names.free
  rw [R.expression_of_named f hf hf', R.expression_of_named a ha ha']
  exact R.expression_of_named (.app f a) _ (t := .app f' a')
    (by simp [interpretNamed, hf', ha', Packed.app])

/-- Assign a complete expression to one free source name. -/
def update (R : Assignment) (x : SVar) (a : ScopedExpr x.sort) : Assignment :=
  { R with
    free := fun s y => if h : SVar.mk y s = x then
      cast (congrArg ScopedExpr (congrArg SVar.sort h).symm) a else R.free s y }

@[simp] theorem update_self (R : Assignment) (x : SVar) (a : ScopedExpr x.sort) :
    (R.update x a).free x.sort x.id = a := by simp [update]

theorem update_other (R : Assignment) (x : SVar) (a : ScopedExpr x.sort)
    (h : SVar.mk y s ≠ x) : (R.update x a).free s y = R.free s y := by simp only [update, h, ↓reduceDIte]

theorem expression_update_fresh (R : Assignment) (x : SVar) (a : ScopedExpr x.sort)
    (e : Expr) (he : e.hasSort s) (hx : x ∉ e.freeVars) :
    (R.update x a).expression e he = R.expression e he := by
  apply expression_support (R.update x a) R e he rfl
  intro y hy
  exact update_other R x a (fun h => hx (h ▸ hy))

end Assignment
end Lisa.SCLambdaToPure.Syntactic

/-! Named abstraction and schematic instantiation commute with the syntactic
assignment. Replacement images are complete expressions and remain simultaneous. -/
namespace Lisa.SCLambdaToPure
open Lambda

namespace Replacement

theorem interpretNamed_congr (e : Expr) (R S : Replacement) (η θ : Names)
    (hc : R.const = S.const)
    (hn : ∀ x ∈ e.freeVars, R.apply (η x) = S.apply (θ x)) :
    (interpretNamed e η).map R.packed = (interpretNamed e θ).map S.packed := by
  induction e generalizing R S η θ with
  | var x => simpa [interpretNamed, packed] using hn x (by simp)
  | const c => simp only [interpretNamed, Option.map_some, packed, apply, hc]
  | app f a ihf iha =>
      have hf := ihf R S η θ hc (fun x hx => hn x (Finset.mem_union_left _ hx))
      have ha := iha R S η θ hc (fun x hx => hn x (Finset.mem_union_right _ hx))
      have mapapp (R : Replacement) (p q : Option Packed.Expr) :
          ((do Packed.app (← p) (← q))).map R.packed =
          (do Packed.app (← p.map R.packed) (← q.map R.packed)) := by
        cases p <;> cases q <;> simp [packed_app]
      simp only [interpretNamed, mapapp, hf, ha]
  | lam x e ih =>
      have hcl : (R.lift x.sort).const = (S.lift x.sort).const := by simp [lift, hc]
      have hh := ih (R.lift x.sort) (S.lift x.sort) (η.bind x) (θ.bind x) hcl (by
        intro y hy
        by_cases h : y = x
        · subst y; simp [apply, lift]
        · simp only [Names.bind_other _ h, apply_shift]
          rw [hn y (by simp [hy, h])])
      simp only [interpretNamed, Option.map_map]
      have hh' := congrArg (Option.map (Packed.lam x.sort)) hh
      simpa only [Option.map_map] using hh'

end Replacement

namespace Syntactic.Assignment

noncomputable def instantiate (R : Assignment) (σ : Instantiation) : Assignment :=
  { R with free := fun s x => R.apply (σ.names ⟨x, s⟩) }

theorem expression_instantiate (R : Assignment) (σ : Instantiation) (e : Expr) (he : e.hasSort s) :
    R.expression (σ.apply e) (σ.hasSort he) = (R.instantiate σ).expression e he := by
  obtain ⟨t, ht⟩ := interpretNamed_sorted (σ.hasSort he) Names.free
  obtain ⟨u, hu⟩ := interpretNamed_sorted he Names.free
  rw [R.expression_of_named _ _ ht, (R.instantiate σ).expression_of_named _ _ hu]
  apply ScopedExpr.ext
  have h := Replacement.interpretNamed_congr e R.replacement (R.instantiate σ).replacement
    σ.names Names.free rfl (by intros; rfl)
  rw [← σ.interpret, ht, hu] at h
  simpa only [Option.map_some, Replacement.packed, Option.some.injEq, Sigma.mk.inj_iff,
    heq_eq_eq, true_and] using h

theorem expression_lam_apply (R : Assignment) (x : SVar) (e : Expr) (he : e.hasSort s)
    (a : ScopedExpr x.sort) :
    Equiv ((R.expression (.lam x e) (s := x.sort >> s) (by
      dsimp only [Expr.hasSort] at he ⊢; simp [Expr.sort, he])).app a).term
      ((R.update x a).expression e he).term := by
  obtain ⟨t, ht⟩ := interpretNamed_sorted he (Names.free.bind x)
  obtain ⟨u, hu⟩ := interpretNamed_sorted he Names.free
  rw [R.expression_of_named (.lam x e) _ (t := .lam x.sort t)
    (by simp [interpretNamed, ht, Packed.lam]), (R.update x a).expression_of_named e he hu]
  apply Lambda.Equiv.trans (Lambda.Equiv.beta _ a.term)
  have h := Replacement.interpretNamed_congr e
    ((Replacement.ofSub (Term.single a.term)).comp (R.replacement.lift x.sort))
    (R.update x a).replacement (Names.free.bind x) Names.free (by
      funext s c
      simpa only [Replacement.comp, Replacement.lift, Replacement.apply_ofSub, replacement,
        update, Term.instantiate] using (R.const s c).term.shift_instantiate a.term) (by
        intro y _
        by_cases hy : y = x
        · subst y
          simp [Replacement.comp, Replacement.apply_ofSub, Replacement.apply,
            Replacement.lift, Term.single, Term.subst, Names.free, replacement]
        · simp only [Names.bind_other _ hy, Names.free, Term.rename, Replacement.apply,
            Replacement.comp, Replacement.lift, Replacement.apply_ofSub, replacement]
          change ((R.free y.sort y.id).term.shift x.sort).instantiate a.term = _
          rw [Term.shift_instantiate]
          exact congrArg ScopedExpr.term (R.update_other x a hy).symm)
  rw [ht, hu] at h
  have hh : ((R.replacement.lift x.sort).apply t).instantiate a.term =
      (R.update x a).replacement.apply u := by
    simpa only [Option.map_some, Replacement.packed, Option.some.injEq, Sigma.mk.inj_iff,
      heq_eq_eq, true_and, ← Replacement.apply_apply, Replacement.apply_ofSub,
      Term.instantiate] using h
  rw [hh]
  exact .refl _

end Syntactic.Assignment
end Lisa.SCLambdaToPure

/-! The total formula translation under an assignment to the source symbols.
Ill-sorted inputs have a harmless default; every derivation uses the sorted
equations below. No restriction is imposed on intermediate higher-order syntax. -/
namespace Lisa.SCLambdaToPure.Syntactic
open Lambda
namespace Assignment

variable {R : Assignment}

/-- Preserve every admitted first-order and logical constant literally. -/
def FixesConstants (R : Assignment) : Prop :=
  ∀ s c (h : FirstOrderShape.Constant s c), R.const s c = ScopedExpr.constant c h

theorem grounding_fixesConstants : grounding.FixesConstants := by
  intro s c h
  simp [grounding, h]

theorem FixesConstants.update (h : R.FixesConstants) (x : SVar) (a : ScopedExpr x.sort) :
    (R.update x a).FixesConstants := h

noncomputable def formula (R : Assignment) (p : Expr) : Pure.Formula Readback.language := by
  classical
  exact if h : isFormula p then (R.expression p h).readFormula else .bot

@[simp] theorem formula_of_sorted (R : Assignment) (p : Expr) (hp : isFormula p) :
    R.formula p = (R.expression p hp).readFormula := by simp only [formula, dif_pos hp]

noncomputable def context (R : Assignment) (Γ : Finset Expr) : Pure.Context Readback.language :=
  Γ.image R.formula

@[simp] theorem context_empty (R : Assignment) : R.context ∅ = ∅ := Finset.image_empty _
@[simp] theorem context_singleton (R : Assignment) (p : Expr) :
    R.context {p} = {R.formula p} := Finset.image_singleton _ _
@[simp] theorem context_insert (R : Assignment) (p : Expr) (Γ : Finset Expr) :
    R.context (insert p Γ) = insert (R.formula p) (R.context Γ) := Finset.image_insert _ _ _
@[simp] theorem context_union (R : Assignment) (Γ Δ : Finset Expr) :
    R.context (Γ ∪ Δ) = R.context Γ ∪ R.context Δ := Finset.image_union _ _

theorem formula_equiv (R : Assignment) {p q : Expr} (h : AlphaBetaEta p q) (hp : isFormula p) :
    R.formula p = R.formula q := by
  have hq : isFormula q := h.preserves_sort.symm.trans hp
  rw [formula_of_sorted R p hp, formula_of_sorted R q hq]
  exact ScopedExpr.readFormula_equiv (R.expression_equiv h hp hq)

theorem expression_unary (R : Assignment) (c : Identifier) {p : Expr} (hp : p.hasSort s) :
    R.expression (.app (.const ⟨c, s >> t⟩) p) (s := t) (by
      dsimp only [Expr.hasSort] at hp ⊢; simp [Expr.sort, hp]) =
      (R.const (s >> t) c).app (R.expression p hp) := by
  rw [expression_app R (f := .const ⟨c, s >> t⟩) rfl hp, expression_const]

theorem expression_binary (R : Assignment) (c : Identifier) {p q : Expr}
    (hp : p.hasSort s) (hq : q.hasSort t) :
    R.expression (.app (.app (.const ⟨c, s >> t >> u⟩) p) q) (s := u) (by
      dsimp only [Expr.hasSort] at hp hq ⊢; simp [Expr.sort, hp, hq]) =
      ((R.const (s >> t >> u) c).app (R.expression p hp)).app (R.expression q hq) := by
  rw [expression_app R (f := .app (.const ⟨c, s >> t >> u⟩) p)
    (by dsimp only [Expr.hasSort] at hp ⊢; simp [Expr.sort, hp]) hq, expression_unary]

theorem formula_top (hR : R.FixesConstants) : R.formula Expr.top = .top := by
  rw [formula_of_sorted R Expr.top rfl]
  dsimp only [Expr.top, SConst.named]
  rw [expression_const, hR _ _ .top]
  exact Option.some.inj (by
    simpa [ScopedExpr.constant, normalize, eval, quote, reflect, readback, Readback.formula] using
      (ScopedExpr.constant _ FirstOrderShape.Constant.top).readFormula_spec.symm)

theorem formula_bot (hR : R.FixesConstants) : R.formula Expr.bot = .bot := by
  rw [formula_of_sorted R Expr.bot rfl]
  dsimp only [Expr.bot, SConst.named]
  rw [expression_const, hR _ _ .bot]
  exact Option.some.inj (by
    simpa [ScopedExpr.constant, normalize, eval, quote, reflect, readback, Readback.formula] using
      (ScopedExpr.constant _ FirstOrderShape.Constant.bot).readFormula_spec.symm)

theorem formula_neg (hR : R.FixesConstants) (hp : isFormula p) : R.formula (Expr.neg p) = .not (R.formula p) := by
  rw [formula_of_sorted R _ (isFormula_neg hp), formula_of_sorted R _ hp]
  dsimp only [Expr.neg, SConst.named]
  rw [expression_unary R (p := p) (t := prop) ⟨"not", 0⟩ hp, hR _ _ .neg]
  exact ScopedExpr.read_neg _

theorem formula_and (hR : R.FixesConstants) (hp : isFormula p) (hq : isFormula q) :
    R.formula (Expr.and p q) = .and (R.formula p) (R.formula q) := by
  rw [formula_of_sorted R _ (isFormula_and hp hq), formula_of_sorted R _ hp, formula_of_sorted R _ hq]
  dsimp only [Expr.and, SConst.named]
  rw [expression_binary R (p := p) (q := q) (u := prop) ⟨"and", 0⟩ hp hq, hR _ _ .and]
  exact ScopedExpr.read_and _ _

theorem formula_or (hR : R.FixesConstants) (hp : isFormula p) (hq : isFormula q) :
    R.formula (Expr.or p q) = .or (R.formula p) (R.formula q) := by
  rw [formula_of_sorted R _ (isFormula_or hp hq), formula_of_sorted R _ hp, formula_of_sorted R _ hq]
  dsimp only [Expr.or, SConst.named]
  rw [expression_binary R (p := p) (q := q) (u := prop) ⟨"or", 0⟩ hp hq, hR _ _ .or]
  exact ScopedExpr.read_or _ _

theorem formula_imp (hR : R.FixesConstants) (hp : isFormula p) (hq : isFormula q) :
    R.formula (Expr.imp p q) = .imp (R.formula p) (R.formula q) := by
  rw [formula_of_sorted R _ (isFormula_imp hp hq), formula_of_sorted R _ hp, formula_of_sorted R _ hq]
  dsimp only [Expr.imp, SConst.named]
  rw [expression_binary R (p := p) (q := q) (u := prop) ⟨"imp", 0⟩ hp hq, hR _ _ .imp]
  exact ScopedExpr.read_imp _ _

theorem formula_iff (hR : R.FixesConstants) (hp : isFormula p) (hq : isFormula q) :
    R.formula (Expr.iff p q) = .iff (R.formula p) (R.formula q) := by
  rw [formula_of_sorted R _ (isFormula_iff hp hq), formula_of_sorted R _ hp, formula_of_sorted R _ hq]
  dsimp only [Expr.iff, SConst.named]
  rw [expression_binary R (p := p) (q := q) (u := prop) ⟨"iff", 0⟩ hp hq, hR _ _ .iff]
  exact ScopedExpr.read_iff _ _

theorem formula_eq (hR : R.FixesConstants) (hp : isTerm p) (hq : isTerm q) :
    R.formula (Expr.eq p q) = .equal (R.expression p hp).readTerm (R.expression q hq).readTerm := by
  rw [formula_of_sorted R _ (isFormula_eq hp hq)]
  dsimp only [Expr.eq, SConst.named]
  rw [expression_binary R (p := p) (q := q) (u := prop) ⟨"eq", 0⟩ hp hq, hR _ _ .eq]
  exact ScopedExpr.read_equal _ _

end Assignment
end Lisa.SCLambdaToPure.Syntactic

/-! Quantifier and epsilon readback under arbitrary source assignments.
Fresh target names are chosen only for reconstruction, independently of the
names occurring in the source proof. -/
namespace Lisa.SCLambdaToPure.Syntactic
open Lambda

namespace ScopedExpr

theorem read_apply (f : ScopedExpr (ind >> prop)) (x : Identifier)
    (hx : SVar.mk x ind ∉ f.term.freeVars) (a : ScopedExpr ind) :
    (f.app a).readFormula = Pure.substOne x a.readTerm
      (f.app (individual x)).readFormula := by
  have h : (f.app (individual x)).substIndividual x a = f.app a := by
    apply ScopedExpr.ext
    change Term.app ((Replacement.single ⟨x, ind⟩ a.term).apply f.term)
      ((Replacement.single ⟨x, ind⟩ a.term).apply (.free x)) = _
    rw [Replacement.single_fresh f.term ⟨x, ind⟩ a.term hx]
    simp [Replacement.apply, Replacement.single, app]
  rw [← h, readFormula_subst]

theorem read_all (f : ScopedExpr (ind >> prop)) (x : Identifier)
    (hx : SVar.mk x ind ∉ f.term.freeVars) :
    (all f).readFormula = Pure.forall_ x (f.app (individual x)).readFormula := by
  rw [← read_all_lambda x (f.app (individual x))]
  exact readFormula_equiv (e := all f) (f := all (lambda x (f.app (individual x))))
    (by exact .app (.refl _) (lambda_apply f hx).symm)

theorem read_ex (f : ScopedExpr (ind >> prop)) (x : Identifier)
    (hx : SVar.mk x ind ∉ f.term.freeVars) :
    (ex f).readFormula = Pure.exists_ x (f.app (individual x)).readFormula := by
  rw [← read_ex_lambda x (f.app (individual x))]
  exact readFormula_equiv (e := ex f) (f := ex (lambda x (f.app (individual x))))
    (by exact .app (.refl _) (lambda_apply f hx).symm)

theorem read_epsilon (f : ScopedExpr (ind >> prop)) (x : Identifier)
    (hx : SVar.mk x ind ∉ f.term.freeVars) :
    (epsilon f).readTerm = Pure.epsilon_ x (f.app (individual x)).readFormula := by
  rw [← read_epsilon_lambda x (f.app (individual x))]
  exact readTerm_equiv (e := epsilon f) (f := epsilon (lambda x (f.app (individual x))))
    (by exact .app (.refl _) (lambda_apply f hx).symm)

end ScopedExpr

namespace Assignment
variable {R : Assignment}

theorem predicate_sort (x : Identifier) (hp : isFormula p) :
    (Expr.lam ⟨x, ind⟩ p).hasSort (ind >> prop) := by
  change p.sort = some prop at hp
  simp [Expr.hasSort, Expr.sort, hp]

noncomputable def predicate (R : Assignment) (x : Identifier) (p : Expr) (hp : isFormula p) :
    ScopedExpr (ind >> prop) :=
  R.expression (.lam ⟨x, ind⟩ p) (predicate_sort x hp)

theorem formula_forall (hR : R.FixesConstants) (x : Identifier) (hp : isFormula p) :
    R.formula (Expr.forall_ ⟨x, ind⟩ p) = (ScopedExpr.all (R.predicate x p hp)).readFormula := by
  rw [formula_of_sorted R _ (isFormula_forall rfl hp)]
  dsimp only [Expr.forall_, SConst.named]
  rw [expression_unary R (p := .lam ⟨x, ind⟩ p) (t := prop) ⟨"forall", 0⟩ (predicate_sort x hp), hR _ _ .all]
  rfl

theorem formula_exists (hR : R.FixesConstants) (x : Identifier) (hp : isFormula p) :
    R.formula (Expr.exists_ ⟨x, ind⟩ p) = (ScopedExpr.ex (R.predicate x p hp)).readFormula := by
  rw [formula_of_sorted R _ (isFormula_exists rfl hp)]
  dsimp only [Expr.exists_, SConst.named]
  rw [expression_unary R (p := .lam ⟨x, ind⟩ p) (t := prop) ⟨"exists", 0⟩ (predicate_sort x hp), hR _ _ .ex]
  rfl

theorem expression_epsilon (hR : R.FixesConstants) (x : Identifier) (hp : isFormula p) :
    R.expression (Expr.epsilon_ (.lam ⟨x, ind⟩ p)) (s := ind)
      (isTerm_epsilon rfl hp) =
      ScopedExpr.epsilon (R.predicate x p hp) := by
  dsimp only [Expr.epsilon_, SConst.named]
  rw [expression_unary R (p := .lam ⟨x, ind⟩ p) (t := ind) ⟨"epsilon", 0⟩ (predicate_sort x hp), hR _ _ .epsilon]
  rfl

theorem formula_substOne (R : Assignment) (x : Identifier) (hp : isFormula p) (ht : isTerm t) :
    R.formula (Expr.substOne ⟨x, ind⟩ t p) = ((R.predicate x p hp).app (R.expression t ht)).readFormula := by
  have h := R.expression_equiv (AlphaBetaEta.beta ⟨x, ind⟩ p t ht)
    (show (Expr.app (.lam ⟨x, ind⟩ p) t).hasSort prop from by
      change p.sort = some prop at hp
      change t.sort = some ind at ht
      simp [Expr.hasSort, Expr.sort, hp, ht]) (isFormula_substOne rfl ht hp)
  rw [formula_of_sorted R _ (isFormula_substOne rfl ht hp)]
  rw [expression_app R (f := .lam ⟨x, ind⟩ p) (predicate_sort x hp) ht] at h
  exact (ScopedExpr.readFormula_equiv h).symm

theorem predicate_apply (R : Assignment) (x : Identifier) (hp : isFormula p) (a : ScopedExpr ind) :
    ((R.predicate x p hp).app a).readFormula = (R.update ⟨x, ind⟩ a).formula p := by
  rw [formula_of_sorted _ p hp]
  exact ScopedExpr.readFormula_equiv (R.expression_lam_apply ⟨x, ind⟩ p hp a)

end Assignment
end Lisa.SCLambdaToPure.Syntactic
