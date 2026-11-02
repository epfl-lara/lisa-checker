import Lisa.LambdaFol.ToPureFol.Binders
import Lisa.LambdaFol.EliminateInstantiation.Instantiation

/-! Assign first-order-compatible expressions to the symbols in named Lisa syntax,
then translate the result to PureFol. These operations preserve sorts and respect
αβη equivalence and simultaneous schematic instantiation. -/
namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization

namespace FirstOrderAssignment

noncomputable def applyExpr (R : FirstOrderAssignment) (e : Expr) (h : e.hasSort s) : FirstOrderCompatibleExpr s :=
  R.apply (Classical.choose (interpretNamed_sorted h Names.free))

theorem applyExpr_of_named (R : FirstOrderAssignment) (e : Expr) (h : e.hasSort s)
    {t : AlphaBetaEtaNormalization.Term s} (ht : interpretNamed e Names.free = some ⟨s, t⟩) :
    R.applyExpr e h = R.apply t := by
  have hh := Classical.choose_spec (interpretNamed_sorted h Names.free)
  have he : t = Classical.choose (interpretNamed_sorted h Names.free) := by
    simpa using ht.symm.trans hh
  simp only [applyExpr, ← he]

theorem applyExpr_support (R S : FirstOrderAssignment) (e : Expr) (h : e.hasSort s)
    (hc : R.const = S.const)
    (hf : ∀ x ∈ e.freeVars, R.free x.sort x.id = S.free x.sort x.id) :
    R.applyExpr e h = S.applyExpr e h := by
  obtain ⟨t, ht⟩ := interpretNamed_sorted h Names.free
  rw [R.applyExpr_of_named e h ht, S.applyExpr_of_named e h ht]
  apply FirstOrderCompatibleExpr.ext
  let Q : SymbolSubstitution := { S.replacement with bound := R.replacement.bound }
  have h₁ : R.replacement.apply t = Q.apply t := by
    refine SymbolSubstitution.apply_congr t R.replacement Q rfl ?_ ?_
    · simp only [replacement, hc, Q]
    · intro u x hx
      exact congrArg FirstOrderCompatibleExpr.term (hf ⟨x, u⟩ (interpretNamed_freeVars ht hx))
  exact h₁.trans (SymbolSubstitution.apply_locallyClosed_congr t (subst_of_interpretNamed ht) Q S.replacement rfl rfl)

theorem applyExpr_equiv (R : FirstOrderAssignment) {e f : Expr} (h : AlphaBetaEta e f)
    (he : e.hasSort s) (hf : f.hasSort s) :
    Equiv (R.applyExpr e he).term (R.applyExpr f hf).term := by
  obtain ⟨a, ha⟩ := interpretNamed_sorted he Names.free
  obtain ⟨b, hb⟩ := interpretNamed_sorted hf Names.free
  rw [R.applyExpr_of_named e he ha, R.applyExpr_of_named f hf hb]
  have hh := interpretNamed_alphaBetaEta h Names.free
  rw [ha, hb] at hh
  cases hh with
  | some hh => exact R.replacement.equiv hh

@[simp] theorem applyExpr_var (R : FirstOrderAssignment) (x : SVar) :
    R.applyExpr (.var x) rfl = R.free x.sort x.id :=
  R.applyExpr_of_named (.var x) rfl (t := .free x.id) rfl

@[simp] theorem applyExpr_const (R : FirstOrderAssignment) (c : SConst) :
    R.applyExpr (.const c) rfl = R.const c.sort c.id :=
  R.applyExpr_of_named (.const c) rfl (t := .const c.id) rfl

theorem applyExpr_app (R : FirstOrderAssignment) {f a : Expr}
    (hf : f.hasSort (s >> t)) (ha : a.hasSort s) :
    R.applyExpr (.app f a) (s := t) (by
      dsimp only [Expr.hasSort] at hf ha ⊢; simp [Expr.sort, hf, ha]) =
      (R.applyExpr f hf).app (R.applyExpr a ha) := by
  obtain ⟨f', hf'⟩ := interpretNamed_sorted hf Names.free
  obtain ⟨a', ha'⟩ := interpretNamed_sorted ha Names.free
  rw [R.applyExpr_of_named f hf hf', R.applyExpr_of_named a ha ha']
  exact R.applyExpr_of_named (.app f a) _ (t := .app f' a')
    (by simp [interpretNamed, hf', ha', Packed.app])

/-- Assign a complete expression to one free source name. -/
def update (R : FirstOrderAssignment) (x : SVar) (a : FirstOrderCompatibleExpr x.sort) : FirstOrderAssignment :=
  { R with
    free := fun s y => if h : SVar.mk y s = x then
      cast (congrArg FirstOrderCompatibleExpr (congrArg SVar.sort h).symm) a else R.free s y }

@[simp] theorem update_self (R : FirstOrderAssignment) (x : SVar) (a : FirstOrderCompatibleExpr x.sort) :
    (R.update x a).free x.sort x.id = a := by simp [update]

theorem update_other (R : FirstOrderAssignment) (x : SVar) (a : FirstOrderCompatibleExpr x.sort)
    (h : SVar.mk y s ≠ x) : (R.update x a).free s y = R.free s y := by simp only [update, h, ↓reduceDIte]

theorem applyExpr_update_fresh (R : FirstOrderAssignment) (x : SVar) (a : FirstOrderCompatibleExpr x.sort)
    (e : Expr) (he : e.hasSort s) (hx : x ∉ e.freeVars) :
    (R.update x a).applyExpr e he = R.applyExpr e he := by
  apply applyExpr_support (R.update x a) R e he rfl
  intro y hy
  exact update_other R x a (fun h => hx (h ▸ hy))

end FirstOrderAssignment
end Lisa.LambdaFol

/-! Named abstraction and schematic instantiation commute with the syntactic
assignment. Replacement images are complete expressions and remain simultaneous. -/
namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization

namespace SymbolSubstitution

theorem interpretNamed_congr (e : Expr) (R S : SymbolSubstitution) (η θ : Names)
    (hc : R.const = S.const)
    (hn : ∀ x ∈ e.freeVars, R.apply (η x) = S.apply (θ x)) :
    (interpretNamed e η).map R.packed = (interpretNamed e θ).map S.packed := by
  induction e generalizing R S η θ with
  | var x => simpa [interpretNamed, packed] using hn x (by simp)
  | const c => simp only [interpretNamed, Option.map_some, packed, apply, hc]
  | app f a ihf iha =>
      have hf := ihf R S η θ hc (fun x hx => hn x (Finset.mem_union_left _ hx))
      have ha := iha R S η θ hc (fun x hx => hn x (Finset.mem_union_right _ hx))
      have mapapp (R : SymbolSubstitution) (p q : Option Packed.Expr) :
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

end SymbolSubstitution

namespace FirstOrderAssignment

noncomputable def instantiate (R : FirstOrderAssignment) (σ : Instantiation) : FirstOrderAssignment :=
  { R with free := fun s x => R.apply (σ.lambdaImages ⟨x, s⟩) }

theorem applyExpr_instantiate (R : FirstOrderAssignment) (σ : Instantiation) (e : Expr) (he : e.hasSort s) :
    R.applyExpr (σ.apply e) (σ.hasSort he) = (R.instantiate σ).applyExpr e he := by
  obtain ⟨t, ht⟩ := interpretNamed_sorted (σ.hasSort he) Names.free
  obtain ⟨u, hu⟩ := interpretNamed_sorted he Names.free
  rw [R.applyExpr_of_named _ _ ht, (R.instantiate σ).applyExpr_of_named _ _ hu]
  apply FirstOrderCompatibleExpr.ext
  have h := SymbolSubstitution.interpretNamed_congr e R.replacement (R.instantiate σ).replacement
    σ.lambdaImages Names.free rfl (by intros; rfl)
  rw [← σ.interpret, ht, hu] at h
  simpa only [Option.map_some, SymbolSubstitution.packed, Option.some.injEq, Sigma.mk.inj_iff,
    heq_eq_eq, true_and] using h

theorem applyExpr_lam_apply (R : FirstOrderAssignment) (x : SVar) (e : Expr) (he : e.hasSort s)
    (a : FirstOrderCompatibleExpr x.sort) :
    Equiv ((R.applyExpr (.lam x e) (s := x.sort >> s) (by
      dsimp only [Expr.hasSort] at he ⊢; simp [Expr.sort, he])).app a).term
      ((R.update x a).applyExpr e he).term := by
  obtain ⟨t, ht⟩ := interpretNamed_sorted he (Names.free.bind x)
  obtain ⟨u, hu⟩ := interpretNamed_sorted he Names.free
  rw [R.applyExpr_of_named (.lam x e) _ (t := .lam x.sort t)
    (by simp [interpretNamed, ht, Packed.lam]), (R.update x a).applyExpr_of_named e he hu]
  apply AlphaBetaEtaNormalization.Equiv.trans (AlphaBetaEtaNormalization.Equiv.beta _ a.term)
  have h := SymbolSubstitution.interpretNamed_congr e
    ((SymbolSubstitution.ofSub (AlphaBetaEtaNormalization.Term.single a.term)).comp (R.replacement.lift x.sort))
    (R.update x a).replacement (Names.free.bind x) Names.free (by
      funext s c
      simpa only [SymbolSubstitution.comp, SymbolSubstitution.lift, SymbolSubstitution.apply_ofSub, replacement,
        update, AlphaBetaEtaNormalization.Term.instantiate] using (R.const s c).term.shift_instantiate a.term) (by
        intro y _
        by_cases hy : y = x
        · subst y
          simp [SymbolSubstitution.comp, SymbolSubstitution.apply_ofSub, SymbolSubstitution.apply,
            SymbolSubstitution.lift, AlphaBetaEtaNormalization.Term.single, AlphaBetaEtaNormalization.Term.subst, Names.free, replacement]
        · simp only [Names.bind_other _ hy, Names.free, AlphaBetaEtaNormalization.Term.rename, SymbolSubstitution.apply,
            SymbolSubstitution.comp, SymbolSubstitution.lift, SymbolSubstitution.apply_ofSub, replacement]
          change ((R.free y.sort y.id).term.shift x.sort).instantiate a.term = _
          rw [AlphaBetaEtaNormalization.Term.shift_instantiate]
          exact congrArg FirstOrderCompatibleExpr.term (R.update_other x a hy).symm)
  rw [ht, hu] at h
  have hh : ((R.replacement.lift x.sort).apply t).instantiate a.term =
      (R.update x a).replacement.apply u := by
    simpa only [Option.map_some, SymbolSubstitution.packed, Option.some.injEq, Sigma.mk.inj_iff,
      heq_eq_eq, true_and, ← SymbolSubstitution.apply_apply, SymbolSubstitution.apply_ofSub,
      AlphaBetaEtaNormalization.Term.instantiate] using h
  rw [hh]
  exact .refl _

end FirstOrderAssignment
end Lisa.LambdaFol

/-! The total formula translation under an assignment to the source symbols.
Ill-sorted inputs have a harmless default; every derivation uses the sorted
equations below. No restriction is imposed on intermediate higher-order syntax. -/
namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization
namespace FirstOrderAssignment

variable {R : FirstOrderAssignment}

theorem FixesConstants.update (h : R.FixesConstants) (x : SVar) (a : FirstOrderCompatibleExpr x.sort) :
    (R.update x a).FixesConstants := h

noncomputable def toPureFolFormula (R : FirstOrderAssignment) (p : Expr) : PureFol.Formula PureFolTranslation.language := by
  classical
  exact if h : isFormula p then (R.applyExpr p h).toPureFolFormula else .bot

@[simp] theorem toPureFolFormula_of_sorted (R : FirstOrderAssignment) (p : Expr) (hp : isFormula p) :
    R.toPureFolFormula p = (R.applyExpr p hp).toPureFolFormula := by simp only [toPureFolFormula, dif_pos hp]

noncomputable def toPureFolFormulaSet (R : FirstOrderAssignment) (Γ : Finset Expr) : Finset (PureFol.Formula PureFolTranslation.language) :=
  Γ.image R.toPureFolFormula

@[simp] theorem toPureFolFormulaSet_empty (R : FirstOrderAssignment) : R.toPureFolFormulaSet ∅ = ∅ := Finset.image_empty _
@[simp] theorem toPureFolFormulaSet_singleton (R : FirstOrderAssignment) (p : Expr) :
    R.toPureFolFormulaSet {p} = {R.toPureFolFormula p} := Finset.image_singleton _ _
@[simp] theorem toPureFolFormulaSet_insert (R : FirstOrderAssignment) (p : Expr) (Γ : Finset Expr) :
    R.toPureFolFormulaSet (insert p Γ) = insert (R.toPureFolFormula p) (R.toPureFolFormulaSet Γ) := Finset.image_insert _ _ _
@[simp] theorem toPureFolFormulaSet_union (R : FirstOrderAssignment) (Γ Δ : Finset Expr) :
    R.toPureFolFormulaSet (Γ ∪ Δ) = R.toPureFolFormulaSet Γ ∪ R.toPureFolFormulaSet Δ := Finset.image_union _ _

theorem toPureFolFormula_equiv (R : FirstOrderAssignment) {p q : Expr} (h : AlphaBetaEta p q) (hp : isFormula p) :
    R.toPureFolFormula p = R.toPureFolFormula q := by
  have hq : isFormula q := h.preserves_sort.symm.trans hp
  rw [toPureFolFormula_of_sorted R p hp, toPureFolFormula_of_sorted R q hq]
  exact FirstOrderCompatibleExpr.toPureFolFormula_equiv (R.applyExpr_equiv h hp hq)

theorem applyExpr_unary (R : FirstOrderAssignment) (c : Identifier) {p : Expr} (hp : p.hasSort s) :
    R.applyExpr (.app (.const ⟨c, s >> t⟩) p) (s := t) (by
      dsimp only [Expr.hasSort] at hp ⊢; simp [Expr.sort, hp]) =
      (R.const (s >> t) c).app (R.applyExpr p hp) := by
  rw [applyExpr_app R (f := .const ⟨c, s >> t⟩) rfl hp, applyExpr_const]

theorem applyExpr_binary (R : FirstOrderAssignment) (c : Identifier) {p q : Expr}
    (hp : p.hasSort s) (hq : q.hasSort t) :
    R.applyExpr (.app (.app (.const ⟨c, s >> t >> u⟩) p) q) (s := u) (by
      dsimp only [Expr.hasSort] at hp hq ⊢; simp [Expr.sort, hp, hq]) =
      ((R.const (s >> t >> u) c).app (R.applyExpr p hp)).app (R.applyExpr q hq) := by
  rw [applyExpr_app R (f := .app (.const ⟨c, s >> t >> u⟩) p)
    (by dsimp only [Expr.hasSort] at hp ⊢; simp [Expr.sort, hp]) hq, applyExpr_unary]

theorem toPureFolFormula_top (hR : R.FixesConstants) : R.toPureFolFormula Expr.top = .top := by
  rw [toPureFolFormula_of_sorted R Expr.top rfl]
  dsimp only [Expr.top, SConst.named]
  rw [applyExpr_const, hR _ _ .top]
  exact Option.some.inj (by
    simpa [FirstOrderCompatibleExpr.constant, normalize, eval, quote, reflect, readback, PureFolTranslation.fromNormalFormula?] using
      (FirstOrderCompatibleExpr.constant _ FirstOrderShape.AllowedConstant.top).toPureFolFormula_spec.symm)

theorem toPureFolFormula_bot (hR : R.FixesConstants) : R.toPureFolFormula Expr.bot = .bot := by
  rw [toPureFolFormula_of_sorted R Expr.bot rfl]
  dsimp only [Expr.bot, SConst.named]
  rw [applyExpr_const, hR _ _ .bot]
  exact Option.some.inj (by
    simpa [FirstOrderCompatibleExpr.constant, normalize, eval, quote, reflect, readback, PureFolTranslation.fromNormalFormula?] using
      (FirstOrderCompatibleExpr.constant _ FirstOrderShape.AllowedConstant.bot).toPureFolFormula_spec.symm)

theorem toPureFolFormula_neg (hR : R.FixesConstants) (hp : isFormula p) : R.toPureFolFormula (Expr.neg p) = .not (R.toPureFolFormula p) := by
  rw [toPureFolFormula_of_sorted R _ (isFormula_neg hp), toPureFolFormula_of_sorted R _ hp]
  dsimp only [Expr.neg, SConst.named]
  rw [applyExpr_unary R (p := p) (t := prop) ⟨"not", 0⟩ hp, hR _ _ .neg]
  exact FirstOrderCompatibleExpr.toPureFolFormula_neg _

theorem toPureFolFormula_and (hR : R.FixesConstants) (hp : isFormula p) (hq : isFormula q) :
    R.toPureFolFormula (Expr.and p q) = .and (R.toPureFolFormula p) (R.toPureFolFormula q) := by
  rw [toPureFolFormula_of_sorted R _ (isFormula_and hp hq), toPureFolFormula_of_sorted R _ hp, toPureFolFormula_of_sorted R _ hq]
  dsimp only [Expr.and, SConst.named]
  rw [applyExpr_binary R (p := p) (q := q) (u := prop) ⟨"and", 0⟩ hp hq, hR _ _ .and]
  exact FirstOrderCompatibleExpr.toPureFolFormula_and _ _

theorem toPureFolFormula_or (hR : R.FixesConstants) (hp : isFormula p) (hq : isFormula q) :
    R.toPureFolFormula (Expr.or p q) = .or (R.toPureFolFormula p) (R.toPureFolFormula q) := by
  rw [toPureFolFormula_of_sorted R _ (isFormula_or hp hq), toPureFolFormula_of_sorted R _ hp, toPureFolFormula_of_sorted R _ hq]
  dsimp only [Expr.or, SConst.named]
  rw [applyExpr_binary R (p := p) (q := q) (u := prop) ⟨"or", 0⟩ hp hq, hR _ _ .or]
  exact FirstOrderCompatibleExpr.toPureFolFormula_or _ _

theorem toPureFolFormula_imp (hR : R.FixesConstants) (hp : isFormula p) (hq : isFormula q) :
    R.toPureFolFormula (Expr.imp p q) = .imp (R.toPureFolFormula p) (R.toPureFolFormula q) := by
  rw [toPureFolFormula_of_sorted R _ (isFormula_imp hp hq), toPureFolFormula_of_sorted R _ hp, toPureFolFormula_of_sorted R _ hq]
  dsimp only [Expr.imp, SConst.named]
  rw [applyExpr_binary R (p := p) (q := q) (u := prop) ⟨"imp", 0⟩ hp hq, hR _ _ .imp]
  exact FirstOrderCompatibleExpr.toPureFolFormula_imp _ _

theorem toPureFolFormula_iff (hR : R.FixesConstants) (hp : isFormula p) (hq : isFormula q) :
    R.toPureFolFormula (Expr.iff p q) = .iff (R.toPureFolFormula p) (R.toPureFolFormula q) := by
  rw [toPureFolFormula_of_sorted R _ (isFormula_iff hp hq), toPureFolFormula_of_sorted R _ hp, toPureFolFormula_of_sorted R _ hq]
  dsimp only [Expr.iff, SConst.named]
  rw [applyExpr_binary R (p := p) (q := q) (u := prop) ⟨"iff", 0⟩ hp hq, hR _ _ .iff]
  exact FirstOrderCompatibleExpr.toPureFolFormula_iff _ _

theorem toPureFolFormula_eq (hR : R.FixesConstants) (hp : isTerm p) (hq : isTerm q) :
    R.toPureFolFormula (Expr.eq p q) = .equal (R.applyExpr p hp).toPureFolTerm (R.applyExpr q hq).toPureFolTerm := by
  rw [toPureFolFormula_of_sorted R _ (isFormula_eq hp hq)]
  dsimp only [Expr.eq, SConst.named]
  rw [applyExpr_binary R (p := p) (q := q) (u := prop) ⟨"eq", 0⟩ hp hq, hR _ _ .eq]
  exact FirstOrderCompatibleExpr.toPureFolFormula_equal _ _

end FirstOrderAssignment
end Lisa.LambdaFol

/-! Translate named quantifiers, epsilon, and individual substitution to PureFol.
Fresh target names are chosen only for reconstruction, independently of the
names occurring in the source proof. -/
namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization

namespace FirstOrderAssignment
variable {R : FirstOrderAssignment}

theorem predicate_sort (x : Identifier) (hp : isFormula p) :
    (Expr.lam ⟨x, ind⟩ p).hasSort (ind >> prop) := by
  change p.sort = some prop at hp
  simp [Expr.hasSort, Expr.sort, hp]

noncomputable def predicate (R : FirstOrderAssignment) (x : Identifier) (p : Expr) (hp : isFormula p) :
    FirstOrderCompatibleExpr (ind >> prop) :=
  R.applyExpr (.lam ⟨x, ind⟩ p) (predicate_sort x hp)

theorem predicate_apply (R : FirstOrderAssignment) (x : Identifier) (hp : isFormula p) (a : FirstOrderCompatibleExpr ind) :
    ((R.predicate x p hp).app a).toPureFolFormula = (R.update ⟨x, ind⟩ a).toPureFolFormula p := by
  rw [toPureFolFormula_of_sorted _ p hp]
  exact FirstOrderCompatibleExpr.toPureFolFormula_equiv (R.applyExpr_lam_apply ⟨x, ind⟩ p hp a)

/-- Translate a quantifier directly to PureFol, using a fresh target name `y`. -/
theorem toPureFolFormula_forall (hR : R.FixesConstants) (x : Identifier) (hp : isFormula p)
    (y : Identifier) (hy : SVar.mk y ind ∉ (R.predicate x p hp).term.freeVars) :
    R.toPureFolFormula (Expr.forall_ ⟨x, ind⟩ p) =
      PureFol.forall_ y ((R.update ⟨x, ind⟩ (FirstOrderCompatibleExpr.individual y)).toPureFolFormula p) := by
  rw [toPureFolFormula_of_sorted R _ (isFormula_forall rfl hp)]
  dsimp only [Expr.forall_, SConst.named]
  rw [applyExpr_unary R (p := .lam ⟨x, ind⟩ p) (t := prop) ⟨"forall", 0⟩ (predicate_sort x hp), hR _ _ .all]
  exact ((R.predicate x p hp).toPureFolFormula_all y hy).trans (congrArg (PureFol.forall_ y) (R.predicate_apply x hp _))

theorem toPureFolFormula_exists (hR : R.FixesConstants) (x : Identifier) (hp : isFormula p)
    (y : Identifier) (hy : SVar.mk y ind ∉ (R.predicate x p hp).term.freeVars) :
    R.toPureFolFormula (Expr.exists_ ⟨x, ind⟩ p) =
      PureFol.exists_ y ((R.update ⟨x, ind⟩ (FirstOrderCompatibleExpr.individual y)).toPureFolFormula p) := by
  rw [toPureFolFormula_of_sorted R _ (isFormula_exists rfl hp)]
  dsimp only [Expr.exists_, SConst.named]
  rw [applyExpr_unary R (p := .lam ⟨x, ind⟩ p) (t := prop) ⟨"exists", 0⟩ (predicate_sort x hp), hR _ _ .ex]
  exact ((R.predicate x p hp).toPureFolFormula_ex y hy).trans (congrArg (PureFol.exists_ y) (R.predicate_apply x hp _))

theorem term_epsilon (hR : R.FixesConstants) (x : Identifier) (hp : isFormula p)
    (y : Identifier) (hy : SVar.mk y ind ∉ (R.predicate x p hp).term.freeVars) :
    (R.applyExpr (Expr.epsilon_ (.lam ⟨x, ind⟩ p)) (isTerm_epsilon rfl hp)).toPureFolTerm =
      PureFol.epsilon_ y ((R.update ⟨x, ind⟩ (FirstOrderCompatibleExpr.individual y)).toPureFolFormula p) := by
  dsimp only [Expr.epsilon_, SConst.named]
  rw [applyExpr_unary R (p := .lam ⟨x, ind⟩ p) (t := ind) ⟨"epsilon", 0⟩ (predicate_sort x hp), hR _ _ .epsilon]
  exact ((R.predicate x p hp).toPureFolTerm_epsilon y hy).trans (congrArg (PureFol.epsilon_ y) (R.predicate_apply x hp _))

/-- Translate individual substitution using the same body as the quantifier equations. -/
theorem toPureFolFormula_substOne (R : FirstOrderAssignment) (x : Identifier) (hp : isFormula p) (ht : isTerm t)
    (y : Identifier) (hy : SVar.mk y ind ∉ (R.predicate x p hp).term.freeVars) :
    R.toPureFolFormula (Expr.substOne ⟨x, ind⟩ t p) =
      PureFol.substOne y (R.applyExpr t ht).toPureFolTerm
        ((R.update ⟨x, ind⟩ (FirstOrderCompatibleExpr.individual y)).toPureFolFormula p) := by
  have h := R.applyExpr_equiv (AlphaBetaEta.beta ⟨x, ind⟩ p t ht)
    (show (Expr.app (.lam ⟨x, ind⟩ p) t).hasSort prop from by
      change p.sort = some prop at hp
      change t.sort = some ind at ht
      simp [Expr.hasSort, Expr.sort, hp, ht]) (isFormula_substOne rfl ht hp)
  rw [toPureFolFormula_of_sorted R _ (isFormula_substOne rfl ht hp)]
  rw [applyExpr_app R (f := .lam ⟨x, ind⟩ p) (predicate_sort x hp) ht] at h
  exact (FirstOrderCompatibleExpr.toPureFolFormula_equiv h).symm.trans
    (((R.predicate x p hp).toPureFolFormula_apply y hy (R.applyExpr t ht)).trans
      (congrArg (PureFol.substOne y (R.applyExpr t ht).toPureFolTerm) (R.predicate_apply x hp _)))

end FirstOrderAssignment
end Lisa.LambdaFol

namespace Lisa.LambdaFol

def AgreeOutside (xs : List SVar) (R S : FirstOrderAssignment) : Prop :=
  ∀ x, x ∉ xs → R.free x.sort x.id = S.free x.sort x.id

end Lisa.LambdaFol

/-! Translation to PureFol is well-defined on αβη formula classes. -/
namespace Lisa.LambdaFol.FirstOrderAssignment
open Instantiation

noncomputable def toPureFolFormulaClass (R : FirstOrderAssignment) (p : LambdaFol.Formula) :
    PureFol.Formula PureFolTranslation.language := R.toPureFolFormula (representative p)

@[simp] theorem toPureFolFormulaClass_ofExpr (R : FirstOrderAssignment) (p : Expr) (hp : isFormula p) :
    R.toPureFolFormulaClass (LambdaFol.ofExpr p hp) = R.toPureFolFormula p :=
  R.toPureFolFormula_equiv ((LambdaFol.ofExpr_eq _ _).mp (of_representative (LambdaFol.ofExpr p hp))) (representative_sort _)

noncomputable def toPureFolFormulaClassSet (R : FirstOrderAssignment) (Γ : Finset LambdaFol.Formula) :
    Finset (PureFol.Formula PureFolTranslation.language) := Γ.image R.toPureFolFormulaClass

@[simp] theorem toPureFolFormulaClassSet_empty (R : FirstOrderAssignment) : R.toPureFolFormulaClassSet ∅ = ∅ := Finset.image_empty _
@[simp] theorem toPureFolFormulaClassSet_singleton (R : FirstOrderAssignment) (p : LambdaFol.Formula) :
    R.toPureFolFormulaClassSet {p} = {R.toPureFolFormulaClass p} := Finset.image_singleton _ _
@[simp] theorem toPureFolFormulaClassSet_insert (R : FirstOrderAssignment) (p : LambdaFol.Formula) (Γ : Finset LambdaFol.Formula) :
    R.toPureFolFormulaClassSet (insert p Γ) = insert (R.toPureFolFormulaClass p) (R.toPureFolFormulaClassSet Γ) := Finset.image_insert _ _ _
@[simp] theorem toPureFolFormulaClassSet_union (R : FirstOrderAssignment) (Γ Δ : Finset LambdaFol.Formula) :
    R.toPureFolFormulaClassSet (Γ ∪ Δ) = R.toPureFolFormulaClassSet Γ ∪ R.toPureFolFormulaClassSet Δ := Finset.image_union _ _

theorem toPureFolFormulaClassSet_raw (R : FirstOrderAssignment) (Γ : Finset Expr) (hΓ : isFSet Γ) :
    R.toPureFolFormulaClassSet (LambdaFol.formulaSet Γ hΓ) = R.toPureFolFormulaSet Γ := by
  ext p
  simp only [toPureFolFormulaClassSet, toPureFolFormulaSet, Finset.mem_image, LambdaFol.mem_formulaSet]
  constructor
  · rintro ⟨q, ⟨e, he, rfl⟩, h⟩
    exact ⟨e, he, by simpa using h⟩
  · rintro ⟨e, he, h⟩
    exact ⟨LambdaFol.ofExpr e (hΓ e he), ⟨e, he, rfl⟩, by simpa using h⟩

theorem toPureFolFormulaClassSet_update_fresh (R : FirstOrderAssignment) (x : SVar) (a : FirstOrderCompatibleExpr x.sort)
    (Γ : Finset LambdaFol.Formula) (hf : LambdaFol.Fresh x Γ) :
    (R.update x a).toPureFolFormulaClassSet Γ = R.toPureFolFormulaClassSet Γ := by
  apply Finset.image_congr
  intro p hp
  obtain ⟨e, he, rfl, hx⟩ := hf p hp
  simp only [toPureFolFormulaClass_ofExpr, toPureFolFormula_of_sorted _ e he]
  rw [R.applyExpr_update_fresh x a e he hx]

theorem toPureFolFormulaClassSet_agreeOutside (R S : FirstOrderAssignment) (xs : List SVar) (Γ : Finset LambdaFol.Formula)
    (hc : S.const = R.const) (hs : AgreeOutside xs S R)
    (hf : ∀ x ∈ xs, LambdaFol.Fresh x Γ) : S.toPureFolFormulaClassSet Γ = R.toPureFolFormulaClassSet Γ := by
  induction xs generalizing S with
  | nil =>
      apply Finset.image_congr
      intro p _
      simp only [toPureFolFormulaClass, toPureFolFormula_of_sorted _ _ (representative_sort p)]
      rw [S.applyExpr_support R _ (representative_sort p) hc (fun x _ => hs x (by simp))]
  | cons x xs ih =>
      let U := S.update x (R.free x.sort x.id)
      have hu : AgreeOutside xs U R := by
        intro y hy
        by_cases h : y = x
        · subst y; exact S.update_self x _
        · exact (S.update_other x _ h).trans (hs y (by simp [h, hy]))
      exact (S.toPureFolFormulaClassSet_update_fresh x _ Γ (hf x (by simp))).symm.trans
        (ih U hc hu (fun y hy => hf y (by simp [hy])))

end Lisa.LambdaFol.FirstOrderAssignment
