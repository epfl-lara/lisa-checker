import Lisa.LambdaFol.ToPureFol.FirstOrderExpressions
import Lisa.LambdaFol.ToPureFol.FirstOrderSubstitution
import Lisa.LambdaFol.ToPureFol.PureFolTranslationSubstitution

/-! Individual substitution on complete source expressions commutes with the
first-order reader. This includes substitution underneath epsilon binders. -/
namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization
namespace FirstOrderCompatibleExpr

def substIndividual (e : FirstOrderCompatibleExpr s) (x : Identifier) (a : FirstOrderCompatibleExpr ind) : FirstOrderCompatibleExpr s where
  term := (SymbolSubstitution.single ⟨x, ind⟩ a.term).apply e.term
  language := by
    apply e.language.replace
    · intro u n; exact .bound n
    · intro y
      by_cases h : y = x
      · subst y; simpa [SymbolSubstitution.single] using a.language
      · simpa [SymbolSubstitution.single, h] using FirstOrderShape.Compatible.individual y
    · intro y; simpa [SymbolSubstitution.single] using FirstOrderShape.Compatible.proposition y
    · intros; rfl
  subst_eq σ := by
    rw [← SymbolSubstitution.apply_ofSub, SymbolSubstitution.apply_apply]
    apply SymbolSubstitution.apply_locallyClosed_congr e.term e.subst_eq
    · funext u y
      by_cases h : SVar.mk y u = SVar.mk x ind
      · cases h
        simpa [SymbolSubstitution.comp, SymbolSubstitution.single, SymbolSubstitution.apply_ofSub] using a.subst_eq σ
      · simp only [SymbolSubstitution.comp, SymbolSubstitution.single, h, ↓reduceDIte,
          SymbolSubstitution.apply, SymbolSubstitution.ofSub]
    · rfl

private theorem normalize_subst (e : FirstOrderCompatibleExpr s) (x : Identifier) (a : FirstOrderCompatibleExpr ind) :
    normalize (e.substIndividual x a).term =
      normalize ((SymbolSubstitution.single ⟨x, ind⟩ (normalize a.term)).apply e.term) :=
  normalize_eq_of_equiv (SymbolSubstitution.single_equiv e.term ⟨x, ind⟩ (normalize_sound a.term))

private theorem normalize_shift (a : FirstOrderCompatibleExpr s) (b : LSort) :
    (normalize a.term).shift b = normalize a.term := by
  change (normalize a.term).rename (Ren.shift b) = _
  rw [← Term.subst_ofRen]
  exact normalize_locallyClosed a.term a.subst_eq _

theorem toPureFolFormula_subst (e : FirstOrderCompatibleExpr prop) (x : Identifier) (a : FirstOrderCompatibleExpr ind) :
    (e.substIndividual x a).toPureFolFormula =
      PureFol.substOne x a.toPureFolTerm e.toPureFolFormula := by
  have hn := FirstOrderShape.normalize_replace_formula
    (FirstOrderShape.preserves_single x (FirstOrderShape.normalize_individual a.language a.subst_eq))
    (FirstOrderShape.normalize_formula e.language e.subst_eq)
  have h := PureFolTranslation.fromNormalFormula_single e.toPureFolFormula_spec x a.toPureFolTerm_spec (normalize_shift a ind)
  rw [← hn, ← normalize_subst e x a, (e.substIndividual x a).toPureFolFormula_spec] at h
  exact Option.some.inj h

theorem toPureFolTerm_subst (e : FirstOrderCompatibleExpr ind) (x : Identifier) (a : FirstOrderCompatibleExpr ind) :
    (e.substIndividual x a).toPureFolTerm =
      e.toPureFolTerm.subst (PureFol.single x a.toPureFolTerm) := by
  have hn := FirstOrderShape.normalize_replace_individual
    (FirstOrderShape.preserves_single x (FirstOrderShape.normalize_individual a.language a.subst_eq))
    (FirstOrderShape.normalize_individual e.language e.subst_eq)
  have h := PureFolTranslation.fromNormalTerm_single e.toPureFolTerm_spec x a.toPureFolTerm_spec (normalize_shift a ind)
  rw [← hn, ← normalize_subst e x a, (e.substIndividual x a).toPureFolTerm_spec] at h
  exact Option.some.inj h

end FirstOrderCompatibleExpr
end Lisa.LambdaFol
