import Lisa.LambdaFol.Translation
import Lisa.LambdaFol.ToPureFol.SignatureAndVariables
import Lisa.LambdaFol.PureFol
import Lisa.LambdaFol.ToPureFol.FirstOrderShape
import Lisa.LambdaFol.ToPureFol.NormalizationScope

/-! Translation to PureFol succeeds on well-scoped first-order shapes. -/

namespace Lisa.LambdaFol.PureFolTranslation

open AlphaBetaEtaNormalization.Algorithm FirstOrderShape

private def ReadsIndividual (ρ : BoundVarMap n) : {s : LSort} → Term s → Prop
  | .ind, e => (fromNormalTerm? ρ e).isSome
  | _, e => (symbolAndArguments? ρ e).isSome

private theorem fromNormalFormula_const_isSome (ρ : BoundVarMap n) (c : Identifier) :
    (fromNormalFormula? ρ (.const c)).isSome := by
  by_cases ht : c = ⟨"top", 0⟩
  · subst c; simp [fromNormalFormula?]
  by_cases hb : c = ⟨"bot", 0⟩
  · subst c; simp [fromNormalFormula?]
  simp [fromNormalFormula?]

private theorem fromNormalFormula_app_isSome (ρ : BoundVarMap n) (f : Term (ind >> prop)) (a : Term ind)
    (hf : (symbolAndArguments? ρ f).isSome) (ha : (fromNormalTerm? ρ a).isSome) :
    (fromNormalFormula? ρ (.app f a)).isSome := by
  by_cases he : ∃ t : Term ind, f = .app (.const ⟨"eq", 0⟩) t
  · obtain ⟨t, rfl⟩ := he
    simp only [symbolAndArguments?] at hf
    cases ht : fromNormalTerm? ρ t <;> simp [ht] at hf
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha
    simp [fromNormalFormula?, ht, ha']
  · obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp hf
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha
    simp only [not_exists] at he
    simp [fromNormalFormula?, hc, ha']

private def ReadsFormula (ρ : BoundVarMap n) : {s : LSort} → Term s → Prop
  | .prop, e => (fromNormalFormula? ρ e).isSome
  | _, e => (symbolAndArguments? ρ e).isSome

private theorem bind_isSome {d : Depth} (ρ : BoundVarMap n) (hρ : ∀ k < d ind, (ρ k).isSome) :
    ∀ k < (d.inc ind) ind, (bind ρ k).isSome := by
  intro k hk
  cases k with
  | zero => rfl
  | succ k => simpa [bind] using hρ k (by simpa using hk)

mutual
private theorem individual_reads {s n : _} {d} {e : Term s} (h : IsTermOrFunction e)
    (hs : Scoped d e) (ρ : BoundVarMap n) (hρ : ∀ k < d ind, (ρ k).isSome) :
    ReadsIndividual ρ e := by
  match h with
  | .bound k => simpa [ReadsIndividual, fromNormalTerm?] using hρ k hs
  | .free x => simp [ReadsIndividual, fromNormalTerm?]
  | .symbol k c => cases k <;> simp [ReadsIndividual, fromNormalTerm?, symbolAndArguments?, arity]
  | @IsTermOrFunction.app s f a hf ha =>
      obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp (individual_reads hf hs.1 ρ hρ)
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (individual_reads ha hs.2 ρ hρ)
      cases s <;> simp [ReadsIndividual, fromNormalTerm?, symbolAndArguments?, hc, ha']

  | .epsilon hp =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (fromNormalFormula_reads hp hs.2 (bind ρ) (bind_isSome ρ hρ))
      simp [ReadsIndividual, fromNormalTerm?, hp']
termination_by structural h
private theorem fromNormalFormula_reads {s n : _} {d} {e : Term s} (h : IsFormulaOrPredicate e)
    (hs : Scoped d e) (ρ : BoundVarMap n) (hρ : ∀ k < d ind, (ρ k).isSome) :
    ReadsFormula ρ e := by
  match h with
  | .free x => simp [ReadsFormula, fromNormalFormula?]
  | .symbol k c => cases k with
    | zero => exact fromNormalFormula_const_isSome ρ c
    | succ k => simp [ReadsFormula, symbolAndArguments?, arity]
  | @IsFormulaOrPredicate.app s f a hf ha =>
      have hf' := fromNormalFormula_reads hf hs.1 ρ hρ
      have ha' := individual_reads ha hs.2 ρ hρ
      cases s with
      | prop => exact fromNormalFormula_app_isSome ρ f a hf' ha'
      | ind | arrow _ _ =>
          obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp hf'
          obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha'
          simp [ReadsFormula, symbolAndArguments?, hc, ha']
  | .neg hp =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (fromNormalFormula_reads hp hs.2 ρ hρ)
      simp [ReadsFormula, fromNormalFormula?, hp']
  | .and hp hq | .or hp hq | .imp hp hq | .iff hp hq =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (fromNormalFormula_reads hp hs.1.2 ρ hρ)
      obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp (fromNormalFormula_reads hq hs.2 ρ hρ)
      simp [ReadsFormula, fromNormalFormula?, hp', hq']
  | .all hp | .ex hp =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (fromNormalFormula_reads hp hs.2 (bind ρ) (bind_isSome ρ hρ))
      simp [ReadsFormula, fromNormalFormula?, hp']

termination_by structural h
end

theorem fromNormalFormula_isSome {e : Term prop} (h : IsFormulaOrPredicate e) (hs : Scoped d e)
    (ρ : BoundVarMap n) (hρ : ∀ k < d ind, (ρ k).isSome) : (fromNormalFormula? ρ e).isSome :=
  fromNormalFormula_reads h hs ρ hρ

theorem fromNormalTerm_isSome {e : Term ind} (h : IsTermOrFunction e) (hs : Scoped d e)
    (ρ : BoundVarMap n) (hρ : ∀ k < d ind, (ρ k).isSome) : (fromNormalTerm? ρ e).isSome :=
  individual_reads h hs ρ hρ

/-- Translation succeeds for well-sorted formulas whose constants and free
variables satisfy the first-order restrictions. -/
theorem fromExprFormula_isSome {p : Expr} (hp : isFormula p)
    (hc : AllowedConstants p)
    (hv : ∀ x ∈ p.freeVars, x.sort = ind ∨ x.sort = prop) :
    (fromExprFormula? p).isSome := by
  obtain ⟨e, he⟩ := interpretNamed_sorted hp Names.free
  have hshape := normalForm_isFirstOrder he hc hv
  have hs := normalize_scoped e (subst_of_interpretNamed he)
  simpa [fromExprFormula?, PureFolTranslation.normalizeExpr?, he] using
    fromNormalFormula_isSome hshape hs (n := 0) (fun _ => none) (by simp [Depth.zero])

end Lisa.LambdaFol.PureFolTranslation
