import Lisa.LambdaFol.ToPureFol.SymbolSubstitution
import Lisa.AlphaBetaEtaNormalization.Reification
import Lisa.LambdaFol.ToPureFol.NormalizationScope
import Lisa.LambdaFol.ToPureFol.FirstOrderShape

/-! Replacement depends only on the symbols occurring in an expression.
For a complete expression it is independent of the ambient-index assignment. -/
namespace Lisa.LambdaFol.SymbolSubstitution
open AlphaBetaEtaNormalization

theorem apply_congr (e : Term s) (R S : SymbolSubstitution)
    (hb : R.bound = S.bound) (hc : R.const = S.const)
    (hf : ∀ u x, SVar.mk x u ∈ e.freeVars → R.free u x = S.free u x) :
    R.apply e = S.apply e := by
  induction e generalizing R S with
  | bound n => exact congrFun (congrFun hb _) n
  | free x => exact hf _ x (by simp)
  | const c => exact congrFun (congrFun hc _) c
  | app f a ihf iha =>
      exact congrArg₂ Term.app
        (ihf R S hb hc (fun u x hx => hf u x (Finset.mem_union_left _ hx)))
        (iha R S hb hc (fun u x hx => hf u x (Finset.mem_union_right _ hx)))
  | lam b e ih =>
      apply congrArg (Term.lam b)
      refine ih (R.lift b) (S.lift b) ?_ ?_ ?_
      · simp [lift, hb]
      · funext u c; simp [lift, hc]
      · intro u x hx
        simp [lift, hf u x hx]

theorem apply_locallyClosed_congr (e : Term s) (he : ∀ σ, e.subst σ = e) (R S : SymbolSubstitution)
    (hf : R.free = S.free) (hc : R.const = S.const) : R.apply e = S.apply e := by
  let σ : Sub := fun _ _ => .const ⟨"_unused", 0⟩
  have h : R.comp (ofSub σ) = S.comp (ofSub σ) := by
    apply SymbolSubstitution.ext
    · funext u n; simp [comp, ofSub, σ, apply, hc]
    · funext u x; simp [comp, ofSub, apply, hf]
    · funext u c; simp [comp, ofSub, apply, hc]
  calc
    R.apply e = R.apply (e.subst σ) := congrArg R.apply (he σ).symm
    _ = S.apply (e.subst σ) := by rw [← apply_ofSub, apply_apply, h, ← apply_apply, apply_ofSub]
    _ = S.apply e := congrArg S.apply (he σ)

theorem abstract_fresh (e : Term s) (x : SVar) (hx : x ∉ e.freeVars) :
    (abstract x).apply e = e.shift x.sort := by
  change (abstract x).apply e = e.rename (Ren.shift x.sort)
  rw [← Term.subst_ofRen, ← apply_ofSub]
  refine apply_congr e _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · intro u y hy
    have hn : SVar.mk y u ≠ x := fun h => hx (h ▸ hy)
    simp [abstract, ofSub, Names.bind_other _ hn, Names.free, Term.rename]

theorem abstract_locallyClosed (e : Term s) (he : ∀ σ, e.subst σ = e) (x : SVar) (σ : Sub) :
    (Term.lam x.sort ((abstract x).apply e)).subst σ = .lam x.sort ((abstract x).apply e) := by
  apply congrArg (Term.lam x.sort)
  rw [← apply_ofSub, apply_apply]
  apply apply_locallyClosed_congr e he
  · funext u y
    by_cases h : SVar.mk y u = x
    · subst x
      simp [comp, abstract, ofSub, Names.bind_self, apply]
    · simp [comp, abstract, ofSub, Names.bind_other _ h, Names.free, Term.rename, apply]
  · rfl

theorem abstract_eta {x : SVar} (f : Term (x.sort >> s)) (hx : x ∉ f.freeVars) :
    Equiv (.lam x.sort ((abstract x).apply (.app f (.free x.id)))) f := by
  rw [apply, abstract_fresh f x hx]
  simpa only [apply, abstract, Names.bind_self] using Equiv.eta f

theorem single_fresh (e : Term s) (x : SVar) (a : Term x.sort) (hx : x ∉ e.freeVars) :
    (single x a).apply e = e := by
  apply Eq.trans (b := (ofSub Sub.id).apply e)
  · refine apply_congr e _ _ rfl rfl ?_
    intro u y hy
    have hn : SVar.mk y u ≠ x := fun h => hx (h ▸ hy)
    simp [single, ofSub, hn]
  · simp

theorem apply_equiv (e : Term s) (R S : SymbolSubstitution)
    (hb : ∀ u n, Equiv (R.bound u n) (S.bound u n))
    (hf : ∀ u x, Equiv (R.free u x) (S.free u x))
    (hc : ∀ u c, Equiv (R.const u c) (S.const u c)) : Equiv (R.apply e) (S.apply e) := by
  induction e generalizing R S with
  | bound n => exact hb _ n
  | free x => exact hf _ x
  | const c => exact hc _ c
  | app f a ihf iha => exact .app (ihf R S hb hf hc) (iha R S hb hf hc)
  | lam b e ih =>
      apply Equiv.lam
      refine ih (R.lift b) (S.lift b) ?_ ?_ ?_
      · intro u n
        by_cases h : u = b
        · subst u; cases n with
          | zero => simpa [lift] using AlphaBetaEtaNormalization.Equiv.refl (Term.bound (s := b) 0)
          | succ n => simpa [lift] using (hb b n).rename (Ren.shift b)
        · simpa [lift, Sub.lift_other h] using (hb u n).rename (Ren.shift b)
      · intro u x; exact (hf u x).rename _
      · intro u c; exact (hc u c).rename _

theorem single_equiv (e : Term s) (x : SVar) {a b : Term x.sort} (h : Equiv a b) :
    Equiv ((single x a).apply e) ((single x b).apply e) := by
  apply apply_equiv
  · intros; exact .refl _
  · intro u y
    by_cases hy : SVar.mk y u = x
    · subst x; simpa [single] using h
    · simp only [single, hy, ↓reduceDIte]; exact .refl _
  · intros; exact .refl _

end Lisa.LambdaFol.SymbolSubstitution

namespace Lisa.LambdaFol
open AlphaBetaEtaNormalization

theorem Scoped.subst_eq {e : Term s} (h : Scoped d e) (σ : Sub)
    (hσ : ∀ u n, n < d u → σ u n = .bound n) : e.subst σ = e := by
  induction e generalizing d σ with
  | bound n => exact hσ _ n h
  | free | const => rfl
  | app f a ihf iha => exact congrArg₂ Term.app (ihf h.1 σ hσ) (iha h.2 σ hσ)
  | lam b e ih =>
      apply congrArg (Term.lam b)
      apply ih h
      intro u n hn
      by_cases hu : u = b
      · subst u; cases n with
        | zero => simp
        | succ n => simp [hσ b n (by simpa using hn), Term.rename, Ren.shift]
      · have hn' : n < d u := by simpa [Depth.inc, hu] using hn
        simp [hσ u n hn', Term.rename, Ren.shift, hu]

theorem normalize_locallyClosed (e : Term s) (he : ∀ σ, e.subst σ = e) (σ : Sub) :
    (normalize e).subst σ = normalize e :=
  (normalize_scoped e he).subst_eq σ (by simp [Depth.zero])

end Lisa.LambdaFol

/-! First-order replacement preserves the canonical epsilon grammar.
This lets normalization and individual replacement commute without a semantic
interpretation or an assumption about first-order provability. -/
namespace Lisa.LambdaFol.FirstOrderShape
open AlphaBetaEtaNormalization

mutual
theorem IsTermOrFunction.rename {e : Term s} (h : IsTermOrFunction e) (ρ : Ren) : IsTermOrFunction (e.rename ρ) := by
  match h with
  | .bound _ => exact .bound _
  | .free _ => exact .free _
  | .symbol n c => exact .symbol n c
  | .app hf ha => exact .app (hf.rename ρ) (ha.rename ρ)
  | .epsilon hp => exact .epsilon (hp.rename (ρ.lift ind))
theorem IsFormulaOrPredicate.rename {e : Term s} (h : IsFormulaOrPredicate e) (ρ : Ren) : IsFormulaOrPredicate (e.rename ρ) := by
  match h with
  | .free _ => exact .free _
  | .symbol n c => exact .symbol n c
  | .app hf ha => exact .app (hf.rename ρ) (ha.rename ρ)
  | .neg hp => exact .neg (hp.rename ρ)
  | .and hp hq => exact .and (hp.rename ρ) (hq.rename ρ)
  | .or hp hq => exact .or (hp.rename ρ) (hq.rename ρ)
  | .imp hp hq => exact .imp (hp.rename ρ) (hq.rename ρ)
  | .iff hp hq => exact .iff (hp.rename ρ) (hq.rename ρ)
  | .all hp => exact .all (hp.rename (ρ.lift ind))
  | .ex hp => exact .ex (hp.rename (ρ.lift ind))
end

structure Preserves (R : SymbolSubstitution) : Prop where
  bound : ∀ n, IsTermOrFunction (R.bound ind n)
  free : ∀ x, IsTermOrFunction (R.free ind x)
  proposition : ∀ x, R.free prop x = .free x
  const : ∀ s c, R.const s c = .const c

theorem Preserves.lift (h : Preserves R) : Preserves (R.lift ind) where
  bound := by
    intro n
    cases n with
    | zero => simpa [SymbolSubstitution.lift] using IsTermOrFunction.bound 0
    | succ n => simpa [SymbolSubstitution.lift] using (h.bound n).rename (Ren.shift ind)
  free x := (h.free x).rename _
  proposition := by intro x; simp [SymbolSubstitution.lift, h.proposition, Term.rename]
  const := by intro s c; simp [SymbolSubstitution.lift, h.const, Term.rename]

mutual
theorem IsTermOrFunction.replace {e : Term s} (h : IsTermOrFunction e) (hR : Preserves R) :
    IsTermOrFunction (R.apply e) := by
  match h with
  | .bound n => exact hR.bound n
  | .free x => exact hR.free x
  | .symbol n c => simpa [SymbolSubstitution.apply, hR.const] using IsTermOrFunction.symbol n c
  | .app hf ha => exact .app (hf.replace hR) (ha.replace hR)
  | .epsilon hp =>
      simpa [SymbolSubstitution.apply, hR.const] using IsTermOrFunction.epsilon (IsFormulaOrPredicate.replace hp hR.lift)
theorem IsFormulaOrPredicate.replace {e : Term s} (h : IsFormulaOrPredicate e) (hR : Preserves R) :
    IsFormulaOrPredicate (R.apply e) := by
  match h with
  | .free x => simpa [SymbolSubstitution.apply, hR.proposition] using IsFormulaOrPredicate.free x
  | .symbol n c => simpa [SymbolSubstitution.apply, hR.const] using IsFormulaOrPredicate.symbol n c
  | .app hf ha => exact .app (hf.replace hR) (ha.replace hR)
  | .neg hp => simpa [SymbolSubstitution.apply, hR.const] using IsFormulaOrPredicate.neg (hp.replace hR)
  | .and hp hq => simpa [SymbolSubstitution.apply, hR.const] using IsFormulaOrPredicate.and (hp.replace hR) (hq.replace hR)
  | .or hp hq => simpa [SymbolSubstitution.apply, hR.const] using IsFormulaOrPredicate.or (hp.replace hR) (hq.replace hR)
  | .imp hp hq => simpa [SymbolSubstitution.apply, hR.const] using IsFormulaOrPredicate.imp (hp.replace hR) (hq.replace hR)
  | .iff hp hq => simpa [SymbolSubstitution.apply, hR.const] using IsFormulaOrPredicate.iff (hp.replace hR) (hq.replace hR)
  | .all hp => simpa [SymbolSubstitution.apply, hR.const] using IsFormulaOrPredicate.all (hp.replace hR.lift)
  | .ex hp => simpa [SymbolSubstitution.apply, hR.const] using IsFormulaOrPredicate.ex (hp.replace hR.lift)
end

theorem normalize_replace_formula (hR : Preserves R) {e : Term prop}
    (h : IsFormulaOrPredicate (normalize e)) : normalize (R.apply e) = R.apply (normalize e) := by
  rw [normalize_eq_of_equiv (R.equiv (normalize_sound e))]
  exact normalize_formula_eq (h.replace hR)

theorem normalize_replace_individual (hR : Preserves R) {e : Term ind}
    (h : IsTermOrFunction (normalize e)) : normalize (R.apply e) = R.apply (normalize e) := by
  rw [normalize_eq_of_equiv (R.equiv (normalize_sound e))]
  exact normalize_individual_eq (h.replace hR)

theorem preserves_abstract (x : Identifier) : Preserves (SymbolSubstitution.abstract ⟨x, ind⟩) where
  bound _ := .bound _
  free := by
    intro y
    change IsTermOrFunction (Names.free.bind ⟨x, ind⟩ ⟨y, ind⟩)
    by_cases h : y = x
    · subst y; simp only [Names.bind_self]; exact .bound _
    · simp [Names.bind, Names.free, h, Term.rename]
      exact .free _
  proposition := by
    intro y
    simp [SymbolSubstitution.abstract, Names.bind, Names.free, Term.rename]
  const _ _ := rfl

theorem preserves_single (x : Identifier) {a : Term ind} (ha : IsTermOrFunction a) :
    Preserves (SymbolSubstitution.single ⟨x, ind⟩ a) where
  bound _ := .bound _
  free := by
    intro y
    by_cases h : y = x
    · subst y; simpa [SymbolSubstitution.single] using ha
    · simpa [SymbolSubstitution.single, h] using IsTermOrFunction.free y
  proposition := by intro y; simp [SymbolSubstitution.single]
  const _ _ := rfl

theorem Compatible.replace {e : Term s} (h : Compatible e) (R : SymbolSubstitution)
    (hb : ∀ u n, Compatible (R.bound u n))
    (hi : ∀ x, Compatible (R.free ind x))
    (hp : ∀ x, Compatible (R.free prop x))
    (hc : ∀ u c, R.const u c = .const c) : Compatible (R.apply e) := by
  induction h generalizing R with
  | bound n => exact hb _ n
  | individual x => exact hi x
  | proposition x => exact hp x
  | const h => simpa [SymbolSubstitution.apply, hc] using Compatible.const h
  | app _ _ ihf iha => exact .app (ihf R hb hi hp hc) (iha R hb hi hp hc)
  | @lam t b e he ih =>
      apply Compatible.lam
      apply ih (R.lift b)
      · intro u n
        by_cases h : u = b
        · subst u; cases n with
          | zero => simpa [SymbolSubstitution.lift] using (Compatible.bound (s := b) 0)
          | succ n => simpa [SymbolSubstitution.lift] using (hb b n).rename (Ren.shift b)
        · simpa [SymbolSubstitution.lift, Sub.lift_other h] using (hb u n).rename (Ren.shift b)
      · intro x; exact (hi x).rename _
      · intro x; exact (hp x).rename _
      · intro u c; simp [SymbolSubstitution.lift, hc, Term.rename]

theorem Compatible.abstract {e : Term s} (h : Compatible e) (x : Identifier) :
    Compatible ((SymbolSubstitution.abstract ⟨x, ind⟩).apply e) := by
  apply h.replace
  · intro u n; exact .bound _
  · intro y
    by_cases hy : y = x
    · subst y
      simp only [SymbolSubstitution.abstract, Names.bind_self]
      exact .bound _
    · simp [SymbolSubstitution.abstract, Names.bind, Names.free, hy, Term.rename]
      exact .individual _
  · intro y
    simp [SymbolSubstitution.abstract, Names.bind, Names.free, Term.rename]
    exact .proposition _
  · intros; rfl

end Lisa.LambdaFol.FirstOrderShape
