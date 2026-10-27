import Lisa.SCLambdaToPure.Readback
import Lisa.SCLambdaToPure.Support

/-! Readback succeeds on well-scoped first-order shapes. -/

namespace Lisa.SCLambdaToPure.Readback

open Lambda FirstOrderShape

private def ReadsIndividual (ρ : Bound n) : {s : LSort} → Term s → Prop
  | .ind, e => (term ρ e).isSome
  | _, e => (spine ρ e).isSome

private theorem individual_reads {e : Term s} (h : Individual e)
    (hs : Supported d xs e) (ρ : Bound n) (hρ : ∀ k < d ind, (ρ k).isSome) :
    ReadsIndividual ρ e := by
  induction h generalizing n d with
  | bound k => simpa [ReadsIndividual, term] using hρ k hs
  | free x => simp [ReadsIndividual, term]
  | symbol k c => cases k <;> simp [ReadsIndividual, term, spine, arity]
  | @app s f a hf ha ihf iha =>
      obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp (ihf hs.1 ρ hρ)
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (iha hs.2 ρ hρ)
      cases s <;> simp [ReadsIndividual, term, spine, hc, ha']

theorem term_isSome {e : Term ind} (h : Individual e) (hs : Supported d xs e)
    (ρ : Bound n) (hρ : ∀ k < d ind, (ρ k).isSome) : (term ρ e).isSome :=
  individual_reads h hs ρ hρ

private theorem formula_const_isSome (ρ : Bound n) (c : Identifier) :
    (formula ρ (.const c)).isSome := by
  by_cases ht : c = ⟨"top", 0⟩
  · subst c; simp [formula]
  by_cases hb : c = ⟨"bot", 0⟩
  · subst c; simp [formula]
  simp [formula]

private theorem formula_app_isSome (ρ : Bound n) (f : Term (ind >> prop)) (a : Term ind)
    (hf : (spine ρ f).isSome) (ha : (term ρ a).isSome) :
    (formula ρ (.app f a)).isSome := by
  by_cases he : ∃ t : Term ind, f = .app (.const ⟨"eq", 0⟩) t
  · obtain ⟨t, rfl⟩ := he
    simp only [spine] at hf
    cases ht : term ρ t <;> simp [ht] at hf
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha
    simp [formula, ht, ha']
  · obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp hf
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha
    simp only [not_exists] at he
    simp [formula, hc, ha']

private def ReadsFormula (ρ : Bound n) : {s : LSort} → Term s → Prop
  | .prop, e => (formula ρ e).isSome
  | _, e => (spine ρ e).isSome

private theorem formula_reads {e : Term s} (h : Formula e)
    (hs : Supported d xs e) (ρ : Bound n) (hρ : ∀ k < d ind, (ρ k).isSome) :
    ReadsFormula ρ e := by
  induction h generalizing n d with
  | free x => simp [ReadsFormula, formula]
  | symbol k c => cases k with
    | zero => exact formula_const_isSome ρ c
    | succ k => simp [ReadsFormula, spine, arity]
  | @app s f a hf ha ih =>
      have hf' := ih hs.1 ρ hρ
      have ha' := term_isSome ha hs.2 ρ hρ
      cases s with
      | prop => exact formula_app_isSome ρ f a hf' ha'
      | ind =>
          obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp hf'
          obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha'
          simp [ReadsFormula, spine, hc, ha']
      | arrow s t =>
          obtain ⟨⟨c, args⟩, hc⟩ := Option.isSome_iff_exists.mp hf'
          obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha'
          simp [ReadsFormula, spine, hc, ha']
  | top => simp [ReadsFormula, formula]
  | bot => simp [ReadsFormula, formula]
  | neg _ ih =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (ih hs.2 ρ hρ)
      simp [ReadsFormula, formula, hp']
  | and _ _ ihp ihq | or _ _ ihp ihq | imp _ _ ihp ihq | iff _ _ ihp ihq =>
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (ihp hs.1.2 ρ hρ)
      obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp (ihq hs.2 ρ hρ)
      simp [ReadsFormula, formula, hp', hq']
  | eq ht hu =>
      obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (term_isSome ht hs.1.2 ρ hρ)
      obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp (term_isSome hu hs.2 ρ hρ)
      simp [ReadsFormula, formula, ht', hu']
  | all _ ih | ex _ ih =>
      have hρ' : ∀ k < (d.inc ind) ind, ((bind ρ) k).isSome := by
        intro k hk
        cases k with
        | zero => rfl
        | succ k => simpa [bind] using hρ k (by simpa using hk)
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp (ih hs.2 (bind ρ) hρ')
      simp [ReadsFormula, formula, hp']

theorem formula_isSome {e : Term prop} (h : Formula e) (hs : Supported d xs e)
    (ρ : Bound n) (hρ : ∀ k < d ind, (ρ k).isSome) : (formula ρ e).isSome :=
  formula_reads h hs ρ hρ

/-- Grounding followed by normalization always yields a readable complete formula. -/
theorem ground_formula_isSome {e : Term prop} (hc : ∀ σ, e.subst σ = e) :
    (formula (n := 0) (fun _ => none) (normalize (Grounding.ground e))).isSome :=
  formula_isSome (Grounding.normalize_ground_formula hc)
    (normalize_supported _ (Grounding.symbols.closed hc)) _ (by simp [Depth.zero])

theorem ground_term_isSome {e : Term ind} (hc : ∀ σ, e.subst σ = e) :
    (term (n := 0) (fun _ => none) (normalize (Grounding.ground e))).isSome :=
  term_isSome (Grounding.normalize_ground_individual hc)
    (normalize_supported _ (Grounding.symbols.closed hc)) _ (by simp [Depth.zero])

end Lisa.SCLambdaToPure.Readback
