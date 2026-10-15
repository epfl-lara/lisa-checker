import Lisa.Lambda.NamedAlpha
import Lisa.Lambda.NamedSubstitution

namespace Lisa.Lambda

/-- Relate failed interpretations or successful terms of the same sort by beta-eta conversion. -/
inductive ResultEquiv : Option (Packed.Expr Γ) → Option (Packed.Expr Γ) → Prop
  | none : ResultEquiv none none
  | some {e f : Term Γ s} : Equiv e f → ResultEquiv (some ⟨s, e⟩) (some ⟨s, f⟩)

namespace ResultEquiv

@[refl] theorem refl (r : Option (Packed.Expr Γ)) : ResultEquiv r r := by
  rcases r with _ | ⟨s, e⟩
  · exact .none
  · exact .some (.refl e)

theorem symm {p q : Option (Packed.Expr Γ)} (h : ResultEquiv p q) : ResultEquiv q p := by
  cases h with
  | none => exact .none
  | some h => exact .some (.symm h)

theorem trans {p q r : Option (Packed.Expr Γ)} (h : ResultEquiv p q)
    (k : ResultEquiv q r) : ResultEquiv p r := by
  cases h with
  | none => cases k; exact .none
  | some h => cases k with | some k => exact .some (.trans h k)

theorem app {f g a b : Option (Packed.Expr Γ)}
    (hf : ResultEquiv f g) (ha : ResultEquiv a b) :
    ResultEquiv (f.bind fun f => a.bind (Packed.app f))
      (g.bind fun g => b.bind (Packed.app g)) := by
  cases hf with
  | none => exact .none
  | @some s f g hf =>
      cases ha with
      | none => exact .none
      | @some u a b ha =>
          cases s with
          | arrow s t =>
              by_cases h : u = s
              · subst u
                simpa [Packed.app] using ResultEquiv.some (Equiv.app hf ha)
              · simpa [Packed.app, h] using (ResultEquiv.none (Γ := Γ))
          | _ => exact .none

theorem lam {p q : Option (Packed.Expr (s :: Γ))} (h : ResultEquiv p q) :
    ResultEquiv (p.map (Packed.lam s)) (q.map (Packed.lam s)) := by
  cases h with
  | none => exact .none
  | some h => exact .some (.lam h)

end ResultEquiv

/-- Interpret every existing named conversion rule in the intrinsic beta-eta calculus. -/
theorem interpretNamed_conversion {p q : Expr} (h : Lisa.Conversion p q) (η : Names Γ) :
    ResultEquiv (interpretNamed p η) (interpretNamed q η) := by
  induction h generalizing Γ with
  | alpha h => rw [interpretNamed_alpha h]
  | symm _ ih => exact (ih η).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ η).trans (ih₂ η)
  | app _ _ ihf iha => exact .app (ihf η) (iha η)
  | lam x _ ih => exact .lam (ih (η.bind x))
  | beta x body arg ha =>
      obtain ⟨a, ha'⟩ := interpretNamed_sorted ha η
      rw [interpretNamed_substOne x body arg η a ha']
      cases hb : interpretNamed body (η.bind x) with
      | none => simp [interpretNamed, hb]; exact .none
      | some w =>
          rcases w with ⟨t, b⟩
          simpa [interpretNamed, hb, ha', Packed.lam, Packed.app, Packed.subst,
            Term.instantiate] using ResultEquiv.some (Equiv.beta b a)
  | eta x f s hf hx =>
      obtain ⟨f', hf'⟩ := interpretNamed_sorted hf η
      simpa [interpretNamed, interpretNamed_bind_fresh f η x hx, hf', Packed.rename,
        Packed.app, Packed.lam] using ResultEquiv.some (Equiv.eta f')

/-- Preserve the original named conversion after name erasure and typed elaboration. -/
theorem elaborate_conversion {p q : Expr} (h : Lisa.Conversion p q) :
    ResultEquiv (elaborate [] (p.toNameless [])) (elaborate [] (q.toNameless [])) := by
  simpa only [interpretNamed_free] using interpretNamed_conversion h (Names.free : Names [])

/-- Compare every well-sorted named conversion successfully with the total normalizer. -/
theorem compareNameless_of_conversion {p q : Expr} (h : Lisa.Conversion p q)
    (hp : p.hasSort s) : compareNameless [] (p.toNameless []) (q.toNameless []) = some true := by
  obtain ⟨a, ha⟩ := elaborate_named hp []
  have hq : q.hasSort s := h.preserves_sort.symm.trans hp
  obtain ⟨b, hb⟩ := elaborate_named hq []
  simp only [List.map_nil] at ha hb
  have he := elaborate_conversion h
  rw [ha, hb] at he
  cases he with
  | some he =>
      apply (compareNameless_true _ _ _).mpr
      exact ⟨s, a, b, ha, hb, he⟩

/-- Refute named conversion when comparison of a sorted source returns false. -/
theorem not_conversion_of_compareNameless_false {p q : Expr} (hp : p.hasSort s)
    (h : compareNameless [] (p.toNameless []) (q.toNameless []) = some false) :
    ¬ Lisa.Conversion p q := by
  intro hc
  have ht := compareNameless_of_conversion hc hp
  rw [h] at ht
  contradiction

end Lisa.Lambda
