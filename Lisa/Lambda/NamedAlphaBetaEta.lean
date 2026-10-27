import Lisa.Lambda.NamedAlpha
import Lisa.Lambda.NamedSubstitution

namespace Lisa.Lambda

/-- Relate failed interpretations or successful terms of the same sort by beta-eta conversion. -/

inductive ResultEquiv : Option (Packed.Expr) → Option (Packed.Expr) → Prop
  | none : ResultEquiv none none
  | some {e f : Term s} : Equiv e f → ResultEquiv (some ⟨s, e⟩) (some ⟨s, f⟩)

namespace ResultEquiv

@[refl] theorem refl (r : Option (Packed.Expr)) : ResultEquiv r r := by
  rcases r with _ | ⟨s, e⟩
  · exact .none
  · exact .some (.refl e)

theorem symm {p q : Option (Packed.Expr)} (h : ResultEquiv p q) : ResultEquiv q p := by
  cases h with
  | none => exact .none
  | some h => exact .some (.symm h)

theorem trans {p q r : Option (Packed.Expr)} (h : ResultEquiv p q)
    (k : ResultEquiv q r) : ResultEquiv p r := by
  cases h with
  | none => cases k; exact .none
  | some h => cases k with | some k => exact .some (.trans h k)

theorem app {f g a b : Option (Packed.Expr)}
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
              · simpa [Packed.app, h] using (ResultEquiv.none )
          | _ => exact .none

theorem lam {p q : Option (Packed.Expr)} (h : ResultEquiv p q) :
    ResultEquiv (p.map (Packed.lam s)) (q.map (Packed.lam s)) := by
  cases h with
  | none => exact .none
  | some h => exact .some (.lam h)

end ResultEquiv

/-- Interpret every existing named conversion rule in the intrinsic beta-eta calculus. -/

theorem interpretNamed_alphaBetaEta {p q : Expr} (h : Lisa.AlphaBetaEta p q) (η : Names) :
    ResultEquiv (interpretNamed p η) (interpretNamed q η) := by
  induction h generalizing η with
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

end Lisa.Lambda
