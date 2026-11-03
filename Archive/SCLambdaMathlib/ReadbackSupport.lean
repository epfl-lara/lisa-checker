import Lisa.SCLambdaToPure.ReadbackTotal

/-! Reading bound indices never turns them into free individual variables. -/

namespace Lisa.SCLambdaToPure.Readback

open FirstOrder Lambda

def names (xs : Finset SVar) : Finset Nat :=
  (xs.filter (fun x => x.sort = ind)).image (fun x => variableCode x.id)

@[simp] theorem names_empty : names ∅ = ∅ := by simp [names]

@[simp] theorem names_union (xs ys : Finset SVar) :
    names (xs ∪ ys) = names xs ∪ names ys := by simp [names, Finset.filter_union, Finset.image_union]

theorem names_mono {xs ys : Finset SVar} (h : xs ⊆ ys) : names xs ⊆ names ys :=
  Finset.image_subset_image (Finset.filter_subset_filter _ h)

theorem mem_names_iff (x : Identifier) (xs : Finset SVar) :
    variableCode x ∈ names xs ↔ SVar.mk x ind ∈ xs := by
  simp only [names, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨y, s⟩, ⟨hy, hs⟩, he⟩
    obtain rfl := variableCode_injective he
    cases hs
    exact hy
  · intro h; exact ⟨⟨x, ind⟩, ⟨h, rfl⟩, rfl⟩

private theorem func_support {c : Symbol} {ts : List (BTerm n)}
    (h : ∀ t ∈ ts, t.varFinsetLeft ⊆ xs) :
    (Language.Term.func c ts.get).varFinsetLeft ⊆ xs := by
  simp only [Language.Term.varFinsetLeft, Finset.biUnion_subset_iff_forall_subset]
  exact fun i _ => h _ (List.get_mem _ _)

private theorem rel_support {c : Symbol} {ts : List (BTerm n)}
    (h : ∀ t ∈ ts, t.varFinsetLeft ⊆ xs) :
    (Language.BoundedFormula.rel c ts.get).freeVarFinset ⊆ xs := by
  simp only [Language.BoundedFormula.freeVarFinset, Finset.biUnion_subset_iff_forall_subset]
  exact fun i _ => h _ (List.get_mem _ _)

private theorem reads_support (e : Term s) (ρ : Bound n) :
    (∀ c args, spine ρ e = some (c, args) →
      ∀ t ∈ args, t.varFinsetLeft ⊆ names e.freeVars) ∧
    (∀ h : s = ind, ∀ t, term ρ (h ▸ e) = some t → t.varFinsetLeft ⊆ names e.freeVars) := by
  induction e with
  | bound k =>
      constructor
      · simp [spine]
      · intro h t ht; subst_vars
        cases hk : ρ k <;> simp [term, hk] at ht
        subst t; simp
  | free x =>
      constructor
      · intro c args h; simp [spine] at h; simp [h.2]
      · intro h t ht; subst_vars
        simp only [term, Option.some.injEq] at ht
        subst t; simp [names]
  | const x =>
      constructor
      · intro c args h; simp [spine] at h; simp [h.2]
      · intro h t ht; subst_vars
        simp only [term, Option.some.injEq] at ht
        subst t; simp
  | lam => exact ⟨by simp [spine], by simp⟩
  | @app s t f a ihf iha =>
      cases s with
      | prop =>
          constructor
          · simp [spine]
          · intro h; subst t; simp [term]
      | arrow =>
          constructor
          · simp [spine]
          · intro h; subst t; simp [term]
      | ind =>
          cases hf : spine ρ f with
          | none =>
              constructor
              · simp [spine, hf]
              · intro h; subst t; simp [term, hf]
          | some v =>
              obtain ⟨c, args⟩ := v
              cases ha : term ρ a with
              | none =>
                  constructor
                  · simp [spine, hf, ha]
                  · intro h; subst t; simp [term, hf, ha]
              | some a' =>
                  have hargs : ∀ b ∈ args ++ [a'],
                      b.varFinsetLeft ⊆ names (f.app a).freeVars := by
                    intro b hb
                    rcases List.mem_append.mp hb with hb | hb
                    · exact (ihf.1 c args hf b hb).trans (by simp)
                    · obtain rfl := List.mem_singleton.mp hb
                      exact (iha.2 rfl _ ha).trans (by simp)
                  constructor
                  · intro c' args' h
                    simp [spine, hf, ha] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact hargs
                  · intro h u hu; subst t
                    simp [term, hf, ha] at hu
                    subst u
                    exact func_support hargs

theorem term_support (e : Term ind) (ρ : Bound n) {t : BTerm n} (ht : term ρ e = some t) :
    t.varFinsetLeft ⊆ names e.freeVars := (reads_support e ρ).2 rfl t ht

theorem spine_support (e : Term s) (ρ : Bound n) {c : Symbol} {args : List (BTerm n)}
    (ht : spine ρ e = some (c, args)) :
    ∀ t ∈ args, t.varFinsetLeft ⊆ names e.freeVars := (reads_support e ρ).1 c args ht

theorem formula_support (e : Term prop) (ρ : Bound n) {p : BFormula n}
    (hp : formula ρ e = some p) : p.freeVarFinset ⊆ names e.freeVars := by
  induction n, ρ, e using formula.induct with
  | case1 n ρ | case2 n ρ =>
      simp [formula] at hp
      subst p
      simp
  | case3 n ρ a ih =>
      cases ha : formula ρ a <;> simp [formula, ha] at hp
      subst p
      simpa [Language.BoundedFormula.not] using ih ha
  | case4 n ρ a b iha ihb | case5 n ρ a b iha ihb | case6 n ρ a b iha ihb | case7 n ρ a b iha ihb =>
      cases ha : formula ρ a <;> simp [formula, ha] at hp
      cases hb : formula ρ b <;> simp [hb] at hp
      subst p
      simpa [Language.BoundedFormula.iff, Language.BoundedFormula.not,
        Min.min, Max.max, Finset.union_assoc, Finset.union_comm,
        Finset.union_left_comm] using Finset.union_subset_union (iha ha) (ihb hb)
  | case8 n ρ t u =>
      cases ht : term ρ t <;> simp [formula, ht] at hp
      cases hu : term ρ u <;> simp [hu] at hp
      subst p
      simpa using Finset.union_subset_union (term_support t ρ ht) (term_support u ρ hu)
  | case9 n ρ a ih | case10 n ρ a ih =>
      cases ha : formula (bind ρ) a <;> simp [formula, ha] at hp
      subst p
      simpa [Language.BoundedFormula.ex, Language.BoundedFormula.not] using ih ha
  | case11 n ρ x | case12 n ρ x _ _ =>
      simp [formula] at hp
      subst p
      simp
  | case13 n ρ f a h =>
      cases hf : spine ρ f with
      | none => simp [formula, hf] at hp
      | some v =>
          obtain ⟨c, args⟩ := v
          cases ha : term ρ a <;> simp [formula, hf, ha] at hp
          subst p
          apply rel_support
          intro b hb
          rcases List.mem_append.mp hb with hb | hb
          · exact (spine_support f ρ hf b hb).trans (by simp)
          · obtain rfl := List.mem_singleton.mp hb
            exact (term_support a ρ ha).trans (by simp)
  | case14 => simp_all [formula]

end Lisa.SCLambdaToPure.Readback
