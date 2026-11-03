import Lisa.SCLambdaToPure.BoundaryBinding

namespace Lisa.SCLambdaToPure.Embedding

open FirstOrder Lambda FirstOrderShape

theorem apps_reify (n : Nat) (f : Term (arity n s)) (ts : Fin n → Term ind) (ρ : Context) :
    (apps n f ts).reify ρ =
      (List.ofFn (fun i => (ts i).reify ρ)).foldl Expr.app (f.reify ρ) := by
  induction n with
  | zero => simp [apps]; rfl
  | succ n ih => simp [apps, ih, List.ofFn_succ, Term.reify]; rfl

private theorem arity_succ_right (n : Nat) (s : LSort) :
    arity (n + 1) s = arity n (ind >> s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [arity, ← ih]

private def rawHead (c : Readback.Symbol) (s : LSort) : Expr :=
  if c.schematic then .var ⟨c.id, s⟩ else .const ⟨c.id, s⟩

private def rawTerm (η : Nat → Identifier) (ρ : Context) (t : Readback.BTerm 0) : Expr :=
  (term (environment η 0) t).reify ρ

private theorem raw_func (η : Nat → Identifier) (ρ : Context)
    (c : Readback.Symbol) (ts : List (Readback.BTerm 0)) :
    rawTerm η ρ (.func c ts.get) =
      (ts.map (rawTerm η ρ)).foldl Expr.app (.const ⟨c.id, arity ts.length ind⟩) := by
  change (apps ts.length (.const c.id) (fun i => term (environment η 0) (ts.get i))).reify ρ = _
  rw [apps_reify]
  have hts : List.ofFn (fun i => rawTerm η ρ (ts.get i)) = ts.map (rawTerm η ρ) := by
    simpa only [List.map_ofFn] using congrArg (List.map (rawTerm η ρ)) (List.ofFn_get ts)
  exact congrArg (List.foldl Expr.app (.const ⟨c.id, arity ts.length ind⟩)) hts

private def Reconstructed (η : Nat → Identifier) (ρ : Context) : {s : LSort} → Term s → Prop
  | .ind, e => ∀ t, Readback.term (n := 0) (fun _ => none) e = some t → rawTerm η ρ t = e.reify ρ
  | _, _ => True

/-- Reading an individual term and reconstructing it recovers its named syntax.
The separate spine assertion accounts for partially applied function symbols. -/
private theorem individual_roundtrip {e : Term s} (he : Individual e)
    (η : Nat → Identifier) (ρ : Context)
    (hη : ∀ x, (⟨x, ind⟩ : SVar) ∈ e.freeVars → η (Readback.variableCode x) = x) :
    (∀ c ts, Readback.spine (n := 0) (fun _ => none) e = some (c, ts) →
      e.reify ρ = (ts.map (rawTerm η ρ)).foldl Expr.app (rawHead c (arity ts.length s)) ∧
        (c.schematic = true → s = ind)) ∧
    Reconstructed η ρ e := by
  induction he with
  | bound k => simp [Readback.spine, Readback.term, Reconstructed]
  | free x =>
      constructor
      · intro c ts hc
        simp only [Readback.spine, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩
        simp [rawHead, arity, Term.reify]
      · intro t ht
        simp only [Readback.term, Option.some.injEq] at ht
        subst t
        simpa [rawTerm, term, environment, Term.reify] using hη x (by simp)
  | symbol n c =>
      constructor
      · intro d ts hd
        simp only [Readback.spine, Option.some.injEq, Prod.mk.injEq] at hd
        rcases hd with ⟨rfl, rfl⟩
        simp [rawHead, arity, Term.reify]
      · cases n with
        | zero =>
            change ∀ t, Readback.term (n := 0) (fun _ => none) (.const (s := ind) c) = some t → _
            intro t ht
            simp only [Readback.term, Option.some.injEq] at ht
            subst t
            simp [rawTerm, term, apps, Term.reify]
        | succ n => trivial
  | @app s f a hf ha ihf iha =>
      have ihf := ihf (fun x hx => hη x (Finset.mem_union_left _ hx))
      have iha := iha (fun x hx => hη x (Finset.mem_union_right _ hx))
      constructor
      · intro c ts hc
        cases hr : Readback.spine (n := 0) (fun _ => none) f with
        | none => simp [Readback.spine, hr] at hc
        | some r =>
            obtain ⟨d, us⟩ := r
            cases ht : Readback.term (n := 0) (fun _ => none) a with
            | none => simp [Readback.spine, hr, ht] at hc
            | some t =>
                simp only [Readback.spine, hr, ht] at hc
                rcases hc with ⟨rfl, rfl⟩
                obtain ⟨hfr, hfc⟩ := ihf.1 _ _ hr
                constructor
                · simp [Term.reify, hfr, ← iha.2 _ ht, List.map_append,
                    List.foldl_append, arity_succ_right]
                · intro h; exact False.elim (LSort.noConfusion (hfc h))
      · cases s with
        | prop => trivial
        | arrow s t => trivial
        | ind =>
          intro t ht
          change Readback.term (n := 0) (fun _ => none) (.app f a) = some t at ht
          have iha := iha.2
          cases hr : Readback.spine (n := 0) (fun _ => none) f with
          | none => simp [Readback.term, hr] at ht
          | some r =>
              obtain ⟨c, us⟩ := r
              cases ha' : Readback.term (n := 0) (fun _ => none) a with
              | none => simp [Readback.term, hr, ha'] at ht
              | some u =>
                  simp only [Readback.term, hr, ha'] at ht
                  change some (Language.Term.func c (us ++ [u]).get) = some t at ht
                  have ht := Option.some.inj ht
                  subst t
                  obtain ⟨hfr, hfc⟩ := ihf.1 _ _ hr
                  have hc : c.schematic = false := by
                    cases hh : c.schematic
                    · rfl
                    · exact False.elim (LSort.noConfusion (hfc hh))
                  rw [raw_func]
                  simp [Term.reify, hfr, ← iha _ ha', List.map_append,
                    List.foldl_append, arity_succ_right, rawHead, hc]

theorem term_roundtrip {e : Term ind} (he : Individual e)
    (η : Nat → Identifier) (ρ : Context)
    (hη : ∀ x, (⟨x, ind⟩ : SVar) ∈ e.freeVars → η (Readback.variableCode x) = x)
    (ht : Readback.term (n := 0) (fun _ => none) e = some t) :
    (term (environment η 0) t).reify ρ = e.reify ρ :=
  (individual_roundtrip he η ρ hη).2 t ht

private theorem formula_spine_roundtrip {e : Term s} (he : Formula e)
    (η : Nat → Identifier) (ρ : Context)
    (hη : ∀ x, (⟨x, ind⟩ : SVar) ∈ e.freeVars → η (Readback.variableCode x) = x)
    (hr : Readback.spine (n := 0) (fun _ => none) e = some (c, ts)) :
    e.reify ρ = (ts.map (rawTerm η ρ)).foldl Expr.app (rawHead c (arity ts.length s)) := by
  induction he generalizing c ts with
  | free x =>
      simp only [Readback.spine, Option.some.injEq, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      simp [rawHead, arity, Term.reify]
  | symbol n c =>
      simp only [Readback.spine, Option.some.injEq, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      simp [rawHead, arity, Term.reify]
  | @app s f a hf ha ih =>
      cases hfr : Readback.spine (n := 0) (fun _ => none) f with
      | none => simp [Readback.spine, hfr] at hr
      | some r =>
          obtain ⟨d, us⟩ := r
          cases har : Readback.term (n := 0) (fun _ => none) a with
          | none => simp [Readback.spine, hfr, har] at hr
          | some t =>
              simp only [Readback.spine, hfr, har] at hr
              rcases hr with ⟨rfl, rfl⟩
              have hfa := ih (fun x hx => hη x (Finset.mem_union_left _ hx)) hfr
              have haa := term_roundtrip ha η ρ (fun x hx => hη x (Finset.mem_union_right _ hx)) har
              simp [Term.reify, hfa, ← haa, List.map_append, List.foldl_append, arity_succ_right,
                rawTerm]
  | top | bot =>
      simp only [Readback.spine, Option.some.injEq, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      simp [rawHead, arity, Term.reify]
  | neg | and | or | imp | iff | all | ex => simp [Readback.spine] at hr
  | @eq t u ht hu =>
      cases htr : Readback.term (n := 0) (fun _ => none) t with
      | none => simp [Readback.spine, htr] at hr
      | some t' =>
          cases hur : Readback.term (n := 0) (fun _ => none) u with
          | none => simp [Readback.spine, htr, hur] at hr
          | some u' =>
              simp [Readback.spine, htr, hur] at hr
              rcases hr with ⟨rfl, rfl⟩
              have htt := term_roundtrip ht η ρ (fun x hx => hη x (by simp [hx])) htr
              have huu := term_roundtrip hu η ρ (fun x hx => hη x (by simp [hx])) hur
              simp [rawHead, arity, Term.reify, rawTerm, ← htt, ← huu]

private theorem raw_rel (η : Nat → Identifier) (ρ : Context)
    (c : Readback.Symbol) (ts : List (Readback.BTerm 0)) :
    (formula η (.rel c ts.get)).reify ρ =
      (ts.map (rawTerm η ρ)).foldl Expr.app (rawHead c (arity ts.length prop)) := by
  simp only [formula, apps_reify]
  have hts : List.ofFn (fun i => rawTerm η ρ (ts.get i)) = ts.map (rawTerm η ρ) := by
    simpa only [List.map_ofFn] using congrArg (List.map (rawTerm η ρ)) (List.ofFn_get ts)
  change (List.ofFn (fun i => rawTerm η ρ (ts.get i))).foldl Expr.app _ = _
  rw [hts]
  simp only [head, rawHead]
  split <;> rfl

noncomputable def related_free (η : Nat → Identifier) (x : Identifier) :
    Related η (ofTyped (.free (s := prop) x)) (.rel ⟨true, x⟩ Fin.elim0) :=
  Related.of_eq rfl

noncomputable def related_const (η : Nat → Identifier) (c : Identifier)
    (hr : Readback.formula (n := 0) (fun _ => none) (.const c) = some p) :
    Related η (ofTyped (.const (s := prop) c)) p := by
  by_cases ht : c = ⟨"top", 0⟩
  · subst c
    simp only [Readback.formula, Option.some.injEq] at hr
    subst p
    exact Related.top
  by_cases hb : c = ⟨"bot", 0⟩
  · subst c
    simp only [Readback.formula, Option.some.injEq] at hr
    subst p
    exact Related.bot
  simp only [Readback.formula, Option.some.injEq] at hr
  have hr : (.rel ⟨false, c⟩ Fin.elim0 : Readback.BFormula 0) = p := by simpa [Readback.formula] using hr
  subst p
  exact Related.of_eq rfl

noncomputable def related_app {f : Term (ind >> prop)} {a : Term ind}
    (he : Formula (.app f a)) (η : Nat → Identifier)
    (hη : ∀ x, (⟨x, ind⟩ : SVar) ∈ (Term.app f a).freeVars → η (Readback.variableCode x) = x)
    (hr : Readback.formula (n := 0) (fun _ => none) (.app f a) = some p) :
    Related η (ofTyped (.app f a)) p := by
  apply Related.of_eq
  apply Subtype.ext
  change AlphaBetaEta.term ((Term.app f a).reify Context.empty) =
    AlphaBetaEta.term ((formula η p).reify Context.empty)
  apply congrArg AlphaBetaEta.term
  by_cases h : ∃ t : Term ind, f = .app (.const ⟨"eq", 0⟩) t
  · obtain ⟨t, rfl⟩ := h
    cases htr : Readback.term (n := 0) (fun _ => none) t with
    | none => simp [Readback.formula, htr] at hr
    | some t' =>
        cases har : Readback.term (n := 0) (fun _ => none) a with
        | none => simp [Readback.formula, htr, har] at hr
        | some a' =>
            simp only [Readback.formula, htr, har] at hr
            change some (.equal t' a') = some p at hr
            have hr := Option.some.inj hr
            subst p
            have hs := formula_spine_roundtrip he η Context.empty hη
              (show Readback.spine (fun _ => none) (.app (.app (.const ⟨"eq", 0⟩) t) a) =
                some (⟨false, ⟨"eq", 0⟩⟩, [t', a']) by simp [Readback.spine, htr, har])
            simpa [formula, rawHead, rawTerm, arity, Term.reify] using hs
  · simp only [not_exists] at h
    cases hfr : Readback.spine (n := 0) (fun _ => none) f with
    | none => simp [Readback.formula, hfr] at hr
    | some r =>
        obtain ⟨c, ts⟩ := r
        cases har : Readback.term (n := 0) (fun _ => none) a with
        | none => simp [Readback.formula, hfr, har] at hr
        | some a' =>
            simp [Readback.formula, hfr, har] at hr
            subst p
            rw [raw_rel]
            exact formula_spine_roundtrip he η Context.empty hη
              (by simp [Readback.spine, hfr, har])

end Lisa.SCLambdaToPure.Embedding


