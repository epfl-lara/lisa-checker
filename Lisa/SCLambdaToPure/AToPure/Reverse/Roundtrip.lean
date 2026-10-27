import Lisa.SCLambdaToPure.AToPure.Readback
import Lisa.SCLambdaToPure.AToPure.Reverse.Embedding
import Lisa.Lambda.Elaboration

/-! Readback followed by embedding preserves canonical syntax exactly.
Working with erased sorted terms avoids casts when collecting application spines;
injectivity of erasure recovers equality of the typed terms. -/
namespace Lisa.SCLambdaToPure.Readback
open Lambda
open FirstOrderShape (Individual Formula)
open PureEmbedding (Variables)
open Embedding (apps head)
open Signature (arity)

private def rawHead (c : Symbol) (s : LSort) : RawTerm :=
  if c.schematic then .free ⟨c.id, s⟩ else .const ⟨c.id, s⟩

private def embedded (v : Variables Identifier n) (t : BTerm n) : RawTerm :=
  (PureEmbedding.term v t).erase

private theorem apps_erase (n : Nat) (f : Term (arity n s)) (ts : Fin n → Term ind) :
    (apps n f ts).erase = (List.ofFn (fun i => (ts i).erase)).foldl RawTerm.app f.erase := by
  induction n with
  | zero => simp [apps]; rfl
  | succ n ih => simp [apps, ih, List.ofFn_succ, Term.erase]; rfl

private theorem head_erase (c : Symbol) (s : LSort) :
    (head c s).erase = rawHead c s := by simp only [head, rawHead]; split <;> rfl

private theorem embedded_func (v : Variables Identifier n) (c : Symbol) (ts : List (BTerm n)) :
    embedded v (.func c ts.get) =
      (ts.map (embedded v)).foldl RawTerm.app (.const ⟨c.id, arity ts.length ind⟩) := by
  simp only [embedded, PureEmbedding.term, apps_erase, Term.erase]
  rw [show List.ofFn (fun i => (PureEmbedding.term v (ts.get i)).erase) =
      ts.map (embedded v) by
    simpa only [List.map_ofFn] using congrArg (List.map (embedded v)) (List.ofFn_get ts)]

private theorem embedded_rel (v : Variables Identifier n) (c : Symbol) (ts : List (BTerm n)) :
    (PureEmbedding.formula v (.rel c ts.get)).erase =
      (ts.map (embedded v)).foldl RawTerm.app (rawHead c (arity ts.length prop)) := by
  simp only [PureEmbedding.formula, apps_erase, head_erase]
  rw [show List.ofFn (fun i => (PureEmbedding.term v (ts.get i)).erase) =
      ts.map (embedded v) by
    simpa only [List.map_ofFn] using congrArg (List.map (embedded v)) (List.ofFn_get ts)]

private theorem arity_succ_right (n : Nat) (s : LSort) :
    arity (n + 1) s = arity n (ind >> s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [arity, ← ih]

private def SpineReconstructed (v : Variables Identifier n) (ρ : Bound n) (e : Term s) : Prop :=
  ∀ c ts, spine ρ e = some (c, ts) →
    e.erase = (ts.map (embedded v)).foldl RawTerm.app (rawHead c (arity ts.length s))

private def IndividualReconstructed (v : Variables Identifier n) (ρ : Bound n) : {s : LSort} → Term s → Prop
  | .ind, e => ∀ t, term ρ e = some t → embedded v t = e.erase
  | _, _ => True

private def FormulaReconstructed (v : Variables Identifier n) (ρ : Bound n) : {s : LSort} → Term s → Prop
  | .prop, e => ∀ p, formula ρ e = some p → (PureEmbedding.formula v p).erase = e.erase
  | _, _ => True

private theorem spine_app {f : Term (ind >> s)} {a : Term ind}
    (hf : SpineReconstructed v ρ f) (ha : IndividualReconstructed v ρ a) :
    SpineReconstructed v ρ (.app f a) := by
  intro c ts hr
  rcases hfr : spine ρ f with _ | ⟨d, us⟩ <;>
    simp [spine, hfr] at hr
  rcases har : term ρ a with _ | t <;>
    simp [har] at hr
  obtain ⟨rfl, rfl⟩ := hr
  simp [Term.erase, hf _ _ hfr, ← ha _ har, List.map_append,
    List.foldl_append, arity_succ_right]

private theorem formula_app_roundtrip (v : Variables Identifier n) (ρ : Bound n)
    (f : Term (ind >> prop)) (a : Term ind) (he : SpineReconstructed v ρ (.app f a)) :
    FormulaReconstructed v ρ (.app f a) := by
  intro p hr
  by_cases h : ∃ t : Term ind, f = .app (.const ⟨"eq", 0⟩) t
  · obtain ⟨t, rfl⟩ := h
    rcases htr : term ρ t with _ | t' <;>
      simp [formula, htr] at hr
    rcases har : term ρ a with _ | a' <;>
      simp [har] at hr
    subst p
    have hs := he ⟨false, ⟨"eq", 0⟩⟩ [t', a'] (by simp [spine, htr, har])
    simpa [PureEmbedding.formula, rawHead, embedded, arity, Term.erase] using hs.symm
  · simp only [not_exists] at h
    rcases hfr : spine ρ f with _ | ⟨c, ts⟩ <;>
      simp [formula, hfr] at hr
    rcases har : term ρ a with _ | a' <;>
      simp [har] at hr
    subst p
    rw [embedded_rel]
    exact (he _ _ (by simp [spine, hfr, har])).symm

private theorem bound_lift (v : Variables Identifier n) (ρ : Bound n)
    (hb : ∀ k i, ρ k = some i → v (.inr i) = .bound k) :
    ∀ k i, Readback.bind ρ k = some i → PureEmbedding.lift v (.inr i) = .bound k := by
  intro k i hi
  cases k with
  | zero =>
      simp only [Readback.bind, Option.some.injEq] at hi
      subst i
      simp
  | succ k =>
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hi
      simp [hb _ _ hj, Term.shift, Term.rename, Ren.shift]

private theorem free_lift {e : Term s} (v : Variables Identifier n)
    (hf : ∀ x, (⟨x, ind⟩ : SVar) ∈ e.freeVars → v (.inl x) = .free x) :
    ∀ x, (⟨x, ind⟩ : SVar) ∈ e.freeVars →
      PureEmbedding.lift v (.inl x) = .free x := by
  intro x hx
  simp [hf x hx, Term.shift, Term.rename]

/-- At this boundary, free individuals are variables, never function symbols. -/

private theorem individual_spine_kind {s n : _} {e : Term s} (h : Individual e)
    (ρ : Bound n) {c : Symbol} {ts : List (BTerm n)}
    (hr : spine ρ e = some (c, ts)) (hc : c.schematic = true) : s = ind := by
  match h with
  | .bound _ => simp [spine] at hr
  | .free _ => rfl
  | .symbol _ _ =>
      simp only [spine, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      contradiction
  | @Individual.app s f a hf _ =>
      rcases hfr : spine ρ f with _ | ⟨d, us⟩ <;>
        simp [spine, hfr] at hr
      rcases har : term ρ a with _ | t <;>
        simp [har] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact False.elim (LSort.noConfusion (individual_spine_kind hf ρ hfr hc))
  | .epsilon _ => simp [spine] at hr
termination_by structural h

mutual

private theorem individual_roundtrip {s n : _} {e : Term s} (h : Individual e)
    (v : Variables Identifier n) (ρ : Bound n)
    (hb : ∀ k i, ρ k = some i → v (.inr i) = .bound k)
    (hf : ∀ x, (⟨x, ind⟩ : SVar) ∈ e.freeVars → v (.inl x) = .free x) :
    SpineReconstructed v ρ e ∧ IndividualReconstructed v ρ e := by
  match h with
  | .bound k =>
      refine ⟨by simp [SpineReconstructed, spine], ?_⟩
      intro t ht
      simp only [term] at ht
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp ht
      simp [embedded, PureEmbedding.term, hb _ _ hi, Term.erase]
  | .free x =>
      constructor
      · intro c ts hr
        simp only [spine] at hr
        obtain ⟨rfl, rfl⟩ := Option.some.inj hr
        simp [Term.erase, rawHead, arity]
      · intro t ht
        simp only [term] at ht
        have ht := Option.some.inj ht
        subst t
        simp [embedded, PureEmbedding.term, hf x (by simp), Term.erase]
  | .symbol k c =>
      constructor
      · intro d ts hr
        simp only [spine] at hr
        obtain ⟨rfl, rfl⟩ := Option.some.inj hr
        simp [Term.erase, rawHead, arity]
      · cases k with
        | zero =>
            intro t ht
            change term ρ (.const (s := ind) c) = some t at ht
            simp only [term] at ht
            have ht := Option.some.inj ht
            subst t
            rfl
        | succ k => trivial
  | @Individual.app s f a hfn ha =>
      have rf := individual_roundtrip hfn v ρ hb (fun x hx => hf x (Finset.mem_union_left _ hx))
      have ra := individual_roundtrip ha v ρ hb (fun x hx => hf x (Finset.mem_union_right _ hx))
      refine ⟨spine_app rf.1 ra.2, ?_⟩
      cases s with
      | prop => trivial
      | arrow _ _ => trivial
      | ind =>
          intro t ht
          rcases hfr : spine ρ f with _ | ⟨c, ts⟩ <;>
            simp [term, hfr] at ht
          rcases har : term ρ a with _ | a' <;>
            simp [har] at ht
          subst t
          rw [embedded_func]
          have hc : c.schematic = false := by
            cases hh : c.schematic
            · rfl
            · exact False.elim (LSort.noConfusion (individual_spine_kind hfn ρ hfr hh))
          simpa [rawHead, hc] using
            (spine_app rf.1 ra.2 c (ts ++ [a']) (by simp [spine, hfr, har])).symm
  | @Individual.epsilon bp hp =>
      refine ⟨by simp [SpineReconstructed, spine], ?_⟩
      intro t ht
      rcases hpr : formula (Readback.bind ρ) bp with _ | p <;>
        simp [term, hpr] at ht
      subst t
      have rp := (formula_roundtrip_aux hp (PureEmbedding.lift v) (Readback.bind ρ)
        (bound_lift v ρ hb) (free_lift v (by simpa using hf))).2 p hpr
      simpa [embedded, PureEmbedding.term, Term.erase] using
        congrArg (fun q => RawTerm.app (.const ⟨⟨"epsilon", 0⟩, (ind >> prop) >> ind⟩)
          (.lam ind q)) rp
termination_by structural h

private theorem formula_roundtrip_aux {s n : _} {e : Term s} (h : Formula e)
    (v : Variables Identifier n) (ρ : Bound n)
    (hb : ∀ k i, ρ k = some i → v (.inr i) = .bound k)
    (hf : ∀ x, (⟨x, ind⟩ : SVar) ∈ e.freeVars → v (.inl x) = .free x) :
    SpineReconstructed v ρ e ∧ FormulaReconstructed v ρ e := by
  match h with
  | .free x =>
      constructor
      · intro c ts hr
        simp only [spine] at hr
        obtain ⟨rfl, rfl⟩ := Option.some.inj hr
        simp [Term.erase, rawHead, arity]
      · intro p hr
        simp only [formula] at hr
        have hr := Option.some.inj hr
        subst p
        rfl
  | .symbol k c =>
      constructor
      · intro d ts hr
        simp only [spine] at hr
        obtain ⟨rfl, rfl⟩ := Option.some.inj hr
        simp [Term.erase, rawHead, arity]
      · cases k with
        | succ k => trivial
        | zero =>
            intro p hr
            change formula ρ (.const (s := prop) c) = some p at hr
            by_cases ht : c = ⟨"top", 0⟩
            · subst c; simp only [formula, Option.some.injEq] at hr; subst p; rfl
            by_cases hb : c = ⟨"bot", 0⟩
            · subst c; simp only [formula, Option.some.injEq] at hr; subst p; rfl
            have hr : (.rel ⟨false, c⟩ Fin.elim0 : BFormula n) = p := by simpa [formula] using hr
            subst p
            rfl
  | @Formula.app s f a hfn ha =>
      have rf := formula_roundtrip_aux hfn v ρ hb (fun x hx => hf x (Finset.mem_union_left _ hx))
      have ra := individual_roundtrip ha v ρ hb (fun x hx => hf x (Finset.mem_union_right _ hx))
      have hs := spine_app rf.1 ra.2
      refine ⟨hs, ?_⟩
      cases s with
      | ind => trivial
      | arrow _ _ => trivial
      | prop => exact formula_app_roundtrip v ρ f a hs
  | .top =>
      constructor
      · intro c ts hr
        simp only [spine] at hr
        obtain ⟨rfl, rfl⟩ := Option.some.inj hr
        rfl
      · intro p hr; simp only [formula] at hr; have hr := Option.some.inj hr; subst p; rfl
  | .bot =>
      constructor
      · intro c ts hr
        simp only [spine] at hr
        obtain ⟨rfl, rfl⟩ := Option.some.inj hr
        rfl
      · intro p hr; simp only [formula] at hr; have hr := Option.some.inj hr; subst p; rfl
  | @Formula.neg bp hp =>
      refine ⟨by simp [SpineReconstructed, spine], ?_⟩
      intro p hr
      rcases hpr : formula ρ bp with _ | p' <;>
        simp [formula, hpr] at hr
      subst p
      have rp := (formula_roundtrip_aux hp v ρ hb (by simpa using hf)).2 p' hpr
      simpa [PureEmbedding.formula, Term.erase] using
        congrArg (RawTerm.app (.const ⟨⟨"not", 0⟩, prop >> prop⟩)) rp
  | @Formula.and bp bq hp hq | @Formula.or bp bq hp hq | @Formula.imp bp bq hp hq | @Formula.iff bp bq hp hq =>
      refine ⟨by simp [SpineReconstructed, spine], ?_⟩
      intro p hr
      rcases hpr : formula ρ bp with _ | p' <;>
        simp [formula, hpr] at hr
      rcases hqr : formula ρ bq with _ | q' <;>
        simp [hqr] at hr
      subst p
      have rp := (formula_roundtrip_aux hp v ρ hb (fun x hx => hf x (by simp [hx]))).2 p' hpr
      have rq := (formula_roundtrip_aux hq v ρ hb (fun x hx => hf x (by simp [hx]))).2 q' hqr
      simp only [PureEmbedding.formula, Term.erase, rp, rq]
  | @Formula.eq bt bu ht hu =>
      have rt := (individual_roundtrip ht v ρ hb (fun x hx => hf x (by simp [hx]))).2
      have ru := (individual_roundtrip hu v ρ hb (fun x hx => hf x (by simp [hx]))).2
      constructor
      · intro c ts hr
        rcases htr : term ρ bt with _ | t <;>
          simp [spine, htr] at hr
        rcases hur : term ρ bu with _ | u <;>
          simp [hur] at hr
        obtain ⟨rfl, rfl⟩ := hr
        simp [Term.erase, ← rt _ htr, ← ru _ hur, rawHead, arity]
      · intro p hr
        rcases htr : term ρ bt with _ | t <;>
          simp [formula, htr] at hr
        rcases hur : term ρ bu with _ | u <;>
          simp [hur] at hr
        subst p
        simpa [PureEmbedding.formula, Term.erase, embedded] using
          congrArg₂ (fun t u => RawTerm.app (.app (.const ⟨⟨"eq", 0⟩, ind >> ind >> prop⟩) t) u)
            (rt _ htr) (ru _ hur)
  | @Formula.all bp hp | @Formula.ex bp hp =>
      refine ⟨by simp [SpineReconstructed, spine], ?_⟩
      intro p hr
      rcases hpr : formula (Readback.bind ρ) bp with _ | p' <;>
        simp [formula, hpr] at hr
      subst p
      have rp := (formula_roundtrip_aux hp (PureEmbedding.lift v) (Readback.bind ρ)
        (bound_lift v ρ hb) (free_lift v (by simpa using hf))).2 p' hpr
      simp only [PureEmbedding.formula, Term.erase, rp]
termination_by structural h
end

theorem term_roundtrip {e : Term ind} (he : Individual e) (v : Variables Identifier n) (ρ : Bound n)
    (hb : ∀ k i, ρ k = some i → v (.inr i) = .bound k)
    (hf : ∀ x, (⟨x, ind⟩ : SVar) ∈ e.freeVars → v (.inl x) = .free x)
    (hr : term ρ e = some t) : PureEmbedding.term v t = e :=
  Term.erase_injective ((individual_roundtrip he v ρ hb hf).2 _ hr)

theorem formula_roundtrip {e : Term prop} (he : Formula e) (v : Variables Identifier n) (ρ : Bound n)
    (hb : ∀ k i, ρ k = some i → v (.inr i) = .bound k)
    (hf : ∀ x, (⟨x, ind⟩ : SVar) ∈ e.freeVars → v (.inl x) = .free x)
    (hr : formula ρ e = some p) : PureEmbedding.formula v p = e :=
  Term.erase_injective ((formula_roundtrip_aux he v ρ hb hf).2 _ hr)

end Lisa.SCLambdaToPure.Readback
