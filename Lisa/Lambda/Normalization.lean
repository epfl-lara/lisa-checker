import Lisa.Lambda.Evaluation

/-! Readback correctness through a relation at increasing per-sort depths.
Only syntax is weakened; the related semantic value stays unchanged. -/
namespace Lisa.Lambda
namespace Depth

def Extends (d k : Depth) : Prop := ∀ s, d s ≤ k s

@[refl] theorem extends_refl (d : Depth) : Extends d d := fun _ => Nat.le_refl _

theorem Extends.trans (h : Extends d k) (h' : Extends k l) : Extends d l := fun s => Nat.le_trans (h s) (h' s)

theorem extends_inc (d : Depth) (s : LSort) : Extends d (d.inc s) := by
  intro t; by_cases h : t = s <;> simp [inc, h]

theorem zero_extends (d : Depth) : Extends zero d := fun _ => Nat.zero_le _

def weaken (d k : Depth) : Ren := fun s n => n + (k s - d s)

@[simp] theorem weaken_self : weaken d d = Ren.id := by funext s n; simp [weaken, Ren.id]

theorem weaken_comp (h : Extends d k) (h' : Extends k l) :
    Ren.comp (weaken d k) (weaken k l) = weaken d l := by
  funext s n
  have := h s; have := h' s
  simp only [Ren.comp, weaken]; omega

@[simp] theorem weaken_inc : weaken d (d.inc b) = Ren.shift b := by
  funext s n
  by_cases h : s = b <;> simp [weaken, inc, Ren.shift, h]
end Depth

/-- A residual prints the same open expression at every later readback depth. -/

def RepresentsAt (d : Depth) (e : Term s) (n : Residual s) : Prop :=
  ∀ k, d.Extends k → Equiv (e.rename (d.weaken k)) (n k)

def Related : (s : LSort) → Depth → Term s → Val s → Prop
  | .ind, d, e, v => RepresentsAt d e v
  | .prop, d, e, v => RepresentsAt d e v
  | .arrow s t, d, e, v => ∀ k, d.Extends k → ∀ a w,
      Related s k a w → Related t k (.app (e.rename (d.weaken k)) a) (v w)

namespace Related

theorem congr (h : Related s d e v) (hef : Equiv e f) : Related s d f v := by
  induction s generalizing d with
  | ind => exact fun k hk => (hef.rename _).symm.trans (h k hk)
  | prop => exact fun k hk => (hef.rename _).symm.trans (h k hk)
  | arrow s t _ ih => exact fun k hk a w ha => ih (h k hk a w ha) (.app (hef.rename _) (.refl a))

theorem mono (h : Related s d e v) (hdk : d.Extends k) : Related s k (e.rename (d.weaken k)) v := by
  cases s with
  | ind => exact fun l hkl => by simpa [Depth.weaken_comp hdk hkl] using h l (hdk.trans hkl)
  | prop => exact fun l hkl => by simpa [Depth.weaken_comp hdk hkl] using h l (hdk.trans hkl)
  | arrow s t =>
      intro l hkl a w ha
      simpa [Depth.weaken_comp hdk hkl] using h l (hdk.trans hkl) a w ha
end Related

theorem fresh_represents (d : Depth) (s : LSort) :
    RepresentsAt (d.inc s) (.bound (s := s) 0) (fresh s (d s)) := by
  intro k hk
  simp only [Term.rename, Depth.weaken, Nat.zero_add, Depth.inc_self, fresh]
  exact .refl _
/-- Sound readback and reflection, proved together by induction on the sort. -/

theorem readback_correct (s : LSort) :
    (∀ d e v, Related s d e v → Equiv e (quote s d v)) ∧
    (∀ d e n, RepresentsAt d e n → Related s d e (reflect s n)) := by
  induction s with
  | ind => exact ⟨fun d _ _ h => by simpa using h d (Depth.extends_refl d), fun _ _ _ h => h⟩
  | prop => exact ⟨fun d _ _ h => by simpa using h d (Depth.extends_refl d), fun _ _ _ h => h⟩
  | arrow s t ihs iht =>
      constructor
      · intro d e v h
        have ha := ihs.2 (d.inc s) (.bound 0) _ (fresh_represents d s)
        have hb := iht.1 _ _ _ (h (d.inc s) (Depth.extends_inc d s) _ _ ha)
        exact (Equiv.eta e).symm.trans (.lam (by simpa using hb))
      · intro d e n hn k hk a w ha
        apply iht.2
        intro l hl
        have hnl := hn l (hk.trans hl)
        have hal := ihs.1 _ _ _ (ha.mono hl)
        simpa [Term.rename, Depth.weaken_comp hk hl] using Equiv.app hnl hal

theorem Term.subst_lift_rename (b : Term t) (σ : Sub) (ρ : Ren) :
    (b.subst (σ.lift s)).rename (ρ.lift s) = b.subst (Sub.lift s (fun t n => (σ t n).rename ρ)) := by
  rw [rename_subst]
  congr 1
  funext u n
  by_cases h : u = s
  · subst u; cases n <;> simp [Sub.lift, Term.rename, Ren.lift, Ren.lift_shift]
  · simp [Sub.lift, h, Ren.lift_shift]

/-- Evaluate under related syntactic and semantic assignments. -/

theorem fundamental (e : Term s) (d : Depth) (σ : Sub) (η : Env)
    (h : ∀ t n, Related t d (σ t n) (η t n)) : Related s d (e.subst σ) (eval e η) := by
  induction e generalizing d σ η with
  | bound n => exact h _ n
  | free x => exact (readback_correct _).2 _ _ _ (fun _ _ => .refl _)
  | const c => exact (readback_correct _).2 _ _ _ (fun _ _ => .refl _)
  | app f a ihf iha => simpa using ihf d σ η h d (Depth.extends_refl d) _ _ (iha d σ η h)
  | lam b e ih =>
      intro k hk a w ha
      let σ' : Sub := fun t n => (σ t n).rename (d.weaken k)
      have h' : ∀ t n, Related t k (Sub.extend σ' a t n) (η.extend w t n) := by
        intro t n
        by_cases ht : t = b
        · subst t; cases n with
          | zero => simpa using ha
          | succ n => simpa [σ'] using (h b n).mono hk
        · simpa [Sub.extend, Env.extend, ht, σ'] using (h t n).mono hk
      have hb := ih k (Sub.extend σ' a) (η.extend w) h'
      have hβ := Equiv.beta ((e.subst (σ.lift b)).rename ((d.weaken k).lift b)) a
      rw [Term.subst_lift_rename, Term.instantiate_subst] at hβ
      simpa only [Term.subst, Term.rename, Term.subst_lift_rename] using hb.congr hβ.symm

theorem normalize_sound (e : Term s) : Equiv e (normalize e) := by
  have h := fundamental e Depth.zero Sub.id ambient (fun t n =>
    (readback_correct t).2 _ _ _ (fun k _ => by
      simp [Sub.id, Term.rename, Depth.weaken, Depth.zero, Nat.add_comm]; exact .refl _))
  simpa using (readback_correct s).1 _ _ _ h

theorem equiv_iff_normalize_eq (e f : Term s) : Equiv e f ↔ normalize e = normalize f :=
  ⟨normalize_eq_of_equiv, fun h => (normalize_sound e).trans (h ▸ (normalize_sound f).symm)⟩

@[simp] theorem normalize_idempotent (e : Term s) : normalize (normalize e) = normalize e :=
  (normalize_eq_of_equiv (normalize_sound e)).symm
end Lisa.Lambda
