import Lisa.Orthologic.Expression
import Std.Data.DHashMap.Basic

/-! Exact structural equality for the cache keys. In particular, two internal
trees that erase to the same Lambda term need not be the same normalization
query. Neither erased terms nor hashes alone are used as keys. -/

namespace Lisa.Orthologic

private def pairwise (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && pairwise f as bs
  | _, _ => false

private theorem pairwise_eq (f : α → β → Bool) (u : α → γ) (v : β → γ)
    (h : ∀ a b, f a b = true ↔ u a = v b) (as : List α) (bs : List β) :
    pairwise f as bs = true ↔ as.map u = bs.map v := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [pairwise]
  | cons a as ih => cases bs <;> simp [pairwise, h, ih]

namespace SimpleExpr

def sameSyntax (p q : SimpleExpr s) : Bool :=
  match p, q with
  | .bound n, .bound m => n == m
  | .free x, .free y | .const x, .const y => x == y
  | @SimpleExpr.app a _ f x, @SimpleExpr.app b _ g y =>
      if h : a = b then sameSyntax (h ▸ f) g && sameSyntax (h ▸ x) y else false
  | .lam _ p, .lam _ q => sameSyntax p q
  | .top, .top => true
  | .conj ps, .conj qs => pairwise (fun p q => sameSyntax p.val q.val) ps.attach qs.attach
  | .all p, .all q | .neg p, .neg q => sameSyntax p q
  | .equal a b, .equal c d => sameSyntax a c && sameSyntax b d
  | _, _ => false
termination_by p.size
decreasing_by
  all_goals try subst_vars
  all_goals try (simp only [size]; omega)
  all_goals exact size_lt_conj p.property

theorem sameSyntax_eq (p q : SimpleExpr s) : sameSyntax p q = true ↔ p = q := by
  apply SimpleExpr.rec
    (motive_1 := fun s p => ∀ q : SimpleExpr s, sameSyntax p q = true ↔ p = q)
    (motive_2 := fun ps => ∀ p ∈ ps, ∀ q, sameSyntax p q = true ↔ p = q)
    (t := p)
  all_goals repeat intro
  case nil => simp_all
  case cons head tail ihh iht a ha b =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ihh b
    · exact iht a ha b
  case app s t f a ihf iha q =>
    cases q <;> try simp [sameSyntax]
    rename_i u g b
    by_cases hs : s = u
    · subst u; simp [ihf, iha]
    · simp [hs]
  case conj ps ih q =>
    cases q <;> try simp [sameSyntax]
    rename_i qs
    simpa using pairwise_eq (fun p q => sameSyntax p.val q.val)
      (fun p : {p // p ∈ ps} => p.val) (fun q : {q // q ∈ qs} => q.val)
      (fun p q => ih p.val p.property q.val) ps.attach qs.attach
  all_goals rename_i q; cases q <;> simp_all [sameSyntax]

instance : DecidableEq (SimpleExpr s) := fun p q =>
  decidable_of_iff (sameSyntax p q = true) (sameSyntax_eq p q)

end SimpleExpr
end Lisa.Orthologic
