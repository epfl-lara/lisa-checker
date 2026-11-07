import Lisa.Orthologic.Internal.Size
import Lisa.Orthologic.Syntax

/-! Exact structural equality for the cache keys. In particular, two internal
trees that erase to the same AlphaBetaEtaNormalization.Algorithm term need not be the same normalization
query. Neither erased terms nor hashes alone are used as keys. -/

namespace Lisa.Orthologic

def CacheKey.listEq (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && CacheKey.listEq f as bs
  | _, _ => false

namespace SimpleExpr

def sameSyntax (p q : SimpleExpr s) : Bool :=
  match p, q with
  | .bound n, .bound m => n == m
  | .free x, .free y | .const x, .const y => x == y
  | @SimpleExpr.app a _ f x, @SimpleExpr.app b _ g y =>
      if h : a = b then sameSyntax (h ▸ f) g && sameSyntax (h ▸ x) y else false
  | .lam _ p, .lam _ q => sameSyntax p q
  | .top, .top => true
  | .conj ps, .conj qs => CacheKey.listEq (fun p q => sameSyntax p.val q.val) ps.attach qs.attach
  | .all p, .all q | .neg p, .neg q => sameSyntax p q
  | .equal a b, .equal c d => sameSyntax a c && sameSyntax b d
  | _, _ => false
termination_by p.size
decreasing_by
  all_goals try subst_vars
  all_goals try (simp only [size]; omega)
  all_goals exact size_lt_conj p.property

end SimpleExpr
end Lisa.Orthologic
