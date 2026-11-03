import Lisa.Lambda.Reduction

namespace Lisa.Lambda.Tests
open Reduction Lisa.ExpressionOrder
example (p : Expr) : AlphaBetaEta (reduceLambda p) p := reduceLambda_alphaBetaEta p
example (p : Expr) : (reduceLambda p).sort = p.sort := reduceLambda_sort p
example (p : Expr) : reduceLambda (reduceLambda p) = reduceLambda p := reduceLambda_idempotent p
example (h : p.hasSort s) : reduceLambda p = reduceLambda q ↔ AlphaBetaEta p q := reduceLambda_eq_iff h
example (p q : Expr) : leq (reduceLambda p) (reduceLambda q) ↔ leq p q := leq_reduceLambda_iff p q
example (f a : Expr) : AlphaBetaEta (reduceLambda (.app f a)) (.app (reduceLambda f) (reduceLambda a)) := reduceLambda_app f a
example (x : SVar) (p : Expr) : AlphaBetaEta (reduceLambda (.lam x p)) (.lam x (reduceLambda p)) := reduceLambda_lam x p
private def p : Expr := .var ⟨⟨"p", 0⟩, prop⟩
private def identity : Expr := .lam ⟨⟨"x", 0⟩, prop⟩ (.var ⟨⟨"x", 0⟩, prop⟩)
#guard reduceLambda (.app identity p) = p
#guard reduceLambda (.app p p) = .app p p
#guard reduceLambda (reduceLambda identity) = reduceLambda identity
end Lisa.Lambda.Tests
