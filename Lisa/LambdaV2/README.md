# Context-free, intrinsically sorted lambda normalization

This package implements total beta-eta normalization by evaluation, conversion decisions, and their correctness proofs. It uses `Term s`: the sort is intrinsic, while binder contexts are absent from the types of terms, substitutions, values, and environments.

Import `Lisa.LambdaV2` for the typed, raw, and named APIs. All implementation declarations live under `Lisa.LambdaV2`; named-substitution helper proofs are also isolated in that namespace.

## The representations

An indexed variable counts only binders of its own sort. Sorts include complete function sorts.

```text
λ(_:prop). λ(_:ind). bound prop 0   refers to the outer prop binder
λ(_:prop). λ(_:prop). bound prop 1  refers to the outer prop binder
λ(_:ind). bound prop 0             contains an ambient prop variable
```

`Term.app` accepts exactly the domain sort required by its function. `Term.lam` records its domain explicitly. Free named identifiers and constants have separate constructors. An ambient indexed variable is a meaningful sorted input, so the evaluator needs no scope check.

`RawTerm` uses the same per-sort indices but allows unchecked applications. `Term.erase` simply forgets typing; `elaborate` checks application sorts. Typed erasure/elaboration round trips are unconditional, without a binder stack or a scope premise.

Shared `Lisa.NamelessExpr` has a different meaning for indices: they count every binder. It is used only by the alpha-correspondence proofs in [NamedAlpha](NamedAlpha.lean). Do not pass its indices off as `RawTerm` indices. The package's raw API takes its own distinct datatype, preventing that accidental mix.

## Evaluation in three definitions

```text
Val ind      = Depth → Term ind
Val prop     = Depth → Term prop
Val (s >> t) = Val s → Val t
```

Function values are ordinary Lean functions. Ground values defer printing indexed variables until readback knows the number of binders introduced in each sort. `Depth` is that ordinary count map; it is not an index on the term or value type.

`eval` is structural recursion. Lambda evaluates to a function which extends the environment with its argument. `quote` introduces binders, applies function values to fresh reflected variables, and reconstructs eta-long syntax. `reflect` allows opaque variables and constants to participate in evaluation by constructing residual applications.

```text
normalize e = quote s Depth.zero (eval e ambient)
```

There are no context transport structures, naturality fields, fuel arguments, or partial evaluator definitions. Freshness and correctness are proved using a logical relation at increasing readback depths.

## Public guarantees

Typed conversion is specified independently by the inductive `Equiv` rules. The central results are:

```text
normalize_sound           : Equiv e (normalize e)
equiv_iff_normalize_eq     : Equiv e f ↔ normalize e = normalize f
normalize_idempotent      : normalize (normalize e) = normalize e
```

`Equiv` is decidable by comparing normalized typed syntax. `normalize_subst` and `normalize_rename` express compatibility after normalization.

The raw API provides `elaborate`, `normalizeNameless`, and `compareNameless`. A failed elaboration means an ill-sorted application. Different result sorts produce `some false` in comparison. Arbitrary ambient indices are accepted. Erasure injectivity, round trips, comparison correctness, and normalization idempotence are proved in [Elaboration](Elaboration.lean).

The named API consumes ordinary `Lisa.Expr`:

```text
compareNamed   : Expr → Expr → Option Bool
normalizeNamed : Expr → Option Expr
```

Its contracts use Lisa's shared named conversion relation:

- `some true` exactly for convertible, well-sorted inputs;
- `some false` exactly for two well-sorted inputs that do not convert;
- `none` exactly when an input is ill-sorted;
- successful normalization preserves sort and gives a convertible expression;
- named normalization is literally idempotent;
- on a sorted source, conversion is equivalent to equality of named normalizations.

Named comparison shares packed-result handling with raw comparison and compares typed normalizations directly. It does not generate names just to decide conversion.

## Why reconstruction needs no separate scope theory

Interpreting a complete named input produces a typed term independent of every ambient indexed substitution:

```text
interpretNamed p Names.free = some ⟨s, e⟩  ⇒  e.subst σ = e
```

This is [subst_of_interpretNamed](NamedReflection.lean), derived from the existing interpretation/substitution law. Combining it with normalization/substitution compatibility proves:

```text
normalize ((normalize e).subst σ) = normalize e
```

That equation is sufficient for named output idempotence. It does not claim the intermediate substituted syntax is literally unchanged before normalization.

`Context` assigns names to indexed variables and carries a finite set of reserved identifiers **for each sort**. This matches the variable namespaces and makes the free-name bound precise. The empty context uses `_ambient` as a default identifier; a fresh binder avoids its sort's reserved names and the body's free identifiers.

Reification of an unrestricted open term is explicitly a naming substitution, not an injective encoding of every ambient index. Any naming assignment on finitely many indexed variables can be represented. For complete named-source inputs, the substitution-independence theorem gives the alpha round trip without relying on defaults to preserve distinct variables. The evaluator itself always preserves distinct ambient indices according to its proved conversion specification.

Binder names are deterministic, but different sorts can reuse an identifier. Exact spelling equality with another normalizer is not an interface requirement; literal canonicality within this package is proved.

## Reading order

| Files | Responsibility |
|---|---|
| [Syntax](Syntax.lean), [Conversion](Conversion.lean) | Sorted terms, per-sort binding algebra, independent beta-eta rules |
| [Semantics](Semantics.lean), [Evaluation](Evaluation.lean) | Ordinary-function evaluation and conversion invariance |
| [Normalization](Normalization.lean), [Decision](Decision.lean), [Substitution](Substitution.lean) | Soundness, canonicality, decisions, substitution consequences |
| [Erasure](Erasure.lean), [Elaboration](Elaboration.lean) | Matching untyped syntax and checked application sorts |
| [NamedEnvironment](NamedEnvironment.lean), [NamedAlpha](NamedAlpha.lean) | Interpret named syntax and prove shared alpha correspondence |
| [NamedSubstitution](NamedSubstitution.lean), [NamedConversion](NamedConversion.lean) | Capture avoidance and named-to-typed conversion |
| [Reification](Reification.lean), [NamedReflection](NamedReflection.lean) | Fresh names and typed-to-named conversion |
| [NamedDecision](NamedDecision.lean) | Final named API and all its contracts |

[Reduction](Reduction.lean) additionally supplies a certified reducer against the shared expression order. It proves conversion, sorting, idempotence, canonicality, reference-order preservation, and application/lambda congruence. This demonstrates the project-facing interface without selecting it in the production checker.

## Verification and size

```powershell
lake build Lisa.LambdaV2.Tests Lisa.LambdaV2.CoreTests Lisa.LambdaV2.InterfaceTests
```

The test targets cover core dependency isolation, capture across sort namespaces, shadowing, higher-order eta expansion, ambient variables, malformed raw/named applications, raw round trips, deterministic fresh naming, 324 named comparison pairs, named idempotence, and the reducer contracts.

The 16 main modules contain **1,412 nonblank lines**, or **1,363 excluding comments**. The umbrella and optional reducer add 50 nonblank lines; the three test modules contain 92. The plan's audited baseline was 1,645 nonblank lines, or 1,555 excluding comments, for the corresponding 16-module scope. Thus the reduction is not solely a difference in comments or blank lines. These are source-size measurements, not performance benchmarks.

The inspected theorem dependencies use Lean's standard `propext`, `Quot.sound`, and, for named results, `Classical.choice`. There are no admitted proofs or added axioms. The code and tests have no dependency on another lambda implementation.

See [the plan](PLAN.md) and [the completed declaration-role audit](DECLARATION_AUDIT.md) for the design rationale and adapted theorem responsibilities.
