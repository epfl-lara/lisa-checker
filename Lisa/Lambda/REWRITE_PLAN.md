# Revised plan: intrinsically sorted terms without binder-context indices

Revised 17 October 2026. This document supersedes the earlier single-raw-datatype proposal. It is a source audit and design plan, not an implementation. Lean signatures below are sketches unless explicitly identified as existing declarations. No production Lean code is changed.

## 1. Revised recommendation

Use **`Term s` with per-sort de Bruijn indices**, removing `Γ` while retaining intrinsic sorting. Use **`Val s` with ordinary Lean function spaces** at arrow sorts and delayed typed syntax at ground sorts. There is no `Term Γ s`, `Var Γ s`, `Val Γ s`, or `Family` in the proposed core.

This is a better simplification candidate than the previous raw-syntax proposal. It removes context dependence without throwing away application typing. Consequently, the following costs from that proposal disappear:

- A separate sort checker for internal terms.
- Sortedness predicates on substitution and environments.
- Sort-preservation side conditions in the core conversion relation.
- Optional core evaluation and normalization.
- The proposed structural compilation layer.
- Successful-compilation witnesses and casts throughout the correctness proof.

However, not every later module becomes simpler. The new representation permits ambient indexed variables. Local closure is no longer enforced by `Γ`, so named reconstruction and global-index adapters need explicit coverage/local-closure results. Replacing `Family` with ordinary functions also changes the normalization proof: depth-indexed residual correspondence replaces semantic transport and naturality.

**Reevaluation:** a likely simplification of core syntax, evaluation, and semantic interfaces; a plausible but unproved simplification of the verified package overall. The strongest uncertainty is now concentrated in normalization soundness and the scope-sensitive named reconstruction proof, rather than dispersed through sorting checks.

| Objective | Revised assessment |
|---|---|
| Remove context indexing from all core syntax and semantic value types | High confidence |
| Retain intrinsic typing of application, substitution, conversion | Directly supported by the proposed types |
| Ordinary functions at semantic arrow sorts | Algorithmically plausible with delayed typed syntax |
| Total normalization for every `Term s` | Plausible by structural evaluation/type-directed readback; Lean prototype required |
| No `available s` checks inside core operations | High confidence with explicit ambient-index interpretation |
| Remove `Family`, Kripke function wrappers, naturality fields | Feasible in the proposed semantics |
| Simplify all named modules | No: many remain similar, reification adds scope premises |
| Preserve public named/checker contracts | Plausible, substantial proof migration |
| Fewer total lines or faster execution | Not established; measure after the proof prototype |

The correct gate is to complete soundness and canonicality of the new typed core before migrating the entire named bridge.

## 2. Target syntax and the meaning of an index

```lean
inductive Term : LSort → Type where
  | bound (s : LSort) (n : Nat) : Term s
  | free (s : LSort) (id : Identifier) : Term s
  | const (s : LSort) (id : Identifier) : Term s
  | app : Term (s >> t) → Term s → Term t
  | lam (s : LSort) : Term t → Term (s >> t)
```

Constructor sorts can be implicit where elaboration is clear. A bound variable counts only binders of its own sort, nearest first. Sort namespaces are keyed by the entire structural `LSort`, including arrow sorts.

```text
λ(_:prop). λ(_:ind). bound prop 0      outer prop binder
λ(_:prop). λ(_:prop). bound prop 1     outer prop binder
λ(_:ind). bound prop 0                ambient prop variable
```

Entering an `ind` binder leaves `prop` indices unchanged. Entering a binder of sort `ind >> prop` changes indices in that arrow-sort namespace, not in the `ind` or `prop` namespaces.

There is one syntax constructor system indexed only by result sort. If an unindexed container is needed, use `SomeTerm := Σ s, Term s`. This packaging does not reintroduce context dependence or an extrinsic typing judgment.

### Intrinsic sorting and extrinsic scope are independent

The type system guarantees that an application has matching argument/domain sorts. A bound reference can never attach to a binder of a different sort, because lookup is within a sort-specific namespace.

It does not guarantee that a referenced binder exists within the term. Interpret references beyond local binders as an infinite supply of ambient indexed variables, one sequence per sort. Thus every `Term s` is a meaningful *open* term; normalization does not need to reject out-of-range indices.

Keep named free identifiers as a separate constructor. An ambient indexed variable is not silently converted to `.free`. Named source expressions translated from an empty binder environment are locally closed in the indexed channel, while retaining named free variables.

The intrinsic typing claim relies on this infinite, sort-separated ambient environment. Do not describe a dangling reference as a closed well-scoped term.

### Does `available s` remain necessary?

Not in the term type, evaluator, substitution, or normalizer. There are still three uses of binder-count information, as ordinary data:

1. `Depth : LSort → Nat` for allocating/rendering fresh variables during readback.
2. A predicate `Scoped d e` for proving that the named boundary has enough binders.
3. Stack lookup in compatibility conversion from the current globally indexed format.

The first allocates fresh semantic variables; it is not input availability checking. The second need not be executed for inputs whose local closure is already proved. The third preserves an existing external API's rejection behavior.

```text
Scoped d (bound s n) iff n < d s
Scoped d (lam s b) iff Scoped (increment d s) b
LocallyClosed e := Scoped zero e
```

All are predicates/data on the same `Term s`, not indices on a second term family.

## 3. Binding operations

```lean
abbrev Ren := LSort → Nat → Nat
abbrev Sub := (s : LSort) → Nat → Term s

Term.rename : Ren → Term s → Term s
Term.subst  : Sub → Term s → Term s
```

Every substitution is intrinsically sort-preserving. There is no `Sub.Sorted` predicate. As in the current code, `Ren` means a variable-to-variable map, not necessarily a bijection.

Let `shift_b` increment indices in namespace `b`. Under a binder of sort `b`, lift renaming as:

```text
lift_b ρ b 0       = 0
lift_b ρ b (n+1)   = ρ b n + 1
lift_b ρ s n       = ρ s n, if s ≠ b
```

Lift substitution as:

```text
lift_b σ b 0       = bound b 0
lift_b σ b (n+1)   = shift_b (σ b n)
lift_b σ s n       = shift_b (σ s n), if s ≠ b
```

The different-sort clause still shifts the **replacement term**. For example, an `ind`-sorted replacement may contain a `prop`-sorted variable, so moving that replacement under a `prop` binder must protect that reference. Only the lookup index avoids the adjustment for different namespaces.

Instantiation uses:

```text
single_b a b 0       = a
single_b a b (n+1)   = bound b n
single_b a s n       = bound s n, if s ≠ b

instantiate : Term t → Term b → Term t
```

The binder sort can be inferred from the argument type. The function substitutes for zero and removes one binder in that namespace; structural recursion lifts the substitution under inner lambdas.

Lean implementation details: updating a dependent `Sub` at one sort needs casts in the equality branch. Isolate these in `Sub.extend`, `Sub.single`, and their simp equations. Other-sort cases require no type transport. Compared with the original context-indexed variables, some `cases v` proofs become sort-equality plus zero/successor cases. Fewer context casts does not imply every binding proof becomes shorter.

Retain the full renaming/substitution identity, composition, and interaction algebra. Removing semantic renaming does not make syntactic renaming unnecessary.

## 4. Typed conversion

```lean
inductive Equiv : Term s → Term s → Prop
```

Retain the current seven constructors: reflexivity, symmetry, transitivity, application congruence, lambda congruence, beta, and eta. Beta needs no sort side condition because the argument's type carries it. Eta shifts `f` in its new binder's sort namespace:

```text
Equiv (lam s (app (shift_s f) (bound s 0))) f
```

Alpha equivalence remains structural. The lambdas themselves preserve their domain-sort ordering; separate namespaces do not identify terms obtained by arbitrarily swapping different-sort lambdas.

Keep `Equiv` independent of the normalizer. Its closure under `rename` and `subst` has unconditional typed statements, just as now. Do not redefine conversion as normalization equality and then call the equivalence theorem a correctness proof.

## 5. Semantics with ordinary functions

### Why per-sort indices are insufficient by themselves

The naive choice `Val base = Term base`, `Val (s >> t) = Val s → Val t`, with every fresh variable printed as zero immediately, confuses old and newly introduced same-sort references. Syntax representing a variable must be rendered at the depth at which it is eventually quoted.

Delay that rendering:

```text
Depth = LSort → Nat
Residual s = Depth → Term s

Val ind       = Residual ind
Val prop      = Residual prop
Val (s >> t)  = Val s → Val t

Env = (s : LSort) → Nat → Val s
```

`Residual s` is a function returning typed syntax, not a new syntax datatype. `Val` has no context index. Arrow values are actual Lean functions with no Kripke map argument or proof field.

### Direct quote and reflect

Define by recursion on the sort:

```text
quote_s   : Depth → Val s → Term s
reflect_s : Residual s → Val s

quote_base d v = v d
reflect_base n = n

quote_(s→t) d f =
  lam s (quote_t (increment d s)
    (f (reflect_s (fresh_s (d s)))))

reflect_(s→t) n =
  fun a => reflect_t (fun d => app (n d) (quote_s d a))
```

The fresh residual allocated at level `l` is:

```text
fresh_s l d = bound s (d s - (l + 1))
```

After allocation at level zero, depth one prints index zero, depth two prints index one. Each sort has its own level counter. Natural subtraction makes the function total, but its intended meaning requires `l < d s`; prove that inequality for actual readback uses. Truncation is not a substitute for freshness correctness.

The mutually dependent quote/reflect construction recurses only into strict subsorts. Prefer a recursive pair/record of functions per sort if Lean's mutual termination checker is awkward. Such a small sort-recursive bundle is acceptable; it must not restore context-indexed `Family` or semantic transport laws.

### Ordinary evaluation

```text
eval : Term s → Env → Val s
```

Evaluation is structurally recursive on typed syntax:

- Indexed variable: environment lookup.
- Named free variable/constant: reflect its constant residual, `fun _ => free ...` or `const ...`.
- Application: ordinary function application.
- Lambda: `fun a => eval body (Env.extend s η a)`.

`Env.extend s η a` inserts `a` at zero of namespace `s`, maps successors there to the old environment, and leaves other namespaces unchanged. It does not transport semantic values: those values already use stable symbolic levels/delayed printing.

Unlike the raw-syntax proposal, no `compile`, optional evaluation, dynamic application check, or proof-directed evaluator is necessary. Lean's structural recursion can use the recursive body evaluator inside the returned function, as the current evaluator already does. Prototype the definition to verify elaboration and universe details.

### Normalize all open terms

Initialize an infinite ambient environment:

```text
ambient s n = reflect_s (fun d => bound s (d s + n))
normalize e = quote_s zero (eval e ambient)
```

The ambient sequence prints above all fresh readback binders in its namespace. At depth `d`, local symbolic variables print below `d s`, ambient indices at or above `d s`. This separates them without an availability bound.

Source lambda evaluation inserts arguments into the environment; readback lambda generation increments depth. These are different operations and must not be conflated. Nested same-sort, different-sort, and higher-order cases must be checked explicitly.

`normalize : Term s → Term s` is total for every internal term. Only entry from original potentially malformed named syntax is optional.

## 6. Revised correctness proof

### Conversion invariance becomes simpler

Retain the evaluation/renaming theorem as environment precomposition:

```text
eval (rename ρ e) η = eval e (fun s n => η s (ρ s n))
```

Retain evaluation/substitution commutation. All terms/substitutions are correctly sorted by type. The lambda cases use environment insertion and lifting equations, not semantic transport.

`Equiv.eval_eq` holds for every typed conversion and every environment. Its eta case uses ordinary `funext` and environment cancellation. There is no `Family.Fn.ext`, `.run Ren.id`, or naturality field. Quoting equal values at zero gives normalization invariance.

### Sound readback still needs a new relation

Ordinary function types contain functions that do not represent object-language terms. Do not claim every `Val s` is denotable, or that quote/reflect are mutual inverses for arbitrary functions. Establish the necessary correspondence for evaluator-generated values using a logical relation.

Let `d ≤ k` be pointwise comparison of depths. Let `W(d,k,e)` be syntactic renaming that adds `k s - d s` to each ambient index of sort `s`, lifted under all binders already inside `e`. It preserves `Term s` automatically. Prove identity and composition for increasing depths.

For `e : Term s` and `n : Residual s`, define:

```text
RepresentsAt d e n :=
  ∀ k ≥ d, Equiv (W(d,k,e)) (n k)
```

No separate sort-correctness clause is needed. A candidate logical relation is:

```text
Related d base e v := RepresentsAt d e v

Related d (s→t) e f :=
  ∀ k ≥ d, ∀ a : Term s, ∀ w : Val s,
    Related k s a w →
    Related k t (app (W(d,k,e)) a) (f w)
```

Keep depth an ordinary argument to the predicate, not an index on `Term` or `Val`. Monotonicity uses the same semantic value:

```text
Related d s e v → Related k s (W(d,k,e)) v, when d ≤ k
```

Prove simultaneously by sort induction:

```text
Related d s e v → Equiv e (quote_s d v)
RepresentsAt d e n → Related d s e (reflect_s n)
```

At arrow quote, extend depth, reflect a fresh zero variable, apply the function relation, quote the codomain result, then use eta and lambda congruence. At arrow reflection, domain readback correctness and application congruence show that delayed application represents the expected syntax at every future depth; invoke codomain reflection correctness.

The ambient residual represents `bound s n` at depth zero. A fundamental theorem relates syntactic substitutions and semantic environments whose assignments are related. Under a lambda, use monotonicity on old assignments and extend both with related arguments. Syntactic beta and lifted-substitution algebra finish the case.

This is substantially closer to the existing `Normalization.lean` proof than the raw-syntax proposal: the sorts remain intrinsic, and there are no compilation witnesses or sorting hypotheses. The important difference is that future depth extension replaces future-context renaming and leaves semantic values unchanged.

### Expected central results

```text
normalize_sound : Equiv e (normalize e)
equiv_iff_normalize_eq : Equiv e f ↔ normalize e = normalize f
normalize_idempotent : normalize (normalize e) = normalize e
```

They hold for all `e f : Term s`, including ambient indexed variables. Decide `Equiv` by structural equality of normalizations, as currently. Typed normalization has no failure case, so the earlier warning about equating two `none` results disappears from the core; it still matters for public named APIs.

### Shape and scope are additional invariants

The conversion-based relation permits residuals with redexes, so it does not itself prove normal-form shape. Define `Neutral` and sort-directed `Normal` predicates on `Term s`, and a semantic readiness predicate if needed. Show the specific reflected variables/constants used by evaluation are ready and evaluation preserves readiness. Do not assert that reflecting arbitrary syntax normalizes it.

Prove local closure preservation separately. Well-sorted open terms are all legitimate core inputs, but the named boundary needs to know no ambient indexed variables were introduced into a translated named term. Type preservation no longer needs a theorem; local closure still does.

The phase gate must include a Lean-checked soundness/canonicality proof for the complete higher-order sort grammar. A working evaluator on examples does not establish that this proof architecture is simpler or even correctly specified.

## 7. Named and existing nameless interfaces

`Lisa.NamelessExpr` in [../Conversion.lean](../Conversion.lean) currently counts **every binder**, irrespective of sort. Its syntax contributes to the original `AlphaEq` specification. The new syntax counts only same-sort binders.

```text
λ(_:prop). λ(_:ind). outerProp
current global index: 1, sort prop
new per-sort index:   0, sort prop
```

Keep this original specification unchanged during the rewrite. Its numeric indices cannot be silently reinterpreted. Provide an explicit adapter where the old format is needed:

1. Global-to-per-sort: look up the global binder position, validate its annotated sort, count preceding binders of that sort.
2. Per-sort-to-global: select the n-th binder of the requested sort in an ordinary stack.

The reverse can fail for ambient indices; it succeeds under a scope predicate matching the supplied stack. Interleaving of unknown ambient sorts is not reconstructible from a per-sort index alone.

The adapter stack is ordinary data at a format boundary, not a context index in the new core. The old `compareNameless Γ` behavior can be preserved with a compatibility wrapper accepting this data. If such clients are unnecessary, isolate/remove those wrappers after migration rather than changing the alpha specification preemptively.

Direct named interpretation becomes:

```text
Names = (x : SVar) → Term x.sort
Packed.Expr = Σ s, Term s
interpretNamed : Lisa.Expr → Names → Option Packed.Expr
```

These are the existing interfaces with `Γ` removed. `Packed.app` still checks source application sorts; that boundary check is genuinely necessary because `Lisa.Expr` permits malformed applications. A failed body still produces a failed lambda interpretation.

Consequently, the earlier plan's proposal to delete `Packed`, `ResultEquiv`, and the optional named interpreter is **withdrawn**. Retaining them is a simple way to preserve proofs about arbitrary original conversions, including malformed bodies/wrappers. A raw auxiliary translation could replace them, but would add another syntax and is not recommended.

## 8. Declaration-by-declaration audit

All sixteen `.lean` files are covered below. Grouped rows assign the stated action to each listed declaration. Constructors/generated projections are covered with their enclosing definitions; derived instances are called out. Names are relative to `Lisa.Lambda` except explicitly named `Lisa.Subst` lemmas.

**Retain** means preserve the role and usually much of the proof, while removing context arguments. **Replace** means redesign the declaration/proof. **Remove** means it is absent from the target architecture; required behavior must still be preserved elsewhere.

### 8.1 Syntax.lean

Source: [Syntax.lean](Syntax.lean).

| Declaration | Revised disposition |
|---|---|
| `Var`, `here`, `there` | Remove the context-indexed variable datatype. Use per-sort numeric indices. |
| `Term`, `bound`, `free`, `const`, `app`, `lam` | Replace by `Term s` above. Keep intrinsic application/result sorting; remove only binder-context indices. |
| `Ren` | Retain as `LSort → Nat → Nat`. |
| `Ren.id`, `Ren.comp` | Retain pointwise identity/composition. |
| `Ren.lift` | Replace by sort-specific zero/successor lifting. |
| `Ren.lift_here`, `Ren.lift_there` | Replace by same-sort zero/successor equations; add different-sort equation. |
| `Ren.lift_id`, `Ren.lift_comp` | Retain, splitting sort equality and numeric cases instead of dependent `Var` cases. |
| `Term.rename` | Retain typed structural traversal with explicit binder-sort lifting. |
| `Term.rename_id`, `Term.rename_comp` | Retain typed equality statements with no context parameters. |
| `Sub` | Retain intrinsic sorting as `(s : LSort) → Nat → Term s`. No sortedness predicate. |
| `Sub.id`, `Sub.ofRen` | Retain, construct numeric bound variables. |
| `Sub.extend` | Retain sort-specific insertion. Equality-branch casts confined here. |
| `Sub.lift` | Replace by typed sort-specific lift; shift replacement terms even when their result sort differs from the binder sort. |
| `Sub.lift_here`, `Sub.lift_there` | Replace by same-sort equations; add different-sort equation. |
| `Sub.lift_id`, `Sub.lift_ofRen` | Retain with binder sort explicit. |
| `Term.subst` | Retain total typed traversal. |
| `Term.subst_id`, `Term.subst_ofRen` | Retain without extra premises. |
| `Term.rename_subst`, `Term.subst_rename`, `Term.subst_comp` | Retain all; isolate per-sort lift arithmetic in reusable lemmas. |
| `Term.single` | Retain with binder sort determined by the typed argument. |
| `Term.instantiate` | Retain as `Term t → Term s → Term t`, with binder sort `s` understood. |

New: `shift_s`, same/different-sort equations, optional `Scoped`/`LocallyClosed`, indexed support, and their preservation lemmas. No internal `sort`, `HasSort`, `Sub.Sorted`, or extrinsic application-checking infrastructure.

### 8.2 Conversion.lean

Source: [Conversion.lean](Conversion.lean).

| Declaration | Revised disposition |
|---|---|
| `Term.shift_instantiate` | Retain: shift only the instantiated sort's namespace. |
| `Term.instantiate_rename`, `Term.instantiate_subst` | Retain with per-sort maps/lifts. |
| `Equiv`, constructors `refl`, `symm`, `trans`, `app`, `lam`, `beta`, `eta` | Retain intrinsically sorted relation; replace context-bound variables with numeric indices and sort-specific shifts. No new sorting side conditions. |
| `Equiv.reflexive` | Retain. |
| `Equiv.rename` | Retain for all per-sort maps. |
| `Term.instantiate_subst_comp` | Retain. |
| `Equiv.subst` | Retain unconditionally for typed substitutions. |

No need for the previous proposal's core `Equiv.preserves_sort`: both endpoints already have the same sort. Scope-sensitive variants remain useful for named reconstruction. Preserve this file's independence from original named syntax and evaluation.

### 8.3 Semantics.lean

Source: [Semantics.lean](Semantics.lean).

| Declaration | Revised disposition |
|---|---|
| `Family`, fields `Obj`, `map`, `map_id`, `map_comp` | Remove. No context-indexed semantic family. |
| `Family.ground` | Remove; typed delayed syntax supplies base values directly. |
| `Family.Fn`, fields `run`, `natural` | Remove; replace by actual Lean function spaces. |
| `Family.Fn.ext` | Remove; ordinary `funext` suffices. |
| `Family.arrow`, `Family.arrow_map_run` | Remove. |
| `Model`, fields `values`, `quote`, `reflect`, `quote_natural`, `reflect_natural` | Remove proof-carrying model structure. Replace by direct sort-recursive definitions; an optional small recursion bundle has no context maps or naturality laws. |
| `Model.ground` | Replace by base semantic type/quote/reflect equations. Ground quote now applies delayed syntax to depth. |
| `Model.arrow` | Replace by ordinary function domain and fresh-level quote/delayed-app reflection. |
| `model` | Remove wrapper; direct recursion on sort. |
| `Val` | Replace `Val Γ s` by `Val s`. |
| `Env` | Replace two-context environment by per-sort indexed assignments into `Val s`. |
| `Env.rename` | Remove semantic transport; add environment precomposition only if useful, clearly distinguished from transport. |
| `Env.extend` | Retain insertion into one sort namespace, no value shifting. |
| `Env.rename_id`, `Env.rename_comp` | Remove old transport statements; any precomposition counterparts are elementary function equalities. |
| `Env.rename_extend` | Replace by insertion/precomposition algebra and different-sort insertion commutation. |
| `evaluation` | Replace proof-carrying evaluator by ordinary structurally recursive `eval`. No compilation layer. |
| `eval` | Retain as direct total evaluator on `Term s`. |
| `eval_natural` | Remove semantic-map statement; evaluation/precomposition and proof-level residual correspondence replace its useful content. |
| `normalize` | Retain total `Term s → Term s`, using ambient environment and root depth. |

New: `Depth`, zero/increment, delayed typed residuals, fresh-level and ambient residuals, direct `quote`/`reflect`, typed environment insertion equations. No sort checker or optional core computation.

### 8.4 Evaluation.lean

Source: [Evaluation.lean](Evaluation.lean).

| Declaration | Revised disposition |
|---|---|
| `eval_bound` | Retain direct typed lookup equation. |
| `eval_free`, `eval_const` | Retain, reflect depth-independent residuals. |
| `eval_app` | Retain, direct function application replaces `.run Ren.id`. |
| `eval_lam_run` | Replace by `eval_lam_apply`, a function applied to a value evaluates the body in an inserted environment. |
| `eval_rename` | Retain environment precomposition; no semantic transport. |
| `eval_subst` | Retain unconditional typed substitution theorem. |
| `Equiv.eval_eq` | Retain for all typed conversions/environments; use ordinary `funext` and environment equations. |
| `normalize_eq_of_equiv` | Retain exactly its mathematical form, quote equal values at zero. |

Expected net simplification: no naturality fields, context quantifiers, compiled-success witnesses, or explicit core sorting hypotheses. Binding insertion/lift equations remain.

### 8.5 Normalization.lean

Source: [Normalization.lean](Normalization.lean).

| Declaration | Revised disposition |
|---|---|
| `Related` | Replace by typed depth-based relation in section 6. No `Γ` or extrinsic sort premises. |
| `Related.congr` | Retain conversion stability. |
| `Related.rename` | Replace by monotonicity/depth-extension with unchanged semantic value. |
| `readback_correct` | Replace simultaneous reflection/readback proof using `RepresentsAt` and fresh-level arithmetic. Main proof risk. |
| `Term.subst_lift_rename` | Retain typed binding algebra; move into binding lemmas if clearer. |
| `fundamental` | Retain logical-relation theorem for a typed substitution and semantic environment; depth replaces target context parameters. |
| `normalize_sound` | Retain unconditional typed statement `Equiv e (normalize e)`. |
| `equiv_iff_normalize_eq` | Retain unconditional statement for `e f : Term s`. |
| `normalize_idempotent` | Retain literal equality, no optional-result premise. |

New: depth extension algebra, residual correspondence, fresh-variable inequalities, local-closure preservation, optional neutral/normal/readiness predicates for shape. Intrinsic sorting eliminates several burdens from the earlier proposal, but soundness is still a new proof, not a text substitution.

### 8.6 Decision.lean

Source: [Decision.lean](Decision.lean).

| Declaration | Revised disposition |
|---|---|
| Derived `DecidableEq Var` | Remove with `Var`; numeric equality already exists. |
| Derived `DecidableEq Term` | Retain at each sort; prototype Lean deriving for the revised indexed datatype. |
| `DecidableRel (@Equiv Γ s)` instance | Retain as `DecidableRel (@Equiv s)`, using canonical equality, with no sorting premise. |

There is no need for the previous proposal's optional core comparison. A heterogeneous `SomeTerm` comparator can check equality of result sorts at the external boundary, as `compareNameless` currently does.

### 8.7 Substitution.lean

Source: [Substitution.lean](Substitution.lean).

| Declaration | Revised disposition |
|---|---|
| `normalize_subst` | Retain its current equation without context parameters or added premises. |
| `normalize_rename` | Retain its current equation without context parameters. |

This should remain a short corollary module. It is a clear improvement over the raw-syntax version of the plan.

### 8.8 Erasure.lean

Source: [Erasure.lean](Erasure.lean).

| Declaration | Revised disposition |
|---|---|
| `Term.index` | Remove; bound variables already contain numeric indices. |
| `Term.erase` | Replace by explicitly named per-sort-to-global format translation with an ordinary binder-sort stack. Optional on arbitrary open terms, proved successful on covered terms. |

Conversion is no longer mere proof erasure: the index convention changes. Add rank/select lemmas. If a new per-sort raw format is separately desired, give it a different name rather than changing `Lisa.NamelessExpr` implicitly. No such extra format is required for this plan.

### 8.9 Elaboration.lean

Source: [Elaboration.lean](Elaboration.lean).

| Declaration | Revised disposition |
|---|---|
| `Var.lookup` | Replace typed global lookup by validated stack lookup plus per-sort rank. No `Var Γ s` witness. |
| `Var.lookup_index`, `Var.lookup_sound` | Replace by rank/select and annotation-validation lemmas. |
| `elaborate` | Retain as optional translation from existing global `NamelessExpr` to `Σ s, Term s`; stack is ordinary data. Application sort checking remains only here/the named boundary. |
| `elaborate_erase` | Retain round trip under stack coverage; totality on all typed terms is lost because ambient indices may not have stack entries. |
| `elaborate_sound` | Retain exact inverse-format theorem for successful global inputs. |
| `normalizeNameless` | Retain compatibility wrapper: validated translation, total typed normalization, checked reverse translation. Prove reverse success for the covered output. |
| `normalizeNameless_erase` | Retain under stack coverage. |
| `normalizeNameless_idempotent` | Retain, using coverage preservation and adapter round trips. |
| `Term.erase_injective` | Replace by injectivity of successful format conversion on terms covered by the same stack. |
| `compareNameless` | Retain wrapper with source validation and same-result-sort check. |
| `compareNameless_erase`, `compareNameless_correct` | Retain for covered typed terms. |
| `NamelessEquiv` | Retain existential same-sort typed witnesses with successful new translations, no context-indexed terms. |
| `compareNameless_true`, `compareNameless_none` | Retain exact legacy behavior, including rejecting invalid global indices/annotations. |
| `normalizeNameless_alpha` | Retain for unchanged original `AlphaEq`. |

Reevaluate production necessity of this module after direct named translation is available. Some existing tests use arbitrary old nameless data; preserve their coverage either through compatibility wrappers or explicitly migrated format tests. Do not weaken rejection expectations.

### 8.10 NamedEnvironment.lean

Source: [NamedEnvironment.lean](NamedEnvironment.lean).

| Declaration | Revised disposition |
|---|---|
| `Names` | Retain as `(x : SVar) → Term x.sort`, only remove `Γ`. No `Names.Sorted` predicate. |
| `Names.free` | Retain typed named free variables. |
| `Names.rename`, `Names.subst` | Retain pointwise typed operations, no contexts. |
| `Names.bind` | Retain selected name → typed zero; shift all other interpretations in the binder's sort namespace. |
| `Names.bind_self`, `Names.bind_other` | Retain with per-sort shift. |
| `Names.bind_rename`, `Names.bind_subst` | Retain with per-sort lifts. |
| `Packed.Expr` | Retain `Σ s, Term s`; remove context parameter. This is useful boundary packaging, not unwanted internal context machinery. |
| `Packed.app` | Retain dynamic result-sort check and its single dependent cast. Necessary for translating raw source applications. |
| `Packed.lam` | Retain, but body and result no longer carry different context indices. |
| `Packed.rename`, `Packed.subst` | Retain thin wrappers on typed operations. |
| `Packed.rename_app`, `Packed.subst_app` | Retain; likely close to current proofs with context variables removed. |
| `interpretNamed` | Retain optional sorted interpretation; binder handling is per-sort. No new raw intermediate syntax. |
| `interpretNamed_support` | Retain free-variable support theorem. |
| `interpretNamed_rename`, `interpretNamed_subst` | Retain commuting statements, with existing `Option.map` structure. |
| `interpretNamed_sort` | Retain exact source-sort inference theorem without extra environment hypotheses. |
| `interpretNamed_sorted` | Retain typed existence witness, now `Term s`. |

New: local closure of canonical named translation and support-sensitive scope preservation for environments. Much of this file is a parameter simplification rather than deletion. The earlier raw plan's removal of `Packed` and `Option` was incompatible with retaining this typed boundary design and is withdrawn.

### 8.11 NamedAlpha.lean

Source: [NamedAlpha.lean](NamedAlpha.lean).

| Declaration | Revised disposition |
|---|---|
| `Names.resolve` | Replace typed contextual substitution through a binder stack by ordinary nearest-name lookup with per-sort rank and typed `Sub`. |
| `Names.resolve_rename` | Retain pointwise compatibility. |
| `Names.resolve_bind` | Retain with sort-specific insertion. |
| `Names.resolve_unbound` | Retain absence from the name stack uses free interpretation. |
| `Names.resolve_bound` | Replace `Var` witness with numeric rank/selection statement; preserve nearest-name shadowing. |
| `interpretNameless` | Retain validated interpretation of original global-index syntax using the adapter stack as data. |
| `interpretNamed_resolve` | Retain commuting theorem establishing agreement with original alpha keys. |
| `interpretNamed_alpha` | Retain under every typed naming environment. |
| `interpretNameless_identity` | Retain identity interpretation/adapter equivalence; original global format still uses stack data. |
| `interpretNamed_free` | Retain canonical named translation equals original erasure followed by validated new elaboration. |
| `elaborate_named_sort` | Retain for named erasure under an ordinary binder stack. |
| `elaborate_named` | Retain successful translation at the original sort, now witness `Term s`. |
| `elaborate_named_none` | Retain exact named sorting-failure characterization. |
| `alpha_iff_interpretNamed_eq` | Retain for sorted inputs; use scoped inverse conversion to recover global alpha keys. |

New: same-sort rank computation and mixed-sort rank/select inverses. The original alpha specification is kept, so this is substantive adapter proof work. Respect `SVar` identity including sort, not just textual identifier.

### 8.12 NamedSubstitution.lean

Source: [NamedSubstitution.lean](NamedSubstitution.lean).

| Declaration | Revised disposition |
|---|---|
| `Lisa.Subst.lookup_without` | Retain unchanged; independent of internal representation. |
| Private `Lisa.Subst.lookup_replace_other`, `lookup_replace_self` | Retain unchanged. |
| `Lisa.Subst.lookup_insert`, `lookup_freeVars` | Retain unchanged. |
| `Represents` | Retain current optional packed correspondence; remove `Γ` only. |
| `interpretNamed_bind_fresh` | Retain; use shift of the newly bound name's sort. |
| `interpretNamed_namedSubst` | Retain complete proof including original capture-avoiding freshening branches. Typed target eliminates any need for new sorting assumptions. |
| `interpretNamed_substOne` | Retain named beta substitution equals typed instantiation; context arguments disappear. |

Expected effect: moderate simplification of target-side dependent bookkeeping, little change to source fresh-name reasoning. Do not predict that changing indices removes the obligation to verify the existing named substitution algorithm.

### 8.13 NamedConversion.lean

Source: [NamedConversion.lean](NamedConversion.lean).

| Declaration | Revised disposition |
|---|---|
| `ResultEquiv`, constructors `none`, `some` | Retain optional same-sort typed relation, no `Γ`. It handles original conversions with ill-sorted bodies/wrappers. |
| `ResultEquiv.refl`, `symm`, `trans` | Retain proofs with contexts removed. |
| `ResultEquiv.app` | Retain sort-check failure propagation. No new conceptual burden. |
| `ResultEquiv.lam` | Retain; source/result terms no longer differ in context indices. |
| `interpretNamed_conversion` | Retain original named conversion → optional typed result equivalence. Beta/eta use revised substitution and shifts. |
| `elaborate_conversion` | Retain consequence through original global-name erasure and new adapter. |
| `compareNameless_of_conversion` | Retain positive comparison for sorted-source named conversions. |
| `not_conversion_of_compareNameless_false` | Retain its consequence. |

Compared with the raw plan, these wrappers now stay. Compared with the current implementation, their shape is familiar and loses context dependence. The core does not need malformed terms to prove statements about malformed source expressions: `ResultEquiv.none` handles them.

### 8.14 Reification.lean

Source: [Reification.lean](Reification.lean).

| Declaration | Revised disposition |
|---|---|
| `Context` | Replace dependent variable-to-name function by ordinary finite per-sort stacks of identifiers. Rename `NameEnv` if `Context` suggests a restored type index. |
| `Context.empty`, `Context.extend` | Retain empty stacks and sort-specific push. |
| `Context.vars` | Retain finite set of names in actual stacks. Do not try to enumerate the range of an arbitrary infinite function from sorts/indices. |
| `Context.mem_vars` | Retain for successful lookup, with finite-stack membership. |
| `Context.vars_extend` | Retain update/set equation. |
| `Context.fresh`, `Context.fresh_not_mem` | Retain deterministic fresh-name policy and proof. |
| `Context.toSub` | Replace by opening substitution agreed on covered references; choose a total extension outside support if needed, but do not claim empty stacks interpret arbitrary ambient indices. |
| `Term.freeVars` | Retain named free support; indexed support tracked separately. |
| `Term.freeVars_rename` | Retain, names unchanged by numeric maps. |
| `Term.reify` | Replace by optional named reconstruction under finite per-sort name stacks. Guaranteed successful on covered terms, sort preserved on success. |
| `Term.reify_sort` | Retain exact successful-output sort theorem. Internal sorting is automatic; optionality comes only from missing names. |
| `Term.reify_freeVars` | Retain named support bound on successful output. |
| `interpretNamed_reify` | Retain typed opening/substitution correspondence; add coverage/lookup premises instead of relying on `Var Γ s`. |
| `interpretNamed_reify_free` | Retain specialization. |

This is the most obvious downstream cost. The current `Γ` makes reconstruction total for an appropriately indexed naming environment. The new syntax allows more open terms, so the finite naming boundary must explicitly cover references. Avoid a global total renaming environment whose infinite range leaves no obviously fresh name; finite support or partial finite stacks are easier to justify.

### 8.15 NamedReflection.lean

Source: [NamedReflection.lean](NamedReflection.lean).

| Declaration | Revised disposition |
|---|---|
| `hasSort_of_interpretNamed` | Retain, inferred from the unchanged source-sort theorem. |
| `alpha_of_interpretNamed_eq` | Retain at canonical named interpretation. |
| Private `reify_under_binder` | Retain with per-sort name insertion, successful reconstruction/coverage premises. |
| `reify_lam_at` | Retain freedom to choose a fresh binder. |
| `reify_rename` | Retain where naming lookup covers mapped support; arbitrary maps can leave a finite stack. |
| `reify_weaken` | Retain safe specialization using matching sort-specific shift/name push. |
| Private `reify_beta`, `reify_eta` | Retain reconstructed original named conversion; freshness and coverage proofs revised. No core sort side conditions. |
| `Equiv.reify` | Retain with a justified opening of the derivation's support or a suitable scope-controlled derivation. Endpoint coverage alone does not ensure every arbitrary conversion intermediate is covered. |
| `Term.subst_empty` | Remove unconditional statement: empty stacks cannot open ambient indices. Replace by identity/opening lemma for locally closed terms. |
| `elaborate_reify` | Retain exact round trip for locally closed typed terms, with successful reconstruction. |
| `alpha_reify_of_elaborate` | Retain for translations of named sources; their local closure is already proved. |
| `conversion_of_compareNameless` | Retain soundness for original named inputs. |
| `compareNameless_iff_conversion` | Retain exact sorted-source named theorem. |

Scope issue requiring care: a symmetric conversion derivation can beta-expand through extra ambient variables even when its endpoints are locally closed. Do not assume every intermediate is locally closed. Two feasible proof strategies are: choose fresh names for the finite support of the entire derivation; or reconstruct the normalization-soundness derivation with explicit scope control rather than using arbitrary `Equiv.reify`. Decide this in the prototype, before promising a short named-reflection migration.

### 8.16 NamedDecision.lean

Source: [NamedDecision.lean](NamedDecision.lean).

| Declaration | Revised disposition |
|---|---|
| `compareNamed` | Retain exact public signature/behavior. Direct canonical named interpretation can avoid the legacy global-index runtime path. |
| `compareNamed_true`, `compareNamed_none`, `compareNamed_false` | Retain exact statements relative to original `Lisa.Conversion` and source sorting. |
| `SortedExpr`, `SortedExpr.Equivalent` | Retain unchanged named-source wrappers. |
| `DecidableRel SortedExpr.Equivalent` | Retain using public comparison theorem. |
| `normalizeNamed` | Retain signature: optional source interpretation → total typed normalization → named reconstruction. Prove no new reconstruction failure on translated inputs. |
| `normalizeNamed_eq` | Revise internal pipeline equation to new `Term s`/naming API; retain a compatibility equation through original erasure if needed. |
| `normalizeNamed_sound`, `normalizeNamed_sort`, `normalizeNamed_none` | Retain exact public statements. |
| `normalizeNamed_reify` | Retain for locally closed terms with successful empty-stack reconstruction. |
| `normalizeNamed_idempotent` | Retain exact public statement, deterministic naming, and output local closure. |
| `conversion_iff_normalizeNamed_eq` | Retain exact current sorted-source statement. Equality of two failed named normalizations is not conversion. |

## 9. New obligations versus deleted obligations

### Delete with context-indexed semantics

- `Family` object maps, identity/composition laws.
- `Family.Fn` future-context arguments and naturality fields.
- `Model` quote/reflect naturality fields.
- Semantic environment transport and its interaction laws.
- Scope-dependent variable witnesses, impossible empty-variable cases, and many context casts.

### Preserve because sorting remains intrinsic

- Typed application and total core normalization.
- Typed `Sub`, `Names`, `Env`, and same-sort conversion.
- Unconditional core soundness, canonicality, and decision statements.
- Existing `Packed`/`ResultEquiv` boundary organization, without `Γ`.

### Add or redesign

- Same-sort numeric zero/successor lifting and different-sort clauses.
- Typed delayed residuals and fresh-level/readback-depth arithmetic.
- A logical relation over ordinary depth data and same semantic values.
- Indexed local-closure/support preservation.
- Coverage-aware fresh naming and round trips.
- Explicit global/per-sort rank/select adapters where preserving old APIs.

An ordinary depth parameter in proofs is not a hidden context index: all terms still have type `Term s` and values `Val s` regardless of that parameter. It is nevertheless genuine bookkeeping and should be counted in the complexity assessment.

## 10. Implementation stages and gates

### Phase 0: freeze contracts and baseline

Keep [../Conversion.lean](../Conversion.lean), the reference calculus, and public checker statements unchanged. Preserve user changes in `COMMENTS.md` and the source files. Record named behavior, serialized-fixture outcomes, assumptions, axiom reports, and representative normalization timings.

### Phase 1: typed per-sort syntax and algebra

Create an experimental namespace/module tree beside production. Implement `Term s`, per-sort maps/substitutions, and independent `Equiv`. Gate: all identity/composition/instantiation lemmas proved; no context index or added sort premises; capture tests include replacement terms containing variables of other sorts.

### Phase 2: direct semantic functions

Implement `Val`, residuals, quote/reflect, environments, and total evaluation. Gate: Lean accepts total structural definitions without `partial`, `unsafe`, fuel, new axioms, or an executable dependency on the old normalizer. Test higher-order arrow-sort binders immediately.

### Phase 3: decisive proof prototype

Complete evaluation invariance, residual correspondence, fresh-level inequalities, logical relation, readback correctness, fundamental theorem, and:

```text
Equiv e (normalize e)
Equiv e f ↔ normalize e = normalize f
normalize (normalize e) = normalize e
```

Also establish local-closure preservation, and a route to scope-controlled named reconstruction. Prove or explicitly schedule normal-form shape/readiness lemmas. Gate: the complete sort grammar, not just first-order examples; axiom audit matches current trust expectations.

Reevaluate simplicity at this point by reading `Semantics`, `Evaluation`, and `Normalization` together. If proof complexity outweighs deleted machinery, stop and revise before porting all named modules. Do not restore `Family` under another name while claiming it disappeared.

### Phase 4: named boundary and compatibility

Port `Names`/`Packed`/`ResultEquiv`, alpha and named substitution correspondence, naming reconstruction, and both conversion directions. Implement legacy global adapters only where needed. Gate: public true/false/none and named normalization theorems exactly recovered; capture/shadowing/sort-name collisions remain covered.

### Phase 5: integrate the checker

[../Combined/Lambda.lean](../Combined/Lambda.lean) mainly uses `normalizeNamed_sound`, `normalizeNamed_idempotent`, `normalizeNamed_none`, and `conversion_iff_normalizeNamed_eq`. Keep these statements unchanged and preserve malformed-source fallback behavior. Existing validity certificates must still refer to the unchanged original calculus.

Gate: all configured library/tests build, combined/cache behavior agrees, serialized original proofs retain validity and assumption counts. Explain any changed result against the reference theorem, not by silently updating expectations.

### Phase 6: remove old code and update documentation

Only after proof/integration gates, remove old context-indexed runtime dependencies. Keep old/new implementations available for differential testing during the migration; do not make the old normalizer part of the new production execution path. Update [README.md](README.md) when implementation changes, not now.

Possible final structure keeps the current file roles, with `Erasure`/`Elaboration` optionally consolidated as `LegacyNameless` and binding arithmetic optionally extracted to `Binding`. File merging is secondary to conceptual simplification.

## 11. Verification details

| Area | Evidence required |
|---|---|
| Binding algebra | Shift/instantiate cancellation; rename/subst identity and composition; cross-sort replacement capture |
| Scope | Canonical named translation locally closed; normalize preserves local closure; empty-stack reconstruction succeeds |
| Open variables | Different ambient indices remain distinct; beta removes only its sort's binder |
| Higher order | Bind/read back variables of arrow sorts; functions taking functions; opaque higher-order constants |
| Eta | Nested same-sort and mixed-sort eta expansion; no symbolic-level aliasing |
| Alpha | Shadowing; same identifier with different sorts; unchanged global alpha-key correspondence |
| Named substitution | Existing capture and nested-freshening regressions; duplicate association lookup semantics |
| Legacy input | Rank/select inverses; wrong global annotation and out-of-range index rejection |
| Normalization | Core soundness/canonicality/idempotence and normal-form shape; named equivalents |
| Trust | `#print axioms` for core/named central results; no new normalization axioms or admitted goals |
| Dependencies | Conversion core remains independent of named syntax and evaluator; production avoids optional reference theories |
| Checker | Combined, cache, and serialized corpus tests, assumptions and closedness unchanged |
| Performance | Same toolchain/inputs, measure normalization, compilation time, checker wall time and memory |

Directly affected tests: `Tests/LambdaCore.lean`, `Tests/NamedIntegration.lean`, `Tests/NamedDecision.lean`, and the pipeline equation in `Tests/CombinedCore.lean`. Update typed constructors and scope-sensitive APIs, retain mathematical cases. Conversion-order, expression-normalization, combined, cached, and serialized-corpus tests remain integration gates.

Use bounded generated named syntax to compare old/new comparison results and normalization idempotence, including malformed cases. This is regression evidence, not the correctness proof. Acceptance equivalence also follows from both implementations' proofs against the same `Lisa.Conversion`. Exact normalized named output equality is a separate naming-policy question.

Preserve the current deterministic fresh-name policy if practical, including the existing `freeX1` exact-output regression. If output names change, prove canonical named equality and compare alpha/conversion classes before deliberately adjusting only name-specific fixtures.

## 12. Revised simplicity assessment

| Area | Compared with current implementation | Compared with the previous raw plan |
|---|---|---|
| Syntax | No `Γ` or dependent `Var`; numeric per-sort arithmetic added | Intrinsic application typing restored |
| Substitution | Fewer context transports; sort-equality branches remain | No sorted-assignment predicates/proofs |
| Semantic definitions | Ordinary arrows; no `Family`, Kripke `run`, naturality fields | No compilation or dynamic core typing |
| Evaluation proof | Ordinary application and environment algebra | No successful-compilation witnesses or sort alignment hypotheses |
| Normalization proof | Depth correspondence replaces context transport | Typed relation, unconditional core results, fewer auxiliary invariants |
| Named interpretation | Mostly same organization, `Γ` removed | Keep familiar `Packed`/`ResultEquiv`; no extra raw syntax |
| Named substitution | Original freshening still needs proof | No new target sorting assumptions |
| Reification | Coverage/local-closure premises added | Typed output sort is automatic before named reconstruction |
| Legacy adapters | Extra global/per-sort translation | Essentially unchanged from earlier plan |
| Runtime | Potential wrapper reduction, but delayed printing may cost | No new core sorting pass |

**My revised judgment:** this version is more likely to simplify the whole package than the raw proposal. It removes one axis of dependence while keeping a useful invariant that the rest of the package already exploits. It is especially promising for `Syntax`, `Semantics`, and `Evaluation`.

It does not make later files cost-free. `Normalization` needs a redesigned proof, and `Reification`/`NamedReflection` need explicit scope handling. Named alpha and legacy-format correspondence still require binder traversal data. None is an identified mathematical obstruction, but both proof effort and actual net readability remain to be established by the phase-3 prototype.

Do not predict a performance improvement merely from erasing context parameters: Lean already erases much of the current proof/index machinery. Delayed residuals may duplicate readback; sort equality and depth updates cost work. First optimize for a clear correct implementation, then benchmark.

## 13. Reference context

The migration audit is based on all current declarations in the sixteen linked Lambda source files, including private named-substitution/reification lemmas and derived/explicit instances. This plan's typed per-sort delayed-residual variant is a proposed construction to verify, not an already checked external implementation.

- [PLFA: DeBruijn](https://plfa.github.io/DeBruijn/) illustrates context-indexed typed syntax and variable maps, useful for comparing the machinery removed here.
- [Emmanuel Suárez Acevedo: Normalization by Evaluation](https://emmanueljs1.github.io/nbe/NbE.html) is a mechanized context-aware development illustrating relevant NbE proof obligations; it does not establish this proposed context-free variant.
- [Marcelo Fiore: Semantic Analysis of Normalisation by Evaluation for Typed Lambda Calculus](https://arxiv.org/abs/2207.08777) provides semantic background, not validation of the proposed Lean definitions.
