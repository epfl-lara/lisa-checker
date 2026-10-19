# Declaration role audit

This accompanies [the revised plan](PLAN.md). It inventories the 16 baseline modules to preserve their mathematical roles while allowing signature and representation changes. It supersedes the previous exact-migration checklist. The dispositions below are implemented and the complete test build passes. A checked item means its role has been retained, adapted, or explicitly removed as described; it does not mean every old identifier remains. Source line numbers identify the read-only audit baseline; they are not proposed dependencies in the new package.

?Adapt? means retain the role with a proved new statement. Equivalent consequences may share one theorem. Removing a representation-specific helper does not require a compatibility alias. The raw input language now admits sorted ambient variables, so finite-stack rejection and its lookup infrastructure are intentionally absent. Named malformed-input behavior and shared-conversion contracts remain required.

## Syntax.lean

- [x] `Var` (line 8): Remove context membership; sorted numeric references replace its role. **Implemented by:** Sorted numeric references in Term.
- [x] `Term` (line 13): Adapt; preserve this mathematical/computational role.
- [x] `Ren` (line 20): Adapt; preserve this mathematical/computational role.
- [x] `id` (line 24): Adapt; preserve this mathematical/computational role.
- [x] `comp` (line 26): Adapt; preserve this mathematical/computational role.
- [x] `lift` (line 28): Adapt; preserve this mathematical/computational role.
- [x] `lift_here` (line 32): Replace by zero, successor, and different-sort lifting equations. **Implemented by:** Ren.lift_zero / Sub.lift_zero.
- [x] `lift_there` (line 34): Replace by successor and different-sort equations. **Implemented by:** lift_succ / lift_other equations.
- [x] `lift_id` (line 37): Adapt; preserve this mathematical/computational role.
- [x] `lift_comp` (line 41): Adapt; preserve this mathematical/computational role.
- [x] `rename` (line 51): Adapt; preserve this mathematical/computational role.
- [x] `rename_id` (line 58): Adapt; preserve this mathematical/computational role.
- [x] `rename_comp` (line 63): Adapt; preserve this mathematical/computational role.
- [x] `Sub` (line 71): Adapt; preserve this mathematical/computational role.
- [x] `id` (line 75): Adapt; preserve this mathematical/computational role.
- [x] `ofRen` (line 77): Adapt; preserve this mathematical/computational role.
- [x] `extend` (line 79): Adapt; preserve this mathematical/computational role.
- [x] `lift` (line 84): Adapt; preserve this mathematical/computational role.
- [x] `lift_here` (line 88): Replace by zero, successor, and different-sort lifting equations. **Implemented by:** Ren.lift_zero / Sub.lift_zero.
- [x] `lift_there` (line 91): Replace by successor and different-sort equations. **Implemented by:** lift_succ / lift_other equations.
- [x] `lift_id` (line 94): Adapt; preserve this mathematical/computational role.
- [x] `lift_ofRen` (line 98): Adapt; preserve this mathematical/computational role.
- [x] `subst` (line 108): Adapt; preserve this mathematical/computational role.
- [x] `subst_id` (line 115): Adapt; preserve this mathematical/computational role.
- [x] `subst_ofRen` (line 120): Adapt; preserve this mathematical/computational role.
- [x] `rename_subst` (line 126): Adapt; preserve this mathematical/computational role.
- [x] `subst_rename` (line 140): Adapt; preserve this mathematical/computational role.
- [x] `subst_comp` (line 150): Adapt; preserve this mathematical/computational role.
- [x] `single` (line 164): Adapt; preserve this mathematical/computational role.
- [x] `instantiate` (line 168): Adapt; preserve this mathematical/computational role.

## Conversion.lean

- [x] `shift_instantiate` (line 7): Adapt; preserve this mathematical/computational role.
- [x] `instantiate_rename` (line 12): Adapt; preserve this mathematical/computational role.
- [x] `instantiate_subst` (line 19): Adapt; preserve this mathematical/computational role.
- [x] `Equiv` (line 31): Adapt; preserve this mathematical/computational role.
- [x] `reflexive` (line 45): Adapt; preserve this mathematical/computational role.
- [x] `rename` (line 47): Adapt; preserve this mathematical/computational role.
- [x] `Term.instantiate_subst_comp` (line 63): Adapt; preserve this mathematical/computational role.
- [x] `Equiv.subst` (line 73): Adapt; preserve this mathematical/computational role.

## Semantics.lean

- [x] `Family` (line 6): Remove semantic context family; direct Val replaces its computational role.
- [x] `ground` (line 18): Replace ground family/model construction by residual values and direct readback.
- [x] `Fn` (line 25): Remove; arrow values are ordinary functions.
- [x] `Fn.ext` (line 30): Remove wrapper extensionality; use funext.
- [x] `arrow` (line 38): Replace arrow family/model construction by function types and recursive quote/reflect.
- [x] `arrow_map_run` (line 46): Remove semantic transport equation.
- [x] `Model` (line 53): Remove transport bundle; use direct typed quote/reflect.
- [x] `ground` (line 66): Replace ground family/model construction by residual values and direct readback.
- [x] `arrow` (line 74): Replace arrow family/model construction by function types and recursive quote/reflect.
- [x] `model` (line 93): Replace by structural Val and readback definitions.
- [x] `Val` (line 98): Adapt; preserve this mathematical/computational role.
- [x] `Env` (line 99): Adapt; preserve this mathematical/computational role.
- [x] `rename` (line 103): Remove semantic context transport; retain syntactic renaming via environment precomposition.
- [x] `extend` (line 106): Adapt; preserve this mathematical/computational role.
- [x] `rename_id` (line 110): Remove semantic transport law.
- [x] `rename_comp` (line 114): Remove semantic transport law.
- [x] `rename_extend` (line 119): Remove semantic transport law; prove ordinary extension equations.
- [x] `evaluation` (line 128): Replace proof-carrying wrapper by direct structural eval.
- [x] `eval` (line 162): Adapt; preserve this mathematical/computational role.
- [x] `eval_natural` (line 164): Remove context-transport statement; eval_rename preserves the distinct syntactic obligation.
- [x] `normalize` (line 169): Adapt; preserve this mathematical/computational role.

## Evaluation.lean

- [x] `eval_bound` (line 8): Adapt; preserve this mathematical/computational role.
- [x] `eval_free` (line 11): Adapt; preserve this mathematical/computational role.
- [x] `eval_const` (line 14): Adapt; preserve this mathematical/computational role.
- [x] `eval_app` (line 17): Adapt; preserve this mathematical/computational role.
- [x] `eval_lam_run` (line 20): Replace by ordinary function-application equation. **Implemented by:** eval_lam_apply.
- [x] `eval_rename` (line 24): Adapt; preserve this mathematical/computational role.
- [x] `eval_subst` (line 39): Adapt; preserve this mathematical/computational role.
- [x] `Equiv.eval_eq` (line 59): Adapt; preserve this mathematical/computational role.
- [x] `normalize_eq_of_equiv` (line 84): Adapt; preserve this mathematical/computational role.

## Normalization.lean

- [x] `Related` (line 6): Adapt; preserve this mathematical/computational role.
- [x] `congr` (line 14): Adapt; preserve this mathematical/computational role.
- [x] `rename` (line 23): Replace semantic transport by depth monotonicity and syntactic weakening equations.
- [x] `readback_correct` (line 35): Adapt; preserve this mathematical/computational role.
- [x] `subst_lift_rename` (line 53): Adapt; preserve this mathematical/computational role. **Implemented by:** Term.subst_lift_rename.
- [x] `fundamental` (line 68): Adapt; preserve this mathematical/computational role.
- [x] `normalize_sound` (line 93): Adapt; preserve this mathematical/computational role.
- [x] `equiv_iff_normalize_eq` (line 100): Adapt; preserve this mathematical/computational role.
- [x] `normalize_idempotent` (line 107): Adapt; preserve this mathematical/computational role.

## Decision.lean

- [x] `(anonymous instance)` (line 9): Adapt; preserve this mathematical/computational role.

## Substitution.lean

- [x] `normalize_subst` (line 6): Adapt; preserve this mathematical/computational role.
- [x] `normalize_rename` (line 11): Adapt; preserve this mathematical/computational role.

## Erasure.lean

- [x] `index` (line 8): Remove conversion from context membership to all-binders index; the new index is already numeric.
- [x] `erase` (line 13): Retain as unconditional structural erasure into matching per-sort RawTerm.

## Elaboration.lean

- [x] `lookup` (line 9): Remove finite-stack membership lookup; raw indexed variables elaborate directly.
- [x] `lookup_index` (line 14): Obsolete with stack lookup removed; no replacement index conversion is needed.
- [x] `lookup_sound` (line 19): Obsolete with stack lookup removed; raw round trips retain their independent correctness role.
- [x] `elaborate` (line 39): Adapt to RawTerm; check application sorts and admit ambient sorted indices.
- [x] `elaborate_erase` (line 57): Retain unconditional round trip; no scope premise.
- [x] `elaborate_sound` (line 67): Retain exact successful raw round trip; no stack parameter.
- [x] `normalizeNameless` (line 115): Adapt; preserve this mathematical/computational role.
- [x] `normalizeNameless_erase` (line 118): Adapt; preserve this mathematical/computational role.
- [x] `normalizeNameless_idempotent` (line 123): Adapt; preserve this mathematical/computational role.
- [x] `Term.erase_injective` (line 134): Retain unconditional injectivity at fixed result sort.
- [x] `compareNameless` (line 140): Adapt; preserve this mathematical/computational role.
- [x] `compareNameless_erase` (line 145): Adapt; preserve this mathematical/computational role.
- [x] `compareNameless_correct` (line 149): Adapt; preserve this mathematical/computational role.
- [x] `NamelessEquiv` (line 154): Adapt; preserve this mathematical/computational role.
- [x] `compareNameless_true` (line 159): Adapt; preserve this mathematical/computational role.
- [x] `compareNameless_none` (line 180): Adapt; preserve this mathematical/computational role.
- [x] `normalizeNameless_alpha` (line 193): Express alpha-invariance through successful named interpretation and the shared typed comparator; relocate after the named alpha bridge. **Implemented by:** normalizeNamed_alpha and interpretNamed_alpha, expressed at the named boundary.

## NamedEnvironment.lean

- [x] `Names` (line 8): Adapt; preserve this mathematical/computational role.
- [x] `free` (line 12): Adapt; preserve this mathematical/computational role.
- [x] `rename` (line 14): Adapt; preserve this mathematical/computational role.
- [x] `subst` (line 16): Adapt; preserve this mathematical/computational role.
- [x] `bind` (line 19): Adapt; preserve this mathematical/computational role.
- [x] `bind_self` (line 23): Adapt; preserve this mathematical/computational role.
- [x] `bind_other` (line 26): Adapt; preserve this mathematical/computational role.
- [x] `bind_rename` (line 30): Adapt; preserve this mathematical/computational role.
- [x] `bind_subst` (line 38): Adapt; preserve this mathematical/computational role.
- [x] `Expr` (line 50): Adapt; preserve this mathematical/computational role.
- [x] `app` (line 52): Adapt; preserve this mathematical/computational role.
- [x] `lam` (line 57): Adapt; preserve this mathematical/computational role.
- [x] `rename` (line 60): Adapt; preserve this mathematical/computational role.
- [x] `subst` (line 63): Adapt; preserve this mathematical/computational role.
- [x] `rename_app` (line 66): Adapt; preserve this mathematical/computational role.
- [x] `subst_app` (line 77): Adapt; preserve this mathematical/computational role.
- [x] `interpretNamed` (line 91): Adapt; preserve this mathematical/computational role.
- [x] `interpretNamed_support` (line 101): Adapt; preserve this mathematical/computational role.
- [x] `interpretNamed_rename` (line 121): Adapt; preserve this mathematical/computational role.
- [x] `interpretNamed_subst` (line 136): Adapt; preserve this mathematical/computational role.
- [x] `interpretNamed_sort` (line 151): Adapt; preserve this mathematical/computational role.
- [x] `interpretNamed_sorted` (line 182): Adapt; preserve this mathematical/computational role.

## NamedAlpha.lean

- [x] `resolve` (line 8): Adapt binder-name resolution; retain only helpers needed by the alpha correspondence proof.
- [x] `resolve_rename` (line 14): Adapt; preserve this mathematical/computational role.
- [x] `resolve_bind` (line 26): Adapt; preserve this mathematical/computational role.
- [x] `resolve_unbound` (line 36): Adapt; preserve this mathematical/computational role.
- [x] `resolve_bound` (line 46): Adapt; preserve this mathematical/computational role.
- [x] `interpretNameless` (line 67): Use a local generalized interpreter for shared alpha keys if needed; keep it distinct from public RawTerm elaboration. **Implemented by:** AlphaKey.interpret (proof helper).
- [x] `interpretNamed_resolve` (line 82): Adapt; preserve this mathematical/computational role. **Implemented by:** AlphaKey.interpret_resolve.
- [x] `interpretNamed_alpha` (line 101): Adapt; preserve this mathematical/computational role.
- [x] `interpretNameless_identity` (line 112): Replace old finite-stack elaborator identity by the needed direct-interpretation correspondence; do not rebuild a public global-index elaborator. **Implemented by:** No public shared-format elaborator; matching raw identity is elaborate_erase.
- [x] `interpretNamed_free` (line 139): Preserve named interpretation agreement with its chosen raw encoding if exposed; old global-stack pipeline equality is not required. **Implemented by:** Direct Names.free interpretation and alpha_iff_interpretNamed_eq; no second runtime pipeline.
- [x] `elaborate_named_sort` (line 145): Reuse direct interpretNamed_sort; do not duplicate sorting solely for the old global-index pipeline. **Implemented by:** interpretNamed_sort.
- [x] `elaborate_named` (line 151): Reuse successful direct interpretation of sorted named terms. **Implemented by:** interpretNamed_sorted.
- [x] `elaborate_named_none` (line 164): Derive exact named failure from direct interpretation sorting. **Implemented by:** interpretNamed_none.
- [x] `alpha_iff_interpretNamed_eq` (line 171): Adapt; preserve this mathematical/computational role.

## NamedSubstitution.lean

- [x] `lookup_without` (line 6): Adapt; preserve this mathematical/computational role.
- [x] `lookup_replace_other` (line 14): Adapt; preserve this mathematical/computational role.
- [x] `lookup_replace_self` (line 22): Adapt; preserve this mathematical/computational role.
- [x] `lookup_insert` (line 32): Adapt; preserve this mathematical/computational role.
- [x] `lookup_freeVars` (line 45): Adapt; preserve this mathematical/computational role.
- [x] `Represents` (line 62): Adapt; preserve this mathematical/computational role.
- [x] `interpretNamed_bind_fresh` (line 68): Adapt; preserve this mathematical/computational role.
- [x] `interpretNamed_namedSubst` (line 77): Adapt; preserve this mathematical/computational role.
- [x] `interpretNamed_substOne` (line 144): Adapt; preserve this mathematical/computational role.

## NamedConversion.lean

- [x] `ResultEquiv` (line 7): Adapt; preserve this mathematical/computational role.
- [x] `refl` (line 13): Adapt; preserve this mathematical/computational role.
- [x] `symm` (line 18): Adapt; preserve this mathematical/computational role.
- [x] `trans` (line 23): Adapt; preserve this mathematical/computational role.
- [x] `app` (line 29): Adapt; preserve this mathematical/computational role.
- [x] `lam` (line 47): Adapt; preserve this mathematical/computational role.
- [x] `interpretNamed_conversion` (line 56): Adapt; preserve this mathematical/computational role.
- [x] `elaborate_conversion` (line 79): Adapt conversion preservation to direct typed results and matching raw interpretation where exposed. **Implemented by:** interpretNamed_conversion.
- [x] `compareNameless_of_conversion` (line 84): Retain positive-comparison consequence using interpreted terms and the shared packed comparator. **Implemented by:** compareNamed_true, reverse implication, via Packed.compare_true.
- [x] `not_conversion_of_compareNameless_false` (line 98): Retain negative-comparison consequence using the new comparison boundary. **Implemented by:** compareNamed_false.

## Reification.lean

- [x] `Context` (line 8): Use finite-range sorted-index naming assignment with explicit reserved identifiers; no context type parameter.
- [x] `empty` (line 12): Adapt; preserve this mathematical/computational role.
- [x] `extend` (line 14): Adapt; preserve this mathematical/computational role.
- [x] `vars` (line 18): Replace by finite used identifiers, which supply the freshness bound. **Implemented by:** Context.used, now a finite identifier set for each sort.
- [x] `mem_vars` (line 22): Replace by the lookup-membership guarantee for reserved identifiers. **Implemented by:** Context.lookup_mem.
- [x] `vars_extend` (line 27): Replace by the reserved-identifier insertion equation. **Implemented by:** Context.extend.used defining equation.
- [x] `fresh` (line 31): Adapt; preserve this mathematical/computational role.
- [x] `fresh_not_mem` (line 34): Adapt; preserve this mathematical/computational role.
- [x] `toSub` (line 40): Adapt; preserve this mathematical/computational role.
- [x] `freeVars` (line 46): Adapt; preserve this mathematical/computational role.
- [x] `freeVars_rename` (line 53): Adapt; preserve this mathematical/computational role.
- [x] `reify` (line 58): Adapt; preserve this mathematical/computational role.
- [x] `reify_sort` (line 67): Adapt; preserve this mathematical/computational role.
- [x] `reify_freeVars` (line 74): Adapt the bound to source free names plus reserved context identifiers; do not claim injectivity.
- [x] `interpretNamed_reify` (line 102): Adapt; preserve this mathematical/computational role.
- [x] `interpretNamed_reify_free` (line 139): Adapt; preserve this mathematical/computational role.

## NamedReflection.lean

- [x] `hasSort_of_interpretNamed` (line 5): Adapt; preserve this mathematical/computational role.
- [x] `alpha_of_interpretNamed_eq` (line 10): Adapt; preserve this mathematical/computational role.
- [x] `reify_under_binder` (line 16): Adapt; preserve this mathematical/computational role.
- [x] `reify_lam_at` (line 34): Adapt; preserve this mathematical/computational role.
- [x] `reify_rename` (line 42): Adapt; preserve this mathematical/computational role.
- [x] `reify_weaken` (line 48): Adapt; preserve this mathematical/computational role.
- [x] `reify_beta` (line 52): Adapt; preserve this mathematical/computational role.
- [x] `reify_eta` (line 70): Adapt; preserve this mathematical/computational role.
- [x] `Equiv.reify` (line 82): Adapt; preserve this mathematical/computational role.
- [x] `Term.subst_empty` (line 108): Replace by invariance under every indexed substitution for complete named-source interpretations. **Implemented by:** subst_of_interpretNamed for every indexed substitution.
- [x] `elaborate_reify` (line 114): Replace by general interpretation/reification-as-substitution and its named-source specialization. **Implemented by:** interpretNamed_reify_free and subst_of_interpretNamed for named-source inputs.
- [x] `alpha_reify_of_elaborate` (line 119): Retain alpha reconstruction from successful direct named interpretation. **Implemented by:** alpha_reify_of_interpretNamed.
- [x] `conversion_of_compareNameless` (line 127): Retain reflection of successful typed/raw comparison of named interpretations. **Implemented by:** compareNamed_true, forward implication, via Packed.compare_true.
- [x] `compareNameless_iff_conversion` (line 135): Retain both comparison/conversion directions using the new boundary. **Implemented by:** compareNamed_true and its sorted-source specialization.

## NamedDecision.lean

- [x] `compareNamed` (line 6): Compare typed normalizations through the reusable packed comparator.
- [x] `compareNamed_true` (line 10): Adapt; preserve this mathematical/computational role.
- [x] `compareNamed_none` (line 23): Adapt; preserve this mathematical/computational role.
- [x] `compareNamed_false` (line 29): Adapt; preserve this mathematical/computational role.
- [x] `SortedExpr` (line 50): Adapt; preserve this mathematical/computational role.
- [x] `SortedExpr.Equivalent` (line 52): Adapt; preserve this mathematical/computational role.
- [x] `(anonymous instance)` (line 54): Adapt; preserve this mathematical/computational role.
- [x] `normalizeNamed` (line 59): Adapt; preserve this mathematical/computational role.
- [x] `normalizeNamed_eq` (line 63): State the new direct-interpretation pipeline equation; do not preserve the old global-stack pipeline as a second implementation. **Implemented by:** normalizeNamed is directly the stated interpretation/normalization/reification pipeline; no alternate pipeline equation.
- [x] `normalizeNamed_sound` (line 70): Adapt; preserve this mathematical/computational role.
- [x] `normalizeNamed_sort` (line 80): Adapt; preserve this mathematical/computational role.
- [x] `normalizeNamed_none` (line 83): Adapt; preserve this mathematical/computational role.
- [x] `normalizeNamed_reify` (line 87): Generalize to normalize the substituted term produced by reification; derive named-source specialization.
- [x] `normalizeNamed_idempotent` (line 92): Retain exact named idempotence via normalization/substitution and source invariance, without a scope framework.
- [x] `conversion_iff_normalizeNamed_eq` (line 103): Adapt; preserve this mathematical/computational role.

## Constructors, fields, instances, and new work

- [x] Preserve all five typed term constructors and intrinsic application sorting; remove context-membership constructors.
- [x] Preserve all seven independent conversion constructors.
- [x] Preserve interpretation-result failure/success distinction; share packed comparison case analysis.
- [x] Remove Family/Model transport fields and laws; preserve computational reflection/readback and prove their correctness directly.
- [x] Preserve term equality and conversion decidability; numeric references need no separate membership-equality derivation.
- [x] Add matching per-sort RawTerm with structural erasure/application-sort elaboration.
- [x] Add depth residuals, ordinary function values, and the depth logical relation.
- [x] Derive named-source substitution invariance from interpretation/substitution compatibility.
- [x] Add the small finite-range naming context and prove reification as substitution; do not silently claim arbitrary open-term injectivity.
- [x] Prove the named idempotence calculation in the plan; do not substitute an unproved stronger scope assertion.
- [x] Preserve useful simp/reflexivity attributes at new call sites; avoid aliases solely for old signatures.
- [x] Independently validate the named consumer against shared conversion/reference order.
- [x] Measure every implementation helper against the 1,645-nonblank-line baseline; tests/docs remain separate.

Explicit baseline declarations inventoried: 199. This is a coverage audit, not a declaration-count target. All 16 corresponding source modules are implemented. The typed, raw, named, and reducer tests compile, and there are no admitted proofs. See README.md for the measured scope and signature changes.

## Verification outcome

- All three test targets pass: `Lisa.LambdaV2.Tests`, `Lisa.LambdaV2.CoreTests`, and `Lisa.LambdaV2.InterfaceTests`.
- All implementation helpers are within this package and its umbrella; dependency closure contains no other lambda implementation.
- Named-substitution helper lemmas use `Lisa.LambdaV2.NamedSubst`, avoiding duplicate declarations in shared namespaces.
- Main implementation: 16 modules, 1,412 nonblank lines; 1,363 excluding comments. The optional reducer and umbrella add 50 nonblank lines, so the full non-test addition is 1,462 lines.
- Scope changes are explicit: raw ambient indices are accepted; shared alpha keys are handled in proof helpers; finite-range naming interprets ambient variables as a substitution. None weakens the stated named decision/canonicality contracts.
