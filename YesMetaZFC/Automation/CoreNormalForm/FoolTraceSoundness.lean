import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaTraceSoundness
/-!
# FOOL-only normalization trace soundness
本模块在公共 normalization trace/checker 之上建立纯 FOOL 语义回放。与完整的
`FoolLambdaTraceSoundness` 不同，这里的可信边界显式拒绝原生 `apply/lam`，并固定
使用 `Config.foolOnly`，因此模型只需提供 `FoolContract`。
-/
namespace YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics
universe x
namespace Term
theorem eval_mem_of_inferSortWith_fool {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) : ∀ (term : Term) (sort : CoreSort), Term.foolFragment term = true → Term.inferSortWith bound term = some sort → M.sortInterp sort (Term.eval env term)
  | Term.bvar annotated index, sort, _hFragment, hSort => by
      simp only [Term.inferSortWith] at hSort
      cases hLookup : TypeCheck.lookupBound? bound index with
      | none => simp [hLookup] at hSort
      | some expected =>
          simp [hLookup] at hSort
          have hAnnotated : expected = annotated := hSort.1
          have hResult : annotated = sort := hSort.2
          subst expected
          subst sort
          simpa only [Term.eval] using hBound index annotated hLookup
  | Term.fvar annotated id, sort, _hFragment, hSort => by
      simp only [Term.inferSortWith, Option.some.injEq] at hSort
      subst sort
      simpa only [Term.eval] using hFree annotated id
  | Term.app symbol arguments, sort, _hFragment, hSort => by
      simp only [Term.inferSortWith] at hSort
      split at hSort <;> try contradiction
      cases hArgumentSorts : Term.inferSortListWith bound arguments with
      | none => simp [hArgumentSorts] at hSort
      | some argumentSorts =>
          simp [hArgumentSorts] at hSort
          have hResult : symbol.outputSort = sort := hSort.2
          subst sort
          simpa only [Term.eval] using
            contract.function_sort symbol (arguments.map (Term.eval env))
  | Term.apply fn argument, sort, hFragment, hSort => by
      simp [Term.foolFragment] at hFragment
  | Term.bool value, sort, _hFragment, hSort => by
      simp only [Term.inferSortWith, Option.some.injEq] at hSort
      subst sort
      simpa only [Term.eval] using contract.bool_sort value
  | Term.notE body, sort, hFragment, hSort => by
      simp only [Term.inferSortWith] at hSort
      cases hBodySort : Term.inferSortWith bound body with
      | none => simp [hBodySort] at hSort
      | some bodySort =>
          simp [hBodySort] at hSort
          have hBodyBool : bodySort = .bool := hSort.1
          have hResult : CoreSort.bool = sort := hSort.2
          subst bodySort
          subst sort
          simpa only [Term.eval] using contract.not_sort _ <|
            eval_mem_of_inferSortWith_fool contract bound env hBound hFree
              body .bool hFragment hBodySort
  | Term.andE left right, sort, hFragment, hSort
  | Term.orE left right, sort, hFragment, hSort
  | Term.impE left right, sort, hFragment, hSort
  | Term.iffE left right, sort, hFragment, hSort => by
      simp only [Term.foolFragment, Bool.and_eq_true] at hFragment
      simp only [Term.inferSortWith] at hSort
      cases hLeftSort : Term.inferSortWith bound left with
      | none => simp [hLeftSort] at hSort
      | some leftSort =>
          simp only [hLeftSort] at hSort
          cases hRightSort : Term.inferSortWith bound right with
          | none => simp [hRightSort] at hSort
          | some rightSort =>
              simp [hRightSort] at hSort
              have hLeftBool : leftSort = .bool := hSort.1.1
              have hRightBool : rightSort = .bool := hSort.1.2
              have hResult : CoreSort.bool = sort := hSort.2
              subst leftSort
              subst rightSort
              subst sort
              have hLeft :=
                eval_mem_of_inferSortWith_fool contract bound env hBound hFree
                  left .bool hFragment.1 hLeftSort
              have hRight :=
                eval_mem_of_inferSortWith_fool contract bound env hBound hFree
                  right .bool hFragment.2 hRightSort
              simp only [Term.eval]
              first
              | exact contract.and_sort _ _ hLeft hRight
              | exact contract.or_sort _ _ hLeft hRight
              | exact contract.imp_sort _ _ hLeft hRight
              | exact contract.iff_sort _ _ hLeft hRight
  | Term.quote formula, sort, _hFragment, hSort => by
      simp only [Term.inferSortWith] at hSort
      split at hSort
      next =>
        simp only [Option.some.injEq] at hSort
        subst sort
        simpa only [Term.eval] using contract.quote_sort (Formula.eval env formula).holds
      next =>
        simp at hSort
  | Term.lam domain codomain body, sort, hFragment, hSort => by
      simp [Term.foolFragment] at hFragment
  | Term.ite targetSort condition thenTerm elseTerm, sort, hFragment, hSort => by
      simp only [Term.foolFragment, Bool.and_eq_true] at hFragment
      simp only [Term.inferSortWith] at hSort
      split at hSort
      next =>
        simp at hSort
      next =>
        cases hThenSort : Term.inferSortWith bound thenTerm with
        | none => simp [hThenSort] at hSort
        | some thenSort =>
            simp only [hThenSort] at hSort
            cases hElseSort : Term.inferSortWith bound elseTerm with
            | none => simp [hElseSort] at hSort
            | some elseSort =>
                simp [hElseSort] at hSort
                have hThenTarget : thenSort = targetSort := hSort.1.1
                have hElseTarget : elseSort = targetSort := hSort.1.2
                have hResult : targetSort = sort := hSort.2
                subst thenSort
                subst elseSort
                subst sort
                simpa only [Term.eval] using
                  contract.ite_sort targetSort _ _ _
                    (eval_mem_of_inferSortWith_fool contract bound env hBound hFree thenTerm targetSort hFragment.1.2 hThenSort)
                    (eval_mem_of_inferSortWith_fool contract bound env hBound hFree elseTerm targetSort hFragment.2 hElseSort)
theorem eval_eq_of_inferred_bool_holds_iff_fool {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) (left right : Term)
    (hLeftFragment : Term.foolFragment left = true) (hRightFragment : Term.foolFragment right = true) (hLeft : Term.inferSortWith bound left = some .bool) (hRight : Term.inferSortWith bound right = some .bool) (hHolds :
    M.boolHolds (Term.eval env left) ↔ M.boolHolds (Term.eval env right)) : SemanticallyEqual env left right :=
  (contract.bool_extensionality _ _ (eval_mem_of_inferSortWith_fool contract bound env hBound hFree left .bool hLeftFragment hLeft)
    (eval_mem_of_inferSortWith_fool contract bound env hBound hFree right .bool hRightFragment hRight)).mpr hHolds
theorem rewriteRootTerm?_fool_sound {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : Term} {rule :
    StepRule} {resultSort : CoreSort} (hSourceFragment : Term.foolFragment source = true) (hTargetFragment : Term.foolFragment target = true) (hSource : Term.inferSortWith bound source = some resultSort) (hTarget :
    Term.inferSortWith bound target = some resultSort) (hStep : rewriteRootTerm? Config.foolOnly source = some (rule, target)) : SemanticallyEqual env source target := by
  cases source with
  | apply fn argument => simp [rewriteRootTerm?, Config.foolOnly] at hStep
  | notE body =>
      simp only [rewriteRootTerm?, Config.foolOnly] at hStep
      cases body <;> simp at hStep
      next value =>
        rcases hStep with ⟨rfl, rfl⟩
        have hResult : resultSort = .bool := (inferSortWith_notE_parts hSource).1
        subst resultSort
        apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
          hBound hFree
        · exact hSourceFragment
        · exact hTargetFragment
        · exact hSource
        · exact hTarget
        · simp only [Term.eval, contract.not_holds, contract.bool_holds]
          cases value <;> simp
      next formula =>
        rcases hStep with ⟨rfl, rfl⟩
        cases hFormula : Formula.checkWith bound formula <;>
          simp [Term.inferSortWith, hFormula] at hSource
        subst resultSort
        apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
          hBound hFree
        · exact hSourceFragment
        · exact hTargetFragment
        · simp [Term.inferSortWith, hFormula]
        · exact hTarget
        · simp only [Term.eval, contract.not_holds, contract.quote_holds, Formula.eval]
  | andE left right =>
      have hSort : resultSort = .bool := inferSortWith_andE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
        hBound hFree (.andE left right) target
        hSourceFragment hTargetFragment hSource hTarget
      simp only [rewriteRootTerm?, Config.foolOnly] at hStep
      cases left <;> cases right <;>
        simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.and_holds, contract.bool_holds, contract.quote_holds] <;>
        try cases ‹Bool› <;>
        simp_all <;>
        try (split at hStep <;> simp_all)
      all_goals
        try (rcases hStep with ⟨_, hTargetEq⟩ <;> simp_all)
      all_goals
        grind [Term.eval, Formula.eval, contract.and_holds, contract.bool_holds, contract.quote_holds]
  | orE left right =>
      have hSort : resultSort = .bool := inferSortWith_orE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
        hBound hFree (.orE left right) target
        hSourceFragment hTargetFragment hSource hTarget
      simp only [rewriteRootTerm?, Config.foolOnly] at hStep
      cases left <;> cases right <;>
        simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.or_holds, contract.bool_holds, contract.quote_holds] <;>
        try cases ‹Bool› <;>
        simp_all <;>
        try (split at hStep <;> simp_all)
      all_goals
        grind [Term.eval, Formula.eval, contract.or_holds, contract.bool_holds, contract.quote_holds]
  | impE left right =>
      have hSort : resultSort = .bool := inferSortWith_impE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
        hBound hFree (.impE left right) target
        hSourceFragment hTargetFragment hSource hTarget
      simp only [rewriteRootTerm?, Config.foolOnly] at hStep
      cases left <;> cases right <;>
        simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.imp_holds, contract.not_holds, contract.bool_holds, contract.quote_holds] <;>
        try cases ‹Bool› <;>
        simp_all <;>
        try (split at hStep <;> simp_all)
      all_goals
        grind [Term.eval, Formula.eval, contract.imp_holds, contract.not_holds, contract.bool_holds, contract.quote_holds]
  | iffE left right =>
      have hSort : resultSort = .bool := inferSortWith_iffE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
        hBound hFree (.iffE left right) target
        hSourceFragment hTargetFragment hSource hTarget
      simp only [rewriteRootTerm?, Config.foolOnly] at hStep
      cases left <;> cases right <;>
        simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.iff_holds, contract.not_holds, contract.bool_holds, contract.quote_holds] <;>
        try cases ‹Bool› <;>
        simp_all <;>
        try (split at hStep <;> simp_all [Term.eval, contract.iff_holds, contract.not_holds, contract.bool_holds, contract.quote_holds])
      case bool.bool leftValue rightValue =>
        cases leftValue <;> cases rightValue
        all_goals
          rcases hStep with ⟨_, rfl⟩ <;>
            simp [Term.eval, contract.not_holds, contract.bool_holds]
      all_goals
        try simp_all [Term.eval, Formula.eval, contract.iff_holds, contract.not_holds, contract.bool_holds, contract.quote_holds]
      all_goals
        try
          rcases hStep with ⟨_, hTargetEq⟩
          rw [← hTargetEq]
          simp [Term.eval, Formula.eval, contract.iff_holds, contract.not_holds, contract.quote_holds]
      all_goals
        try
          rcases hStep with ⟨hStructure, _, hTargetEq⟩
          rw [← hTargetEq]
          simp [Term.eval, contract.bool_holds]
  | quote formula =>
      have hSort : resultSort = .bool := inferSortWith_quote_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
        hBound hFree (.quote formula) target
        hSourceFragment hTargetFragment hSource hTarget
      cases formula <;>
        simp [rewriteRootTerm?, Config.foolOnly] at hStep <;>
        grind [Term.eval, Formula.eval, contract.quote_holds, contract.bool_holds]
  | lam domain codomain body => simp [rewriteRootTerm?, Config.foolOnly] at hStep
  | ite sort condition thenTerm elseTerm =>
      simp only [rewriteRootTerm?, Config.foolOnly] at hStep
      by_cases hTrue : condition = .trueE
      · subst condition
        simp at hStep
        rcases hStep with ⟨_, hTargetEq⟩
        subst target
        change Term.eval env (.ite sort .trueE thenTerm elseTerm) =
          Term.eval env thenTerm
        rw [Term.eval_ite contract]
        simp [Formula.Satisfies, Formula.eval]
      · by_cases hFalse : condition = .falseE
        · subst condition
          simp at hStep
          rcases hStep with ⟨_, hTargetEq⟩
          subst target
          change Term.eval env (.ite sort .falseE thenTerm elseTerm) =
            Term.eval env elseTerm
          rw [Term.eval_ite contract]
          simp [Formula.Satisfies, Formula.eval]
        · by_cases hEqual : SyntaxEq.termEq thenTerm elseTerm = true
          · have hTerms : thenTerm = elseTerm :=
              SyntaxEq.termEq_eq_true.mp hEqual
            subst elseTerm
            simp [hEqual] at hStep
            rcases hStep with ⟨_, hTargetEq⟩
            subst target
            change Term.eval env (.ite sort condition thenTerm thenTerm) =
              Term.eval env thenTerm
            rw [Term.eval_ite contract]
            by_cases hCondition : Formula.Satisfies env condition <;>
              simp [hCondition]
          · cases sort with
            | object | prop | named | arrow => simp [hEqual] at hStep
            | bool =>
                have hResult : resultSort = .bool :=
                  inferSortWith_ite_eq_declared hSource
                subst resultSort
                apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
                  hBound hFree (.ite .bool condition thenTerm elseTerm) target
                  hSourceFragment hTargetFragment hSource hTarget
                by_cases hThenTrue : thenTerm = .bool true
                · by_cases hElseFalse : elseTerm = .bool false
                  · subst thenTerm
                    subst elseTerm
                    simp [hEqual] at hStep
                    rcases hStep with ⟨_, hTargetEq⟩
                    subst target
                    by_cases hCondition : Formula.Satisfies env condition <;>
                      simp only [Formula.Satisfies] at hCondition <;>
                      simp [Term.eval_ite contract, Term.eval, Formula.Satisfies, hCondition, contract.quote_holds, contract.bool_holds]
                  · subst thenTerm
                    simp [hEqual] at hStep
                    rcases hStep with ⟨_, hTargetEq⟩
                    subst target
                    by_cases hCondition : Formula.Satisfies env condition <;>
                      simp only [Formula.Satisfies] at hCondition <;>
                      simp [Term.eval_ite contract, Term.eval, Formula.Satisfies, hCondition, contract.or_holds, contract.quote_holds, contract.bool_holds]
                · by_cases hThenFalse : thenTerm = .bool false
                  · by_cases hElseTrue : elseTerm = .bool true
                    · subst thenTerm
                      subst elseTerm
                      simp [hEqual] at hStep
                      rcases hStep with ⟨_, hTargetEq⟩
                      subst target
                      by_cases hCondition : Formula.Satisfies env condition <;>
                        simp only [Formula.Satisfies] at hCondition <;>
                        simp [Term.eval_ite contract, Term.eval, Formula.eval, Formula.Satisfies, hCondition, contract.quote_holds, contract.bool_holds]
                    · subst thenTerm
                      simp [hEqual] at hStep
                      rcases hStep with ⟨_, hTargetEq⟩
                      subst target
                      by_cases hCondition : Formula.Satisfies env condition <;>
                        simp only [Formula.Satisfies] at hCondition <;>
                        simp [Term.eval_ite contract, Term.eval, Formula.eval, Formula.Satisfies, hCondition, contract.and_holds, contract.quote_holds, contract.bool_holds]
                  · by_cases hElseTrue : elseTerm = .bool true
                    · subst elseTerm
                      simp [hEqual] at hStep
                      rcases hStep with ⟨_, hTargetEq⟩
                      subst target
                      by_cases hCondition : Formula.Satisfies env condition <;>
                        simp only [Formula.Satisfies] at hCondition <;>
                        simp [Term.eval_ite contract, Term.eval, Formula.Satisfies, hCondition, contract.imp_holds, contract.quote_holds, contract.bool_holds]
                    · by_cases hElseFalse : elseTerm = .bool false
                      · subst elseTerm
                        simp [hEqual] at hStep
                        rcases hStep with ⟨_, hTargetEq⟩
                        subst target
                        by_cases hCondition : Formula.Satisfies env condition <;>
                          simp only [Formula.Satisfies] at hCondition <;>
                          simp [Term.eval_ite contract, Term.eval, Formula.Satisfies, hCondition, contract.and_holds, contract.quote_holds, contract.bool_holds]
                      · simp [hEqual, hThenTrue, hThenFalse, hElseTrue, hElseFalse] at hStep
  | bvar => simp [rewriteRootTerm?] at hStep
  | fvar => simp [rewriteRootTerm?] at hStep
  | app => simp [rewriteRootTerm?] at hStep
  | bool => simp [rewriteRootTerm?] at hStep
theorem rewriteRootTerm?_fool_sound_of_typed {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : Term}
    {rule : StepRule} {sourceSort targetSort : CoreSort} (hSourceFragment : Term.foolFragment source = true) (hTargetFragment : Term.foolFragment target = true) (hSource : Term.inferSortWith bound source = some
    sourceSort) (hTarget : Term.inferSortWith bound target = some targetSort) (hStep : rewriteRootTerm? Config.foolOnly source = some (rule, target)) : SemanticallyEqual env source target := by
  cases source with
  | apply fn argument => simp [Term.foolFragment] at hSourceFragment
  | lam domain codomain body => simp [Term.foolFragment] at hSourceFragment
  | notE body =>
      rcases inferSortWith_notE_parts hSource with ⟨rfl, hBody⟩
      have hTargetBool :=
        rewriteRootNot_target_bool hBody hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | andE left right =>
      rcases inferSortWith_andE_parts hSource with ⟨rfl, hLeft, hRight⟩
      have hTargetBool := rewriteRootAnd_target_bool hLeft hRight hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | orE left right =>
      rcases inferSortWith_orE_parts hSource with ⟨rfl, hLeft, hRight⟩
      have hTargetBool := rewriteRootOr_target_bool hLeft hRight hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | impE left right =>
      rcases inferSortWith_impE_parts hSource with ⟨rfl, hLeft, hRight⟩
      have hTargetBool := rewriteRootImp_target_bool hLeft hRight hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | iffE left right =>
      rcases inferSortWith_iffE_parts hSource with ⟨rfl, hLeft, hRight⟩
      have hTargetBool := rewriteRootIff_target_bool hLeft hRight hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | quote formula =>
      rcases inferSortWith_quote_parts hSource with ⟨rfl, hFormula⟩
      have hTargetBool := rewriteRootQuote_target_bool hFormula hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | ite declared condition thenTerm elseTerm =>
      rcases inferSortWith_ite_parts hSource with
        ⟨rfl, hCondition, hThen, hElse⟩
      have hTargetDeclared :=
        rewriteRootIte_target_sort hCondition hThen hElse hStep
      have hTargetSort : targetSort = sourceSort :=
        inferSortWith_unique hTarget hTargetDeclared
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | bvar => simp [rewriteRootTerm?] at hStep
  | fvar => simp [rewriteRootTerm?] at hStep
  | app => simp [rewriteRootTerm?] at hStep
  | bool => simp [rewriteRootTerm?] at hStep
end Term
namespace Formula
theorem satisfies_boolEquality_iff_fool {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) (left right : Term)
    (hLeftFragment : Term.foolFragment left = true) (hRightFragment : Term.foolFragment right = true) (hLeft : Term.inferSortWith bound left = some .bool) (hRight : Term.inferSortWith bound right = some .bool) :
    Formula.Satisfies env (.equal .bool left right) ↔ (M.boolHolds (Term.eval env left) ↔ M.boolHolds (Term.eval env right)) := by
  have hLeftMem :=
    Term.eval_mem_of_inferSortWith_fool contract bound env hBound hFree
      left .bool hLeftFragment hLeft
  have hRightMem :=
    Term.eval_mem_of_inferSortWith_fool contract bound env hBound hFree
      right .bool hRightFragment hRight
  simpa only [Formula.Satisfies, Formula.eval] using
    contract.bool_extensionality _ _ hLeftMem hRightMem
theorem rewriteRootFormula?_fool_sound {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : Formula} {rule :
    StepRule} (hSourceFragment : Formula.foolFragment source = true) (_hTargetFragment : Formula.foolFragment target = true) (hSource : Formula.checkWith bound source = true) (_hTarget : Formula.checkWith bound target =
    true) (hStep : rewriteRootFormula? Config.foolOnly source = some (rule, target)) : SemanticallyEquivalent env source target := by
  cases source with
  | trueE => simp [rewriteRootFormula?] at hStep
  | falseE => simp [rewriteRootFormula?] at hStep
  | atom => simp [rewriteRootFormula?] at hStep
  | equal sort left right =>
      simp only [Formula.foolFragment, Bool.and_eq_true] at hSourceFragment
      have hSorts := inferSortWith_of_check_equal hSource
      by_cases hRefl : SyntaxEq.termEq left right = true
      · have hTerms : left = right := SyntaxEq.termEq_eq_true.mp hRefl
        subst right
        simp [rewriteRootFormula?, Config.foolOnly, hRefl] at hStep
        rcases hStep with ⟨_, rfl⟩
        simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · cases sort with
        | arrow domain codomain => simp [rewriteRootFormula?, Config.foolOnly, hRefl] at hStep
        | bool =>
            have hBool :=
              satisfies_boolEquality_iff_fool contract bound env hBound hFree
                left right hSourceFragment.1 hSourceFragment.2
                hSorts.1 hSorts.2
            simp [rewriteRootFormula?, Config.foolOnly, hRefl] at hStep
            cases left <;> cases right <;>
              try cases ‹Bool› <;> try cases ‹Bool›
            all_goals
              rcases hStep with ⟨_, rfl⟩
              simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.bool_holds, contract.quote_holds] at hBool ⊢
            all_goals exact hBool
        | object => simp [rewriteRootFormula?, Config.foolOnly, hRefl] at hStep
        | prop => simp [rewriteRootFormula?, Config.foolOnly, hRefl] at hStep
        | named => simp [rewriteRootFormula?, Config.foolOnly, hRefl] at hStep
  | boolTerm term =>
      simp only [Formula.foolFragment] at hSourceFragment
      cases term with
      | bool value =>
          cases value <;>
            simp [rewriteRootFormula?, Config.foolOnly] at hStep <;>
            rcases hStep with ⟨_, rfl⟩ <;>
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.bool_holds]
      | notE body =>
          simp [rewriteRootFormula?, Config.foolOnly] at hStep
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.not_holds]
      | andE left right =>
          simp [rewriteRootFormula?, Config.foolOnly] at hStep
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.and_holds]
      | orE left right =>
          simp [rewriteRootFormula?, Config.foolOnly] at hStep
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.or_holds]
      | impE left right =>
          simp [rewriteRootFormula?, Config.foolOnly] at hStep
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.imp_holds]
      | iffE left right =>
          simp [rewriteRootFormula?, Config.foolOnly] at hStep
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.iff_holds]
      | quote formula =>
          simp [rewriteRootFormula?, Config.foolOnly] at hStep
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.quote_holds]
      | ite sort condition thenTerm elseTerm =>
          cases sort <;> simp [rewriteRootFormula?, Config.foolOnly] at hStep
          next =>
            rcases hStep with ⟨_, rfl⟩
            by_cases hCondition : Formula.Satisfies env condition <;>
              simp only [Formula.Satisfies] at hCondition <;>
              simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval_ite contract, hCondition]
      | bvar => simp [rewriteRootFormula?, Config.foolOnly] at hStep
      | fvar => simp [rewriteRootFormula?, Config.foolOnly] at hStep
      | app => simp [rewriteRootFormula?, Config.foolOnly] at hStep
      | apply => simp [Term.foolFragment] at hSourceFragment
      | lam => simp [Term.foolFragment] at hSourceFragment
  | neg body =>
      cases body <;>
        simp [rewriteRootFormula?, Config.foolOnly] at hStep
      all_goals
        rcases hStep with ⟨_, rfl⟩
        simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
  | imp left right =>
      by_cases hEqual : SyntaxEq.formulaEq left right = true
      · have hFormulas : left = right := SyntaxEq.formulaEq_eq_true.mp hEqual
        subst right
        cases left <;>
          simp [rewriteRootFormula?, Config.foolOnly, hEqual] at hStep <;>
          rcases hStep with ⟨_, rfl⟩ <;>
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · cases left <;> cases right <;>
          simp [rewriteRootFormula?, Config.foolOnly, hEqual] at hStep
        all_goals
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
  | conj left right =>
      by_cases hEqual : SyntaxEq.formulaEq left right = true
      · have hFormulas : left = right := SyntaxEq.formulaEq_eq_true.mp hEqual
        subst right
        cases left <;>
          simp [rewriteRootFormula?, Config.foolOnly, hEqual] at hStep <;>
          rcases hStep with ⟨_, rfl⟩ <;>
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · cases left <;> cases right <;>
          simp [rewriteRootFormula?, Config.foolOnly, hEqual] at hStep
        all_goals
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
  | disj left right =>
      by_cases hEqual : SyntaxEq.formulaEq left right = true
      · have hFormulas : left = right := SyntaxEq.formulaEq_eq_true.mp hEqual
        subst right
        cases left <;>
          simp [rewriteRootFormula?, Config.foolOnly, hEqual] at hStep <;>
          rcases hStep with ⟨_, rfl⟩ <;>
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · cases left <;> cases right <;>
          simp [rewriteRootFormula?, Config.foolOnly, hEqual] at hStep
        all_goals
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
  | iffE left right =>
      by_cases hEqual : SyntaxEq.formulaEq left right = true
      · have hFormulas : left = right := SyntaxEq.formulaEq_eq_true.mp hEqual
        subst right
        cases left <;>
          simp [rewriteRootFormula?, Config.foolOnly, hEqual] at hStep <;>
          rcases hStep with ⟨_, rfl⟩ <;>
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · cases left <;> cases right <;>
          simp [rewriteRootFormula?, Config.foolOnly, hEqual] at hStep
        all_goals
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
  | forallE sort body =>
      cases body <;>
        simp [rewriteRootFormula?, Config.foolOnly] at hStep
      rcases hStep with ⟨_, rfl⟩
      simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
  | existsE sort body =>
      cases body <;>
        simp [rewriteRootFormula?, Config.foolOnly] at hStep
      rcases hStep with ⟨_, rfl⟩
      simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
end Formula
open _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics.Formula _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics.Term
mutual
  theorem Formula.rewriteOnceFormula?_fool_sound {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target :
      Formula} {rule : StepRule} (hSourceFragment : Formula.foolFragment source = true) (hTargetFragment : Formula.foolFragment target = true) (hSource : Formula.checkWith bound source = true) (hTarget :
      Formula.checkWith bound target = true) (hStep : rewriteOnceFormula? Config.foolOnly source = some (rule, target)) : SemanticallyEquivalent env source target := by
    cases source with
    | trueE => simp [rewriteOnceFormula?] at hStep
    | falseE => simp [rewriteOnceFormula?] at hStep
    | atom predicate args =>
        simp only [Formula.foolFragment] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceTermList? Config.foolOnly args with
        | none => simp [hRewrite, rewriteRootFormula?] at hStep
        | some value =>
            rcases value with ⟨childRule, args'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.foolFragment] at hTargetFragment
            obtain ⟨sourceSorts, hSourceArgs⟩ :=
              inferSortListWith_of_check_atom hSource
            obtain ⟨targetSorts, hTargetArgs⟩ :=
              inferSortListWith_of_check_atom hTarget
            have hArgs :=
              Term.rewriteOnceTermList?_fool_sound contract bound env hBound hFree
                hSourceFragment hTargetFragment hSourceArgs hTargetArgs hRewrite
            change
              SemanticallyEquivalent env (Formula.atom predicate args) (Formula.atom predicate args')
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            change (M.predicateInterp predicate (args.map (Term.eval env)) ↔ M.predicateInterp predicate (args'.map (Term.eval env)))
            rw [hArgs]
    | equal sort left right =>
        simp only [Formula.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hLeftRewrite : rewriteOnceTerm? Config.foolOnly left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceSorts := inferSortWith_of_check_equal hSource
            have hTargetSorts := inferSortWith_of_check_equal hTarget
            have hLeftSem :=
              Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceSorts.1 hTargetSorts.1 hLeftRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            change (Term.eval env left = Term.eval env right ↔ Term.eval env left' = Term.eval env right)
            change Term.eval env left = Term.eval env left' at hLeftSem
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceTerm? Config.foolOnly right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceSorts := inferSortWith_of_check_equal hSource
                have hTargetSorts := inferSortWith_of_check_equal hTarget
                have hRightSem :=
                  Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                    hSourceFragment.2 hTargetFragment.2
                    hSourceSorts.2 hTargetSorts.2 hRightRewrite
                simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
                change (Term.eval env left = Term.eval env right ↔ Term.eval env left = Term.eval env right')
                change Term.eval env right = Term.eval env right' at hRightSem
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootFormula?_fool_sound contract bound env
                  hBound hFree (by
                    simpa [Formula.foolFragment, Bool.and_eq_true] using
                      hSourceFragment)
                  hTargetFragment
                  hSource hTarget hStep
    | boolTerm term =>
        simp only [Formula.foolFragment] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceTerm? Config.foolOnly term with
        | some value =>
            rcases value with ⟨childRule, term'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.foolFragment] at hTargetFragment
            have hSourceSort := inferSortWith_of_check_boolTerm hSource
            have hTargetSort := inferSortWith_of_check_boolTerm hTarget
            have hTermSem :=
              Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                hSourceFragment hTargetFragment
                hSourceSort hTargetSort hRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            change (M.boolHolds (Term.eval env term) ↔ M.boolHolds (Term.eval env term'))
            change Term.eval env term = Term.eval env term' at hTermSem
            rw [hTermSem]
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootFormula?_fool_sound contract bound env
              hBound hFree hSourceFragment hTargetFragment
              hSource hTarget hStep
    | neg body =>
        simp only [Formula.foolFragment] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceFormula? Config.foolOnly body with
        | some value =>
            rcases value with ⟨childRule, body'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.foolFragment] at hTargetFragment
            have hSourceBody := checkWith_of_check_neg hSource
            have hTargetBody := checkWith_of_check_neg hTarget
            have hBodySem :=
              Formula.rewriteOnceFormula?_fool_sound contract bound env hBound hFree
                hSourceFragment hTargetFragment
                hSourceBody hTargetBody hRewrite
            simpa only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval] using
              not_congr hBodySem
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootFormula?_fool_sound contract bound env
              hBound hFree hSourceFragment hTargetFragment
              hSource hTarget hStep
    | imp left right =>
        simp only [Formula.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hLeftRewrite : rewriteOnceFormula? Config.foolOnly left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceParts := checkWith_of_check_imp hSource
            have hTargetParts := checkWith_of_check_imp hTarget
            have hLeftSem :=
              Formula.rewriteOnceFormula?_fool_sound contract bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceParts.1 hTargetParts.1 hLeftRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            constructor
            · intro h hLeft'
              exact h (hLeftSem.mpr hLeft')
            · intro h hLeft
              exact h (hLeftSem.mp hLeft)
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceFormula? Config.foolOnly right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceParts := checkWith_of_check_imp hSource
                have hTargetParts := checkWith_of_check_imp hTarget
                have hRightSem :=
                  Formula.rewriteOnceFormula?_fool_sound contract bound env
                    hBound hFree hSourceFragment.2 hTargetFragment.2
                    hSourceParts.2 hTargetParts.2 hRightRewrite
                simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
                constructor
                · intro h hLeft
                  exact hRightSem.mp (h hLeft)
                · intro h hLeft
                  exact hRightSem.mpr (h hLeft)
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootFormula?_fool_sound contract bound env
                  hBound hFree (by
                    simpa [Formula.foolFragment, Bool.and_eq_true] using
                      hSourceFragment)
                  hTargetFragment
                  hSource hTarget hStep
    | conj left right =>
        simp only [Formula.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hLeftRewrite : rewriteOnceFormula? Config.foolOnly left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceParts := checkWith_of_check_conj hSource
            have hTargetParts := checkWith_of_check_conj hTarget
            have hLeftSem :=
              Formula.rewriteOnceFormula?_fool_sound contract bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceParts.1 hTargetParts.1 hLeftRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            constructor
            · intro h
              exact ⟨hLeftSem.mp h.1, h.2⟩
            · intro h
              exact ⟨hLeftSem.mpr h.1, h.2⟩
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceFormula? Config.foolOnly right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceParts := checkWith_of_check_conj hSource
                have hTargetParts := checkWith_of_check_conj hTarget
                have hRightSem :=
                  Formula.rewriteOnceFormula?_fool_sound contract bound env
                    hBound hFree hSourceFragment.2 hTargetFragment.2
                    hSourceParts.2 hTargetParts.2 hRightRewrite
                simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
                constructor
                · intro h
                  exact ⟨h.1, hRightSem.mp h.2⟩
                · intro h
                  exact ⟨h.1, hRightSem.mpr h.2⟩
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootFormula?_fool_sound contract bound env
                  hBound hFree (by
                    simpa [Formula.foolFragment, Bool.and_eq_true] using
                      hSourceFragment)
                  hTargetFragment
                  hSource hTarget hStep
    | disj left right =>
        simp only [Formula.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hLeftRewrite : rewriteOnceFormula? Config.foolOnly left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceParts := checkWith_of_check_disj hSource
            have hTargetParts := checkWith_of_check_disj hTarget
            have hLeftSem :=
              Formula.rewriteOnceFormula?_fool_sound contract bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceParts.1 hTargetParts.1 hLeftRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            constructor
            · intro h
              cases h with
              | inl hLeft => exact Or.inl (hLeftSem.mp hLeft)
              | inr hRight => exact Or.inr hRight
            · intro h
              cases h with
              | inl hLeft => exact Or.inl (hLeftSem.mpr hLeft)
              | inr hRight => exact Or.inr hRight
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceFormula? Config.foolOnly right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceParts := checkWith_of_check_disj hSource
                have hTargetParts := checkWith_of_check_disj hTarget
                have hRightSem :=
                  Formula.rewriteOnceFormula?_fool_sound contract bound env
                    hBound hFree hSourceFragment.2 hTargetFragment.2
                    hSourceParts.2 hTargetParts.2 hRightRewrite
                simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
                constructor
                · intro h
                  cases h with
                  | inl hLeft => exact Or.inl hLeft
                  | inr hRight => exact Or.inr (hRightSem.mp hRight)
                · intro h
                  cases h with
                  | inl hLeft => exact Or.inl hLeft
                  | inr hRight => exact Or.inr (hRightSem.mpr hRight)
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootFormula?_fool_sound contract bound env
                  hBound hFree (by
                    simpa [Formula.foolFragment, Bool.and_eq_true] using
                      hSourceFragment)
                  hTargetFragment
                  hSource hTarget hStep
    | iffE left right =>
        simp only [Formula.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hLeftRewrite : rewriteOnceFormula? Config.foolOnly left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceParts := checkWith_of_check_iffE hSource
            have hTargetParts := checkWith_of_check_iffE hTarget
            have hLeftSem :=
              Formula.rewriteOnceFormula?_fool_sound contract bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceParts.1 hTargetParts.1 hLeftRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            constructor
            · intro h
              exact ⟨fun hLeft' => h.mp (hLeftSem.mpr hLeft'), fun hRight => hLeftSem.mp (h.mpr hRight)⟩
            · intro h
              exact ⟨fun hLeft => h.mp (hLeftSem.mp hLeft), fun hRight => hLeftSem.mpr (h.mpr hRight)⟩
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceFormula? Config.foolOnly right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceParts := checkWith_of_check_iffE hSource
                have hTargetParts := checkWith_of_check_iffE hTarget
                have hRightSem :=
                  Formula.rewriteOnceFormula?_fool_sound contract bound env
                    hBound hFree hSourceFragment.2 hTargetFragment.2
                    hSourceParts.2 hTargetParts.2 hRightRewrite
                simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
                constructor
                · intro h
                  exact ⟨fun hLeft => hRightSem.mp (h.mp hLeft), fun hRight' => h.mpr (hRightSem.mpr hRight')⟩
                · intro h
                  exact ⟨fun hLeft => hRightSem.mpr (h.mp hLeft), fun hRight => h.mpr (hRightSem.mp hRight)⟩
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootFormula?_fool_sound contract bound env
                  hBound hFree (by
                    simpa [Formula.foolFragment, Bool.and_eq_true] using
                      hSourceFragment)
                  hTargetFragment
                  hSource hTarget hStep
    | forallE sort body =>
        simp only [Formula.foolFragment] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceFormula? Config.foolOnly body with
        | some value =>
            rcases value with ⟨childRule, body'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.foolFragment] at hTargetFragment
            have hSourceBody := checkWith_of_check_forallE hSource
            have hTargetBody := checkWith_of_check_forallE hTarget
            have hBodySem (value : M.Carrier) (hValue : M.sortInterp sort value) :=
              Formula.rewriteOnceFormula?_fool_sound contract (sort :: bound) (env.push value) (Env.respectsBound_push hBound hValue)
                (Env.respectsFree_push hFree value)
                hSourceFragment hTargetFragment
                hSourceBody hTargetBody hRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            constructor
            · intro h value hValue
              exact (hBodySem value hValue).mp (h value hValue)
            · intro h value hValue
              exact (hBodySem value hValue).mpr (h value hValue)
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootFormula?_fool_sound contract bound env
              hBound hFree hSourceFragment hTargetFragment
              hSource hTarget hStep
    | existsE sort body =>
        simp only [Formula.foolFragment] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceFormula? Config.foolOnly body with
        | some value =>
            rcases value with ⟨childRule, body'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.foolFragment] at hTargetFragment
            have hSourceBody := checkWith_of_check_existsE hSource
            have hTargetBody := checkWith_of_check_existsE hTarget
            have hBodySem (value : M.Carrier) (hValue : M.sortInterp sort value) :=
              Formula.rewriteOnceFormula?_fool_sound contract (sort :: bound) (env.push value) (Env.respectsBound_push hBound hValue)
                (Env.respectsFree_push hFree value)
                hSourceFragment hTargetFragment
                hSourceBody hTargetBody hRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            constructor
            · rintro ⟨value, hValue, hBody⟩
              exact ⟨value, hValue, (hBodySem value hValue).mp hBody⟩
            · rintro ⟨value, hValue, hBody⟩
              exact ⟨value, hValue, (hBodySem value hValue).mpr hBody⟩
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootFormula?_fool_sound contract bound env
              hBound hFree hSourceFragment hTargetFragment
              hSource hTarget hStep
  theorem Term.rewriteOnceTerm?_fool_sound {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : Term} {rule
      : StepRule} {sourceSort targetSort : CoreSort} (hSourceFragment : Term.foolFragment source = true) (hTargetFragment : Term.foolFragment target = true) (hSource : Term.inferSortWith bound source = some sourceSort)
      (hTarget : Term.inferSortWith bound target = some targetSort) (hStep : rewriteOnceTerm? Config.foolOnly source = some (rule, target)) : SemanticallyEqual env source target := by
    cases source with
    | bvar => simp [rewriteOnceTerm?] at hStep
    | fvar => simp [rewriteOnceTerm?] at hStep
    | bool => simp [rewriteOnceTerm?] at hStep
    | app symbol args =>
        simp only [Term.foolFragment] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hRewrite : rewriteOnceTermList? Config.foolOnly args with
        | none => simp [hRewrite, rewriteRootTerm?] at hStep
        | some value =>
            rcases value with ⟨childRule, args'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.foolFragment] at hTargetFragment
            obtain ⟨_, sourceSorts, hSourceArgs⟩ :=
              inferSortWith_app_parts hSource
            obtain ⟨_, targetSorts, hTargetArgs⟩ :=
              inferSortWith_app_parts hTarget
            have hArgsSem :=
              Term.rewriteOnceTermList?_fool_sound contract bound env hBound hFree
                hSourceFragment hTargetFragment hSourceArgs hTargetArgs hRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.functionInterp symbol (args.map (Term.eval env)) =
                M.functionInterp symbol (args'.map (Term.eval env))
            rw [hArgsSem]
    | apply fn arg => simp [Term.foolFragment] at hSourceFragment
    | notE body =>
        simp only [Term.foolFragment] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hRewrite : rewriteOnceTerm? Config.foolOnly body with
        | some value =>
            rcases value with ⟨childRule, body'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.foolFragment] at hTargetFragment
            have hSourceBody := (inferSortWith_notE_parts hSource).2
            have hTargetBody := (inferSortWith_notE_parts hTarget).2
            have hBodySem :=
              Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                hSourceFragment hTargetFragment
                hSourceBody hTargetBody hRewrite
            simp only [SemanticallyEqual, Term.eval]
            change M.notValue (Term.eval env body) = M.notValue (Term.eval env body')
            rw [hBodySem]
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootTerm?_fool_sound_of_typed contract bound env
              hBound hFree hSourceFragment hTargetFragment
              hSource hTarget hStep
    | andE left right =>
        simp only [Term.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hLeftRewrite : rewriteOnceTerm? Config.foolOnly left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceParts := inferSortWith_andE_parts hSource
            have hTargetParts := inferSortWith_andE_parts hTarget
            have hLeftSem :=
              Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceParts.2.1 hTargetParts.2.1 hLeftRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.andValue (Term.eval env left) (Term.eval env right) =
                M.andValue (Term.eval env left') (Term.eval env right)
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceTerm? Config.foolOnly right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Term.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceParts := inferSortWith_andE_parts hSource
                have hTargetParts := inferSortWith_andE_parts hTarget
                have hRightSem :=
                  Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                    hSourceFragment.2 hTargetFragment.2
                    hSourceParts.2.2 hTargetParts.2.2 hRightRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.andValue (Term.eval env left) (Term.eval env right) =
                    M.andValue (Term.eval env left) (Term.eval env right')
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootTerm?_fool_sound_of_typed contract bound env
                  hBound hFree (by
                    simpa [Term.foolFragment, Bool.and_eq_true] using
                      hSourceFragment)
                  hTargetFragment
                  hSource hTarget hStep
    | orE left right =>
        simp only [Term.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hLeftRewrite : rewriteOnceTerm? Config.foolOnly left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceParts := inferSortWith_orE_parts hSource
            have hTargetParts := inferSortWith_orE_parts hTarget
            have hLeftSem :=
              Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceParts.2.1 hTargetParts.2.1 hLeftRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.orValue (Term.eval env left) (Term.eval env right) =
                M.orValue (Term.eval env left') (Term.eval env right)
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceTerm? Config.foolOnly right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Term.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceParts := inferSortWith_orE_parts hSource
                have hTargetParts := inferSortWith_orE_parts hTarget
                have hRightSem :=
                  Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                    hSourceFragment.2 hTargetFragment.2
                    hSourceParts.2.2 hTargetParts.2.2 hRightRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.orValue (Term.eval env left) (Term.eval env right) =
                    M.orValue (Term.eval env left) (Term.eval env right')
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootTerm?_fool_sound_of_typed contract bound env
                  hBound hFree (by
                    simpa [Term.foolFragment, Bool.and_eq_true] using
                      hSourceFragment)
                  hTargetFragment
                  hSource hTarget hStep
    | impE left right =>
        simp only [Term.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hLeftRewrite : rewriteOnceTerm? Config.foolOnly left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceParts := inferSortWith_impE_parts hSource
            have hTargetParts := inferSortWith_impE_parts hTarget
            have hLeftSem :=
              Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceParts.2.1 hTargetParts.2.1 hLeftRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.impValue (Term.eval env left) (Term.eval env right) =
                M.impValue (Term.eval env left') (Term.eval env right)
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceTerm? Config.foolOnly right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Term.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceParts := inferSortWith_impE_parts hSource
                have hTargetParts := inferSortWith_impE_parts hTarget
                have hRightSem :=
                  Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                    hSourceFragment.2 hTargetFragment.2
                    hSourceParts.2.2 hTargetParts.2.2 hRightRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.impValue (Term.eval env left) (Term.eval env right) =
                    M.impValue (Term.eval env left) (Term.eval env right')
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootTerm?_fool_sound_of_typed contract bound env
                  hBound hFree (by
                    simpa [Term.foolFragment, Bool.and_eq_true] using
                      hSourceFragment)
                  hTargetFragment
                  hSource hTarget hStep
    | iffE left right =>
        simp only [Term.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hLeftRewrite : rewriteOnceTerm? Config.foolOnly left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceParts := inferSortWith_iffE_parts hSource
            have hTargetParts := inferSortWith_iffE_parts hTarget
            have hLeftSem :=
              Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceParts.2.1 hTargetParts.2.1 hLeftRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.iffValue (Term.eval env left) (Term.eval env right) =
                M.iffValue (Term.eval env left') (Term.eval env right)
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceTerm? Config.foolOnly right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Term.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceParts := inferSortWith_iffE_parts hSource
                have hTargetParts := inferSortWith_iffE_parts hTarget
                have hRightSem :=
                  Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                    hSourceFragment.2 hTargetFragment.2
                    hSourceParts.2.2 hTargetParts.2.2 hRightRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.iffValue (Term.eval env left) (Term.eval env right) =
                    M.iffValue (Term.eval env left) (Term.eval env right')
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootTerm?_fool_sound_of_typed contract bound env
                  hBound hFree (by
                    simpa [Term.foolFragment, Bool.and_eq_true] using
                      hSourceFragment)
                  hTargetFragment
                  hSource hTarget hStep
    | quote formula =>
        simp only [Term.foolFragment] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hRewrite : rewriteOnceFormula? Config.foolOnly formula with
        | some value =>
            rcases value with ⟨childRule, formula'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.foolFragment] at hTargetFragment
            have hSourceFormula := (inferSortWith_quote_parts hSource).2
            have hTargetFormula := (inferSortWith_quote_parts hTarget).2
            have hFormulaSem :=
              Formula.rewriteOnceFormula?_fool_sound contract bound env hBound hFree
                hSourceFragment hTargetFragment
                hSourceFormula hTargetFormula hRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.quoteValue (Formula.eval env formula).holds =
                M.quoteValue (Formula.eval env formula').holds
            exact (contract.quote_eq_iff _ _).2 hFormulaSem
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootTerm?_fool_sound_of_typed contract bound env
              hBound hFree hSourceFragment hTargetFragment
              hSource hTarget hStep
    | lam domain codomain body => simp [Term.foolFragment] at hSourceFragment
    | ite declared condition thenTerm elseTerm =>
        simp only [Term.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hConditionRewrite :
            rewriteOnceFormula? Config.foolOnly condition with
        | some value =>
            rcases value with ⟨childRule, condition'⟩
            simp [hConditionRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceParts := inferSortWith_ite_parts hSource
            have hTargetParts := inferSortWith_ite_parts hTarget
            have hConditionSem :=
              Formula.rewriteOnceFormula?_fool_sound contract bound env hBound hFree
                hSourceFragment.1.1 hTargetFragment.1.1
                hSourceParts.2.1 hTargetParts.2.1 hConditionRewrite
            have hConditionEq : (Formula.eval env condition).holds = (Formula.eval env condition').holds :=
              propext hConditionSem
            simp only [SemanticallyEqual, Term.eval]
            change
              M.iteValue (Formula.eval env condition).holds (Term.eval env thenTerm) (Term.eval env elseTerm) =
                M.iteValue (Formula.eval env condition').holds (Term.eval env thenTerm) (Term.eval env elseTerm)
            rw [hConditionEq]
        | none =>
            simp [hConditionRewrite] at hStep
            cases hThenRewrite : rewriteOnceTerm? Config.foolOnly thenTerm with
            | some value =>
                rcases value with ⟨childRule, thenTerm'⟩
                simp [hThenRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Term.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceParts := inferSortWith_ite_parts hSource
                have hTargetParts := inferSortWith_ite_parts hTarget
                have hThenSem :=
                  Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                    hSourceFragment.1.2 hTargetFragment.1.2
                    hSourceParts.2.2.1 hTargetParts.2.2.1 hThenRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.iteValue (Formula.eval env condition).holds (Term.eval env thenTerm) (Term.eval env elseTerm) =
                    M.iteValue (Formula.eval env condition).holds (Term.eval env thenTerm') (Term.eval env elseTerm)
                rw [hThenSem]
            | none =>
                simp [hThenRewrite] at hStep
                cases hElseRewrite : rewriteOnceTerm? Config.foolOnly elseTerm with
                | some value =>
                    rcases value with ⟨childRule, elseTerm'⟩
                    simp [hElseRewrite] at hStep
                    rcases hStep with ⟨rfl, rfl⟩
                    simp only [Term.foolFragment, Bool.and_eq_true] at hTargetFragment
                    have hSourceParts := inferSortWith_ite_parts hSource
                    have hTargetParts := inferSortWith_ite_parts hTarget
                    have hElseSem :=
                      Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                        hSourceFragment.2 hTargetFragment.2
                        hSourceParts.2.2.2 hTargetParts.2.2.2 hElseRewrite
                    simp only [SemanticallyEqual, Term.eval]
                    change
                      M.iteValue (Formula.eval env condition).holds (Term.eval env thenTerm) (Term.eval env elseTerm) =
                        M.iteValue (Formula.eval env condition).holds (Term.eval env thenTerm) (Term.eval env elseTerm')
                    rw [hElseSem]
                | none =>
                    simp [hElseRewrite] at hStep
                    exact rewriteRootTerm?_fool_sound_of_typed contract bound env
                      hBound hFree (by
                        simpa [Term.foolFragment, Bool.and_eq_true] using
                          hSourceFragment)
                      hTargetFragment
                      hSource hTarget hStep
  theorem Term.rewriteOnceTermList?_fool_sound {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : List
      Term} {rule : StepRule} {sourceSorts targetSorts : List CoreSort} (hSourceFragment : Term.foolFragmentList source = true) (hTargetFragment : Term.foolFragmentList target = true) (hSource : Term.inferSortListWith
      bound source = some sourceSorts) (hTarget : Term.inferSortListWith bound target = some targetSorts) (hStep : rewriteOnceTermList? Config.foolOnly source = some (rule, target)) : ListSemanticallyEqual env source
      target := by
    cases source with
    | nil => simp [rewriteOnceTermList?] at hStep
    | cons term rest =>
        simp only [Term.foolFragmentList, Bool.and_eq_true] at hSourceFragment
        obtain ⟨sourceSort, sourceRestSorts, rfl, hSourceTerm, hSourceRest⟩ :=
          inferSortListWith_cons_parts hSource
        simp only [rewriteOnceTermList?] at hStep
        cases hTermRewrite : rewriteOnceTerm? Config.foolOnly term with
        | some value =>
            rcases value with ⟨childRule, term'⟩
            simp [hTermRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.foolFragmentList, Bool.and_eq_true] at hTargetFragment
            obtain ⟨targetSort, targetRestSorts, rfl, hTargetTerm, hTargetRest⟩ :=
              inferSortListWith_cons_parts hTarget
            have hTermSem :=
              Term.rewriteOnceTerm?_fool_sound contract bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceTerm hTargetTerm hTermRewrite
            change
              Term.eval env term :: rest.map (Term.eval env) =
                Term.eval env term' :: rest.map (Term.eval env)
            rw [hTermSem]
        | none =>
            simp [hTermRewrite] at hStep
            cases hRestRewrite : rewriteOnceTermList? Config.foolOnly rest with
            | none => simp [hRestRewrite] at hStep
            | some value =>
                rcases value with ⟨childRule, rest'⟩
                simp [hRestRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Term.foolFragmentList, Bool.and_eq_true] at hTargetFragment
                obtain ⟨targetSort, targetRestSorts, rfl, hTargetTerm, hTargetRest⟩ :=
                  inferSortListWith_cons_parts hTarget
                have hRestSem :=
                  Term.rewriteOnceTermList?_fool_sound contract bound env hBound hFree
                    hSourceFragment.2 hTargetFragment.2
                    hSourceRest hTargetRest hRestRewrite
                change
                  Term.eval env term :: rest.map (Term.eval env) =
                    Term.eval env term :: rest'.map (Term.eval env)
                rw [hRestSem]
end
namespace Formula
def FoolSatisfiable (formula : Formula) : Prop :=
  ∃ (M : Model.{x}) (env : Env M), Nonempty (FoolContract M) ∧
    Env.RespectsFree env ∧ Formula.Satisfies env formula
end Formula
namespace Step
theorem sound_of_foolCheck {M : Model} (contract : FoolContract M) (env : Env M) (hFree : Env.RespectsFree env) (step : Step) (hCheck : step.foolCheck = true) : TraceExpr.SemanticallyEquivalent env step.before step.after := by
  have hBound : Env.RespectsBound [] env := Env.respectsBound_nil env
  simp only
    [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Step.foolCheck, Bool.and_eq_true] at hCheck
  have hBeforeFragment := hCheck.1.1
  have hAfterFragment := hCheck.1.2
  have hStepCheck := hCheck.2
  rcases step with ⟨stepRule, before, after⟩
  unfold _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Step.check at hStepCheck
  rcases Bool.and_eq_true_iff.mp hStepCheck with ⟨hChecks, hRewrite⟩
  rcases Bool.and_eq_true_iff.mp hChecks with ⟨hBefore, hAfter⟩
  cases before with
  | term source =>
      cases after with
      | term target =>
          cases hSourceSort : Term.inferSortWith [] source with
          | none => simp [TraceExpr.check?, Term.inferSort?, hSourceSort] at hBefore
          | some sourceSort =>
              cases hTargetSort : Term.inferSortWith [] target with
              | none => simp [TraceExpr.check?, Term.inferSort?, hTargetSort] at hAfter
              | some targetSort =>
                  cases hStep :
                      rewriteOnceTerm? Config.foolOnly source with
                  | none => simp [TraceExpr.rewriteOnce?, hStep] at hRewrite
                  | some value =>
                      rcases value with ⟨rule, rewritten⟩
                      simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq, SyntaxEq.termEq_eq_true] at hRewrite
                      rcases hRewrite with ⟨_, hTarget⟩
                      subst target
                      simpa [TraceExpr.SemanticallyEquivalent] using
                        Term.rewriteOnceTerm?_fool_sound contract [] env
                          hBound hFree hBeforeFragment hAfterFragment
                          hSourceSort hTargetSort hStep
      | formula target =>
          cases hStep : rewriteOnceTerm? Config.foolOnly source <;>
            simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq] at hRewrite
  | formula source =>
      cases after with
      | term target =>
          cases hStep : rewriteOnceFormula? Config.foolOnly source <;>
            simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq] at hRewrite
      | formula target =>
          cases hStep :
              rewriteOnceFormula? Config.foolOnly source with
          | none => simp [TraceExpr.rewriteOnce?, hStep] at hRewrite
          | some value =>
              rcases value with ⟨rule, rewritten⟩
              simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq, SyntaxEq.formulaEq_eq_true] at hRewrite
              rcases hRewrite with ⟨_, hTarget⟩
              subst target
              exact
                Formula.rewriteOnceFormula?_fool_sound contract [] env
                  hBound hFree hBeforeFragment hAfterFragment (by simpa [TraceExpr.check?, Formula.check?] using hBefore)
                    (by simpa [TraceExpr.check?, Formula.check?] using hAfter)
                    hStep
end Step
namespace Trace
theorem replay?_fool_sound {M : Model} (contract : FoolContract M) (env : Env M) (hFree : Env.RespectsFree env) (steps : List Step) (source target : TraceExpr) (hSteps : steps.all Step.foolCheck = true) (hReplay : _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay? Config.foolOnly source steps = some target) : TraceExpr.SemanticallyEquivalent env source target := by
  induction steps generalizing source with
  | nil =>
      simp [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?] at hReplay
      subst target
      exact TraceExpr.semanticallyEquivalent_refl env source
  | cons step rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hSteps
      simp only
        [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?] at hReplay
      by_cases hLink : (TraceExpr.eq source step.before && step.check Config.foolOnly) = true
      · simp [hLink] at hReplay
        have hLinkParts := Bool.and_eq_true_iff.mp hLink
        have hSource : source = step.before :=
          TraceExpr.eq_eq_true.mp hLinkParts.1
        have hStep :
            TraceExpr.SemanticallyEquivalent env step.before step.after :=
          Step.sound_of_foolCheck contract env hFree step hSteps.1
        have hRest :
            TraceExpr.SemanticallyEquivalent env step.after target :=
          ih step.after hSteps.2 hReplay
        subst source
        exact TraceExpr.semanticallyEquivalent_trans hStep hRest
      · simp [hLink] at hReplay
theorem sound_of_foolCheck {M : Model} (contract : FoolContract M) (env : Env M) (hFree : Env.RespectsFree env) (trace : Trace) (hCheck : trace.foolCheck = true) : TraceExpr.SemanticallyEquivalent env trace.source trace.target := by
  simp only
    [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.foolCheck, Bool.and_eq_true] at hCheck
  have hSteps := hCheck.1.2
  have hStepsList :
      trace.steps.toList.all Step.foolCheck = true := by
    simpa only [Array.all_toList] using hSteps
  have hTrace := hCheck.2
  unfold _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.check at hTrace
  rcases Bool.and_eq_true_iff.mp hTrace with ⟨_, hReplayCheck⟩
  cases hReplay :
      _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?
        Config.foolOnly trace.source trace.steps.toList with
  | none => simp [hReplay] at hReplayCheck
  | some replayTarget =>
      have hEndpoints := Bool.and_eq_true_iff.mp (by
        simpa [hReplay] using hReplayCheck)
      have hTarget : replayTarget = trace.target :=
        TraceExpr.eq_eq_true.mp hEndpoints.1
      subst replayTarget
      exact replay?_fool_sound contract env hFree trace.steps.toList
        trace.source trace.target hStepsList hReplay
end Trace
end Semantics
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
