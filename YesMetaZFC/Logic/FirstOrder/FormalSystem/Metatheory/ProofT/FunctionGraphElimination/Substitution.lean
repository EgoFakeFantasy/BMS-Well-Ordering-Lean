import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Elimination
import YesMetaZFC.Logic.FirstOrder.Hilbert.Substitution

/-!
# 函数图编译的替换合同

本模块比较两条计算路径：直接编译源项的自由变量替换，与先编译源项、再把一份
共享替换项的编译值代入结果。两条路径可以分配不同见证区间，因此结论是图条件
上下文中的可导出等式，而不是脆弱的语法等式。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination

universe u v w

set_option autoImplicit false

variable
  {σ : Signature.{u, v, w}}
  [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol]

/-- 对单项编译结果执行对象语言自由变量替换。 -/
def TermResult.substituteFree
    (target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ)
    (compiled : TermResult σ) : TermResult σ where
  next := compiled.next
  value :=
    Term.substituteFree target id replacement
      compiled.value
  conditions :=
    compiled.conditions.map
      (Formula.substituteFree target id replacement)

/-- 对参数表编译结果逐值、逐条件执行自由变量替换。 -/
def ArgsResult.substituteFree
    (target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ)
    (compiled : ArgsResult σ) : ArgsResult σ where
  next := compiled.next
  values :=
    compiled.values.map
      (Term.substituteFree target id replacement)
  conditions :=
    compiled.conditions.map
      (Formula.substituteFree target id replacement)

omit [DecidableEq σ.FuncSymbol] in
/-- 自由变量替换保持线性条件块的合取布局。 -/
theorem condition_conjunction_substituteFree
    (target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ)
    (conditions : List (Formula σ))
    (core : Formula σ) :
    Formula.substituteFree target id replacement
        (condition_conjunction conditions core) =
      condition_conjunction
        (conditions.map
          (Formula.substituteFree
            target id replacement))
        (Formula.substituteFree
          target id replacement core) := by
  induction conditions with
  | nil =>
      rfl
  | cons condition conditions ih =>
      simp [condition_conjunction,
        Formula.substituteFree, ih]

omit [DecidableEq σ.FuncSymbol] in
/--
对连续偶数见证都新鲜的 bound-closed 项，其源变量替换可穿过整段存在闭包。
-/
theorem close_witnesses_from_substituteFree
    (closedSort target : σ.SortSymbol)
    (id : FreeVarId) (replacement : Term σ)
    (start count : Nat) (body : Formula σ)
    (hClosed : Term.BoundClosed replacement)
    (hFresh :
      ∀ index,
        start ≤ index →
        index < start + count →
          (closedSort, witness_id index) ∉
            Term.freeSupport replacement) :
    Formula.substituteFree target (source_id id)
        replacement
        (close_witnesses_from
          closedSort start count body) =
      close_witnesses_from closedSort start count
        (Formula.substituteFree target
          (source_id id) replacement body) := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      have hTailFresh :
          ∀ index,
            start ≤ index →
            index < start + count →
              (closedSort, witness_id index) ∉
                Term.freeSupport replacement := by
        intro index hLower hUpper
        exact hFresh index hLower (by omega)
      have hCurrentFresh :
          (closedSort, witness_id (start + count)) ∉
            Term.freeSupport replacement :=
        hFresh (start + count) (by omega) (by omega)
      have hDistinct :
          (target, source_id id) ≠
            (closedSort,
              witness_id (start + count)) := by
        intro hEqual
        exact
          (source_id_ne_witness_id
            id (start + count))
            (congrArg Prod.snd hEqual)
      simp only [close_witnesses_from,
        Formula.substituteFree]
      apply congrArg (Formula.existsE closedSort)
      calc
        Formula.substituteFree target (source_id id)
            replacement
            (Formula.closeFreeAt closedSort
              (witness_id (start + count)) 0
              (close_witnesses_from
                closedSort start count body)) =
          Formula.closeFreeAt closedSort
            (witness_id (start + count)) 0
            (Formula.substituteFree target
              (source_id id) replacement
              (close_witnesses_from
                closedSort start count body)) :=
          (Formula.closeFreeAt_substituteFree_comm_of_pair_ne
            closedSort target
            (source_id id)
            (witness_id (start + count))
            0 replacement
            (close_witnesses_from
              closedSort start count body)
            hDistinct hClosed hCurrentFresh).symm
        _ =
          Formula.closeFreeAt closedSort
            (witness_id (start + count)) 0
            (close_witnesses_from closedSort start count
              (Formula.substituteFree target
                (source_id id) replacement body)) := by
          rw [ih hTailFresh]

/--
参数表的扁平图闭包与源变量替换交换；新鲜性只需覆盖该参数表实际占用的见证区间。
-/
theorem terms_flat_closure_substituteFree
    (D : Data σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ)
    (start : Nat) (sources : List (Term σ))
    (continuation : List (Term σ) → Formula σ)
    (hClosed : Term.BoundClosed replacement)
    (hFresh :
      ∀ index,
        start ≤ index →
        index < (terms D start sources).next →
          (D.sort, witness_id index) ∉
            Term.freeSupport replacement) :
    Formula.substituteFree target (source_id id)
        replacement
        (terms_flat_closure D start sources
          continuation) =
      close_witnesses_from D.sort start
        ((terms D start sources).next - start)
        (condition_conjunction
          ((terms D start sources).conditions.map
            (Formula.substituteFree target
              (source_id id) replacement))
          (Formula.substituteFree target
            (source_id id) replacement
            (continuation
              (terms D start sources).values))) := by
  rw [terms_flat_closure,
    close_witnesses_from_substituteFree
      D.sort target id replacement
      start ((terms D start sources).next - start)]
  · exact congrArg
      (close_witnesses_from D.sort start
        ((terms D start sources).next - start)) <|
        condition_conjunction_substituteFree
          target (source_id id) replacement
          (terms D start sources).conditions
          (continuation
            (terms D start sources).values)
  · exact hClosed
  · intro index hLower hUpper
    apply hFresh index hLower
    rwa [Nat.add_sub_of_le
      (terms_next_ge D start sources)] at hUpper

/--
关系续延下，参数表闭包的替换结果正是逐条件、逐值替换后的参数化闭包。
-/
theorem relation_flat_closure_substituteFree
    (D : Data σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ)
    (start : Nat) (relation : σ.RelSymbol)
    (arguments : List (Term σ))
    (hClosed : Term.BoundClosed replacement)
    (hFresh :
      ∀ index,
        start ≤ index →
        index < (terms D start arguments).next →
          (D.sort, witness_id index) ∉
            Term.freeSupport replacement) :
    Formula.substituteFree target (source_id id)
        replacement
        (terms_flat_closure D start arguments
          (Formula.rel relation)) =
      let parameterized :=
        (terms D start arguments).substituteFree
          target (source_id id) replacement
      close_witnesses_from D.sort start
        (parameterized.next - start)
        (condition_conjunction
          parameterized.conditions
          (Formula.rel relation
            parameterized.values)) := by
  rw [terms_flat_closure_substituteFree
    D target id replacement start arguments
      (Formula.rel relation) hClosed hFresh]
  simp [ArgsResult.substituteFree,
    Formula.substituteFree]

/--
“共享值代入已闭关系原子”的整体项闭包不暴露任何偶数见证变量。
-/
theorem term_flat_relation_substitute_witness_fresh
    (D : Data σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ)
    (start : Nat) (relation : σ.RelSymbol)
    (arguments : List (Term σ)) (index : Nat) :
    (D.sort, witness_id index) ∉
      Formula.freeSupport
        (term_flat_closure D start replacement <| fun value =>
          Formula.substituteFree target
            (source_id id) value
            (FunctionGraphElimination.relation
              D relation arguments)) := by
  let shared := term D start replacement
  apply close_witnesses_from_witness_fresh
  intro hOutside
  have hConditionFresh :
      ∀ condition,
        condition ∈ shared.conditions →
          (D.sort, witness_id index) ∉
            Formula.freeSupport condition := by
    rcases hOutside with hBelow | hAbove
    · exact term_conditions_witness_fresh_below
        D start replacement hBelow
    · rw [Nat.add_sub_of_le
          (term_next_ge D start replacement)]
        at hAbove
      exact term_conditions_witness_fresh_above
        D start replacement hAbove
  have hValueFresh :
      (D.sort, witness_id index) ∉
        Term.freeSupport shared.value := by
    rcases hOutside with hBelow | hAbove
    · exact term_value_witness_fresh_below
        D start replacement hBelow
    · rw [Nat.add_sub_of_le
          (term_next_ge D start replacement)]
        at hAbove
      exact term_value_witness_fresh_above
        D start replacement hAbove
  apply condition_conjunction_fresh
  · intro condition hCondition
    exact hConditionFresh condition <| by
      simpa [shared] using hCondition
  · exact Formula.not_mem_freeSupport_substituteFree
      (D.sort, witness_id index)
      target (source_id id) shared.value
      (FunctionGraphElimination.relation
        D relation arguments)
      hValueFresh
      (relation_witness_fresh
        D relation arguments index)

omit [DecidableEq σ.FuncSymbol] in
private theorem term_substitute_admissible
    {target sort : σ.SortSymbol} {id : FreeVarId}
    {replacement source : Term σ}
    (hReplacement :
      Term.Admissible replacement target)
    (hSource : Term.Admissible source sort) :
    Term.Admissible
      (Term.substituteFree target id replacement source)
      sort :=
  ⟨TermWellSorted.substituteFree
      id hSource.1 hReplacement.1,
    Term.substituteFree_scoped
      hSource.2 hReplacement.2⟩

omit [DecidableEq σ.FuncSymbol] in
private theorem args_substitute_admissible
    {target : σ.SortSymbol} {id : FreeVarId}
    {replacement : Term σ}
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hReplacement :
      Term.Admissible replacement target)
    (hSources : ArgsAdmissible sources sorts) :
    ArgsAdmissible
      (sources.map
        (Term.substituteFree target id replacement))
      sorts := by
  constructor
  · exact ArgsWellSorted.substituteFree
      target id hReplacement.1 hSources.1
  · intro term hTerm
    rcases List.mem_map.mp hTerm with
      ⟨source, hSource, rfl⟩
    exact Term.substituteFree_scoped
      (hSources.2 source hSource)
      hReplacement.2

namespace GraphPresentation

variable {D : Data σ}

/--
参数表图条件在源变量代入一个 admissible 共享值后仍可同时满足。
-/
theorem terms_substitute_conditions_truth
    (P : GraphPresentation D)
    (target : σ.SortSymbol) (id : FreeVarId)
    {replacement : Term σ}
    (hReplacement :
      Term.Admissible replacement target)
    (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsAdmissible sources sorts)
    (hFresh :
      ∀ index,
        start ≤ index →
        index < (terms D start sources).next →
          (D.sort, witness_id index) ∉
            Term.freeSupport replacement) :
    let parameterized :=
      (terms D start sources).substituteFree
        target (source_id id) replacement
    Derives P.theory []
      (close_witnesses_from D.sort start
        (parameterized.next - start)
        (condition_conjunction
          parameterized.conditions Formula.truth)) := by
  let compiled := terms D start sources
  let parameterized :=
    compiled.substituteFree
      target (source_id id) replacement
  have hTruth :=
    P.terms_flat_truth start hSources
  have hSubstituted :=
    Derives.substituteFree_theorem
      P.theory_sentence target
      (source_id id) hReplacement hTruth
  rw [terms_flat_closure_substituteFree
    D target id replacement start sources
      (fun _ => Formula.truth)
      hReplacement.2 hFresh] at hSubstituted
  simpa [compiled, parameterized,
    ArgsResult.substituteFree,
    Formula.substituteFree] using hSubstituted

mutual

/--
直接编译项替换，与在另一见证区间编译原项后代入共享编译值，结果可证相等。
-/
theorem term_substitute_compiled_eq
    (P : GraphPresentation D)
    (target : σ.SortSymbol) (id : FreeVarId)
    {replacement : Term σ}
    (hReplacement :
      Term.Admissible replacement target)
    (replacementStart localStart sourceStart : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort) :
    let shared :=
      term D replacementStart replacement
    let compiledLocal :=
      term D localStart
        (Term.substituteFree target id
          replacement source)
    let parameterized :=
      (term D sourceStart source).substituteFree
        target (source_id id) shared.value
    Derives P.theory
      (shared.conditions ++
        compiledLocal.conditions ++
          parameterized.conditions)
      (Formula.equal compiledLocal.value
        parameterized.value) := by
  cases source with
  | var value =>
      cases value with
      | bvar variableSort index =>
          let shared :=
            term D replacementStart replacement
          have hValue :
              Term.Admissible
                (.var (.bvar variableSort index)) sort := by
            simpa using hSource
          have hRefl :=
            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_refl
              (T := P.theory)
              (Γ := shared.conditions)
              (.var (.bvar variableSort index))
              (sort := sort)
              (hTermCheck :=
                Term.check_certificate_of_admissible
                  hValue)
          simpa [Term.substituteFree, term,
            TermResult.substituteFree, shared] using
              hRefl
      | fvar variableSort freeId =>
          by_cases hTarget :
              variableSort = target ∧ freeId = id
          · rcases hTarget with ⟨rfl, rfl⟩
            have hEqual :=
              term_compiled_eq P
                replacementStart localStart
                hReplacement
            have hSymmetry :=
              _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_symm
                hEqual
            simpa [Term.substituteFree, term,
              TermResult.substituteFree,
              source_id_injective.eq_iff] using
                hSymmetry
          · have hEncoded :
                ¬(variableSort = target ∧
                  source_id freeId = source_id id) := by
              intro hEqual
              exact hTarget
                ⟨hEqual.1,
                  source_id_injective hEqual.2⟩
            let shared :=
              term D replacementStart replacement
            have hValue :
                Term.Admissible
                  (.var
                    (.fvar variableSort
                      (source_id freeId))) sort := by
              simpa [source_term] using
                source_term_admissible hSource
            have hRefl :=
              _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_refl
                (T := P.theory)
                (Γ := shared.conditions)
                (.var
                  (.fvar variableSort
                    (source_id freeId)))
                (sort := sort)
                (hTermCheck :=
                  Term.check_certificate_of_admissible
                    hValue)
            simpa [Term.substituteFree, term,
              TermResult.substituteFree,
              hTarget, hEncoded, shared] using hRefl
  | app function arguments =>
      have hArguments :=
        app_arguments_admissible
          function arguments hSource
      have hShared :
          Term.Admissible
            (term D replacementStart
              replacement).value target :=
        ⟨(term_well_formed
            D replacementStart
              hReplacement.1).1,
          (term_scoped
            D replacementStart
              hReplacement.2).1⟩
      have hSubstitutedArguments :=
        args_substitute_admissible
          (id := id) hReplacement hArguments
      by_cases hFunction : function = D.symbol
      · subst function
        let shared :=
          term D replacementStart replacement
        let localArguments :=
          terms D (localStart + 1)
            (arguments.map
              (Term.substituteFree target id
                replacement))
        let sourceArguments :=
          terms D (sourceStart + 1) arguments
        let parameterizedArguments :=
          sourceArguments.substituteFree
            target (source_id id) shared.value
        let localResult :=
          Term.var
            (.fvar D.sort
              (witness_id localStart))
        let sourceResult :=
          Term.var
            (.fvar D.sort
              (witness_id sourceStart))
        let parameterizedResult :=
          Term.substituteFree target
            (source_id id) shared.value
            sourceResult
        let Γ :=
          shared.conditions ++
            (D.graph localArguments.values
                localResult ::
              localArguments.conditions) ++
            (D.graph parameterizedArguments.values
                parameterizedResult ::
              parameterizedArguments.conditions)
        have hSort : sort = D.sort := by
          apply TermWellSorted.sort_unique
            hSource.1
          rw [← D.codomain_eq]
          exact TermWellSorted.app
            D.symbol hArguments.1
        subst sort
        have hLocalArguments :
            ArgsAdmissible localArguments.values
              (σ.funcDomain D.symbol) := by
          simpa [localArguments] using
            terms_admissible D (localStart + 1)
              hSubstitutedArguments
        have hSourceArguments :
            ArgsAdmissible sourceArguments.values
              (σ.funcDomain D.symbol) := by
          simpa [sourceArguments] using
            terms_admissible D (sourceStart + 1)
              hArguments
        have hParameterizedArguments :
            ArgsAdmissible
              parameterizedArguments.values
              (σ.funcDomain D.symbol) := by
          simpa [parameterizedArguments,
            ArgsResult.substituteFree] using
              args_substitute_admissible
                hShared hSourceArguments
        have hLocalResult :
            Term.Admissible localResult D.sort :=
          ⟨TermWellSorted.fvar D.sort
              (witness_id localStart),
            TermScoped.fvar D.sort
              (witness_id localStart)⟩
        have hParameterizedResult :
            Term.Admissible
              parameterizedResult D.sort :=
          term_substitute_admissible
            hShared
            ⟨TermWellSorted.fvar D.sort
                (witness_id sourceStart),
              TermScoped.fvar D.sort
                (witness_id sourceStart)⟩
        have hArgumentsEqual :=
          terms_substitute_compiled_eq P
            target id hReplacement
            replacementStart
            (localStart + 1)
            (sourceStart + 1)
            hArguments
        have hArgumentsEqual' :
            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
              P.theory Γ localArguments.values
                parameterizedArguments.values := by
          apply hArgumentsEqual.context_weaken
          intro formula hFormula
          rcases List.mem_append.mp hFormula with
            hFirst | hParameterizedCondition
          · rcases List.mem_append.mp hFirst with
              hSharedCondition | hLocalCondition
            · simp [Γ, shared, hSharedCondition]
            · simp [Γ, localArguments,
                hLocalCondition]
          · simpa [Γ, shared, sourceArguments,
              parameterizedArguments] using
                Or.inr (Or.inr
                  (Or.inr (Or.inr
                    hParameterizedCondition)))
        have hGraphEquivalent :=
          P.graph_args_congr
            hLocalArguments hParameterizedArguments
            hLocalResult hArgumentsEqual'
        have hLocalGraph :
            Derives P.theory Γ
              (D.graph localArguments.values
                localResult) :=
          Derives.assumption_of_mem
            (by simp [Γ])
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                graph_admissible D
                  hLocalArguments hLocalResult)
        have hAligned :
            Derives P.theory Γ
              (D.graph parameterizedArguments.values
                localResult) :=
          Derives.iff_elim_right
            hGraphEquivalent hLocalGraph
        have hParameterizedGraph :
            Derives P.theory Γ
              (D.graph parameterizedArguments.values
                parameterizedResult) :=
          Derives.assumption_of_mem
            (by simp [Γ])
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                graph_admissible D
                  hParameterizedArguments
                  hParameterizedResult)
        have hFunctional :
            Derives P.theory Γ
              (Formula.imp
                (D.graph
                  parameterizedArguments.values
                  localResult)
                (Formula.imp
                  (D.graph
                    parameterizedArguments.values
                    parameterizedResult)
                  (Formula.equal localResult
                    parameterizedResult))) :=
          (P.functional hParameterizedArguments
            hLocalResult
            hParameterizedResult).context_weaken
              (by simp)
        have hResult :=
          (hFunctional.imp_elim hAligned).imp_elim
            hParameterizedGraph
        have hGraphSubstitution :
            D.graph parameterizedArguments.values
                parameterizedResult =
              Formula.substituteFree target
                (source_id id) shared.value
                (D.graph sourceArguments.values
                  sourceResult) := by
          exact D.graph_substituteFree
            target (source_id id) shared.value
              sourceArguments.values sourceResult
        dsimp only [Γ] at hResult
        rw [hGraphSubstitution] at hResult
        have hWitness :
            ¬(D.sort = target ∧
              witness_id sourceStart =
                source_id id) := by
          intro hEqual
          exact
            (source_id_ne_witness_id
              id sourceStart) hEqual.2.symm
        simpa [term, TermResult.substituteFree,
          ArgsResult.substituteFree,
          shared, localArguments,
          sourceArguments,
          parameterizedArguments,
          localResult, sourceResult,
          parameterizedResult, Γ,
          Term.substituteFree, hWitness] using
            hResult
      · let shared :=
          term D replacementStart replacement
        let localArguments :=
          terms D localStart
            (arguments.map
              (Term.substituteFree target id
                replacement))
        let sourceArguments :=
          terms D sourceStart arguments
        let parameterizedArguments :=
          sourceArguments.substituteFree
            target (source_id id) shared.value
        have hArgumentsEqual :=
          terms_substitute_compiled_eq P
            target id hReplacement
            replacementStart localStart sourceStart
            hArguments
        have hLocalArguments :
            ArgsAdmissible localArguments.values
              (σ.funcDomain function) := by
          simpa [localArguments] using
            terms_admissible D localStart
              hSubstitutedArguments
        have hSourceArguments :
            ArgsAdmissible sourceArguments.values
              (σ.funcDomain function) := by
          simpa [sourceArguments] using
            terms_admissible D sourceStart
              hArguments
        have hParameterizedArguments :
            ArgsAdmissible
              parameterizedArguments.values
              (σ.funcDomain function) := by
          simpa [parameterizedArguments,
            ArgsResult.substituteFree] using
              args_substitute_admissible
                hShared hSourceArguments
        have hResult :=
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.function_term_congr_arguments_of_equalities
            (T := P.theory) function
            hLocalArguments
            hParameterizedArguments
            hArgumentsEqual
        simpa [term, Term.substituteFree,
          hFunction,
          TermResult.substituteFree,
          ArgsResult.substituteFree,
          shared, localArguments,
          sourceArguments,
          parameterizedArguments] using hResult

/-- 参数表版本逐项给出替换编译结果等式。 -/
theorem terms_substitute_compiled_eq
    (P : GraphPresentation D)
    (target : σ.SortSymbol) (id : FreeVarId)
    {replacement : Term σ}
    (hReplacement :
      Term.Admissible replacement target)
    (replacementStart localStart sourceStart : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsAdmissible sources sorts) :
    let shared :=
      term D replacementStart replacement
    let compiledLocal :=
      terms D localStart
        (sources.map
          (Term.substituteFree target id replacement))
    let parameterized :=
      (terms D sourceStart sources).substituteFree
        target (source_id id) shared.value
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
      P.theory
      (shared.conditions ++
        compiledLocal.conditions ++
          parameterized.conditions)
      compiledLocal.values parameterized.values := by
  cases sources with
  | nil =>
      exact .nil
  | cons head tail =>
      rcases ArgsAdmissible.exists_cons hSources with
        ⟨headSort, tailSorts, hSorts,
          hHead, hTail⟩
      subst sorts
      let shared :=
        term D replacementStart replacement
      let localHead :=
        term D localStart
          (Term.substituteFree target id
            replacement head)
      let sourceHead :=
        term D sourceStart head
      let parameterizedHead :=
        sourceHead.substituteFree
          target (source_id id) shared.value
      let localTail :=
        terms D localHead.next
          (tail.map
            (Term.substituteFree target id replacement))
      let sourceTail :=
        terms D sourceHead.next tail
      let parameterizedTail :=
        sourceTail.substituteFree
          target (source_id id) shared.value
      let Γ :=
        shared.conditions ++
          (localHead.conditions ++
            localTail.conditions) ++
          (parameterizedHead.conditions ++
            parameterizedTail.conditions)
      have hHeadEqual :=
        term_substitute_compiled_eq P
          target id hReplacement
          replacementStart localStart sourceStart
          hHead
      have hHeadEqual' :
          Derives P.theory Γ
            (Formula.equal localHead.value
              parameterizedHead.value) := by
        apply hHeadEqual.context_weaken
        intro formula hFormula
        rcases List.mem_append.mp hFormula with
          hFirst | hParameterizedCondition
        · rcases List.mem_append.mp hFirst with
            hSharedCondition | hLocalCondition
          · simp [Γ, shared, hSharedCondition]
          · simp [Γ, localHead, hLocalCondition]
        · simpa [Γ, shared, sourceHead,
            parameterizedHead] using
              Or.inr (Or.inr
                (Or.inr (Or.inl
                  hParameterizedCondition)))
      have hTailEqual :=
        terms_substitute_compiled_eq P
          target id hReplacement
          replacementStart
          localHead.next sourceHead.next
          hTail
      have hTailEqual' :
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
            P.theory Γ localTail.values
              parameterizedTail.values := by
        apply hTailEqual.context_weaken
        intro formula hFormula
        rcases List.mem_append.mp hFormula with
          hFirst | hParameterizedCondition
        · rcases List.mem_append.mp hFirst with
            hSharedCondition | hLocalCondition
          · simp [Γ, shared, hSharedCondition]
          · simp [Γ, localTail, hLocalCondition]
        · simpa [Γ, shared, sourceTail,
            parameterizedTail] using
              Or.inr (Or.inr
                (Or.inr (Or.inr
                  hParameterizedCondition)))
      have hEqual :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality.cons
          hHeadEqual' hTailEqual'
      simpa [terms, TermResult.substituteFree,
        ArgsResult.substituteFree,
        shared, localHead, sourceHead,
        parameterizedHead, localTail,
        sourceTail, parameterizedTail, Γ,
        List.map_append, List.append_assoc] using
          hEqual

end

/--
两个不相交见证区间编译同一关系原子时，左侧闭包可在图理论中重建右侧闭包。
-/
theorem relation_flat_imp_of_disjoint
    (P : GraphPresentation D)
    (relation : σ.RelSymbol)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissible arguments
        (σ.relDomain relation))
    (leftStart rightStart : Nat)
    (hDisjoint :
      (terms D leftStart arguments).next ≤
          rightStart ∨
        (terms D rightStart arguments).next ≤
          leftStart) :
    Derives P.theory []
      (Formula.imp
        (terms_flat_closure D leftStart arguments
          (Formula.rel relation))
        (terms_flat_closure D rightStart arguments
          (Formula.rel relation))) := by
  let left := terms D leftStart arguments
  let right := terms D rightStart arguments
  let leftFormula :=
    terms_flat_closure D leftStart arguments
      (Formula.rel relation)
  let rightFormula :=
    terms_flat_closure D rightStart arguments
      (Formula.rel relation)
  have hLeftValues :
      ArgsAdmissible left.values
        (σ.relDomain relation) := by
    simpa [left] using
      terms_admissible D leftStart hArguments
  have hRightValues :
      ArgsAdmissible right.values
        (σ.relDomain relation) := by
    simpa [right] using
      terms_admissible D rightStart hArguments
  have hLeftFormula :
      Formula.Admissible leftFormula := by
    exact terms_flat_closure_admissible
      D leftStart hArguments
      (Formula.rel relation)
      (fun hValues =>
        Formula.Admissible.rel hValues)
  apply Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hLeftFormula)
  let Γ : Context σ := [leftFormula]
  have hLeftClosed :
      Derives P.theory Γ leftFormula :=
    Derives.assumption_of_mem
      (by simp [Γ])
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          hLeftFormula)
  change Derives P.theory Γ rightFormula
  apply P.terms_flat_elim_to_conditions
      leftStart hArguments
      (Formula.rel relation)
  · intro values hValues
    exact Formula.Admissible.rel hValues
  · intro index hLower hUpper formula hFormula
    have hFormulaEq : formula = leftFormula :=
      List.mem_singleton.mp <| by
        simpa [Γ] using hFormula
    subst formula
    exact relation_flat_witness_fresh
      D leftStart relation arguments index
  · intro index hLower hUpper
    exact relation_flat_witness_fresh
      D rightStart relation arguments index
  · simpa [leftFormula, Γ] using hLeftClosed
  · let Δ : Context σ :=
      left.conditions ++
        Formula.rel relation left.values :: Γ
    apply P.terms_flat_derives_from_conditions
        rightStart hArguments
        (Γ := Δ)
        (continuation := Formula.rel relation)
    · intro index hLower hUpper formula hFormula
      rcases List.mem_append.mp hFormula with
        hCondition | hFormula
      · rcases hDisjoint with hBefore | hAfter
        · exact terms_conditions_witness_fresh_above
            D leftStart arguments
              (Nat.le_trans hBefore hLower)
              formula <| by
                simpa [left] using hCondition
        · exact terms_conditions_witness_fresh_below
            D leftStart arguments
              (Nat.lt_of_lt_of_le
                hUpper hAfter)
              formula <| by
                simpa [left] using hCondition
      · rcases List.mem_cons.mp hFormula with
          rfl | hFormula
        · rcases hDisjoint with hBefore | hAfter
          · simpa [Formula.freeSupport, left] using
              terms_values_witness_fresh_above
                D leftStart arguments
                  (Nat.le_trans hBefore hLower)
          · simpa [Formula.freeSupport, left] using
              terms_values_witness_fresh_below
                D leftStart arguments
                  (Nat.lt_of_lt_of_le
                    hUpper hAfter)
        · have hFormulaEq :
              formula = leftFormula :=
            List.mem_singleton.mp <| by
              simpa [Γ] using hFormula
          subst formula
          exact relation_flat_witness_fresh
            D leftStart relation arguments index
    · intro values hValues
      exact Formula.Admissible.rel hValues
    · have hEqual :=
        terms_compiled_eq P
          leftStart rightStart hArguments
      have hEqual' :
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
            P.theory
            (right.conditions ++ Δ)
            left.values right.values := by
        apply hEqual.context_weaken
        intro formula hFormula
        rcases List.mem_append.mp hFormula with
          hLeftCondition | hRightCondition
        · exact List.mem_append.mpr <| Or.inr <|
            List.mem_append.mpr <| Or.inl <| by
              simpa [left] using hLeftCondition
        · exact List.mem_append.mpr <| Or.inl <| by
            simpa [right] using hRightCondition
      have hEquivalent :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.relation_congr_arguments_of_equalities
          (T := P.theory) relation
          hLeftValues hRightValues hEqual'
      have hLeftCore :
          Derives P.theory
            (right.conditions ++ Δ)
            (Formula.rel relation left.values) :=
        Derives.assumption_of_mem
          (List.mem_append.mpr <| Or.inr <|
            List.mem_append.mpr <| Or.inr <| by
              simp)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible <|
              Formula.Admissible.rel hLeftValues)
      exact Derives.iff_elim_right
        hEquivalent hLeftCore

/-- 不相交见证区间中的两份关系原子编译闭包逻辑等价。 -/
theorem relation_flat_iff_of_disjoint
    (P : GraphPresentation D)
    (relation : σ.RelSymbol)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissible arguments
        (σ.relDomain relation))
    (leftStart rightStart : Nat)
    (hDisjoint :
      (terms D leftStart arguments).next ≤
          rightStart ∨
        (terms D rightStart arguments).next ≤
          leftStart) :
    Derives P.theory []
      (Formula.iff
        (terms_flat_closure D leftStart arguments
          (Formula.rel relation))
        (terms_flat_closure D rightStart arguments
          (Formula.rel relation))) := by
  apply Derives.iff_intro
  · exact Derives.imp_elim_assumption <|
      relation_flat_imp_of_disjoint P relation
        hArguments leftStart rightStart hDisjoint
  · have hDisjoint' :
        (terms D rightStart arguments).next ≤
            leftStart ∨
          (terms D leftStart arguments).next ≤
            rightStart :=
      hDisjoint.elim Or.inr Or.inl
    exact Derives.imp_elim_assumption <|
      relation_flat_imp_of_disjoint P relation
        hArguments rightStart leftStart hDisjoint'

/-- 同一关系原子的扁平编译闭包与见证起点无关。 -/
theorem relation_flat_iff
    (P : GraphPresentation D)
    (relation : σ.RelSymbol)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissible arguments
        (σ.relDomain relation))
    (leftStart rightStart : Nat) :
    Derives P.theory []
      (Formula.iff
        (terms_flat_closure D leftStart arguments
          (Formula.rel relation))
        (terms_flat_closure D rightStart arguments
          (Formula.rel relation))) := by
  let commonStart :=
    max (terms D leftStart arguments).next
      (terms D rightStart arguments).next
  have hLeft :=
    relation_flat_iff_of_disjoint P relation
      hArguments leftStart commonStart <|
        Or.inl <| by
          exact Nat.le_max_left _ _
  have hRight :=
    relation_flat_iff_of_disjoint P relation
      hArguments rightStart commonStart <|
        Or.inl <| by
          exact Nat.le_max_right _ _
  exact
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
      hLeft <|
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
          hRight

/-- 公共关系原子编译器等价于任意起点的扁平参数闭包。 -/
theorem relation_iff_flat
    (P : GraphPresentation D)
    (relation : σ.RelSymbol)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissible arguments
        (σ.relDomain relation))
    (start : Nat) :
    Derives P.theory []
      (Formula.iff
        (FunctionGraphElimination.relation
          D relation arguments)
        (terms_flat_closure D start arguments
          (Formula.rel relation))) := by
  simpa [FunctionGraphElimination.relation,
    terms_flat_closure,
    close_witnesses_from_zero_start] using
      relation_flat_iff P relation
        hArguments 0 start

/--
关系原子的直接替换编译，与原参数编译后代入共享编译值，在全部图条件下逻辑等价。
-/
theorem relation_substitute_core_iff
    (P : GraphPresentation D)
    (target : σ.SortSymbol) (id : FreeVarId)
    {replacement : Term σ}
    (hReplacement :
      Term.Admissible replacement target)
    (replacementStart localStart sourceStart : Nat)
    (relation : σ.RelSymbol)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissible arguments
        (σ.relDomain relation)) :
    let shared :=
      term D replacementStart replacement
    let compiledLocal :=
      terms D localStart
        (arguments.map
          (Term.substituteFree target id replacement))
    let parameterized :=
      (terms D sourceStart arguments).substituteFree
        target (source_id id) shared.value
    Derives P.theory
      (shared.conditions ++
        compiledLocal.conditions ++
          parameterized.conditions)
      (Formula.iff
        (Formula.rel relation compiledLocal.values)
        (Formula.rel relation parameterized.values)) := by
  let shared :=
    term D replacementStart replacement
  let compiledLocal :=
    terms D localStart
      (arguments.map
        (Term.substituteFree target id replacement))
  let source :=
    terms D sourceStart arguments
  let parameterized :=
    source.substituteFree
      target (source_id id) shared.value
  have hShared :
      Term.Admissible shared.value target := by
    exact
      ⟨(term_well_formed
          D replacementStart hReplacement.1).1,
        (term_scoped
          D replacementStart hReplacement.2).1⟩
  have hSubstituted :
      ArgsAdmissible
        (arguments.map
          (Term.substituteFree target id replacement))
        (σ.relDomain relation) :=
    args_substitute_admissible
      (id := id) hReplacement hArguments
  have hLocal :
      ArgsAdmissible compiledLocal.values
        (σ.relDomain relation) := by
    simpa [compiledLocal] using
      terms_admissible D localStart hSubstituted
  have hSource :
      ArgsAdmissible source.values
        (σ.relDomain relation) := by
    simpa [source] using
      terms_admissible D sourceStart hArguments
  have hParameterized :
      ArgsAdmissible parameterized.values
        (σ.relDomain relation) := by
    simpa [parameterized,
      ArgsResult.substituteFree] using
        args_substitute_admissible
          (id := source_id id) hShared hSource
  have hEqual :=
    terms_substitute_compiled_eq P
      target id hReplacement
      replacementStart localStart sourceStart
      hArguments
  have hEquivalent :=
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.relation_congr_arguments_of_equalities
      (T := P.theory) relation
      hLocal hParameterized hEqual
  simpa [shared, compiledLocal, source,
    parameterized] using hEquivalent

/--
关系原子的直接替换编译，等价于先求出一份共享替换值，再将其代入原关系编译。
-/
theorem relation_substitute_iff
    (P : GraphPresentation D)
    (target : σ.SortSymbol) (id : FreeVarId)
    {replacement : Term σ}
    (hReplacement :
      Term.Admissible replacement target)
    (relation : σ.RelSymbol)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissible arguments
        (σ.relDomain relation)) :
    Derives P.theory []
      (Formula.iff
        (FunctionGraphElimination.relation D relation
          (arguments.map
            (Term.substituteFree
              target id replacement)))
        (term_flat_closure D 0 replacement <| fun value =>
          Formula.substituteFree target
            (source_id id) value
            (FunctionGraphElimination.relation
              D relation arguments))) := by
  let shared := term D 0 replacement
  let sourceStart := shared.next
  let source := terms D sourceStart arguments
  let parameterized :=
    source.substituteFree
      target (source_id id) shared.value
  let localStart := source.next
  let substituted :=
    arguments.map
      (Term.substituteFree target id replacement)
  let compiledLocal :=
    terms D localStart substituted
  let localCore :=
    Formula.rel relation compiledLocal.values
  let parameterizedCore :=
    Formula.rel relation parameterized.values
  let localFlat :=
    terms_flat_closure D localStart substituted
      (Formula.rel relation)
  let parameterizedFlat :=
    close_witnesses_from D.sort sourceStart
      (parameterized.next - sourceStart)
      (condition_conjunction
        parameterized.conditions parameterizedCore)
  let sharedCore :=
    Formula.substituteFree target
      (source_id id) shared.value
      (FunctionGraphElimination.relation
        D relation arguments)
  have hShared :
      Term.Admissible shared.value target :=
    ⟨(term_well_formed
        D 0 hReplacement.1).1,
      (term_scoped
        D 0 hReplacement.2).1⟩
  have hSubstituted :
      ArgsAdmissible substituted
        (σ.relDomain relation) := by
    simpa [substituted] using
      args_substitute_admissible
        (id := id) hReplacement hArguments
  have hSource :
      ArgsAdmissible source.values
        (σ.relDomain relation) := by
    simpa [source] using
      terms_admissible D sourceStart hArguments
  have hParameterized :
      ArgsAdmissible parameterized.values
        (σ.relDomain relation) := by
    simpa [parameterized,
      ArgsResult.substituteFree] using
        args_substitute_admissible
          (id := source_id id)
          hShared hSource
  have hSharedLocal :
      shared.next ≤ localStart := by
    simpa [sourceStart, source, localStart] using
      terms_next_ge D shared.next arguments
  have hParameterizedConditions :
      ∀ condition,
        condition ∈ parameterized.conditions →
          Formula.Admissible condition := by
    intro condition hCondition
    rcases List.mem_map.mp (by
      simpa [parameterized, source,
        ArgsResult.substituteFree] using hCondition) with
      ⟨sourceCondition, hSourceCondition, rfl⟩
    exact Formula.Admissible.substituteFree
      target (source_id id)
      (terms_conditions_admissible
        D sourceStart hArguments
        sourceCondition <| by
          simpa [source] using hSourceCondition)
      hShared
  have hLocalConditions :
      ∀ condition,
        condition ∈ compiledLocal.conditions →
          Formula.Admissible condition := by
    simpa [compiledLocal] using
      terms_conditions_admissible
        D localStart hSubstituted
  have hLocalFlat :
      Formula.Admissible localFlat := by
    exact terms_flat_closure_admissible
      D localStart hSubstituted
      (Formula.rel relation)
      (fun hValues =>
        Formula.Admissible.rel hValues)
  have hParameterizedCore :
      Formula.Admissible parameterizedCore := by
    exact Formula.Admissible.rel hParameterized
  have hSharedFresh :
      ∀ index,
        sourceStart ≤ index →
        index < source.next →
          (D.sort, witness_id index) ∉
            Term.freeSupport shared.value := by
    intro index hLower hUpper
    exact term_value_witness_fresh_above
      D 0 replacement <| by
        simpa [sourceStart, shared] using hLower
  have hSubstitutionEquivalent :
      Derives P.theory []
        (Formula.iff sharedCore
          parameterizedFlat) := by
    have hEquivalent :=
      relation_iff_flat P relation
        hArguments sourceStart
    have hSubstitutedEquivalent :=
      Derives.substituteFree_theorem
        P.theory_sentence target
        (source_id id) hShared hEquivalent
    simp only [Formula.substituteFree]
      at hSubstitutedEquivalent
    rw [relation_flat_closure_substituteFree
      D target id shared.value sourceStart
      relation arguments hShared.2 hSharedFresh]
      at hSubstitutedEquivalent
    simpa [sharedCore, parameterizedFlat,
      source, parameterized] using
        hSubstitutedEquivalent
  have hParameterizedTruth :
      Derives P.theory []
        (close_witnesses_from D.sort sourceStart
          (parameterized.next - sourceStart)
          (condition_conjunction
            parameterized.conditions
            Formula.truth)) := by
    have hTruth :=
      P.terms_substitute_conditions_truth
        target id hShared sourceStart
        hArguments hSharedFresh
    simpa [source, parameterized] using hTruth
  have hLocalTruth :
      Derives P.theory []
        (close_witnesses_from D.sort localStart
          (compiledLocal.next - localStart)
          (condition_conjunction
            compiledLocal.conditions
            Formula.truth)) := by
    simpa [localFlat, terms_flat_closure,
      compiledLocal] using
        P.terms_flat_truth
          localStart hSubstituted
  have hSharedTruth :
      Derives P.theory []
        (close_witnesses_from D.sort 0
          shared.next
          (condition_conjunction
            shared.conditions Formula.truth)) := by
    simpa [term_flat_closure, shared] using
      P.term_flat_truth 0 hReplacement
  have hCore :
      Derives P.theory
        (shared.conditions ++
          compiledLocal.conditions ++
            parameterized.conditions)
        (Formula.iff localCore
          parameterizedCore) := by
    simpa [shared, sourceStart, source,
      parameterized, localStart, substituted,
      compiledLocal, localCore,
      parameterizedCore] using
        relation_substitute_core_iff P
          target id hReplacement
          0 localStart sourceStart
          relation hArguments
  let Γ₁ : Context σ :=
    shared.conditions ++
      parameterized.conditions
  have hParameterizedConditionFreshAbove :
      ∀ index,
        localStart ≤ index →
        ∀ condition,
          condition ∈ parameterized.conditions →
            (D.sort, witness_id index) ∉
              Formula.freeSupport condition := by
    intro index hLower condition hCondition
    rcases List.mem_map.mp (by
      simpa [parameterized, source,
        ArgsResult.substituteFree] using hCondition) with
      ⟨sourceCondition, hSourceCondition, rfl⟩
    apply Formula.not_mem_freeSupport_substituteFree
    · exact term_value_witness_fresh_above
        D 0 replacement
          (Nat.le_trans hSharedLocal hLower)
    · exact terms_conditions_witness_fresh_above
        D sourceStart arguments
          (by simpa [source, localStart] using hLower)
          sourceCondition <| by
            simpa [source] using hSourceCondition
  have hParameterizedCoreFreshAbove :
      ∀ index,
        localStart ≤ index →
          (D.sort, witness_id index) ∉
            Formula.freeSupport parameterizedCore := by
    intro index hLower
    have hFresh :=
      Formula.not_mem_freeSupport_substituteFree
        (D.sort, witness_id index)
        target (source_id id) shared.value
        (Formula.rel relation source.values)
        (term_value_witness_fresh_above
          D 0 replacement
          (Nat.le_trans hSharedLocal hLower))
        (by
          simpa [Formula.freeSupport, source] using
            terms_values_witness_fresh_above
              D sourceStart arguments <| by
                simpa [source, localStart] using hLower)
    simpa [parameterizedCore, parameterized,
      ArgsResult.substituteFree,
      Formula.substituteFree] using hFresh
  have hLocalParameterizedCore :
      Derives P.theory Γ₁
        (Formula.iff localFlat
          parameterizedCore) := by
    apply closed_conditions_iff_source_in_context
        P.theory_sentence D.sort localStart
        (compiledLocal.next - localStart)
        hLocalConditions hParameterizedCore
    · intro index hLower hUpper formula hFormula
      rcases List.mem_append.mp hFormula with
        hSharedCondition | hParameterizedCondition
      · exact term_conditions_witness_fresh_above
          D 0 replacement
            (Nat.le_trans hSharedLocal hLower)
            formula <| by
              simpa [shared] using hSharedCondition
      · exact hParameterizedConditionFreshAbove
          index hLower formula <| by
            simpa [Γ₁] using hParameterizedCondition
    · intro index hLower hUpper
      exact hParameterizedCoreFreshAbove
        index hLower
    · apply hLocalTruth.context_weaken
      intro formula hFormula
      cases hFormula
    · apply hCore.context_weaken
      intro formula hFormula
      rcases List.mem_append.mp hFormula with
        hFirst | hParameterizedCondition
      · rcases List.mem_append.mp hFirst with
          hSharedCondition | hLocalCondition
        · simp [Γ₁, hSharedCondition]
        · simp [Γ₁, hLocalCondition]
      · simp [Γ₁, hParameterizedCondition]
  let Γ₂ : Context σ := shared.conditions
  have hParameterizedLocal :
      Derives P.theory Γ₂
        (Formula.iff parameterizedFlat
          localFlat) := by
    apply closed_conditions_iff_source_in_context
        P.theory_sentence D.sort sourceStart
        (parameterized.next - sourceStart)
        hParameterizedConditions hLocalFlat
    · intro index hLower hUpper formula hFormula
      exact term_conditions_witness_fresh_above
        D 0 replacement
          (by simpa [sourceStart, shared] using hLower)
          formula <| by
            simpa [Γ₂, shared] using hFormula
    · intro index hLower hUpper
      exact relation_flat_witness_fresh
        D localStart relation substituted index
    · apply hParameterizedTruth.context_weaken
      intro formula hFormula
      cases hFormula
    · have hEquivalent :
          Derives P.theory
            (parameterized.conditions ++ Γ₂)
            (Formula.iff localFlat
              parameterizedCore) := by
        apply hLocalParameterizedCore.context_weaken
        intro formula hFormula
        rcases List.mem_append.mp hFormula with
          hSharedCondition | hParameterizedCondition
        · exact List.mem_append.mpr <|
            Or.inr <| by
              simpa [Γ₂] using hSharedCondition
        · exact List.mem_append.mpr <|
            Or.inl hParameterizedCondition
      exact
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
          hEquivalent
  have hOuterLocal :
      Derives P.theory []
        (Formula.iff
          (term_flat_closure D 0 replacement <| fun value =>
            Formula.substituteFree target
              (source_id id) value
              (FunctionGraphElimination.relation
                D relation arguments))
          localFlat) := by
    have hSharedEquivalent :
        Derives P.theory shared.conditions
          (Formula.iff sharedCore localFlat) :=
      _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
        (hSubstitutionEquivalent.context_weaken
          (by
            intro formula hFormula
            cases hFormula))
        (by simpa [Γ₂] using hParameterizedLocal)
    have hClosed :=
      closed_conditions_iff_source_in_context
        (conditions := shared.conditions)
        (core := sharedCore)
        (source := localFlat)
        P.theory_sentence D.sort 0 shared.next
        (by
          simpa [shared] using
            term_conditions_admissible
              D 0 hReplacement)
        hLocalFlat
        (Γ := ([] : Context σ))
        (by
          intro index hLower hUpper formula hFormula
          cases hFormula)
        (by
          intro index hLower hUpper
          exact relation_flat_witness_fresh
            D localStart relation substituted index)
        hSharedTruth
        (by simpa using hSharedEquivalent)
    simpa [term_flat_closure, sharedCore,
      shared] using hClosed
  have hDirect :=
    relation_iff_flat P relation
      hSubstituted localStart
  exact
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
      hDirect <|
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
          hOuterLocal

/--
等式原子的两端分别满足替换编译合同，因而两张编译等式在全部图条件下逻辑等价。
-/
theorem equality_substitute_core_iff
    (P : GraphPresentation D)
    (target : σ.SortSymbol) (id : FreeVarId)
    {replacement : Term σ}
    (hReplacement :
      Term.Admissible replacement target)
    (replacementStart localStart sourceStart : Nat)
    {left right : Term σ} {sort : σ.SortSymbol}
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort) :
    let shared :=
      term D replacementStart replacement
    let localLeft :=
      term D localStart
        (Term.substituteFree target id replacement left)
    let sourceLeft :=
      term D sourceStart left
    let parameterizedLeft :=
      sourceLeft.substituteFree
        target (source_id id) shared.value
    let localRight :=
      term D localLeft.next
        (Term.substituteFree target id replacement right)
    let sourceRight :=
      term D sourceLeft.next right
    let parameterizedRight :=
      sourceRight.substituteFree
        target (source_id id) shared.value
    let Γ :=
      shared.conditions ++
        (localLeft.conditions ++ localRight.conditions) ++
        (parameterizedLeft.conditions ++
          parameterizedRight.conditions)
    Derives P.theory Γ
      (Formula.iff
        (Formula.equal localLeft.value localRight.value)
        (Formula.equal
          parameterizedLeft.value
          parameterizedRight.value)) := by
  let shared :=
    term D replacementStart replacement
  let localLeft :=
    term D localStart
      (Term.substituteFree target id replacement left)
  let sourceLeft :=
    term D sourceStart left
  let parameterizedLeft :=
    sourceLeft.substituteFree
      target (source_id id) shared.value
  let localRight :=
    term D localLeft.next
      (Term.substituteFree target id replacement right)
  let sourceRight :=
    term D sourceLeft.next right
  let parameterizedRight :=
    sourceRight.substituteFree
      target (source_id id) shared.value
  let Γ :=
    shared.conditions ++
      (localLeft.conditions ++ localRight.conditions) ++
      (parameterizedLeft.conditions ++
        parameterizedRight.conditions)
  have hShared :
      Term.Admissible shared.value target := by
    exact
      ⟨(term_well_formed
          D replacementStart hReplacement.1).1,
        (term_scoped
          D replacementStart hReplacement.2).1⟩
  have hLeftSubstituted :=
    term_substitute_admissible
      (id := id) hReplacement hLeft
  have hRightSubstituted :=
    term_substitute_admissible
      (id := id) hReplacement hRight
  have hLocalLeft :
      Term.Admissible localLeft.value sort := by
    exact
      ⟨(term_well_formed
          D localStart hLeftSubstituted.1).1,
        (term_scoped
          D localStart hLeftSubstituted.2).1⟩
  have hLocalRight :
      Term.Admissible localRight.value sort := by
    exact
      ⟨(term_well_formed
          D localLeft.next hRightSubstituted.1).1,
        (term_scoped
          D localLeft.next hRightSubstituted.2).1⟩
  have hSourceLeft :
      Term.Admissible sourceLeft.value sort := by
    exact
      ⟨(term_well_formed
          D sourceStart hLeft.1).1,
        (term_scoped
          D sourceStart hLeft.2).1⟩
  have hSourceRight :
      Term.Admissible sourceRight.value sort := by
    exact
      ⟨(term_well_formed
          D sourceLeft.next hRight.1).1,
        (term_scoped
          D sourceLeft.next hRight.2).1⟩
  have hParameterizedLeft :
      Term.Admissible parameterizedLeft.value sort := by
    simpa [parameterizedLeft,
      TermResult.substituteFree] using
        term_substitute_admissible
          (id := source_id id) hShared hSourceLeft
  have hParameterizedRight :
      Term.Admissible parameterizedRight.value sort := by
    simpa [parameterizedRight,
      TermResult.substituteFree] using
        term_substitute_admissible
          (id := source_id id) hShared hSourceRight
  have hLeftEqual :=
    term_substitute_compiled_eq P
      target id hReplacement
      replacementStart localStart sourceStart hLeft
  have hLeftEqual' :
      Derives P.theory Γ
        (Formula.equal localLeft.value
          parameterizedLeft.value) := by
    apply hLeftEqual.context_weaken
    intro formula hFormula
    rcases List.mem_append.mp hFormula with
      hFirst | hParameterizedCondition
    · rcases List.mem_append.mp hFirst with
        hSharedCondition | hLocalCondition
      · simp [Γ, shared, hSharedCondition]
      · simp [Γ, localLeft, hLocalCondition]
    · simpa [Γ, shared, sourceLeft,
        parameterizedLeft] using
          Or.inr (Or.inr
            (Or.inr (Or.inl
              hParameterizedCondition)))
  have hRightEqual :=
    term_substitute_compiled_eq P
      target id hReplacement
      replacementStart localLeft.next
        sourceLeft.next hRight
  have hRightEqual' :
      Derives P.theory Γ
        (Formula.equal localRight.value
          parameterizedRight.value) := by
    apply hRightEqual.context_weaken
    intro formula hFormula
    rcases List.mem_append.mp hFormula with
      hFirst | hParameterizedCondition
    · rcases List.mem_append.mp hFirst with
        hSharedCondition | hLocalCondition
      · simp [Γ, shared, hSharedCondition]
      · simp [Γ, localRight, hLocalCondition]
    · simpa [Γ, shared, sourceRight,
        parameterizedRight] using
          Or.inr (Or.inr
            (Or.inr (Or.inr
              hParameterizedCondition)))
  have hEquivalent :=
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_iff_of_equalities
      hLocalLeft hParameterizedLeft
      hLocalRight hParameterizedRight
      hLeftEqual' hRightEqual'
  simpa [shared, localLeft, sourceLeft,
    parameterizedLeft, localRight,
    sourceRight, parameterizedRight, Γ] using
      hEquivalent

end GraphPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
