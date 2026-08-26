import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Closure

/-!
# 函数图消去的原子合同

本模块把定义扩张中的原子合同从递归编译器中抽出。结论暂时保留在编译条件
上下文中：见证闭包的透明性与定义扩张的原子消去随后分别消费这些接口。
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

omit [DecidableEq σ.FuncSymbol] in
/-- 从右结合条件链中取出任一已登记条件。 -/
theorem condition_conjunction_member
    {T : Theory σ} {Γ : Context σ}
    {conditions : List (Formula σ)}
    {core condition : Formula σ}
    (hConjunction :
      Derives T Γ
        (condition_conjunction conditions core))
    (hCondition : condition ∈ conditions) :
    Derives T Γ condition := by
  induction conditions with
  | nil =>
      cases hCondition
  | cons head tail ih =>
      simp only [condition_conjunction] at hConjunction
      rcases List.mem_cons.mp hCondition with
        rfl | hCondition
      · exact Derives.conj_elim_left hConjunction
      · exact ih
          (Derives.conj_elim_right hConjunction)
          hCondition

omit [DecidableEq σ.FuncSymbol] in
/-- 从右结合条件链中取出末端核心公式。 -/
theorem condition_conjunction_core
    {T : Theory σ} {Γ : Context σ}
    {conditions : List (Formula σ)}
    {core : Formula σ}
    (hConjunction :
      Derives T Γ
        (condition_conjunction conditions core)) :
    Derives T Γ core := by
  induction conditions with
  | nil =>
      simpa [condition_conjunction] using
        hConjunction
  | cons head tail ih =>
      exact ih <|
        Derives.conj_elim_right <| by
          simpa [condition_conjunction] using
            hConjunction

omit [DecidableEq σ.FuncSymbol] in
/-- 逐项已证明的条件与核心可以重建完整右结合条件链。 -/
theorem condition_conjunction_intro
    {T : Theory σ} {Γ : Context σ}
    {conditions : List (Formula σ)}
    {core : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        Derives T Γ condition)
    (hCore : Derives T Γ core) :
    Derives T Γ
      (condition_conjunction conditions core) := by
  induction conditions with
  | nil =>
      simpa [condition_conjunction] using hCore
  | cons condition conditions ih =>
      simp only [condition_conjunction]
      apply Derives.conj_intro
      · exact hConditions condition (by simp)
      · exact ih
          (fun candidate hCandidate =>
            hConditions candidate
              (by simp [hCandidate]))

omit [DecidableEq σ.FuncSymbol] in
/-- 已证明的条件块可一次性向后续推导提供全部登记条件。 -/
theorem condition_conjunction_cut
    {T : Theory σ} {Γ : Context σ}
    {conditions : List (Formula σ)}
    {core conclusion : Formula σ}
    (hBlock :
      Derives T Γ
        (condition_conjunction conditions core))
    (hConclusion :
      Derives T (conditions ++ Γ) conclusion) :
    Derives T Γ conclusion := by
  apply Derives.multi_cut
    (premises := conditions)
  · intro condition hCondition
    exact condition_conjunction_member
      hBlock hCondition
  · exact hConclusion

omit [DecidableEq σ.FuncSymbol] in
/--
条件列表上下文中的核心等价，可以内化为两个右结合条件链在空上下文中的等价。
`multi_cut` 负责把条件链投影出的各条件回放给原证明。
-/
theorem condition_conjunction_iff_of_context
    {T : Theory σ}
    {conditions : List (Formula σ)}
    {left right : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        Formula.Admissible condition)
    (hEquivalent :
      Derives T conditions
        (Formula.iff left right)) :
    Derives T []
      (Formula.iff
        (condition_conjunction conditions left)
        (condition_conjunction conditions right)) := by
  have hLeft :=
    Formula.Admissible.iff_left
      hEquivalent.admissible
  have hRight :=
    Formula.Admissible.iff_right
      hEquivalent.admissible
  apply Derives.iff_intro
  · let block :=
      condition_conjunction conditions left
    have hBlock :
        Derives T [block] block :=
      Derives.assumption_of_mem (by simp)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible <|
            condition_conjunction_admissible
              hConditions hLeft)
    have hPremises :
        ∀ condition, condition ∈ conditions →
          Derives T [block] condition := by
      intro condition hCondition
      exact condition_conjunction_member
        hBlock hCondition
    have hEquivalent' :
        Derives T [block]
          (Formula.iff left right) := by
      apply Derives.multi_cut
        (premises := conditions)
      · exact hPremises
      · simpa using
          hEquivalent.context_weaken_append
    have hRight' :=
      Derives.iff_elim_right hEquivalent' <|
        condition_conjunction_core hBlock
    exact condition_conjunction_intro
      hPremises hRight'
  · let block :=
      condition_conjunction conditions right
    have hBlock :
        Derives T [block] block :=
      Derives.assumption_of_mem (by simp)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible <|
            condition_conjunction_admissible
              hConditions hRight)
    have hPremises :
        ∀ condition, condition ∈ conditions →
          Derives T [block] condition := by
      intro condition hCondition
      exact condition_conjunction_member
        hBlock hCondition
    have hEquivalent' :
        Derives T [block]
          (Formula.iff left right) := by
      apply Derives.multi_cut
        (premises := conditions)
      · exact hPremises
      · simpa using
          hEquivalent.context_weaken_append
    have hLeft' :=
      Derives.iff_elim_left hEquivalent' <|
        condition_conjunction_core hBlock
    exact condition_conjunction_intro
      hPremises hLeft'

omit [DecidableEq σ.FuncSymbol] in
/-- 句子理论中的逻辑等价可提升到任意连续见证闭包。 -/
theorem close_witnesses_from_iff_mono_theory
    {T : Theory σ}
    (hTheory :
      ∀ {formula}, T formula →
        Formula.Sentence formula)
    (sort : σ.SortSymbol) (start count : Nat)
    {left right : Formula σ}
    (hEquivalent :
      Derives T []
        (Formula.iff left right)) :
    Derives T []
      (Formula.iff
        (close_witnesses_from
          sort start count left)
        (close_witnesses_from
          sort start count right)) := by
  induction count with
  | zero =>
      simpa using hEquivalent
  | succ count ih =>
      apply
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.exists_iff_mono
          (sort := sort)
          (eigen := witness_id (start + count))
      · intro formula hFormula
        rw [(hTheory hFormula).2]
        simp
      · intro formula hFormula
        cases hFormula
      · simpa [close_witnesses_from] using ih

omit [DecidableEq σ.FuncSymbol] in
/--
与连续见证区间新鲜的左合取项可以整体移出该区间。量词合同只使用理论公理的
sentence 性与该侧公式的区间新鲜性。
-/
theorem close_witnesses_from_conj_left_iff
    {T : Theory σ}
    (hTheory :
      ∀ {formula}, T formula →
        Formula.Sentence formula)
    (sort : σ.SortSymbol) (start count : Nat)
    {side body : Formula σ}
    (hSide : Formula.Admissible side)
    (hBody : Formula.Admissible body)
    (hFresh :
      ∀ index,
        start ≤ index →
        index < start + count →
          (sort, witness_id index) ∉
            Formula.freeSupport side) :
    Derives T []
      (Formula.iff
        (close_witnesses_from sort start count
          (Formula.conj side body))
        (Formula.conj side
          (close_witnesses_from
            sort start count body))) := by
  induction count with
  | zero =>
      simpa using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_refl_m
          (T := T) (Γ := [])
          (Formula.Admissible.conj hSide hBody)
  | succ count ih =>
      let eigen :=
        witness_id (start + count)
      let inner :=
        close_witnesses_from
          sort start count body
      have hInner :
          Formula.Admissible inner :=
        close_witnesses_from_admissible
          sort start count hBody
      have hLifted :=
        close_witnesses_from_iff_mono_theory
          hTheory sort (start + count) 1 <|
            ih (fun index hLower hUpper =>
              hFresh index hLower (by omega))
      have hMove :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.exists_conj_left_iff
          (T := T) (Γ := [])
          hSide hInner
          (hFresh (start + count)
            (by omega) (by omega))
      have hMove' :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
          hMove
      simpa [close_witnesses_from,
        eigen, inner] using
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
            hLifted hMove'

omit [DecidableEq σ.FuncSymbol] in
private theorem source_conj_truth_iff
    {source : Formula σ}
    (hSource : Formula.Admissible source) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff source
        (Formula.conj source Formula.truth)) := by
  derive_prop

omit [DecidableEq σ.FuncSymbol] in
/-- 条件链以源公式结尾时，等价于源公式与纯条件可满足块的合取。 -/
theorem condition_conjunction_source_iff
    {conditions : List (Formula σ)}
    {source : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        Formula.Admissible condition)
    (hSource : Formula.Admissible source) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff
        (condition_conjunction conditions source)
        (Formula.conj source
          (condition_conjunction
            conditions Formula.truth))) := by
  have hCongruence :=
    condition_conjunction_iff_mono
      hConditions
      (source_conj_truth_iff hSource)
  have hRotate :=
    condition_conjunction_rotate_iff
      hConditions hSource
      Formula.Admissible.truth
  exact
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
      hCongruence hRotate

omit [DecidableEq σ.FuncSymbol] in
private theorem conj_theorem_iff_left
    {T : Theory σ}
    {left right : Formula σ}
    (hLeft : Formula.Admissible left)
    (hRight : Derives T [] right) :
    Derives T []
      (Formula.iff
        (Formula.conj left right) left) := by
  apply Derives.iff_intro
  · have hConjunction :
        Derives T
          [Formula.conj left right]
          (Formula.conj left right) :=
      Derives.assumption_of_mem (by simp)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible <|
            Formula.Admissible.conj
              hLeft hRight.admissible)
    exact Derives.conj_elim_left hConjunction
  · have hLeft' :
        Derives T [left] left :=
      Derives.assumption_of_mem (by simp)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hLeft)
    exact Derives.conj_intro hLeft' <|
      hRight.context_weaken_cons

omit [DecidableEq σ.FuncSymbol] in
/--
闭包条件透明性：条件块可满足、条件上下文中核心与源公式等价、且源公式不含该
见证区间时，整个见证闭包等价于源公式。
-/
theorem closed_conditions_iff_source
    {T : Theory σ}
    (hTheory :
      ∀ {formula}, T formula →
        Formula.Sentence formula)
    (sort : σ.SortSymbol) (start count : Nat)
    {conditions : List (Formula σ)}
    {core source : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        Formula.Admissible condition)
    (hSource : Formula.Admissible source)
    (hFresh :
      ∀ index,
        start ≤ index →
        index < start + count →
          (sort, witness_id index) ∉
            Formula.freeSupport source)
    (hSatisfiable :
      Derives T []
        (close_witnesses_from sort start count
          (condition_conjunction
            conditions Formula.truth)))
    (hEquivalent :
      Derives T conditions
        (Formula.iff core source)) :
    Derives T []
      (Formula.iff
        (close_witnesses_from sort start count
          (condition_conjunction conditions core))
        source) := by
  have hConditionEquivalent :=
    condition_conjunction_iff_of_context
      hConditions hEquivalent
  have hClosedEquivalent :=
    close_witnesses_from_iff_mono_theory
      hTheory sort start count
        hConditionEquivalent
  have hSourceBlock :=
    Derives.of_empty
      (T := T) (Γ := []) <|
        condition_conjunction_source_iff
          hConditions hSource
  have hClosedSourceBlock :=
    close_witnesses_from_iff_mono_theory
      hTheory sort start count
        hSourceBlock
  have hConditionBody :
      Formula.Admissible
        (condition_conjunction
          conditions Formula.truth) :=
    condition_conjunction_admissible
      hConditions Formula.Admissible.truth
  have hMove :=
    close_witnesses_from_conj_left_iff
      hTheory sort start count
      hSource hConditionBody hFresh
  have hCollapse :=
    conj_theorem_iff_left
      hSource hSatisfiable
  exact
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
      hClosedEquivalent <|
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hClosedSourceBlock <|
            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
              hMove hCollapse

mutual

/-- 奇数区源项不含任何偶数编号见证变量。 -/
theorem source_term_witness_fresh
    {τ : Signature.{u, v, w}}
    (sort : τ.SortSymbol) (index : Nat)
    (source : Term τ) :
    (sort, witness_id index) ∉
      Term.freeSupport (source_term source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sourceSort depth =>
          simp [source_term, Term.freeSupport]
      | fvar sourceSort id =>
          simp only [source_term,
            Term.freeSupport, List.mem_singleton]
          intro hEqual
          have hId :
              witness_id index =
                source_id id :=
            congrArg Prod.snd hEqual
          exact
            (source_id_ne_witness_id id index)
              hId.symm
  | app function arguments =>
      simpa [source_term, Term.freeSupport] using
        source_terms_witness_fresh
          sort index arguments

/-- 奇数区源参数表不含任何偶数编号见证变量。 -/
theorem source_terms_witness_fresh
    {τ : Signature.{u, v, w}}
    (sort : τ.SortSymbol) (index : Nat)
    (sources : List (Term τ)) :
    (sort, witness_id index) ∉
      Term.freeSupportList
        (sources.map source_term) := by
  cases sources with
  | nil =>
      simp [Term.freeSupportList]
  | cons head tail =>
      simpa [Term.freeSupportList] using
        And.intro
          (source_term_witness_fresh
            sort index head)
          (source_terms_witness_fresh
            sort index tail)

end

namespace DefinitionPresentation

variable {D : Data σ}

/-- 编译参数下的关系原子等价于奇数区源参数关系原子。 -/
theorem relation_core_iff
    (P : DefinitionPresentation D)
    (relation : σ.RelSymbol)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissible arguments
        (σ.relDomain relation)) :
    Derives P.extension
      (terms D 0 arguments).conditions
      (Formula.iff
        (Formula.rel relation
          (terms D 0 arguments).values)
        (Formula.rel relation
          (arguments.map source_term))) := by
  have hCompiled :=
    terms_admissible D 0 hArguments
  have hSource :=
    source_terms_admissible hArguments
  exact
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.relation_congr_arguments_of_equalities
      (T := P.extension)
      (Γ := (terms D 0 arguments).conditions)
      relation hCompiled hSource
      (P.terms_values_eq_source 0 hArguments)

/-- 编译两项后的等式原子等价于奇数区源项等式原子。 -/
theorem equality_core_iff
    (P : DefinitionPresentation D)
    {left right : Term σ}
    {sort : σ.SortSymbol}
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort) :
    Derives P.extension
      ((term D 0 left).conditions ++
        (term D (term D 0 left).next right).conditions)
      (Formula.iff
        (Formula.equal
          (term D 0 left).value
          (term D (term D 0 left).next right).value)
        (Formula.equal
          (source_term left)
          (source_term right))) := by
  let compiledLeft := term D 0 left
  let compiledRight :=
    term D compiledLeft.next right
  have hCompiledLeft :
      Term.Admissible compiledLeft.value sort := by
    exact
      ⟨(term_well_formed
          D 0 hLeft.1).1,
        (term_scoped
          D 0 hLeft.2).1⟩
  have hCompiledRight :
      Term.Admissible compiledRight.value sort := by
    exact
      ⟨(term_well_formed
          D compiledLeft.next hRight.1).1,
        (term_scoped
          D compiledLeft.next hRight.2).1⟩
  have hLeftEq :=
    P.term_value_eq_source 0 hLeft
  have hLeftEq' :
      Derives P.extension
        (compiledLeft.conditions ++
          compiledRight.conditions)
        (Formula.equal
          compiledLeft.value
          (source_term left)) := by
    apply hLeftEq.context_weaken
    intro formula hFormula
    exact List.mem_append.mpr
      (Or.inl hFormula)
  have hRightEq :=
    P.term_value_eq_source
      compiledLeft.next hRight
  have hRightEq' :
      Derives P.extension
        (compiledLeft.conditions ++
          compiledRight.conditions)
        (Formula.equal
          compiledRight.value
          (source_term right)) := by
    apply hRightEq.context_weaken
    intro formula hFormula
    exact List.mem_append.mpr
      (Or.inr hFormula)
  have hCore :=
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_iff_of_equalities
      (sort := sort)
      hCompiledLeft
      (source_term_admissible hLeft)
      hCompiledRight
      (source_term_admissible hRight)
      hLeftEq' hRightEq'
  simpa [compiledLeft, compiledRight] using hCore

/-- 关系原子的函数图关系化结果等价于奇数区源原子。 -/
theorem relation_iff_source
    (P : DefinitionPresentation D)
    (relation : σ.RelSymbol)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissible arguments
        (σ.relDomain relation)) :
    Derives P.extension []
      (Formula.iff
        (FunctionGraphElimination.relation
          D relation arguments)
        (Formula.rel relation
          (arguments.map source_term))) := by
  let compiled :=
    terms D 0 arguments
  have hConditions :
      ∀ condition,
        condition ∈ compiled.conditions →
          Formula.Admissible condition := by
    simpa [compiled] using
      terms_conditions_admissible
        D 0 hArguments
  have hSource :
      Formula.Admissible
        (Formula.rel relation
          (arguments.map source_term)) :=
    Formula.Admissible.rel <|
      source_terms_admissible hArguments
  have hFresh :
      ∀ index,
        0 ≤ index →
        index < 0 + compiled.next →
          (D.sort, witness_id index) ∉
            Formula.freeSupport
              (Formula.rel relation
                (arguments.map source_term)) := by
    intro index hLower hUpper
    simpa [Formula.freeSupport] using
      source_terms_witness_fresh
        D.sort index arguments
  have hSatisfiable :
      Derives P.extension []
        (close_witnesses_from
          D.sort 0 compiled.next
          (condition_conjunction
            compiled.conditions Formula.truth)) := by
    have hBase :=
      (P.toGraphPresentation).terms_conditions_closed
        hArguments
    have hExtension :=
      hBase.theory_weaken P.base_subset
    simpa [compiled,
      close_witnesses_from_zero_start] using
        hExtension
  have hClosed :=
    closed_conditions_iff_source
      P.extension_sentence
      D.sort 0 compiled.next
      hConditions hSource hFresh
      hSatisfiable <| by
        simpa [compiled] using
          P.relation_core_iff
            relation hArguments
  simpa [FunctionGraphElimination.relation,
    compiled,
    close_witnesses_from_zero_start] using
      hClosed

/-- 等式原子的函数图关系化结果等价于奇数区源等式。 -/
theorem equality_iff_source
    (P : DefinitionPresentation D)
    {left right : Term σ}
    {sort : σ.SortSymbol}
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort) :
    Derives P.extension []
      (Formula.iff
        (FunctionGraphElimination.equality
          D left right)
        (Formula.equal
          (source_term left)
          (source_term right))) := by
  let compiledLeft :=
    term D 0 left
  let compiledRight :=
    term D compiledLeft.next right
  let conditions :=
    compiledLeft.conditions ++
      compiledRight.conditions
  have hLeftConditions :
      ∀ condition,
        condition ∈ compiledLeft.conditions →
          Formula.Admissible condition := by
    simpa [compiledLeft] using
      term_conditions_admissible
        D 0 hLeft
  have hRightConditions :
      ∀ condition,
        condition ∈ compiledRight.conditions →
          Formula.Admissible condition := by
    simpa [compiledLeft, compiledRight] using
      term_conditions_admissible
        D (term D 0 left).next hRight
  have hConditions :
      ∀ condition,
        condition ∈ conditions →
          Formula.Admissible condition := by
    intro condition hCondition
    rcases List.mem_append.mp <| by
        simpa [conditions] using hCondition with
      hCondition | hCondition
    · exact hLeftConditions condition hCondition
    · exact hRightConditions condition hCondition
  have hSource :
      Formula.Admissible
        (Formula.equal
          (source_term left)
          (source_term right)) :=
    Formula.Admissible.equal
      (source_term_admissible hLeft)
      (source_term_admissible hRight)
  have hFresh :
      ∀ index,
        0 ≤ index →
        index < 0 + compiledRight.next →
          (D.sort, witness_id index) ∉
            Formula.freeSupport
              (Formula.equal
                (source_term left)
                (source_term right)) := by
    intro index hLower hUpper
    simp only [Formula.freeSupport,
      List.mem_append]
    intro hMember
    rcases hMember with hMember | hMember
    · exact
        source_term_witness_fresh
          D.sort index left hMember
    · exact
        source_term_witness_fresh
          D.sort index right hMember
  have hPair :
      ArgsAdmissible [left, right]
        [sort, sort] :=
    ArgsAdmissible.cons hLeft <|
      ArgsAdmissible.cons hRight
        ArgsAdmissible.nil
  have hSatisfiable :
      Derives P.extension []
        (close_witnesses_from
          D.sort 0 compiledRight.next
          (condition_conjunction
            conditions Formula.truth)) := by
    have hBase :=
      (P.toGraphPresentation).terms_conditions_closed
        hPair
    have hExtension :=
      hBase.theory_weaken P.base_subset
    simpa [compiledLeft, compiledRight,
      conditions, terms,
      close_witnesses_from_zero_start] using
        hExtension
  have hClosed :=
    closed_conditions_iff_source
      P.extension_sentence
      D.sort 0 compiledRight.next
      hConditions hSource hFresh
      hSatisfiable <| by
        simpa [compiledLeft, compiledRight,
          conditions] using
            P.equality_core_iff hLeft hRight
  simpa [FunctionGraphElimination.equality,
    compiledLeft, compiledRight, conditions,
    close_witnesses_from_zero_start] using
      hClosed

end DefinitionPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
