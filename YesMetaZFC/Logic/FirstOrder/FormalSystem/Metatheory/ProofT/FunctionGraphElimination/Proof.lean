import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Formula

/-!
# 函数图消去的证明辅助层

本模块固定推导翻译反复消费的两个不变量：完整公式不会暴露局部偶数见证；同一
源项在不同见证区间中的编译值由函数图单值性唯一确定。完整 substitution 与
Hilbert 推导翻译分别位于后续专门模块。
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
/-- 连续见证闭包会关闭区间内变量，并保持区间外已有的新鲜性。 -/
theorem close_witnesses_from_witness_fresh
    (sort : σ.SortSymbol) (start count index : Nat)
    (body : Formula σ)
    (hBody :
      (index < start ∨ start + count ≤ index) →
        (sort, witness_id index) ∉
          Formula.freeSupport body) :
    (sort, witness_id index) ∉
      Formula.freeSupport
        (close_witnesses_from
          sort start count body) := by
  induction count with
  | zero =>
      simpa [close_witnesses_from] using hBody <| by
        by_cases hIndex : index < start
        · exact Or.inl hIndex
        · exact Or.inr (by omega)
  | succ count ih =>
      by_cases hIndex : index = start + count
      · subst index
        exact
          Formula.not_mem_freeSupport_closeFreeAt
            sort (witness_id (start + count)) 0
              (close_witnesses_from
                sort start count body)
      · apply
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (sort, witness_id index)
            sort (witness_id (start + count)) 0
        exact ih <| by
          intro hOutside
          rcases hOutside with hBelow | hAbove
          · exact hBody (Or.inl hBelow)
          · exact hBody (Or.inr <| by omega)

omit [DecidableEq σ.FuncSymbol] in
/-- 从零开始的见证闭包不暴露任何偶数见证变量。 -/
theorem close_witnesses_witness_fresh
    (sort : σ.SortSymbol) (count index : Nat)
    (body : Formula σ)
    (hBody :
      count ≤ index →
        (sort, witness_id index) ∉
          Formula.freeSupport body) :
    (sort, witness_id index) ∉
      Formula.freeSupport
        (close_witnesses sort count body) := by
  rw [← close_witnesses_from_zero_start]
  exact close_witnesses_from_witness_fresh
    sort 0 count index body <| by
      intro hOutside
      rcases hOutside with hBelow | hAbove
      · omega
      · exact hBody (by simpa using hAbove)

/-- 关系原子的编译结果不暴露任何局部见证变量。 -/
theorem relation_witness_fresh
    (D : Data σ) (relation : σ.RelSymbol)
    (arguments : List (Term σ)) (index : Nat) :
    (D.sort, witness_id index) ∉
      Formula.freeSupport
        (FunctionGraphElimination.relation
          D relation arguments) := by
  let compiled := terms D 0 arguments
  apply close_witnesses_witness_fresh
  intro hIndex
  apply condition_conjunction_fresh
  · intro condition hCondition
    exact terms_conditions_witness_fresh_above
      D 0 arguments hIndex condition <| by
        simpa [compiled] using hCondition
  · simpa [Formula.freeSupport, compiled] using
      terms_values_witness_fresh_above
        D 0 arguments hIndex

/-- 等式原子的编译结果不暴露任何局部见证变量。 -/
theorem equality_witness_fresh
    (D : Data σ) (left right : Term σ)
    (index : Nat) :
    (D.sort, witness_id index) ∉
      Formula.freeSupport
        (FunctionGraphElimination.equality
          D left right) := by
  let compiledLeft := term D 0 left
  let compiledRight :=
    term D compiledLeft.next right
  have hLeftNext :
      compiledLeft.next ≤ compiledRight.next := by
    simpa [compiledLeft, compiledRight] using
      term_next_ge D (term D 0 left).next right
  apply close_witnesses_witness_fresh
  intro hIndex
  apply condition_conjunction_fresh
  · intro condition hCondition
    rcases List.mem_append.mp hCondition with
      hCondition | hCondition
    · exact term_conditions_witness_fresh_above
        D 0 left
          (Nat.le_trans hLeftNext hIndex)
          condition <| by
            simpa [compiledLeft] using hCondition
    · exact term_conditions_witness_fresh_above
        D (term D 0 left).next right
          hIndex condition <| by
            simpa [compiledLeft, compiledRight] using
              hCondition
  · simp only [Formula.freeSupport, List.mem_append]
    intro hMember
    rcases hMember with hMember | hMember
    · exact term_value_witness_fresh_above
        D 0 left
          (Nat.le_trans hLeftNext hIndex) <| by
            simpa [compiledLeft] using hMember
    · exact term_value_witness_fresh_above
        D (term D 0 left).next right
          hIndex <| by
            simpa [compiledLeft, compiledRight] using
              hMember

/-- 完整公式编译后，所有偶数图见证都已在其原子内部关闭。 -/
theorem formula_witness_fresh
    (D : Data σ) (source : Formula σ)
    (index : Nat) :
    (D.sort, witness_id index) ∉
      Formula.freeSupport (formula D source) := by
  cases source with
  | falsum | truth =>
      simp [formula, Formula.freeSupport]
  | rel relation arguments =>
      simpa [formula] using
        relation_witness_fresh
          D relation arguments index
  | equal left right =>
      simpa [formula] using
        equality_witness_fresh D left right index
  | neg body =>
      simpa [formula, Formula.freeSupport] using
        formula_witness_fresh D body index
  | conj left right
  | disj left right
  | imp left right
  | iff left right =>
      simpa [formula, Formula.freeSupport] using
        And.intro
          (formula_witness_fresh D left index)
          (formula_witness_fresh D right index)
  | forallE sort body
  | existsE sort body =>
      let eigen :=
        FreshVariable.fresh_id sort [body]
      let opened :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      have hOpened :=
        formula_witness_fresh D opened index
      have hClosed :=
        Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
          (D.sort, witness_id index)
          sort (source_id eigen) 0
          (formula D opened) hOpened
      simpa [formula, Formula.freeSupport,
        eigen, opened] using hClosed
termination_by Formula.complexity source
decreasing_by
  all_goals
    simp_all [Formula.complexity] <;>
      first
      | exact Nat.lt_succ_of_le
          (Nat.le_max_left _ _)
      | exact Nat.lt_succ_of_le
          (Nat.le_max_right _ _)
      | omega

namespace GraphPresentation

variable {D : Data σ}

mutual

/--
同一源项在任意两个见证区间中的编译结果，由两边图条件共同唯一确定。
-/
theorem term_compiled_eq
    (P : GraphPresentation D)
    (leftStart rightStart : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort) :
    Derives P.theory
      ((term D leftStart source).conditions ++
        (term D rightStart source).conditions)
      (Formula.equal
        (term D leftStart source).value
        (term D rightStart source).value) := by
  cases source with
  | var value =>
      let compiledValue :=
        (term D leftStart
          (.var value)).value
      have hValue :
          Term.Admissible compiledValue sort := by
        exact
          ⟨(term_well_formed
              D leftStart hSource.1).1,
            (term_scoped
              D leftStart hSource.2).1⟩
      cases value <;>
        simpa [term] using
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_refl
            (T := P.theory) (Γ := [])
            compiledValue
            (sort := sort)
            (hTermCheck :=
              Term.check_certificate_of_admissible
                hValue)
  | app function arguments =>
      have hArguments :=
        app_arguments_admissible
          function arguments hSource
      by_cases hFunction : function = D.symbol
      · subst function
        let leftArguments :=
          terms D (leftStart + 1) arguments
        let rightArguments :=
          terms D (rightStart + 1) arguments
        let leftResult :=
          Term.var
            (.fvar D.sort
              (witness_id leftStart))
        let rightResult :=
          Term.var
            (.fvar D.sort
              (witness_id rightStart))
        let Γ :=
          (D.graph leftArguments.values leftResult ::
              leftArguments.conditions) ++
            (D.graph rightArguments.values rightResult ::
              rightArguments.conditions)
        have hSort : sort = D.sort := by
          apply TermWellSorted.sort_unique
            hSource.1
          rw [← D.codomain_eq]
          exact TermWellSorted.app
            D.symbol hArguments.1
        subst sort
        have hLeftArguments :
            ArgsAdmissible leftArguments.values
              (σ.funcDomain D.symbol) := by
          simpa [leftArguments] using
            terms_admissible D
              (leftStart + 1) hArguments
        have hRightArguments :
            ArgsAdmissible rightArguments.values
              (σ.funcDomain D.symbol) := by
          simpa [rightArguments] using
            terms_admissible D
              (rightStart + 1) hArguments
        have hLeftResult :
            Term.Admissible leftResult D.sort :=
          ⟨TermWellSorted.fvar D.sort
              (witness_id leftStart),
            TermScoped.fvar D.sort
              (witness_id leftStart)⟩
        have hRightResult :
            Term.Admissible rightResult D.sort :=
          ⟨TermWellSorted.fvar D.sort
              (witness_id rightStart),
            TermScoped.fvar D.sort
              (witness_id rightStart)⟩
        have hArgumentsEqual :=
          terms_compiled_eq P
            (leftStart + 1) (rightStart + 1)
            hArguments
        have hArgumentsEqual' :
            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
              P.theory Γ leftArguments.values
                rightArguments.values := by
          apply hArgumentsEqual.context_weaken
          intro formula hFormula
          rcases List.mem_append.mp hFormula with
            hFormula | hFormula
          · simp [Γ, leftArguments, hFormula]
          · simp [Γ, rightArguments, hFormula]
        have hGraphEquivalent :=
          P.graph_args_congr
            hLeftArguments hRightArguments
            hLeftResult hArgumentsEqual'
        have hLeftGraph :
            Derives P.theory Γ
              (D.graph leftArguments.values
                leftResult) :=
          Derives.assumption_of_mem
            (by simp [Γ])
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                graph_admissible D
                  hLeftArguments hLeftResult)
        have hAligned :
            Derives P.theory Γ
              (D.graph rightArguments.values
                leftResult) :=
          Derives.iff_elim_right
            hGraphEquivalent hLeftGraph
        have hRightGraph :
            Derives P.theory Γ
              (D.graph rightArguments.values
                rightResult) :=
          Derives.assumption_of_mem
            (by simp [Γ])
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                graph_admissible D
                  hRightArguments hRightResult)
        have hFunctional :
            Derives P.theory Γ
              (Formula.imp
                (D.graph rightArguments.values
                  leftResult)
                (Formula.imp
                  (D.graph rightArguments.values
                    rightResult)
                  (Formula.equal leftResult
                    rightResult))) :=
          (P.functional hRightArguments
            hLeftResult hRightResult).context_weaken
              (by simp)
        have hEqual :=
          hFunctional.imp_elim hAligned
        have hResult :=
          hEqual.imp_elim hRightGraph
        simpa [term, leftArguments,
          rightArguments, leftResult,
          rightResult, Γ] using hResult
      · have hEqual :=
          terms_compiled_eq P
            leftStart rightStart hArguments
        have hLeftArguments :=
          terms_admissible D leftStart hArguments
        have hRightArguments :=
          terms_admissible D rightStart hArguments
        have hResult :=
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.function_term_congr_arguments_of_equalities
            (T := P.theory)
            function hLeftArguments
              hRightArguments hEqual
        simpa [term, hFunction] using hResult

/-- 同一源参数表的两次编译逐位置相等。 -/
theorem terms_compiled_eq
    (P : GraphPresentation D)
    (leftStart rightStart : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsAdmissible sources sorts) :
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
      P.theory
      ((terms D leftStart sources).conditions ++
        (terms D rightStart sources).conditions)
      (terms D leftStart sources).values
      (terms D rightStart sources).values := by
  cases sources with
  | nil =>
      exact .nil
  | cons head tail =>
      rcases ArgsAdmissible.exists_cons hSources with
        ⟨headSort, tailSorts, hSorts,
          hHead, hTail⟩
      subst sorts
      let leftHead := term D leftStart head
      let rightHead := term D rightStart head
      let leftTail :=
        terms D leftHead.next tail
      let rightTail :=
        terms D rightHead.next tail
      let Γ :=
        (leftHead.conditions ++
            leftTail.conditions) ++
          (rightHead.conditions ++
            rightTail.conditions)
      have hHeadEqual :=
        term_compiled_eq P
          leftStart rightStart hHead
      have hHeadEqual' :
          Derives P.theory Γ
            (Formula.equal leftHead.value
              rightHead.value) := by
        apply hHeadEqual.context_weaken
        intro formula hFormula
        rcases List.mem_append.mp hFormula with
          hFormula | hFormula
        · simp [Γ, leftHead, hFormula]
        · simp [Γ, rightHead, hFormula]
      have hTailEqual :=
        terms_compiled_eq P
          leftHead.next rightHead.next hTail
      have hTailEqual' :
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
            P.theory Γ leftTail.values
              rightTail.values := by
        apply hTailEqual.context_weaken
        intro formula hFormula
        rcases List.mem_append.mp hFormula with
          hFormula | hFormula
        · simp [Γ, leftTail, hFormula]
        · simp [Γ, rightTail, hFormula]
      have hEqual :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality.cons
          hHeadEqual' hTailEqual'
      simpa [terms, leftHead, rightHead,
        leftTail, rightTail, Γ,
        List.append_assoc] using hEqual

end

/--
同一项在相邻且不相交的两个见证区间中各求值一次，基础图理论可证明两个结果相等。
-/
theorem term_flat_next_eq
    (P : GraphPresentation D) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort) :
    Derives P.theory []
      (term_flat_closure D start source <| fun left =>
        term_flat_closure D
          (term D start source).next source <| fun right =>
            Formula.equal left right) := by
  let left := term D start source
  let right := term D left.next source
  have hLeft :
      Term.Admissible left.value sort :=
    ⟨(term_well_formed
        D start hSource.1).1,
      (term_scoped
        D start hSource.2).1⟩
  have hRight :
      Term.Admissible right.value sort := by
    exact
      ⟨(term_well_formed
          D left.next hSource.1).1,
        (term_scoped
          D left.next hSource.2).1⟩
  apply P.term_flat_derives_from_conditions
    start hSource
  · intro index hLower hUpper formula hFormula
    cases hFormula
  · intro leftValue hLeftValue
    exact term_flat_closure_admissible
      D left.next hSource
      (fun rightValue =>
        Formula.equal leftValue rightValue)
      (by
        intro rightValue hRightValue
        exact Formula.Admissible.equal
          hLeftValue hRightValue)
  · apply P.term_flat_derives_from_conditions
      left.next hSource
    · intro index hLower hUpper formula hFormula
      exact term_conditions_witness_fresh_above
        D start source hLower formula <| by
          simpa [left] using hFormula
    · intro rightValue hRightValue
      exact Formula.Admissible.equal
        hLeft hRightValue
    · have hEqual :=
        term_compiled_eq P
          start left.next hSource
      apply hEqual.context_weaken
      intro formula hFormula
      rcases List.mem_append.mp hFormula with
        hLeftCondition | hRightCondition
      · exact List.mem_append.mpr
          (Or.inr <| List.mem_append.mpr
            (Or.inl hLeftCondition))
      · exact List.mem_append.mpr
          (Or.inl <| by
            simpa [left, right] using
              hRightCondition)

end GraphPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
