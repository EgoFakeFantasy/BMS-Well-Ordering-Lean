import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Substitution.Quantifier

/-!
# 函数图编译器的源变量新鲜性

本模块补全函数图编译的另一半命名空间不变量：原语法中的自由变量经奇数编号
重编码后，不会由项值、图条件或完整公式编译凭空引入。量词分支中特别处理
canonical eigenvariable；若待跟踪变量恰为该 eigenvariable，则最终关闭直接消去它，
否则 opening 保持其新鲜性并递归传递。
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

mutual

/--
原项中的新鲜自由变量经奇数编号后，同时对编译值与全部图条件保持新鲜。
-/
theorem term_compiled_source_fresh
    (D : Data σ) (start : Nat)
    (target : σ.SortSymbol) (id : FreeVarId)
    (source : Term σ)
    (hFresh :
      (target, id) ∉ Term.freeSupport source) :
    (target, source_id id) ∉
        Term.freeSupport (term D start source).value ∧
      ∀ condition,
        condition ∈ (term D start source).conditions →
          (target, source_id id) ∉
            Formula.freeSupport condition := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          constructor
          · simpa [term, source_term] using
              source_term_fresh target id
                (.var (.bvar sort index)) hFresh
          · intro condition hCondition
            simp [term] at hCondition
      | fvar sort freeId =>
          constructor
          · simpa [term, source_term] using
              source_term_fresh target id
                (.var (.fvar sort freeId)) hFresh
          · intro condition hCondition
            simp [term] at hCondition
  | app function arguments =>
      have hArguments :
          (target, id) ∉
            Term.freeSupportList arguments := by
        simpa [Term.freeSupport] using hFresh
      by_cases hFunction : function = D.symbol
      · subst function
        let compiled :=
          terms D (start + 1) arguments
        let result :=
          Term.var
            (.fvar D.sort (witness_id start))
        have hCompiled :=
          terms_compiled_source_fresh
            D (start + 1) target id
              arguments hArguments
        have hResult :
            (target, source_id id) ∉
              Term.freeSupport result := by
          simp only [result, Term.freeSupport,
            List.mem_singleton]
          intro hEqual
          have hId :
              source_id id = witness_id start :=
            congrArg Prod.snd hEqual
          exact
            (source_id_ne_witness_id id start)
              hId
        constructor
        · simpa [term, result] using hResult
        · intro condition hCondition
          simp only [term] at hCondition
          rcases List.mem_cons.mp hCondition with
            rfl | hCondition
          · exact graph_freeSupport_fresh
              D hCompiled.1 hResult
          · exact hCompiled.2 condition <| by
              simpa [compiled] using hCondition
      · have hCompiled :=
          terms_compiled_source_fresh
            D start target id arguments hArguments
        constructor
        · simpa [term, hFunction,
            Term.freeSupport] using hCompiled.1
        · simpa [term, hFunction] using hCompiled.2

/--
原参数表中的新鲜自由变量经奇数编号后，同时对全部编译值与图条件保持新鲜。
-/
theorem terms_compiled_source_fresh
    (D : Data σ) (start : Nat)
    (target : σ.SortSymbol) (id : FreeVarId)
    (sources : List (Term σ))
    (hFresh :
      (target, id) ∉
        Term.freeSupportList sources) :
    (target, source_id id) ∉
        Term.freeSupportList
          (terms D start sources).values ∧
      ∀ condition,
        condition ∈ (terms D start sources).conditions →
          (target, source_id id) ∉
            Formula.freeSupport condition := by
  cases sources with
  | nil =>
      simp [terms, Term.freeSupportList]
  | cons head tail =>
      have hParts :
          (target, id) ∉ Term.freeSupport head ∧
            (target, id) ∉
              Term.freeSupportList tail := by
        simpa [Term.freeSupportList] using hFresh
      have hHead :=
        term_compiled_source_fresh
          D start target id head hParts.1
      have hTail :=
        terms_compiled_source_fresh
          D (term D start head).next
            target id tail hParts.2
      constructor
      · simpa [terms, Term.freeSupportList] using
          And.intro hHead.1 hTail.1
      · intro condition hCondition
        simp only [terms, List.mem_append]
          at hCondition
        exact hCondition.elim
          (hHead.2 condition)
          (hTail.2 condition)

end

/-- 关系原子编译保持奇数编码后的源变量新鲜性。 -/
theorem relation_compiled_source_fresh
    (D : Data σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (relation : σ.RelSymbol)
    (arguments : List (Term σ))
    (hFresh :
      (target, id) ∉
        Term.freeSupportList arguments) :
    (target, source_id id) ∉
      Formula.freeSupport
        (FunctionGraphElimination.relation
          D relation arguments) := by
  let compiled := terms D 0 arguments
  have hCompiled :=
    terms_compiled_source_fresh
      D 0 target id arguments hFresh
  rw [FunctionGraphElimination.relation,
    ← close_witnesses_from_zero_start]
  apply close_witnesses_from_fresh
  apply condition_conjunction_fresh
  · intro condition hCondition
    exact hCompiled.2 condition <| by
      simpa [compiled] using hCondition
  · simpa [Formula.freeSupport, compiled] using
      hCompiled.1

/-- 等式原子编译保持奇数编码后的源变量新鲜性。 -/
theorem equality_compiled_source_fresh
    (D : Data σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (left right : Term σ)
    (hFresh :
      (target, id) ∉
        Formula.freeSupport
          (Formula.equal left right)) :
    (target, source_id id) ∉
      Formula.freeSupport
        (FunctionGraphElimination.equality
          D left right) := by
  let compiledLeft := term D 0 left
  let compiledRight :=
    term D compiledLeft.next right
  have hParts :
      (target, id) ∉ Term.freeSupport left ∧
        (target, id) ∉ Term.freeSupport right := by
    simpa [Formula.freeSupport] using hFresh
  have hLeft :=
    term_compiled_source_fresh
      D 0 target id left hParts.1
  have hRight :=
    term_compiled_source_fresh
      D compiledLeft.next target id
        right hParts.2
  rw [FunctionGraphElimination.equality,
    ← close_witnesses_from_zero_start]
  apply close_witnesses_from_fresh
  apply condition_conjunction_fresh
  · intro condition hCondition
    rcases List.mem_append.mp hCondition with
      hCondition | hCondition
    · exact hLeft.2 condition <| by
        simpa [compiledLeft] using hCondition
    · exact hRight.2 condition <| by
        simpa [compiledLeft, compiledRight] using
          hCondition
  · simpa [Formula.freeSupport,
      compiledLeft, compiledRight] using
        And.intro hLeft.1 hRight.1

/--
完整公式编译保持奇数编码后的源变量新鲜性。

若待跟踪变量正是当前 canonical eigenvariable，最终 `closeFreeAt` 直接关闭它；
否则 opening 不会引入该变量，故可递归使用同一不变量。
-/
theorem formula_compiled_source_fresh
    (D : Data σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (source : Formula σ)
    (hFresh :
      (target, id) ∉ Formula.freeSupport source) :
    (target, source_id id) ∉
      Formula.freeSupport (formula D source) := by
  cases source with
  | falsum | truth =>
      simp [formula, Formula.freeSupport]
  | rel relation arguments =>
      simpa [formula] using
        relation_compiled_source_fresh
          D target id relation arguments <| by
            simpa [Formula.freeSupport] using hFresh
  | equal left right =>
      simpa [formula] using
        equality_compiled_source_fresh
          D target id left right hFresh
  | neg body =>
      simpa [formula, Formula.freeSupport] using
        formula_compiled_source_fresh
          D target id body hFresh
  | conj left right
  | disj left right
  | imp left right
  | iff left right =>
      have hParts :
          (target, id) ∉ Formula.freeSupport left ∧
            (target, id) ∉
              Formula.freeSupport right := by
        simpa [Formula.freeSupport] using hFresh
      simpa [formula, Formula.freeSupport] using
        And.intro
          (formula_compiled_source_fresh
            D target id left hParts.1)
          (formula_compiled_source_fresh
            D target id right hParts.2)
  | forallE sort body
  | existsE sort body =>
      let eigen :=
        FreshVariable.fresh_id sort [body]
      let opened :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      by_cases hEigen :
          (target, id) = (sort, eigen)
      · have hEncoded :
            (target, source_id id) =
              (sort, source_id eigen) := by
          have hSort : target = sort :=
            congrArg
              (fun pair :
                σ.SortSymbol × FreeVarId =>
                  pair.1) hEigen
          have hId : id = eigen :=
            congrArg
              (fun pair :
                σ.SortSymbol × FreeVarId =>
                  pair.2) hEigen
          exact Prod.ext hSort
            (congrArg source_id hId)
        rw [hEncoded]
        simpa [formula, Formula.freeSupport,
          eigen, opened] using
            Formula.not_mem_freeSupport_closeFreeAt
              sort (source_id eigen) 0
                (formula D opened)
      · have hReplacementFresh :
            (target, id) ∉
              Term.freeSupport
                (.var (.fvar sort eigen)) := by
          simpa [Term.freeSupport] using hEigen
        have hOpenedFresh :
            (target, id) ∉
              Formula.freeSupport opened := by
          dsimp [opened]
          exact Formula.not_mem_freeSupport_openAt
            (target, id) sort 0
            (.var (.fvar sort eigen)) body
            hReplacementFresh hFresh
        have hCompiledFresh :=
          formula_compiled_source_fresh
            D target id opened hOpenedFresh
        have hClosedFresh :=
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (target, source_id id)
            sort (source_id eigen) 0
            (formula D opened) hCompiledFresh
        simpa [formula, Formula.freeSupport,
          eigen, opened] using hClosedFresh
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

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
