import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.FunctionApplication
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hierarchy

/-!
# 函数求值图消去的 `Delta0` 证书

函数图编译器的具体图条件只使用函数谓词、定义域成员、图成员与等式。
因此其层级证明是纯句法的，不依赖映射谓词理论中的全体性或单值性公理。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace FunctionApplication

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 函数求值 guard 的 `Delta0` 证书。 -/
theorem guard_delta0
    (function argument : SetTerm) :
    Formula.IsDelta0 set_levy_bound
      (guard function argument) := by
  simpa [guard] using
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.isFunction
        [function])
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [argument, domₘ(function)])

/-- 具体函数求值图的 `Delta0` 证书。 -/
theorem graph_delta0
    (arguments : List SetTerm)
    (result : SetTerm) :
    Formula.IsDelta0 set_levy_bound
      (graph arguments result) := by
  cases arguments with
  | nil =>
      simpa [graph] using
        (Formula.IsDelta0.falsum :
          Formula.IsDelta0 set_levy_bound
            (Formula.falsum : SetFormula))
  | cons function tail =>
      cases tail with
      | nil =>
          simpa [graph] using
            (Formula.IsDelta0.falsum :
              Formula.IsDelta0 set_levy_bound
                (Formula.falsum : SetFormula))
      | cons argument rest =>
          cases rest with
          | cons extra rest =>
              simpa [graph] using
                (Formula.IsDelta0.falsum :
                  Formula.IsDelta0 set_levy_bound
                    (Formula.falsum : SetFormula))
          | nil =>
              have hGuard :=
                guard_delta0 function argument
              have hGraph :
                  Formula.IsDelta0 set_levy_bound
                    ((⟨argument, result⟩ₘ ∈ₘ function)) :=
                Formula.IsDelta0.rel
                  RelationSymbol.membership
                  [⟨argument, result⟩ₘ, function]
              have hFallback :
                  Formula.IsDelta0 set_levy_bound
                    (result ≐ₘ function) :=
                Formula.IsDelta0.equal result function
              simpa [graph] using
                Formula.IsDelta0.conj
                  (Formula.IsDelta0.imp hGuard hGraph)
                  (Formula.IsDelta0.imp
                    (Formula.IsDelta0.neg hGuard)
                    hFallback)

/-! ## 图表示的层级接口 -/

/-- 带有 `Delta0` 图条件证书的函数图表示。 -/
structure Delta0GraphPresentation
    (D : Data signature)
    (bound : Formula.LevyBound signature)
    extends GraphPresentation D where
  graph_delta0 :
    ∀ arguments result,
      Formula.IsDelta0 bound
        (D.graph arguments result)

variable
  {D : Data signature}
  {bound : Formula.LevyBound signature}

mutual
  def term_conditions_delta0
      (P : Delta0GraphPresentation D bound)
      (start : Nat)
      (source : SetTerm)
      (condition : SetFormula) :
      condition ∈
          (term D start source).conditions →
        Formula.IsDelta0 bound condition := by
    intro hCondition
    cases source with
    | var value =>
        cases value <;>
          simp [term] at hCondition
    | app function arguments =>
        by_cases hFunction : function = D.symbol
        · subst function
          simp only [term] at hCondition
          rcases List.mem_cons.mp hCondition with
            hHead | hTail
          · subst condition
            exact P.graph_delta0 _ _
          · exact
              terms_conditions_delta0
                P (start + 1) arguments condition hTail
        · have hCondition' :
              condition ∈ (terms D start arguments).conditions := by
            simpa [term, hFunction] using hCondition
          exact
            terms_conditions_delta0
              P start arguments condition hCondition'
  def terms_conditions_delta0
      (P : Delta0GraphPresentation D bound)
      (start : Nat)
      (sources : List SetTerm)
      (condition : SetFormula) :
      condition ∈
          (terms D start sources).conditions →
        Formula.IsDelta0 bound condition := by
    intro hCondition
    cases sources with
    | nil =>
        simp [terms] at hCondition
    | cons head tail =>
        simp only [terms, List.mem_append] at hCondition
        rcases hCondition with
          hHead | hTail
        · exact
            term_conditions_delta0
              P start head condition hHead
        · exact
            terms_conditions_delta0
              P (term D start head).next tail condition hTail
end

/-- 单项编译产生的每一条图条件都保持 `Delta0`。 -/
theorem term_conditions_delta0_of_mem
    (P : Delta0GraphPresentation D bound)
    (start : Nat)
    (source : SetTerm)
    (condition : SetFormula)
    (hCondition :
      condition ∈ (term D start source).conditions) :
    Formula.IsDelta0 bound condition :=
  term_conditions_delta0 P start source condition hCondition

/-- 参数表编译产生的每一条图条件都保持 `Delta0`。 -/
theorem terms_conditions_delta0_of_mem
    (P : Delta0GraphPresentation D bound)
    (start : Nat)
    (sources : List SetTerm)
    (condition : SetFormula)
    (hCondition :
      condition ∈ (terms D start sources).conditions) :
    Formula.IsDelta0 bound condition :=
  terms_conditions_delta0 P start sources condition hCondition

/-- `Delta0` 条件列表与 `Delta0` 核心合取后仍为 `Delta0`。 -/
theorem condition_conjunction_delta0
    (conditions : List SetFormula)
    (core : SetFormula)
    (hConditions :
      ∀ condition, condition ∈ conditions →
        Formula.IsDelta0 bound condition)
    (hCore : Formula.IsDelta0 bound core) :
    Formula.IsDelta0 bound
      (condition_conjunction conditions core) := by
  induction conditions with
  | nil =>
      simpa [condition_conjunction] using hCore
  | cons head tail ih =>
      apply Formula.IsDelta0.conj
      · exact hConditions head (by simp)
      · apply ih
        · intro condition hCondition
          exact hConditions condition (by simp [hCondition])

/-- 单项编译条件与 `Delta0` 核心合取后的层级证书。 -/
theorem term_condition_conjunction_delta0
    (P : Delta0GraphPresentation D bound)
    (start : Nat)
    (source : SetTerm)
    (core : SetFormula)
    (hCore : Formula.IsDelta0 bound core) :
    Formula.IsDelta0 bound
      (condition_conjunction
        (term D start source).conditions core) :=
  condition_conjunction_delta0
    _ core
    (fun condition hCondition =>
      term_conditions_delta0_of_mem
        P start source condition hCondition)
    hCore

/-- 参数表编译条件与 `Delta0` 核心合取后的层级证书。 -/
theorem terms_condition_conjunction_delta0
    (P : Delta0GraphPresentation D bound)
    (start : Nat)
    (sources : List SetTerm)
    (core : SetFormula)
    (hCore : Formula.IsDelta0 bound core) :
    Formula.IsDelta0 bound
      (condition_conjunction
        (terms D start sources).conditions core) :=
  condition_conjunction_delta0
    _ core
    (fun condition hCondition =>
      terms_conditions_delta0_of_mem
        P start sources condition hCondition)
    hCore

/-- `Delta0` 主体的有限见证闭包是 `Sigma1`。 -/
theorem close_witnesses_sigma1_of_delta0
    (count : Nat)
    (body : SetFormula)
    (hBody : Formula.IsDelta0 bound body) :
    Formula.IsSigma1 bound
      (close_witnesses SetSort.set count body) := by
  induction count with
  | zero =>
      simpa [close_witnesses] using hBody.to_sigma1
  | succ count ih =>
      simpa [close_witnesses] using
        Formula.IsSigma1.exists_closeFreeAt
          SetSort.set (witness_id count) ih

/-- 单项编译的条件闭包在 `Delta0` 核心下是 `Sigma1`。 -/
theorem term_condition_closure_sigma1
    (P : Delta0GraphPresentation D bound)
    (start : Nat)
    (source : SetTerm)
    (core : SetFormula)
    (hCore : Formula.IsDelta0 bound core) :
    Formula.IsSigma1 bound
      (close_witnesses SetSort.set
        ((term D start source).next - start)
        (condition_conjunction
          (term D start source).conditions core)) :=
  close_witnesses_sigma1_of_delta0
    _
    _
    (term_condition_conjunction_delta0
      P start source core hCore)

/-- 参数表编译的条件闭包在 `Delta0` 核心下是 `Sigma1`。 -/
theorem terms_condition_closure_sigma1
    (P : Delta0GraphPresentation D bound)
    (start : Nat)
    (sources : List SetTerm)
    (core : SetFormula)
    (hCore : Formula.IsDelta0 bound core) :
    Formula.IsSigma1 bound
      (close_witnesses SetSort.set
        ((terms D start sources).next - start)
        (condition_conjunction
          (terms D start sources).conditions core)) :=
  close_witnesses_sigma1_of_delta0
    _
    _
    (terms_condition_conjunction_delta0
      P start sources core hCore)

/-- `Delta0` 图条件自动得到 `Sigma1` 分类。 -/
theorem Delta0GraphPresentation.graph_sigma1
    {D : Data signature}
    {bound : Formula.LevyBound signature}
    (P : Delta0GraphPresentation D bound)
    (arguments : List SetTerm)
    (result : SetTerm) :
    Formula.IsSigma1 bound
      (D.graph arguments result) :=
  (P.graph_delta0 arguments result).to_sigma1

/-- `Delta0` 图条件自动得到 `Pi1` 分类。 -/
theorem Delta0GraphPresentation.graph_pi1
    {D : Data signature}
    {bound : Formula.LevyBound signature}
    (P : Delta0GraphPresentation D bound)
    (arguments : List SetTerm)
    (result : SetTerm) :
    Formula.IsPi1 bound
      (D.graph arguments result) :=
  (P.graph_delta0 arguments result).to_pi1

/-- 函数求值图的具体 `Delta0` 表示实例。 -/
def delta0_graph_presentation :
    Delta0GraphPresentation
      FunctionApplication.data
      ProofT.set_levy_bound where
  toGraphPresentation := graph_presentation
  graph_delta0 := graph_delta0

end FunctionApplication
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
