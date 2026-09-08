import YesMetaZFC.Logic.FirstOrder.FormalSystem.ExpressionEncoding
import YesMetaZFC.Logic.FirstOrder.LevyHierarchy
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicFormulaTemplate

/-!
# ProofT 的局部证明码域

Rosser 比较不需要“全体自然数”作为集合存在；它只需要候选证明码相对每个外部
标准 numeral 可切分。本模块固定一个纯集合论局部域：

* `point = 0` 或 `0 ∈ point`；
* 若 `x ∈ point`，则 `S(x) = point` 或 `S(x) ∈ point`。

定义、支撑与层级分类均由内在类型语法直接保证。该条件的 numeral realization 和
有限边界切分位于 `ProofT.SuccessorCodeDomain`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 纯集合论语言中由成员关系给出的标准 Lévy 有界量词参数。 -/
def set_levy_bound : Formula.LevyBound signature where
  sort := SetSort.set
  relation := RelationSymbol.membership
  domains := by rfl

/-- 后继码域模板的唯一 free 槽位。 -/
abbrev successor_code_domain_free : SetContext := [SetSort.set]

/-- 对象证明码沿 von Neumann 后继无缺口的内在条件模板。 -/
def successor_code_domain : FormulaTemplate.Unary where
  body :=
    let point : SetOpenTerm successor_code_domain_free := .fvar .here
    ((point ≐ₘ ∅ₘ) ∨ₘ (∅ₘ ∈ₘ point)) ∧ₘ
      set_levy_bound.boundedForall point
        ((Sₘ(bₘ[.here]) ≐ₘ point.weakenBound SetSort.set) ∨ₘ
          (Sₘ(bₘ[.here]) ∈ₘ point.weakenBound SetSort.set))

/-- 后继码域模板本体是正式的 Lévy `Delta0` 公式。 -/
theorem successor_code_domain_body_delta0 :
    Formula.IsDelta0 set_levy_bound successor_code_domain.body := by
  let point : SetOpenTerm successor_code_domain_free := .fvar .here
  have hBody :
      Formula.IsDelta0 set_levy_bound
        ((Sₘ(bₘ[.here]) ≐ₘ point.weakenBound SetSort.set) ∨ₘ
          (Sₘ(bₘ[.here]) ∈ₘ point.weakenBound SetSort.set)) :=
    Formula.IsDelta0.disj
      (Formula.IsDelta0.equal
        (Sₘ(bₘ[.here])) (point.weakenBound SetSort.set))
      (Formula.IsDelta0.rel (ℬ := set_levy_bound)
        RelationSymbol.membership
        𝒂ₘ(Sₘ(bₘ[.here]), point.weakenBound SetSort.set))
  simpa [successor_code_domain, point] using
    Formula.IsDelta0.conj
      (Formula.IsDelta0.disj
        (Formula.IsDelta0.equal point ∅ₘ)
        (Formula.IsDelta0.rel (ℬ := set_levy_bound)
          RelationSymbol.membership
          𝒂ₘ(∅ₘ, point)))
      (Formula.IsDelta0.bounded_forall point hBody)

/-- 在任意内在上下文中实例化后的后继码域仍是正式的 Lévy `Delta0` 公式。 -/
theorem successor_code_domain_delta0
    {bound free : SetContext}
    (point : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (successor_code_domain point) := by
  exact Formula.IsDelta0.substituteMapped
    (boundSubstitution := VariableSubstitution.empty)
    (freeSubstitution :=
      VariableSubstitution.cons point VariableSubstitution.empty)
    successor_code_domain_body_delta0

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
