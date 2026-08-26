import YesMetaZFC.SetTheory.Definitional.Project
import YesMetaZFC.SetTheory.Definitional.Project.Hierarchy.Syntax

/-!
# 项目公式 schema 的语义解释

纯语法数据位于 `Project.Hierarchy.Syntax`；本模块只增加结构中的表示关系。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project

universe u

namespace UnarySchema

/-- 一元 schema 在参数环境下表示的纸面类。 -/
def denote {ℳ : Structure.{u}} {parameterCount : Nat}
    (schema : UnarySchema parameterCount)
    (env : Env ℳ parameterCount) (value : ℳ.Domain) : Prop :=
  Formula.satisfies (env.push value) schema.body

end UnarySchema

namespace BinarySchema

/-- 二元 schema 在参数环境下表示的纸面二元类关系。 -/
def denote {ℳ : Structure.{u}} {parameterCount : Nat}
    (schema : BinarySchema parameterCount)
    (env : Env ℳ parameterCount)
    (input output : ℳ.Domain) : Prop :=
  Formula.satisfies ((env.push input).push output) schema.body

end BinarySchema
end Project
end Definitional
end SetTheory
end YesMetaZFC
