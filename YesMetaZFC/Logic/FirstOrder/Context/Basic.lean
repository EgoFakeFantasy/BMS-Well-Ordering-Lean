import YesMetaZFC.Logic.Theory.Basic
/-!
# 一阶局部上下文的纯语法基本层

有限上下文只是公式列表；本模块不引入结构或满足关系。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w x
/-- 一阶局部上下文，列表顺序不承担逻辑含义。 -/
abbrev Context (σ : Signature.{u, v, w}) := List (Formula σ)
namespace Context
end Context
end FirstOrder
end Logic
end YesMetaZFC
