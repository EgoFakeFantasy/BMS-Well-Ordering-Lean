import YesMetaZFC.Logic.Theory.Basic

/-!
# 类型化局部上下文

局部上下文中的公式共享同一个有限 free 上下文。该层供未来自然演绎前端与演绎
定理使用，不进入最小可信 Hilbert 推导核。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

/-- 共享 free 上下文的一阶局部假设列表。 -/
abbrev Context (σ : Signature.{u, v, w})
    (free : SortContext σ) :=
  List (OpenFormula σ free)

end FirstOrder
end Logic
end YesMetaZFC
