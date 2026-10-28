import BMSConstructibleBridge.SecondOrderHereditaryCandidateSource

/-! # 原 Z₂ 中每个固定外部高度的 BMS 良基性对象推导

对象语言是原二阶算术 signature_m，背景是原 SecondOrderArithmetic.theory_m，
目标为原 SecondOrderConcreteFormula.closed_m H，正式关系为原 Derives。
每个原模型的每个实数候选均取得实际完整遗传源，逐个消去 Prop 存在证书
后沿原纯算术矩阵迁移和 Type 0 完备性回传。不保留 hSources 或基底守卫。

目标排除当前高度始终 ≤ H 的生成数组严格一步展开下降链，不限制种子高度。
H 是外部模式索引；这里没有用内部统一真值断言替换原模式，也不宣称
整个不限行数 BMS 的统一良序命题已在 Z₂ 中证明。目标没有打包线性可比性，
原 ZFC 的完整 StrictWellOrder 接口由独立的 FinalAssembly 保留。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderHereditaryBMSWellOrder

open Logic FirstOrder

set_option autoImplicit false

universe u

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (H : Nat) :
    (SecondOrderConcreteFormula.closed_m H).TrueIn ℳ :=
  PowerlessBMSNonemptyTransfer.closed_l H (fun X => SecondOrderHereditaryCandidateSource.exists_l hℳ X)

theorem derives_m (H : Nat) :
    Derives SecondOrderArithmetic.theory_m [] (SecondOrderConcreteFormula.closed_m H) :=
  PowerlessBMSNonemptyTransfer.derives_m H (fun hℳ X =>
    SecondOrderHereditaryCandidateSource.exists_l hℳ X)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderHereditaryBMSWellOrder
