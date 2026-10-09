import BMSConstructibleBridge.PowerlessFormulaConstructor

/-! # 编译器保留的有限构造证书

证书记录实际选出的同一数码与变量槽界，供证明该输出属于内部合法性关系。
这是宿主 Prop 中的有限构造记录，不是内部合法性本身；不宣称非标准合法码
都有这种外部有限证书。零、成员、相等、NAND、指定槽存在量词保留原编码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCodeDerivation

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

inductive derivation_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e T t₁ t₂ t₃ : carrier_l 𝒩) : carrier_l 𝒩 → carrier_l 𝒩 → Prop
  | zero {N} : derivation_l ω e T t₁ t₂ t₃ e N
  | membership {a b c N} (hCode : PowerlessFormulaConstructor.constructor_l ω e T e a b c)
      (ha : member_l 𝒩 a N) (hb : member_l 𝒩 b N) : derivation_l ω e T t₁ t₂ t₃ c N
  | equality {a b c N} (hCode : PowerlessFormulaConstructor.constructor_l ω e T t₁ a b c)
      (ha : member_l 𝒩 a N) (hb : member_l 𝒩 b N) : derivation_l ω e T t₁ t₂ t₃ c N
  | nand {a b c N} (hCode : PowerlessFormulaConstructor.constructor_l ω e T t₂ a b c)
      (ha : derivation_l ω e T t₁ t₂ t₃ a N) (hb : derivation_l ω e T t₁ t₂ t₃ b N) :
      derivation_l ω e T t₁ t₂ t₃ c N
  | existential {i b c N} (hCode : PowerlessFormulaConstructor.constructor_l ω e T t₃ i b c)
      (hi : member_l 𝒩 i N) (hb : derivation_l ω e T t₁ t₂ t₃ b N) :
      derivation_l ω e T t₁ t₂ t₃ c N
  | widen {c N M} (h : derivation_l ω e T t₁ t₂ t₃ c N)
      (hN : member_l 𝒩 N ω) (hM : member_l 𝒩 M ω) (hNM : subset_l N M) :
      derivation_l ω e T t₁ t₂ t₃ c M

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCodeDerivation
