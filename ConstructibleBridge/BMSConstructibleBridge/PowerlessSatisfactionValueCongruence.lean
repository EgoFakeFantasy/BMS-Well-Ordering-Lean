import BMSConstructibleBridge.PowerlessSatisfactionSpecification

/-! # 原满足关系规格的全 raw 取值同余

在任意纯 ℒ 结构中固定 ω、A、零码、三个标签、构造图 T 和合法性图 F。
若 R 与 Q 在全部 raw 码和赋值坐标上取值等价，则更新分支、定义域、零码
条件及原四方程逐项等价，因此同一 Sat 规格可在两图之间传输。

本模块仅是原规格的语义同余，不要求任何模型公理，不使用模型外部归纳或
选择，不构造共同界或求值图，也不宣称对象推导终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionValueCongruence

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 全 raw 取值对应保留同一个更新赋值及全部见证。 -/
theorem exists_l (ω A R Q f i b : carrier_l 𝒩)
    (hValue : ∀ c g, value_l R c g ↔ value_l Q c g) :
    PowerlessFiniteEvaluationRelationEquations.exists_l ω A R f i b ↔
      PowerlessFiniteEvaluationRelationEquations.exists_l ω A Q f i b := by
  constructor
  · rintro ⟨m, hm, hf, hi, a, ha, g, hg, hUpdate, hR⟩
    exact ⟨m, hm, hf, hi, a, ha, g, hg, hUpdate, (hValue b g).mp hR⟩
  · rintro ⟨m, hm, hf, hi, a, ha, g, hg, hUpdate, hQ⟩
    exact ⟨m, hm, hf, hi, a, ha, g, hg, hUpdate, (hValue b g).mpr hQ⟩

/-- 定义域守卫和长度见证固定，只替换查询前提。 -/
theorem domain_l (ω A F R Q : carrier_l 𝒩)
    (hValue : ∀ c f, value_l R c f ↔ value_l Q c f) :
    PowerlessSatisfactionSpecification.domain_l ω A F R ↔
      PowerlessSatisfactionSpecification.domain_l ω A F Q := by
  constructor
  · intro h c f hQ
    exact h c f ((hValue c f).mpr hQ)
  · intro h c f hR
    exact h c f ((hValue c f).mp hR)

/-- 零码恒假在同一零参数上保持。 -/
theorem zero_l (e R Q : carrier_l 𝒩)
    (hValue : ∀ c f, value_l R c f ↔ value_l Q c f) :
    PowerlessSatisfactionSpecification.zero_l e R ↔
      PowerlessSatisfactionSpecification.zero_l e Q := by
  constructor
  · intro h f hQ
    exact h f ((hValue e f).mpr hQ)
  · intro h f hR
    exact h f ((hValue e f).mp hR)

/-- 四个方程逐项传输；NAND 同时替换两条子查询，存在分支使用更新同余。 -/
private theorem equations_transfer_l (ω A e t₁ t₂ t₃ T F R Q : carrier_l 𝒩)
    (hValue : ∀ c f, value_l R c f ↔ value_l Q c f)
    (h : PowerlessSatisfactionSpecification.equations_l ω A e t₁ t₂ t₃ T F R) :
    PowerlessSatisfactionSpecification.equations_l ω A e t₁ t₂ t₃ T F Q := by
  intro c L f hc hL hf a b
  have hFour := h c L f hc hL hf a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hCode ha hb
    exact (hValue c f).symm.trans (hFour.1 hCode ha hb)
  · intro hCode ha hb
    exact (hValue c f).symm.trans (hFour.2.1 hCode ha hb)
  · intro hCode ha hb
    exact (hValue c f).symm.trans ((hFour.2.2.1 hCode ha hb).trans
      (not_congr (and_congr (hValue a f) (hValue b f))))
  · intro hCode ha hb
    exact (hValue c f).symm.trans ((hFour.2.2.2 hCode ha hb).trans
      (exists_l ω A R Q f a b hValue))

/-- 所有构造子、变量槽、合法性和赋值守卫保持原参数。 -/
theorem equations_l (ω A e t₁ t₂ t₃ T F R Q : carrier_l 𝒩)
    (hValue : ∀ c f, value_l R c f ↔ value_l Q c f) :
    PowerlessSatisfactionSpecification.equations_l ω A e t₁ t₂ t₃ T F R ↔
      PowerlessSatisfactionSpecification.equations_l ω A e t₁ t₂ t₃ T F Q :=
  ⟨equations_transfer_l ω A e t₁ t₂ t₃ T F R Q hValue,
    equations_transfer_l ω A e t₁ t₂ t₃ T F Q R (fun c f => (hValue c f).symm)⟩

/-- 全 raw 取值等价传输原 Sat 规格，不添加图域或模型公理前提。 -/
theorem spec_l (ω A e t₁ t₂ t₃ T F R Q : carrier_l 𝒩)
    (hValue : ∀ c f, value_l R c f ↔ value_l Q c f) :
    PowerlessSatisfactionSpecification.spec_l ω A e t₁ t₂ t₃ T F R ↔
      PowerlessSatisfactionSpecification.spec_l ω A e t₁ t₂ t₃ T F Q := by
  unfold PowerlessSatisfactionSpecification.spec_l
  exact and_congr (domain_l ω A F R Q hValue)
    (and_congr (zero_l e R Q hValue) (equations_l ω A e t₁ t₂ t₃ T F R Q hValue))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionValueCongruence
