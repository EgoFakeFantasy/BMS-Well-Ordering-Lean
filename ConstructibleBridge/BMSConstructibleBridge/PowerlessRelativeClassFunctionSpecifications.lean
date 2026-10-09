import BMSConstructibleBridge.PowerlessMemberSatisfactionFunctionAbsolute
import BMSConstructibleBridge.PowerlessMemberDefFunctionAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassFunctionAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassBounded

/-! # 同一原 Sat／Def 图在实际 Class 中的完整规格

完整图的无界量词由 Class 函数绝对性逐坐标处理，原规范行矩阵只使用
已证明的 Δ₀ 绝对性。G、D、U 及全部参数保持不变；不把整张图规格
误分类为 Δ₀，不预设共同壳初等或完整源理论。供实际覆盖包装配使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionSpecifications

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
    SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

theorem satisfaction_l
    (ω e t₁ t₂ t₃ P N F U G : M)
    (hG : map_l (ℳ := 𝒱) G.val U.val U.val)
    (hRead : ∀ a r : SecondOrderQuotient.type_l hℳ, value_l (ℳ := 𝒱) G.val a r ↔
      member_l 𝒱 a U.val ∧ member_l 𝒱 r U.val ∧
        PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒱)
          ω.val a e.val N.val P.val U.val U.val t₁.val t₂.val t₃.val F.val r) :
    PowerlessMemberSatisfactionFunctionAbsolute.spec_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ P N F U G := by
  refine ⟨(PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) G U U).mpr hG, ?_⟩
  intro a r
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree r |>.pushFree F |>.pushFree t₃ |>.pushFree t₂ |>.pushFree t₁
      |>.pushFree U |>.pushFree U |>.pushFree P |>.pushFree N |>.pushFree e
      |>.pushFree a |>.pushFree ω
  have hMatrix : PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒩₀)
      ω a e N P U U t₁ t₂ t₃ F r ↔
      PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒱)
        ω.val a.val e.val N.val P.val U.val U.val t₁.val t₂.val t₃.val F.val r.val := by
    let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
      PowerlessSatisfactionNormalizedMatrix.formula_m
        (.fvar .here)
        (.fvar (.there .here))
        (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there (.there (.there (.there .here))))))
        (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
    have hφ : Formula.IsDelta0 StabilityFrame.membershipLevyBound φ :=
      PowerlessSatisfactionNormalizedMatrix.delta_l _ _ _ _ _ _ _ _ _ _ _ _
    have h := PowerlessRelativeClassBounded.formula_l (hBase := hBase) hφ η
    simpa only [φ, PowerlessSatisfactionNormalizedMatrix.formula_l, Term.eval,
      Env.pushFree_here, Env.pushFree_there, PowerlessRelativeClassRelativization.env_l, η] using h
  exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G a r).trans
    ((hRead a.val r.val).trans (and_congr Iff.rfl (and_congr Iff.rfl hMatrix.symm)))

/-- 原有限赋值覆盖保持同一 U；不把有界 Seq 检查冒充完整覆盖。 -/
theorem coverage_l (ω U : M)
    (hCoverage : ∀ a : SecondOrderQuotient.type_l hℳ, member_l 𝒱 a U.val → ∀ f,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω.val a f → member_l 𝒱 f U.val) :
    ∀ a : M, member_l 𝒩₀ a U → ∀ f : M,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒩₀) ω a f → member_l 𝒩₀ f U := by
  intro a ha f h
  obtain ⟨n, hn, hf⟩ := h
  exact hCoverage a.val ha f.val ⟨n.val, hn, (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f n a).mp hf⟩

theorem def_l
    (ω e N Q U G D : M)
    (hD : map_l (ℳ := 𝒱) D.val U.val U.val)
    (hRead : ∀ a r : SecondOrderQuotient.type_l hℳ, value_l (ℳ := 𝒱) D.val a r ↔
      member_l 𝒱 a U.val ∧ member_l 𝒱 r U.val ∧
        PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒱)
          ω.val e.val N.val Q.val U.val G.val a r) :
    PowerlessMemberDefFunctionAbsolute.spec_l (𝒩 := 𝒩₀) ω e N Q U G D := by
  refine ⟨(PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) D U U).mpr hD, ?_⟩
  intro a r
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree r |>.pushFree a |>.pushFree G |>.pushFree U
      |>.pushFree Q |>.pushFree N |>.pushFree e |>.pushFree ω
  have hMatrix : PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒩₀) ω e N Q U G a r ↔
      PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒱)
        ω.val e.val N.val Q.val U.val G.val a.val r.val := by
    let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
      PowerlessMemberDefImageBounded.formula_m
        (.fvar .here)
        (.fvar (.there .here))
        (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there (.there (.there (.there .here))))))
        (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    have hφ : Formula.IsDelta0 StabilityFrame.membershipLevyBound φ :=
      PowerlessMemberDefImageBounded.delta_l _ _ _ _ _ _ _ _
    have h := PowerlessRelativeClassBounded.formula_l (hBase := hBase) hφ η
    simpa only [φ, PowerlessMemberDefImageBounded.formula_l, Term.eval,
      Env.pushFree_here, Env.pushFree_there, PowerlessRelativeClassRelativization.env_l, η] using h
  exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) D a r).trans
    ((hRead a.val r.val).trans (and_congr Iff.rfl (and_congr Iff.rfl hMatrix.symm)))

#print axioms satisfaction_l
#print axioms def_l
#print axioms coverage_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionSpecifications
