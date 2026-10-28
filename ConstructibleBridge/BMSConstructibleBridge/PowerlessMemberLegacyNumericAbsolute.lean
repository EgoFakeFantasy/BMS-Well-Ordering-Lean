import BMSConstructibleBridge.PowerlessLegacyNumericSyntax
import BMSConstructibleBridge.PowerlessMemberBounded

/-! # 旧数字图资格在传递成员域中的绝对性

十个参数都是同一 W 的实际成员。只对已分类的纯 Δ₀ 数字资格使用
传递域绝对性，不把共同捕获域 I 假定为传递，也不重新选 Q 或 V。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberLegacyNumericAbsolute

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {W : carrier_l ℳ}
  {hW : ∃ x, member_l ℳ x W}

local notation "𝒩₀" => PowerlessMemberStructure.structure_l W hW
local notation "M" => PowerlessMemberStructure.type_l (ℳ := ℳ) W

theorem spec_l (hTrans : PowerlessNaturalOrder.transitive_l W)
    (ω e t₁ t₂ t₃ t₄ P N V Q : M) :
    PowerlessLegacyNumericSyntax.spec_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ t₄ P N V Q ↔
      PowerlessLegacyNumericSyntax.spec_l (𝒩 := ℳ)
        ω.val e.val t₁.val t₂.val t₃.val t₄.val P.val N.val V.val Q.val := by
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree Q |>.pushFree V |>.pushFree N |>.pushFree P
      |>.pushFree t₄ |>.pushFree t₃ |>.pushFree t₂ |>.pushFree t₁
      |>.pushFree e |>.pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    PowerlessLegacyNumericSyntax.formula_m
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
  have hφ : Formula.IsDelta0 StabilityFrame.membershipLevyBound φ :=
    PowerlessLegacyNumericSyntax.delta_l _ _ _ _ _ _ _ _ _ _
  have h := PowerlessMemberBounded.formula_l
    (fun x hx y hy => hTrans x y hx hy) hφ η
  simpa only [φ, PowerlessLegacyNumericSyntax.formula_l, Term.eval,
    Env.pushFree_here, Env.pushFree_there, PowerlessRelativization.env_l, η] using h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberLegacyNumericAbsolute
