import BMSConstructibleBridge.SecondOrderFunctions
import BMSConstructibleBridge.GraphDomain

/-!
# 任意模型中的内部根良基域

严格沿用原根无内部下降链公式，不将其换成外部 `Acc`。前缀函数图在同一
模型内由理解公理产生，故子根遗传性适用于非标准、非 β 的 Henkin 模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDomain

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions

set_option autoImplicit false

universe u

/-- 只量化模型实数中的全函数图，链的索引覆盖模型自身全部数域。 -/
def wf_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (R : set_l ℳ) (a : num_l ℳ) : Prop :=
  ∀ X : set_l ℳ, function_l X → relation_l X (zero_l ℳ) a →
    ∃ i b c, relation_l X i b ∧ relation_l X (succ_l i) c ∧ ¬relation_l R c b

def environment_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (R : set_l ℳ) (a : num_l ℳ) : Env ℳ [] [.set, .num] :=
  ((Env.empty (M := ℳ)).pushFree a).pushFree R

/-- 原域公式在任意模型中恰好表达内部无下降链，不表达外部可达性。 -/
theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (η : Env ℳ [] [.set, .num]) :
    Formula.satisfies η GraphDomain.formula_m ↔
      wf_l (η.freeVal .here) (η.freeVal (.there .here)) := by
  simp only [GraphDomain.formula_m, GraphDomain.matrix_m, GraphDomain.function_m, Formula.satisfies,
    SecondOrderPairing.edge_l]
  rfl

/-- 删边不会引入新的内部下降链。 -/
theorem mono_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (R S : set_l ℳ) (a : num_l ℳ)
    (h : ∀ b c, relation_l S b c → relation_l R b c) (h₁ : wf_l R a) : wf_l S a := by
  intro X hX h₂
  obtain ⟨i, b, c, h₃, h₄, h₅⟩ := h₁ X hX h₂
  exact ⟨i, b, c, h₃, h₄, fun h₆ => h₅ (h c b h₆)⟩

/-- 用内部前缀图证明子根遗传性，不从内部域证书产生宿主 `Acc`。 -/
theorem child_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (a b : num_l ℳ)
    (h : wf_l R a) (h₁ : relation_l R b a) : wf_l R b := by
  intro X hX h₂
  obtain ⟨Y, h₀, h₃⟩ := prefix_l hℳ X a
  obtain ⟨i, c, d, h₄, h₅, h₆⟩ :=
    h Y (prefix_function_l hℳ X Y a hX h₀ h₃) ((h₀ a).mpr rfl)
  rcases predecessor_l hℳ i with rfl | ⟨i, rfl⟩
  · have h₄ := (h₀ c).mp h₄
    have h₅ := (hX (zero_l ℳ)).unique ((h₃ (zero_l ℳ) d).mp h₅) h₂
    subst c
    subst d
    exact False.elim (h₆ h₁)
  · exact ⟨i, c, d, (h₃ i c).mp h₄, (h₃ (succ_l i) d).mp h₅, h₆⟩

/-- 无子节点的根满足同一内部域公式。 -/
theorem leaf_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (R : set_l ℳ) (a : num_l ℳ) (h : ∀ b, ¬relation_l R b a) : wf_l R a := by
  intro X hX h₁
  obtain ⟨b, h₂, _⟩ := hX (succ_l (zero_l ℳ))
  exact ⟨zero_l ℳ, a, b, h₁, h₂, h b⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDomain
