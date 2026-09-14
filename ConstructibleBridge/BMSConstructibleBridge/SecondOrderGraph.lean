import BMSConstructibleBridge.SecondOrderBisimulation
import BMSConstructibleBridge.SecondOrderDomain

/-!
# 任意二阶模型中的内部图码与成员关系

图码只携带内部根无下降链证书，绝不携带宿主 `Acc`。相等和成员的换码律
使用同一模型中的双模拟见证；子根域保持确保外延性遍历整个实际解释域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

structure code_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m) where
  real : set_l ℳ
  root : num_l ℳ
  wf : SecondOrderDomain.wf_l real root

def eq_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (A B : code_l ℳ) : Prop :=
  SecondOrderBisimulation.eq_l A.real B.real A.root B.root

def mem_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (A B : code_l ℳ) : Prop :=
  ∃ b, relation_l B.real b B.root ∧ SecondOrderBisimulation.eq_l A.real B.real A.root b

theorem refl_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (A : code_l ℳ) : eq_l A A :=
  SecondOrderBisimulation.refl_l hℳ A.real A.root

theorem symm_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) {A B : code_l ℳ} (h : eq_l A B) : eq_l B A :=
  SecondOrderBisimulation.symm_l hℳ A.real B.real A.root B.root h

theorem trans_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) {A B C : code_l ℳ} (h : eq_l A B) (h₁ : eq_l B C) :
    eq_l A C := SecondOrderBisimulation.trans_l hℳ A.real B.real C.real A.root B.root C.root h h₁

private theorem mem_right {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) {A B C : code_l ℳ} (h : eq_l B C) (h₁ : mem_l A B) :
    mem_l A C := by
  obtain ⟨b, h₁, h₂⟩ := h₁
  obtain ⟨c, h₃, h₄⟩ := (SecondOrderBisimulation.match_l B.real C.real B.root C.root h).1 b h₁
  exact ⟨c, h₃, SecondOrderBisimulation.trans_l hℳ A.real B.real C.real A.root b c h₂ h₄⟩

theorem mem_congr_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) {A B C D : code_l ℳ} (h : eq_l A B) (h₁ : eq_l C D) :
    mem_l A C ↔ mem_l B D := by
  constructor
  · rintro ⟨c, h₂, h₃⟩
    exact mem_right hℳ h₁ ⟨c, h₂,
      SecondOrderBisimulation.trans_l hℳ B.real A.real C.real B.root A.root c (symm_l hℳ h) h₃⟩
  · rintro ⟨d, h₂, h₃⟩
    exact mem_right hℳ (symm_l hℳ h₁) ⟨d, h₂,
      SecondOrderBisimulation.trans_l hℳ A.real B.real D.real A.root B.root d h h₃⟩

def child_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (A : code_l ℳ) (a : num_l ℳ)
    (h : relation_l A.real a A.root) : code_l ℳ :=
  ⟨A.real, a, SecondOrderDomain.child_l hℳ A.real A.root a A.wf h⟩

theorem child_mem_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (A : code_l ℳ) (a : num_l ℳ)
    (h : relation_l A.real a A.root) : mem_l (child_l hℳ A a h) A :=
  ⟨a, h, SecondOrderBisimulation.refl_l hℳ A.real a⟩

/-- 用实际域内子码证明外延性，不把无域证书的任意节点当作对象。 -/
theorem ext_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (A B : code_l ℳ) :
    eq_l A B ↔ ∀ C : code_l ℳ, mem_l C A ↔ mem_l C B := by
  refine ⟨fun h C => mem_congr_l hℳ (refl_l hℳ C) h, fun h => ?_⟩
  apply (SecondOrderBisimulation.unfold_l hℳ A.real B.real A.root B.root).mpr
  constructor
  · intro a h₁
    exact (h (child_l hℳ A a h₁)).mp (child_mem_l hℳ A a h₁)
  · intro b h₁
    obtain ⟨a, h₂, h₃⟩ := (h (child_l hℳ B b h₁)).mpr (child_mem_l hℳ B b h₁)
    exact ⟨a, h₂, SecondOrderBisimulation.symm_l hℳ B.real A.real b a h₃⟩

/-- 对象理解产生空关系实数，进而给出非空的内部图解释域。 -/
theorem empty_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : ∃ A : code_l ℳ, ∀ B, ¬mem_l B A := by
  obtain ⟨R, hR⟩ := SecondOrderModel.comprehension_l hℳ .falsum rfl (Env.empty (M := ℳ))
  have h : ∀ a b, ¬relation_l R a b := fun a b h => (hR (value_l a b)).mp h
  refine ⟨⟨R, zero_l ℳ, SecondOrderDomain.leaf_l R (zero_l ℳ) (fun b => h b _)⟩, ?_⟩
  rintro B ⟨b, h₁, _⟩
  exact h b _ h₁

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraph
