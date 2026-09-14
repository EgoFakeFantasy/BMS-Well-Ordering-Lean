import BMSConstructibleBridge.SecondOrderGraph
import YesMetaZFC.SetTheory.Language

/-!
# 任意二阶模型中的内部图码商结构

只对已满足内部根域公式的代码取商，等词为商上的真正相等。成员通过两端
换码律下降到商。此处证明外延性和空对象，不宣称基础、全部 TMC 公理或
商成员关系的宿主良基性；尤其不从非 β 模型制造外部 `Acc`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderQuotient

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic

set_option autoImplicit false

universe u

def setoid_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : Setoid (SecondOrderGraph.code_l ℳ) :=
  ⟨SecondOrderGraph.eq_l, ⟨SecondOrderGraph.refl_l hℳ,
    SecondOrderGraph.symm_l hℳ, SecondOrderGraph.trans_l hℳ⟩⟩

def type_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) := Quotient (setoid_l hℳ)

def mk_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) : type_l hℳ :=
  Quotient.mk (setoid_l hℳ) A

theorem eq_iff_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ) :
    mk_l hℳ A = mk_l hℳ B ↔ SecondOrderGraph.eq_l A B :=
  ⟨fun h => Quotient.exact h, fun h => @Quotient.sound _ (setoid_l hℳ) A B h⟩

theorem surj_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (a : type_l hℳ) :
    ∃ A : SecondOrderGraph.code_l ℳ, mk_l hℳ A = a :=
  Quotient.inductionOn a (fun A => ⟨A, rfl⟩)

def mem_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (a b : type_l hℳ) : Prop :=
  Quotient.liftOn₂ a b SecondOrderGraph.mem_l (by
    intro A B C D h h₁
    exact propext (SecondOrderGraph.mem_congr_l hℳ h h₁))

theorem mem_iff_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ) :
    mem_l hℳ (mk_l hℳ A) (mk_l hℳ B) ↔ SecondOrderGraph.mem_l A B := Iff.rfl

/-- 同一模型的内部图商给出纯集合论签名的实际结构，不增加原模型假设。 -/
def structure_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : FirstOrder.Structure.{0, 0, 0, u} ℒ where
  Carrier _ := type_l hℳ
  nonempty _ := by
    obtain ⟨A, _⟩ := SecondOrderGraph.empty_l hℳ
    exact ⟨mk_l hℳ A⟩
  funcInterp f := nomatch f
  relInterp
    | .membership, .cons a (.cons b .nil) => mem_l hℳ a b

theorem ext_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (a b : type_l hℳ) :
    (∀ c, mem_l hℳ c a ↔ mem_l hℳ c b) → a = b := by
  refine Quotient.inductionOn₂ a b (fun A B h => ?_)
  exact Quotient.sound ((SecondOrderGraph.ext_l hℳ A B).mpr (fun C => h (mk_l hℳ C)))

theorem empty_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : ∃ a : type_l hℳ, ∀ b, ¬mem_l hℳ b a := by
  obtain ⟨A, h⟩ := SecondOrderGraph.empty_l hℳ
  refine ⟨mk_l hℳ A, fun b => ?_⟩
  obtain ⟨B, rfl⟩ := surj_l hℳ b
  exact h B

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderQuotient
