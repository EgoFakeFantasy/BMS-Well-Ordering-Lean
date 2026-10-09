import BMSConstructibleBridge.SecondOrderLegalMemberIndependence
import BMSConstructibleBridge.SecondOrderPairObjects

/-!
# 包含空母集分支的相对模型 Def 关系

非空分支使用全部内部合法公式及有效参数的精确子集族；空分支为 {∅}。
两分支合成全域且唯一的商对象关系，只在 Prop 中提供证书。此关系仍带原
模型及图呈现参数，不是纯集合语言 AST，不能作为 Def 对象定理交付。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDef

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderQuotient

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def nonempty_l (hℳ : Theory.Models ℳ theory_m) (X Y : type_l hℳ) : Prop :=
  ∃ (A : SecondOrderGraph.code_l ℳ) (a : num_l ℳ)
    (ha : SecondOrderPairing.relation_l A.real a A.root)
    (V E D Q R T F : set_l ℳ) (H : SecondOrderGraph.code_l ℳ),
    mk_l hℳ A = X ∧
      SecondOrderLegalMemberCollection.presentation_l hℳ A a ha V E D Q R T F H ∧ mk_l hℳ H = Y

def spec_l (hℳ : Theory.Models ℳ theory_m) (X Y : type_l hℳ) : Prop :=
  ((∀ z, ¬mem_l hℳ z X) ∧ SecondOrderPairObjects.pair_l hℳ X X Y) ∨ nonempty_l hℳ X Y

theorem nonempty_member_l (hℳ : Theory.Models ℳ theory_m) {X Y : type_l hℳ}
    (h : nonempty_l hℳ X Y) : ∃ z, mem_l hℳ z X := by
  obtain ⟨A, a, ha, _, _, _, _, _, _, _, _, hAX, _, _⟩ := h
  exact ⟨mk_l hℳ (SecondOrderGraph.child_l hℳ A a ha),
    (congrArg (mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A a ha))) hAX) ▸
      SecondOrderGraph.child_mem_l hℳ A a ha⟩

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {X Y Z : type_l hℳ}
    (hY : spec_l hℳ X Y) (hZ : spec_l hℳ X Z) : Y = Z := by
  rcases hY with ⟨hEmpty, hPair⟩ | hY
  · rcases hZ with ⟨_, hPair'⟩ | hZ
    · exact SecondOrderPairObjects.pair_unique_l hℳ hPair hPair'
    · obtain ⟨z, hz⟩ := nonempty_member_l hℳ hZ
      exact False.elim (hEmpty z hz)
  · rcases hZ with ⟨hEmpty, _⟩ | hZ
    · obtain ⟨z, hz⟩ := nonempty_member_l hℳ hY
      exact False.elim (hEmpty z hz)
    · obtain ⟨A, a, ha, V, E, D, Q, R, T, F, H, hAX, P, hHY⟩ := hY
      obtain ⟨B, b, hb, V', E', D', Q', R', U, G, J, hBX, P', hJZ⟩ := hZ
      have hHJ := SecondOrderLegalMemberIndependence.unique_l hℳ A B a b ha hb
        (hAX.trans hBX.symm) V V' E E' D D' Q Q' R R' T U F G H J P P'
      exact hHY.symm.trans (((eq_iff_l hℳ H J).mpr hHJ).trans hJZ)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (X : type_l hℳ) :
    ∃! Y, spec_l hℳ X Y := by
  classical
  have hExists : ∃ Y, spec_l hℳ X Y := by
    by_cases hX : ∃ z, mem_l hℳ z X
    · obtain ⟨A, rfl⟩ := surj_l hℳ X
      obtain ⟨z, hz⟩ := hX
      obtain ⟨Z, rfl⟩ := surj_l hℳ z
      obtain ⟨a, ha, _⟩ := hz
      obtain ⟨V, E, D, Q, R, T, F, H, P, _⟩ := SecondOrderLegalMemberCollection.exists_l hℳ A a ha
      exact ⟨mk_l hℳ H, Or.inr ⟨A, a, ha, V, E, D, Q, R, T, F, H, rfl, P, rfl⟩⟩
    · obtain ⟨Y, hY⟩ := SecondOrderPairObjects.pair_exists_l hℳ X X
      exact ⟨Y, Or.inl ⟨fun z hz => hX ⟨z, hz⟩, hY⟩⟩
  obtain ⟨Y, hY⟩ := hExists
  exact ⟨Y, hY, fun Z hZ => unique_l hℳ hZ hY⟩

#print axioms unique_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDef
