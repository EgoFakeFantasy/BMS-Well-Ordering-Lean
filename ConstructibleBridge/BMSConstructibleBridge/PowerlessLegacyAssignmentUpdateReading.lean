import BMSConstructibleBridge.SecondOrderLegacyAssignmentUpdate
import BMSConstructibleBridge.PowerlessLegacyAssignmentSyntax

/-! # 任意类内更新赋值仍表示原前插码

不只处理预先构造的一对赋值：任意同域类内更新图都满足新填充连接式。
类外输出先由实际陪域守卫排除，随后核验全部内部数槽。环境枚举 U
仍无类成员前提；其唯一输出消去新槽读数中的原数值代表。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentUpdateReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderFiniteAssignmentLift (number_l)
open PowerlessLegacyAssignmentSyntax (link_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

theorem point_l (K : source_coding_l hℳ) {ω A f g x : type_l hℳ B}
    (hω : ω.val = K.omega) (L l : SecondOrderModel.num_l ℳ)
    (hf : map_l (ℳ := structure_l hℳ B hBase) f (number_l hBase K ω hω L) A)
    (hg : map_l (ℳ := structure_l hℳ B hBase) g (number_l hBase K ω hω L) A)
    (hUpdate : PowerlessAssignmentUpdate.update_l (ℳ := structure_l hℳ B hBase)
      f (number_l hBase K ω hω l) x g)
    (i : SecondOrderModel.num_l ℳ) (y : SecondOrderQuotient.type_l hℳ) :
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g.val (numberCode_l K i).val y ↔
      (i = l ∧ y = x.val) ∨ i ≠ l ∧
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val (numberCode_l K i).val y := by
  classical
  have hClass {F : type_l hℳ B}
      (hF : map_l (ℳ := structure_l hℳ B hBase) F (number_l hBase K ω hω L) A)
      (h : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val (numberCode_l K i).val y) :
      PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
    have hRaw := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F _ A).mp hF
    exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property
      (SecondOrderFunctionProperties.value_mem_l hℳ hRaw h).2
  by_cases hy : PowerlessRelativeClassCorrespondence.member_l hℳ B y
  · let y' : type_l hℳ B := ⟨y, hy⟩
    have hNum : number_l hBase K ω hω i = number_l hBase K ω hω l ↔ i = l := by
      constructor
      · intro h
        have hRaw := congrArg (fun a : type_l hℳ B => a.val) h
        exact numberCode_injective_l K (Subtype.ext hRaw)
      · exact fun h => h ▸ rfl
    have hValue : y' = x ↔ y = x.val := ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g
      (number_l hBase K ω hω i) y').symm.trans
      ((hUpdate _ y').trans (or_congr (and_congr hNum hValue)
        (and_congr (not_congr hNum)
          (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f
            (number_l hBase K ω hω i) y'))))
  · have hG : ¬value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g.val (numberCode_l K i).val y :=
      fun h => hy (hClass hg h)
    have hF : ¬value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val (numberCode_l K i).val y :=
      fun h => hy (hClass hf h)
    have hx : y ≠ x.val := fun h => hy (h.symm ▸ x.property)
    simp only [hG, hF, hx, and_false, or_self]

theorem prepend_l (K : source_coding_l hℳ) {ω A f g x : type_l hℳ B}
    (hω : ω.val = K.omega) {E : SecondOrderModel.set_l ℳ}
    {c l d v L z : SecondOrderModel.num_l ℳ} {U : SecondOrderQuotient.type_l hℳ}
    (hd : SecondOrderAssignmentSyntax.extension_l E c l d v) (hLength : SecondOrderOrder.lt_l l L)
    (hf : map_l (ℳ := structure_l hℳ B hBase) f (number_l hBase K ω hω L) A)
    (hg : map_l (ℳ := structure_l hℳ B hBase) g (number_l hBase K ω hω L) A)
    (hUpdate : PowerlessAssignmentUpdate.update_l (ℳ := structure_l hℳ B hBase)
      f (number_l hBase K ω hω l) x g)
    (hLink : link_l K E c l L z U f.val)
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val)
    (hx : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K v).val x.val) :
    link_l K E d (SecondOrderModel.succ_l l) L z U g.val := by
  intro i y
  rw [point_l K hω L l hf hg hUpdate i y]
  classical
  by_cases hi : i = l
  · subst i
    have hPad (j : SecondOrderModel.num_l ℳ) :
        SecondOrderLegacyAssignmentPadding.padded_l E d (SecondOrderModel.succ_l l) L z l j ↔ j = v := by
      simp only [SecondOrderLegacyAssignmentPadding.prepend_l hℳ hd hLength,
        eq_self, true_and, ne_eq, not_true_eq_false, false_and, or_false]
    simp only [eq_self, true_and, ne_eq, not_true_eq_false, false_and, or_false, hPad, exists_eq_left]
    exact ⟨fun h => h ▸ hx, fun h => SecondOrderFunctionProperties.value_unique_l hℳ hU h hx⟩
  · have hPad (j : SecondOrderModel.num_l ℳ) :
        SecondOrderLegacyAssignmentPadding.padded_l E d (SecondOrderModel.succ_l l) L z i j ↔
          SecondOrderLegacyAssignmentPadding.padded_l E c l L z i j := by
      simp only [SecondOrderLegacyAssignmentPadding.prepend_l hℳ hd hLength,
        hi, false_and, ne_eq, not_false_eq_true, true_and, false_or]
    simp only [hi, false_and, ne_eq, not_false_eq_true, true_and, false_or, hPad]
    exact hLink i y

#print axioms point_l
#print axioms prepend_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentUpdateReading
