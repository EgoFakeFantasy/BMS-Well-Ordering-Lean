import BMSConstructibleBridge.PowerlessLegacyAssignmentUpdateReading
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRestriction

/-! # 指定旧赋值上的实际前插更新图

类内有限映射的数槽读数确定整个函数对象。原前插构造先取得一对
赋值图，再由外延性把旧图对齐到任意给定旧赋值；新图保留完整更新
及新填充连接规格。不使用完整 Collection 或 Type 层选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentFrontInsert

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderFiniteAssignmentLift (number_l)
open PowerlessLegacyAssignmentSyntax (link_l)
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem ext_l (K : source_coding_l hℳ) {ω A f g : type_l hℳ B}
    (hω : ω.val = K.omega) (L : SecondOrderModel.num_l ℳ)
    (hf : map_l (ℳ := structure_l hℳ B hBase) f (number_l hBase K ω hω L) A)
    (hg : map_l (ℳ := structure_l hℳ B hBase) g (number_l hBase K ω hω L) A)
    (hRead : ∀ i : SecondOrderModel.num_l ℳ, ∀ y : type_l hℳ B,
      value_l (ℳ := structure_l hℳ B hBase) f (number_l hBase K ω hω i) y ↔
        value_l (ℳ := structure_l hℳ B hBase) g (number_l hBase K ω hω i) y) : f = g := by
  apply PowerlessRelativeClassFunctionRestriction.ext_l hf hg
  intro x y
  classical
  by_cases hx : mem_l hℳ x.val K.omega
  · obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨x.val, hx⟩
    have hiRaw := congrArg (fun q => q.val) hi
    have hiEq : number_l hBase K ω hω i = x := Subtype.ext hiRaw
    rw [← hiEq]
    exact hRead i y
  · have hFalse {F : type_l hℳ B}
        (hF : map_l (ℳ := structure_l hℳ B hBase) F (number_l hBase K ω hω L) A) :
        ¬value_l (ℳ := structure_l hℳ B hBase) F x y := by
      intro h
      have hxL := (PowerlessRelativeClassFunctionProperties.value_mem_l hF h).1
      exact hx (SecondOrderOmegaTransitive.member_l hℳ (k := (numberCode_l K L).val)
        (x := x.val) K.omega_spec (numberCode_l K L).property hxL)
    exact ⟨fun h => (hFalse hf h).elim, fun h => (hFalse hg h).elim⟩

theorem exists_l (K : source_coding_l hℳ) {ω A f x : type_l hℳ B}
    (hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω) (hω : ω.val = K.omega)
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    {c l d v L z : SecondOrderModel.num_l ℳ} {U : SecondOrderQuotient.type_l hℳ}
    (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hd : SecondOrderAssignmentSyntax.extension_l E c l d v) (hLength : SecondOrderOrder.lt_l l L)
    (hf : map_l (ℳ := structure_l hℳ B hBase) f (number_l hBase K ω hω L) A)
    (hLink : link_l K E c l L z U f.val)
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val)
    (hx : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K v).val x.val) :
    ∃ g : type_l hℳ B,
      map_l (ℳ := structure_l hℳ B hBase) g (number_l hBase K ω hω L) A ∧
        PowerlessAssignmentUpdate.update_l (ℳ := structure_l hℳ B hBase)
          f (number_l hBase K ω hω l) x g ∧
            link_l K E d (SecondOrderModel.succ_l l) L z U g.val := by
  obtain ⟨F, g, hF, hg, hUpdate, hRead, _⟩ :=
    SecondOrderLegacyAssignmentUpdate.exists_l K hΩ hω hE hc hd L z hLength hU hx
  have hFf : F = f := ext_l K hω L hF hf (fun i y =>
    (hRead i y).trans ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase)
      f (number_l hBase K ω hω i) y).trans (hLink i y.val)).symm)
  subst F
  exact ⟨g, hg, hUpdate, PowerlessLegacyAssignmentUpdateReading.prepend_l K hω
    hd hLength hf hg hUpdate hLink hU hx⟩

#print axioms ext_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyAssignmentFrontInsert
