import BMSConstructibleBridge.PowerlessRootedFamilyNormalizationSyntax
import BMSConstructibleBridge.PowerlessNumberSuccessorReading
import BMSConstructibleBridge.SecondOrderRootedRealFamilyNormalization

/-! # 同一原零根规范化族的全部内部数读数

实际纯 Δ₀ 正文与原二阶族规范化逐数一致。配数输出、行标记及
后继均通过原商数码的单射性认同；没有模型外部标准性假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRootedFamilyNormalizationReading

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRootedFamilyNormalizationSyntax

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private abbrev e_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
private abbrev o_l (K : source_coding_l hℳ) :=
  (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val

theorem root_l (K : source_coding_l hℳ) {S U : SecondOrderQuotient.type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hU : ∀ c, mem_l hℳ c U → mem_l hℳ c K.omega) {H : SecondOrderModel.set_l ℳ}
    (hTrace : setRel_l K ⟨U, hU⟩ H) (i r : SecondOrderModel.num_l ℳ) :
    PowerlessRootedFamilyNormalizationSyntax.root_l (𝒩 := 𝒱) K.omega (e_l K) (o_l K) S U
      (numberCode_l K i).val (numberCode_l K r).val ↔
        SecondOrderRootedRealFamilyNormalization.root_l H i r := by
  constructor
  · rintro ⟨c, _hc, hPair, hRow⟩
    obtain rfl := (PowerlessBoundedNumericPairing.instance_l K hS _ r c).mp hPair
    exact (PowerlessRootedRealSyntax.row_instance_l K hS hU hTrace _ _).mp hRow
  · intro hRoot
    exact ⟨(numberCode_l K (SecondOrderPairing.value_l (SecondOrderModel.succ_l
      (SecondOrderModel.zero_l ℳ)) r)).val,
      (numberCode_l K _).property, (PowerlessBoundedNumericPairing.instance_l K hS _ r _).mpr rfl,
      (PowerlessRootedRealSyntax.row_instance_l K hS hU hTrace _ _).mpr hRoot⟩

theorem graph_l (K : source_coding_l hℳ) {S U : SecondOrderQuotient.type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hU : ∀ c, mem_l hℳ c U → mem_l hℳ c K.omega) {H : SecondOrderModel.set_l ℳ}
    (hTrace : setRel_l K ⟨U, hU⟩ H) (i a b : SecondOrderModel.num_l ℳ) :
    PowerlessRootedFamilyNormalizationSyntax.graph_l (𝒩 := 𝒱) K.omega (e_l K) S U
      (numberCode_l K i).val (numberCode_l K a).val (numberCode_l K b).val ↔
        SecondOrderRootedRealFamilyNormalization.graph_l H i a b := by
  constructor
  · rintro ⟨c, _hc, d, _hd, hPair, hTag, hRow⟩
    obtain rfl := (PowerlessBoundedNumericPairing.instance_l K hS a b c).mp hPair
    obtain rfl := (PowerlessBoundedNumericPairing.instance_l K hS _ _ d).mp hTag
    exact (PowerlessRootedRealSyntax.row_instance_l K hS hU hTrace _ _).mp hRow
  · intro hGraph
    exact ⟨(numberCode_l K (SecondOrderPairing.value_l a b)).val, (numberCode_l K _).property,
      (numberCode_l K (SecondOrderPairing.value_l (SecondOrderModel.zero_l ℳ)
        (SecondOrderPairing.value_l a b))).val, (numberCode_l K _).property,
      (PowerlessBoundedNumericPairing.instance_l K hS a b _).mpr rfl,
      (PowerlessBoundedNumericPairing.instance_l K hS _ _ _).mpr rfl,
      (PowerlessRootedRealSyntax.row_instance_l K hS hU hTrace _ _).mpr hGraph⟩

theorem edge_l (K : source_coding_l hℳ) {S U : SecondOrderQuotient.type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hU : ∀ c, mem_l hℳ c U → mem_l hℳ c K.omega) {H : SecondOrderModel.set_l ℳ}
    (hTrace : setRel_l K ⟨U, hU⟩ H) (i a b : SecondOrderModel.num_l ℳ) :
    PowerlessRootedFamilyNormalizationSyntax.edge_l (𝒩 := 𝒱) K.omega (e_l K) (o_l K) S U
      (numberCode_l K i).val (numberCode_l K a).val (numberCode_l K b).val ↔
        SecondOrderRootedRealFamilyNormalization.edge_l H i a b := by
  have hEq (n m : SecondOrderModel.num_l ℳ) :
      (numberCode_l K n).val = (numberCode_l K m).val ↔ n = m :=
    ⟨fun h => numberCode_injective_l K (Subtype.ext h), fun h => congrArg (fun j => (numberCode_l K j).val) h⟩
  constructor
  · rintro ⟨r, hr, hRoot, c, hc, hSucc, hBody⟩
    obtain ⟨r₀, hr₀⟩ := numberCode_surjective_l K ⟨r, hr⟩
    have hr₀' : (numberCode_l K r₀).val = r := congrArg Subtype.val hr₀
    obtain ⟨c₀, hc₀⟩ := numberCode_surjective_l K ⟨c, hc⟩
    have hc₀' : (numberCode_l K c₀).val = c := congrArg Subtype.val hc₀
    subst r c
    refine ⟨r₀, (root_l K hS hU hTrace i r₀).mp hRoot, c₀,
      (hEq a _).mp ((PowerlessNumberSuccessorReading.successor_l K c₀ _).mp hSucc), ?_⟩
    rcases hBody with ⟨hb, hGraph⟩ | ⟨d, hd, hSuccD, hGraph⟩
    · exact Or.inl ⟨(hEq b _).mp hb, (graph_l K hS hU hTrace i c₀ r₀).mp hGraph⟩
    · obtain ⟨d₀, hd₀⟩ := numberCode_surjective_l K ⟨d, hd⟩
      have hd₀' : (numberCode_l K d₀).val = d := congrArg Subtype.val hd₀
      subst d
      exact Or.inr ⟨d₀, (hEq b _).mp ((PowerlessNumberSuccessorReading.successor_l K d₀ _).mp hSuccD),
        (graph_l K hS hU hTrace i c₀ d₀).mp hGraph⟩
  · rintro ⟨r, hRoot, c, rfl, hBody⟩
    refine ⟨(numberCode_l K r).val, (numberCode_l K r).property,
      (root_l K hS hU hTrace i r).mpr hRoot, (numberCode_l K c).val, (numberCode_l K c).property,
      (PowerlessNumberSuccessorReading.successor_l K c _).mpr rfl, ?_⟩
    rcases hBody with ⟨rfl, hGraph⟩ | ⟨d, rfl, hGraph⟩
    · exact Or.inl ⟨rfl, (graph_l K hS hU hTrace i c r).mpr hGraph⟩
    · exact Or.inr ⟨(numberCode_l K d).val, (numberCode_l K d).property,
        (PowerlessNumberSuccessorReading.successor_l K d _).mpr rfl,
        (graph_l K hS hU hTrace i c d).mpr hGraph⟩

theorem body_l (K : source_coding_l hℳ) {S U : SecondOrderQuotient.type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hU : ∀ c, mem_l hℳ c U → mem_l hℳ c K.omega) {H : SecondOrderModel.set_l ℳ}
    (hTrace : setRel_l K ⟨U, hU⟩ H) (i z : SecondOrderModel.num_l ℳ) :
    PowerlessRootedFamilyNormalizationSyntax.body_l (𝒩 := 𝒱) K.omega (e_l K) (o_l K) S U
      (numberCode_l K i).val (numberCode_l K z).val ↔
        ∃ a b, SecondOrderPairing.value_l a b = z ∧
          SecondOrderRootedRealFamilyNormalization.edge_l H i a b := by
  constructor
  · rintro ⟨a, ha, b, hb, hPair, hEdge⟩
    obtain ⟨a₀, ha₀⟩ := numberCode_surjective_l K ⟨a, ha⟩
    obtain ⟨b₀, hb₀⟩ := numberCode_surjective_l K ⟨b, hb⟩
    have ha₀' : (numberCode_l K a₀).val = a := congrArg Subtype.val ha₀
    have hb₀' : (numberCode_l K b₀).val = b := congrArg Subtype.val hb₀
    subst a b
    have hCode := (PowerlessBoundedNumericPairing.instance_l K hS a₀ b₀ _).mp hPair
    exact ⟨a₀, b₀, numberCode_injective_l K (Subtype.ext hCode.symm),
      (edge_l K hS hU hTrace i a₀ b₀).mp hEdge⟩
  · rintro ⟨a, b, hPair, hEdge⟩
    refine ⟨(numberCode_l K a).val, (numberCode_l K a).property,
      (numberCode_l K b).val, (numberCode_l K b).property,
      (PowerlessBoundedNumericPairing.instance_l K hS a b _).mpr ?_,
      (edge_l K hS hU hTrace i a b).mpr hEdge⟩
    exact congrArg (fun n => (numberCode_l K n).val) hPair.symm

#print axioms edge_l
#print axioms body_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRootedFamilyNormalizationReading
