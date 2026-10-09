import BMSConstructibleBridge.PowerlessCodedCollectionSyntax
import BMSConstructibleBridge.PowerlessNumberSuccessorReading

/-! # 原带标签收集与拼接的全部内部数读数

纯检查器读取同一族与索引迹。筛选、标签配数和新根后继的规格
覆盖任意内部自然数，不只覆盖后来被证明良基的节点。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedCollectionReading

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private abbrev e_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

def roots_l (I : SecondOrderModel.set_l ℳ) (c : SecondOrderModel.num_l ℳ) : Prop :=
  ∃ i, SecondOrderModel.mem_l i I ∧ SecondOrderPairing.value_l i (SecondOrderModel.zero_l ℳ) = c

def tagged_l (H I : SecondOrderModel.set_l ℳ) (c d : SecondOrderModel.num_l ℳ) : Prop :=
  ∃ i a b, SecondOrderModel.mem_l i I ∧ SecondOrderPairing.value_l i a = c ∧
    SecondOrderPairing.value_l i b = d ∧ SecondOrderPairing.relation_l H i (SecondOrderPairing.value_l a b)

def graft_l (G P : SecondOrderModel.set_l ℳ) (c d : SecondOrderModel.num_l ℳ) : Prop :=
  ∃ a, c = SecondOrderModel.succ_l a ∧
    ((d = SecondOrderModel.zero_l ℳ ∧ SecondOrderModel.mem_l a P) ∨
      ∃ b, d = SecondOrderModel.succ_l b ∧ SecondOrderPairing.relation_l G a b)

theorem roots_instance_l (K : source_coding_l hℳ) {S I₀ : SecondOrderQuotient.type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hI : ∀ c, mem_l hℳ c I₀ → mem_l hℳ c K.omega) {I : SecondOrderModel.set_l ℳ}
    (hTrace : setRel_l K ⟨I₀, hI⟩ I) (c : SecondOrderModel.num_l ℳ) :
    PowerlessCodedCollectionSyntax.roots_l (𝒩 := 𝒱) K.omega (e_l K) S I₀ (numberCode_l K c).val ↔
      roots_l I c := by
  constructor
  · rintro ⟨i, hi, hiI, hPair⟩
    obtain ⟨i₀, hi₀⟩ := numberCode_surjective_l K ⟨i, hi⟩
    have hi₀' : (numberCode_l K i₀).val = i := congrArg Subtype.val hi₀
    subst i
    have hCode := (PowerlessBoundedNumericPairing.instance_l K hS i₀ _ _).mp hPair
    exact ⟨i₀, (hTrace i₀).mp hiI, numberCode_injective_l K (Subtype.ext hCode.symm)⟩
  · rintro ⟨i, hiI, hPair⟩
    exact ⟨(numberCode_l K i).val, (numberCode_l K i).property, (hTrace i).mpr hiI,
      (PowerlessBoundedNumericPairing.instance_l K hS i _ _).mpr
        (congrArg (fun n => (numberCode_l K n).val) hPair.symm)⟩

theorem tagged_instance_l (K : source_coding_l hℳ) {S U I₀ : SecondOrderQuotient.type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hU : ∀ c, mem_l hℳ c U → mem_l hℳ c K.omega)
    (hI : ∀ c, mem_l hℳ c I₀ → mem_l hℳ c K.omega) {H I : SecondOrderModel.set_l ℳ}
    (hUTrace : setRel_l K ⟨U, hU⟩ H) (hITrace : setRel_l K ⟨I₀, hI⟩ I)
    (c d : SecondOrderModel.num_l ℳ) :
    PowerlessCodedCollectionSyntax.tagged_l (𝒩 := 𝒱) K.omega (e_l K) S U I₀
      (numberCode_l K c).val (numberCode_l K d).val ↔ tagged_l H I c d := by
  constructor
  · rintro ⟨i, hi, a, ha, b, hb, t, _ht, hiI, hC, hD, hT, hRow⟩
    obtain ⟨i₀, hi₀⟩ := numberCode_surjective_l K ⟨i, hi⟩
    obtain ⟨a₀, ha₀⟩ := numberCode_surjective_l K ⟨a, ha⟩
    obtain ⟨b₀, hb₀⟩ := numberCode_surjective_l K ⟨b, hb⟩
    have hi₀' : (numberCode_l K i₀).val = i := congrArg Subtype.val hi₀
    have ha₀' : (numberCode_l K a₀).val = a := congrArg Subtype.val ha₀
    have hb₀' : (numberCode_l K b₀).val = b := congrArg Subtype.val hb₀
    subst i a b
    obtain rfl := (PowerlessBoundedNumericPairing.instance_l K hS a₀ b₀ t).mp hT
    have hC' := (PowerlessBoundedNumericPairing.instance_l K hS i₀ a₀ _).mp hC
    have hD' := (PowerlessBoundedNumericPairing.instance_l K hS i₀ b₀ _).mp hD
    exact ⟨i₀, a₀, b₀, (hITrace i₀).mp hiI,
      numberCode_injective_l K (Subtype.ext hC'.symm), numberCode_injective_l K (Subtype.ext hD'.symm),
      (PowerlessRootedRealSyntax.row_instance_l K hS hU hUTrace _ _).mp hRow⟩
  · rintro ⟨i, a, b, hiI, hC, hD, hRow⟩
    exact ⟨(numberCode_l K i).val, (numberCode_l K i).property,
      (numberCode_l K a).val, (numberCode_l K a).property,
      (numberCode_l K b).val, (numberCode_l K b).property,
      (numberCode_l K (SecondOrderPairing.value_l a b)).val, (numberCode_l K _).property,
      (hITrace i).mpr hiI,
      (PowerlessBoundedNumericPairing.instance_l K hS i a _).mpr
        (congrArg (fun n => (numberCode_l K n).val) hC.symm),
      (PowerlessBoundedNumericPairing.instance_l K hS i b _).mpr
        (congrArg (fun n => (numberCode_l K n).val) hD.symm),
      (PowerlessBoundedNumericPairing.instance_l K hS a b _).mpr rfl,
      (PowerlessRootedRealSyntax.row_instance_l K hS hU hUTrace _ _).mpr hRow⟩

theorem graft_instance_l (K : source_coding_l hℳ) {S G₀ P₀ : SecondOrderQuotient.type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hG : ∀ c, mem_l hℳ c G₀ → mem_l hℳ c K.omega)
    (hP : ∀ c, mem_l hℳ c P₀ → mem_l hℳ c K.omega) {G P : SecondOrderModel.set_l ℳ}
    (hGTrace : setRel_l K ⟨G₀, hG⟩ G) (hPTrace : setRel_l K ⟨P₀, hP⟩ P)
    (c d : SecondOrderModel.num_l ℳ) :
    PowerlessCodedCollectionSyntax.graft_l (𝒩 := 𝒱) K.omega (e_l K) S G₀ P₀
      (numberCode_l K c).val (numberCode_l K d).val ↔ graft_l G P c d := by
  have hEq (n m : SecondOrderModel.num_l ℳ) :
      (numberCode_l K n).val = (numberCode_l K m).val ↔ n = m :=
    ⟨fun h => numberCode_injective_l K (Subtype.ext h), fun h => congrArg (fun j => (numberCode_l K j).val) h⟩
  constructor
  · rintro ⟨a, ha, hSucc, hBody⟩
    obtain ⟨a₀, ha₀⟩ := numberCode_surjective_l K ⟨a, ha⟩
    have ha₀' : (numberCode_l K a₀).val = a := congrArg Subtype.val ha₀
    subst a
    refine ⟨a₀, (hEq c _).mp ((PowerlessNumberSuccessorReading.successor_l K a₀ _).mp hSucc), ?_⟩
    rcases hBody with ⟨hd, haP⟩ | ⟨b, hb, hSuccB, hRow⟩
    · exact Or.inl ⟨(hEq d _).mp hd, (hPTrace a₀).mp haP⟩
    · obtain ⟨b₀, hb₀⟩ := numberCode_surjective_l K ⟨b, hb⟩
      have hb₀' : (numberCode_l K b₀).val = b := congrArg Subtype.val hb₀
      subst b
      exact Or.inr ⟨b₀, (hEq d _).mp ((PowerlessNumberSuccessorReading.successor_l K b₀ _).mp hSuccB),
        (PowerlessRootedRealSyntax.row_instance_l K hS hG hGTrace a₀ b₀).mp hRow⟩
  · rintro ⟨a, rfl, hBody⟩
    refine ⟨(numberCode_l K a).val, (numberCode_l K a).property,
      (PowerlessNumberSuccessorReading.successor_l K a _).mpr rfl, ?_⟩
    rcases hBody with ⟨rfl, haP⟩ | ⟨b, rfl, hRow⟩
    · exact Or.inl ⟨rfl, (hPTrace a).mpr haP⟩
    · exact Or.inr ⟨(numberCode_l K b).val, (numberCode_l K b).property,
        (PowerlessNumberSuccessorReading.successor_l K b _).mpr rfl,
        (PowerlessRootedRealSyntax.row_instance_l K hS hG hGTrace a b).mpr hRow⟩

#print axioms roots_instance_l
#print axioms tagged_instance_l
#print axioms graft_instance_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedCollectionReading
