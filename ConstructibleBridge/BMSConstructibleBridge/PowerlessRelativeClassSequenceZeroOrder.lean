import BMSConstructibleBridge.PowerlessRelativeClassSequenceSlices
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRestriction
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationWellOrder

/-! # 内部零长度序列的良序基例

空定义域上的集合函数由图外延性唯一。因而精确定长切片在空关系下良序；
空长度对象本身可作该关系，不选择新的序关系或函数。正式出口仍为原 Z₂
中的守卫化对象推导，供后续实际内部长度归纳使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceZeroOrder

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem unique_l {n X f g : type_l hℳ B}
    (hn : ∀ i, ¬member_l ClassModel i n)
    (hf : map_l (ℳ := ClassModel) f n X) (hg : map_l (ℳ := ClassModel) g n X) : f = g := by
  apply PowerlessRelativeClassFunctionRestriction.ext_l hf hg
  intro i x
  exact iff_of_false
    (fun h => hn i (PowerlessRelativeClassFunctionProperties.value_mem_l hf h).1)
    (fun h => hn i (PowerlessRelativeClassFunctionProperties.value_mem_l hg h).1)

theorem wellOrder_l {n X P : type_l hℳ B}
    (hn : ∀ i, ¬member_l ClassModel i n)
    (hP : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := ClassModel) n X P) :
    ThirdOrderSemantics.wellOrder_l (ℳ := ClassModel) P n := by
  have hNoValue (f g : type_l hℳ B) : ¬value_l (ℳ := ClassModel) n f g := by
    rintro ⟨p, hp, _⟩
    exact hn p hp
  refine ⟨fun f _ => hNoValue f f, ?_, ?_, ?_⟩
  · intro f g k _ hfg _
    exact (hNoValue f g hfg).elim
  · intro f g hfg
    exact Or.inr (Or.inl (unique_l hn ((hP f).mp hfg.1) ((hP g).mp hfg.2)))
  · intro U hU
    obtain ⟨f, hf⟩ := hU.2
    exact ⟨f, hf, fun g _ => hNoValue g f⟩

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let n : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let X : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let P : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  .imp (PowerlessRelativeHierarchySyntax.empty_m n) <|
    .imp (PowerlessRelativeClassSequenceSlices.spec_m n X P)
      (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m P n)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, PowerlessRelativeHierarchySyntax.empty_m, Formula.satisfies,
    PowerlessRelativeClassSequenceSlices.spec_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  exact fun hn hP => wellOrder_l (hBase := hBase) hn hP

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m
    (fun _ hℳ B hBase => models_l hℳ B hBase)

#print axioms unique_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceZeroOrder
