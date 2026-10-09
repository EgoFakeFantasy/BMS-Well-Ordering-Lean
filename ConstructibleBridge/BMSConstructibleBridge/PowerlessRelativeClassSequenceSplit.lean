import BMSConstructibleBridge.PowerlessRelativeClassSequenceSlices
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRestriction

/-! # 内部后继长度序列的前缀与末项

限制图、末项和有序对均为实际相对类对象。后继只使用明确的成员分解，
不要求外部标准长度、母集枚举、Collection 或宿主层选择函数。
本模块提供语义辅助接口；对象公式与正式推导由调用方另行封装。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceSplit

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

def prefix_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (n X f g : carrier_l ℳ₀) : Prop :=
  ∀ i, member_l ℳ₀ i n → ∀ x, member_l ℳ₀ x X → (value_l g i x ↔ value_l f i x)

def split_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (n X P f p : carrier_l ℳ₀) : Prop :=
  ∃ g a, member_l ℳ₀ g P ∧ member_l ℳ₀ a X ∧ ordered_l g a p ∧
    prefix_l n X f g ∧ value_l f n a

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

private theorem prefix_unique_l {n X f g g' : type_l hℳ B}
    (hg : map_l (ℳ := ClassModel) g n X) (hg' : map_l (ℳ := ClassModel) g' n X)
    (hp : prefix_l (ℳ₀ := ClassModel) n X f g)
    (hp' : prefix_l (ℳ₀ := ClassModel) n X f g') : g = g' := by
  apply PowerlessRelativeClassFunctionRestriction.ext_l hg hg'
  intro i x
  constructor
  · intro hix
    have hmem := PowerlessRelativeClassFunctionProperties.value_mem_l hg hix
    exact (hp' i hmem.1 x hmem.2).mpr ((hp i hmem.1 x hmem.2).mp hix)
  · intro hix
    have hmem := PowerlessRelativeClassFunctionProperties.value_mem_l hg' hix
    exact (hp i hmem.1 x hmem.2).mpr ((hp' i hmem.1 x hmem.2).mp hix)

theorem exists_unique_l {n m X P f : type_l hℳ B}
    (hf : map_l (ℳ := ClassModel) f m X)
    (hSucc : ∀ i : type_l hℳ B, member_l ClassModel i m ↔ member_l ClassModel i n ∨ i = n)
    (hP : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := ClassModel) n X P) :
    ∃! p : type_l hℳ B, split_l (ℳ₀ := ClassModel) n X P f p := by
  have hSub : subset_l (ℳ := ClassModel) n m := fun i hi => (hSucc i).mpr (Or.inl hi)
  obtain ⟨g, hg, hRead⟩ := PowerlessRelativeClassFunctionRestriction.exists_l hf hSub
  have hPrefix : prefix_l (ℳ₀ := ClassModel) n X f g := by
    intro i hi x _
    exact ⟨fun hx => ((hRead i x).mp hx).2, fun hx => (hRead i x).mpr ⟨hi, hx⟩⟩
  obtain ⟨a, ⟨ha, hna⟩, _⟩ := hf.2 n ((hSucc n).mpr (Or.inr rfl))
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ g.val a.val
  let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase g.property a.property hp⟩
  have hPair : ordered_l (ℳ := ClassModel) g a p' :=
    (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) g a p').mpr hp
  refine ⟨p', ⟨g, a, (hP g).mpr hg, ha, hPair, hPrefix, hna⟩, ?_⟩
  intro q hq
  obtain ⟨k, b, hk, _, hPair', hPrefix', hnb⟩ := hq
  have hkg : k = g := prefix_unique_l ((hP k).mp hk) hg hPrefix' hPrefix
  have hba : b = a := PowerlessRelativeClassFunctionProperties.value_unique_l hf hnb hna
  subst k
  subst b
  exact Subtype.ext (SecondOrderPairObjects.ordered_unique_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) g a q).mp hPair') hp)

theorem injective_l {n m X P f f' p : type_l hℳ B}
    (hf : map_l (ℳ := ClassModel) f m X) (hf' : map_l (ℳ := ClassModel) f' m X)
    (hSucc : ∀ i : type_l hℳ B, member_l ClassModel i m ↔ member_l ClassModel i n ∨ i = n)
    (hP : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := ClassModel) n X P)
    (hp : split_l (ℳ₀ := ClassModel) n X P f p)
    (hp' : split_l (ℳ₀ := ClassModel) n X P f' p) : f = f' := by
  obtain ⟨g, a, hg, _, hPair, hPrefix, hLast⟩ := hp
  obtain ⟨g', a', _, _, hPair', hPrefix', hLast'⟩ := hp'
  have hEq := (SecondOrderPairObjects.ordered_eq_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) g a p).mp hPair)
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) g' a' p).mp hPair')).mp rfl
  have hgg : g = g' := Subtype.ext hEq.1
  have haa : a = a' := Subtype.ext hEq.2
  subst g'
  subst a'
  have hgMap := (hP g).mp hg
  have hForward {f₀ f₁ : type_l hℳ B} (h₀ : map_l (ℳ := ClassModel) f₀ m X)
      (hp₀ : prefix_l (ℳ₀ := ClassModel) n X f₀ g)
      (hp₁ : prefix_l (ℳ₀ := ClassModel) n X f₁ g)
      (hl₀ : value_l (ℳ := ClassModel) f₀ n a) (hl₁ : value_l (ℳ := ClassModel) f₁ n a) :
      ∀ i x : type_l hℳ B, value_l (ℳ := ClassModel) f₀ i x → value_l (ℳ := ClassModel) f₁ i x := by
    intro i x hix
    have hmem := PowerlessRelativeClassFunctionProperties.value_mem_l h₀ hix
    rcases (hSucc i).mp hmem.1 with hi | hi
    · have hgix := (hp₀ i hi x hmem.2).mpr hix
      have hgmem := PowerlessRelativeClassFunctionProperties.value_mem_l hgMap hgix
      exact (hp₁ i hgmem.1 x hgmem.2).mp hgix
    · subst i
      have hxa := PowerlessRelativeClassFunctionProperties.value_unique_l h₀ hix hl₀
      exact hxa.symm ▸ hl₁
  apply PowerlessRelativeClassFunctionRestriction.ext_l hf hf'
  exact fun i x => ⟨hForward hf hPrefix hPrefix' hLast hLast' i x,
    hForward hf' hPrefix' hPrefix hLast' hLast i x⟩

#print axioms exists_unique_l
#print axioms injective_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceSplit
