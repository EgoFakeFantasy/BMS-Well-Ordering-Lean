import BMSConstructibleBridge.PowerlessSourceOpening
import BMSConstructibleBridge.PowerlessRelativeClassFunctionAbsolute

/-! # 不预设完整源理论的有限赋值编码

复用原 SourceTuple 请求和编码关系。其忠实性只需要类内 Kuratowski
有序对坐标唯一性；存在性只需要配对与给定集合的对闭包，不消费
尚待证明的 Separation 或 Collection。所有编码存在量词保留在 Prop。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassTupleCoding

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.type_l PowerlessRelativeClassStructure.structure_l

universe u

theorem bounded_mono_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {A D : carrier_l 𝒩}
    (hAD : ∀ x, member_l 𝒩 x A → member_l 𝒩 x D) (n : Nat)
    (v : Values 𝒩.Carrier (List.replicate n .set)) :
    PowerlessSourceTuple.bounded_l A n v → PowerlessSourceTuple.bounded_l D n v := by
  match n, v with
  | 0, .nil => exact fun _ => trivial
  | n + 1, .cons x v => exact fun h => ⟨hAD x h.1, bounded_mono_l hAD n v h.2⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "CType" => PowerlessRelativeClassStructure.type_l hℳ B

private theorem ordered_exists_l (a b : CType) : ∃ p : CType, ordered_l (ℳ := ClassModel) a b p := by
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ a.val b.val
  let p' : CType := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase a.property b.property hp⟩
  exact ⟨p', (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) a b p').mpr hp⟩

private theorem coordinates_l {a b x z p : CType}
    (h : ordered_l (ℳ := ClassModel) a b p) (hp : ordered_l (ℳ := ClassModel) x z p) : a = x ∧ b = z := by
  have hRaw := (SecondOrderPairObjects.ordered_eq_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) a b p).mp h)
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x z p).mp hp)).mp rfl
  exact ⟨Subtype.ext hRaw.1, Subtype.ext hRaw.2⟩

theorem pair_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Δ))
    (η : Env ClassModel [] Δ) {p x z : CType} (hp : ordered_l (ℳ := ClassModel) x z p) (y : CType) :
    (PowerlessSourcePack.pair_m φ).satisfies ((η.pushFree p).pushFree y) ↔
      φ.satisfies (((η.pushFree z).pushFree x).pushFree y) := by
  rw [PowerlessSourcePack.formula_l]
  constructor
  · rintro ⟨a, b, hab, hφ⟩
    obtain ⟨rfl, rfl⟩ := coordinates_l hab hp
    exact hφ
  · exact fun hφ => ⟨x, z, hp, hφ⟩

theorem code_exists_l (A e : CType) (he : member_l ClassModel e A)
    (hA : ∀ a b p : CType, member_l ClassModel a A → member_l ClassModel b A →
      ordered_l (ℳ := ClassModel) a b p → member_l ClassModel p A)
    (n : Nat) (v : Values (ClassModel).Carrier (List.replicate n .set))
    (hv : PowerlessSourceTuple.bounded_l A n v) :
    ∃ p : CType, member_l ClassModel p A ∧ PowerlessSourceTuple.code_l (ℳ := ClassModel) e n v p := by
  match n, v with
  | 0, .nil => exact ⟨e, he, rfl⟩
  | 1, .cons x .nil => exact ⟨x, hv.1, rfl⟩
  | n + 2, .cons x (.cons z v) =>
    obtain ⟨q, hq⟩ := ordered_exists_l (hBase := hBase) x z
    obtain ⟨p, hp, hCode⟩ := code_exists_l A e he hA (n + 1) (.cons q v)
      ⟨hA x z q hv.1 hv.2.1 hq, hv.2.2⟩
    exact ⟨p, hp, q, hq, hCode⟩

theorem formula_l {Δ : SortContext ℒ} (η : Env ClassModel [] Δ) (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Δ)))
    (v : Values (ClassModel).Carrier (List.replicate n .set)) {e p : CType}
    (hp : PowerlessSourceTuple.code_l (ℳ := ClassModel) e n v p) (y : CType) :
    (PowerlessSourceTuple.form_m n φ).satisfies ((η.pushFree p).pushFree y) ↔
      φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y) := by
  match n, v with
  | 0, .nil => exact PowerlessSourceTuple.empty_formula_l φ η p y
  | 1, .cons x .nil =>
    change p = x at hp
    subst p
    rfl
  | n + 2, .cons x (.cons z v) =>
    obtain ⟨q, hq, hp⟩ := hp
    exact (formula_l η (n + 1) (PowerlessSourcePack.pair_m φ) (.cons q v) hp y).trans
      (pair_l φ (PowerlessSourceTuple.env_l η n v) hq y)

#print axioms code_exists_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassTupleCoding
