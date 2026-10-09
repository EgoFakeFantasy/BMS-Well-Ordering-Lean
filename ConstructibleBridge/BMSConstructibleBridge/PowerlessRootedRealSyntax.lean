import BMSConstructibleBridge.PowerlessBoundedNumericPairing
import BMSConstructibleBridge.PowerlessBMSQuotientReals

/-! # 带根实数码的纯语言读取公式

两次实际数配对分别读取标记行与原图边；所有中间数以同一 ω 为界。
语义对应覆盖任意内部自然数，不假定配数满射或模型外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRootedRealSyntax

open Logic FirstOrder StabilityFrame ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def row_m {Γ Δ : SortContext ℒ} (ω e S V a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up ω) (up e) (up S) (up a) (up b) (.bvar .here))
    (member_m (.bvar .here) (up V))

theorem row_delta_m {Γ Δ : SortContext ℒ} (ω e S V a b : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (row_m ω e S V a b) :=
  .bounded_exists _ (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _) (.rel _ _))

def row_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S V a b : carrier_l 𝒩) : Prop :=
  ∃ c, member_l 𝒩 c ω ∧ PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e S a b c ∧ member_l 𝒩 c V

theorem row_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S V a b : Term ℒ Γ Δ .set) :
    (row_m ω e S V a b).satisfies η ↔ row_l (ω.eval η) (e.eval η) (S.eval η) (V.eval η) (a.eval η) (b.eval η) := by
  simp only [row_m, row_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def edge_m {Γ Δ : SortContext ℒ} (ω e S V a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up ω) (up e) (up S) (up a) (up b) (.bvar .here))
    (row_m (up ω) (up e) (up S) (up V) (up e) (.bvar .here))

theorem edge_delta_m {Γ Δ : SortContext ℒ} (ω e S V a b : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (edge_m ω e S V a b) :=
  .bounded_exists _ (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _) (row_delta_m _ _ _ _ _ _))

def edge_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S V a b : carrier_l 𝒩) : Prop :=
  ∃ c, member_l 𝒩 c ω ∧ PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e S a b c ∧ row_l ω e S V e c

theorem edge_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S V a b : Term ℒ Γ Δ .set) :
    (edge_m ω e S V a b).satisfies η ↔ edge_l (ω.eval η) (e.eval η) (S.eval η) (V.eval η) (a.eval η) (b.eval η) := by
  simp only [edge_m, edge_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    row_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem row_instance_l (K : source_coding_l hℳ) {S V : SecondOrderQuotient.type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hV : ∀ c, mem_l hℳ c V → mem_l hℳ c K.omega) {F : SecondOrderModel.set_l ℳ}
    (hTrace : setRel_l K ⟨V, hV⟩ F) (n m : SecondOrderModel.num_l ℳ) :
    row_l (𝒩 := 𝒱) K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S V
      (numberCode_l K n).val (numberCode_l K m).val ↔ SecondOrderPairing.relation_l F n m := by
  constructor
  · rintro ⟨c, _, hPair, hcV⟩
    obtain rfl := (PowerlessBoundedNumericPairing.instance_l K hS n m c).mp hPair
    exact (hTrace (SecondOrderPairing.value_l n m)).mp hcV
  · intro hEdge
    exact ⟨(numberCode_l K (SecondOrderPairing.value_l n m)).val,
      (numberCode_l K (SecondOrderPairing.value_l n m)).property,
      (PowerlessBoundedNumericPairing.instance_l K hS n m _).mpr rfl,
      (hTrace (SecondOrderPairing.value_l n m)).mpr hEdge⟩

theorem edge_instance_l (K : source_coding_l hℳ) {S V : SecondOrderQuotient.type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hV : ∀ c, mem_l hℳ c V → mem_l hℳ c K.omega) {F : SecondOrderModel.set_l ℳ}
    (hTrace : setRel_l K ⟨V, hV⟩ F) (n m : SecondOrderModel.num_l ℳ) :
    edge_l (𝒩 := 𝒱) K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S V
      (numberCode_l K n).val (numberCode_l K m).val ↔
        SecondOrderPairing.relation_l F (SecondOrderModel.zero_l ℳ) (SecondOrderPairing.value_l n m) := by
  constructor
  · rintro ⟨c, _, hPair, hRow⟩
    obtain rfl := (PowerlessBoundedNumericPairing.instance_l K hS n m c).mp hPair
    exact (row_instance_l K hS hV hTrace _ _).mp hRow
  · intro hRow
    exact ⟨(numberCode_l K (SecondOrderPairing.value_l n m)).val,
      (numberCode_l K (SecondOrderPairing.value_l n m)).property,
      (PowerlessBoundedNumericPairing.instance_l K hS n m _).mpr rfl,
      (row_instance_l K hS hV hTrace _ _).mpr hRow⟩

#print axioms row_delta_m
#print axioms edge_delta_m
#print axioms row_instance_l
#print axioms edge_instance_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRootedRealSyntax
