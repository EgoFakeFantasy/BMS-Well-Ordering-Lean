import BMSConstructibleBridge.PowerlessAssignmentUpdate
import BMSConstructibleBridge.PowerlessMapBounded
import BMSConstructibleBridge.SecondOrderFunctionProperties
import BMSConstructibleBridge.SecondOrderAxioms

/-! # 有限赋值单变量更新的纯 Δ₀ 检查

检查只量化给定定义域与陪域。与全对象更新关系的等价显式要求两张图
同域映射、变量属于定义域及新值属于陪域；不能把这些 guard 删掉。
原商坐标唯一性排除域外图值，完整条件式回传原 Z₂ 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentUpdateBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (n A f i a g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  membershipLevyBound.boundedForall n <| membershipLevyBound.boundedForall (up A) <|
    .iff (PowerlessValueBounded.formula_m (w g) (.bvar (.there .here)) (.bvar .here))
      (.disj (.conj (.equal (.bvar (.there .here)) (w i)) (.equal (.bvar .here) (w a)))
        (.conj (.neg (.equal (.bvar (.there .here)) (w i)))
          (PowerlessValueBounded.formula_m (w f) (.bvar (.there .here)) (.bvar .here))))

theorem delta_l {Γ Δ : SortContext ℒ} (n A f i a g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m n A f i a g) :=
  .bounded_forall n (.bounded_forall (up A) (.iff (PowerlessValueBounded.delta_l _ _ _)
    (.disj (.conj (.equal _ _) (.equal _ _))
      (.conj (.neg (.equal _ _)) (PowerlessValueBounded.delta_l _ _ _)))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (n A f i a g : carrier_l 𝒩) : Prop :=
  ∀ x, member_l 𝒩 x n → ∀ y, member_l 𝒩 y A →
    (value_l (ℳ := 𝒩) g x y ↔ (x = i ∧ y = a) ∨ (x ≠ i ∧ value_l (ℳ := 𝒩) f x y))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (n A f i a g : Term ℒ Γ Δ .set) :
    (formula_m n A f i a g).satisfies η ↔
      holds_l (n.eval η) (A.eval η) (f.eval η) (i.eval η) (a.eval η) (g.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem update_iff_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {n A f i a g : type_l hℳ}
    (hf : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f n A)
    (hg : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) g n A)
    (hi : mem_l hℳ i n) (ha : mem_l hℳ a A) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) n A f i a g ↔
      PowerlessAssignmentUpdate.update_l (ℳ := SecondOrderQuotient.structure_l hℳ) f i a g := by
  constructor
  · intro h x y
    constructor
    · intro hValue
      have hxy := SecondOrderFunctionProperties.value_mem_l hℳ hg hValue
      exact (h x hxy.1 y hxy.2).mp hValue
    · intro hValue
      have hxy : mem_l hℳ x n ∧ mem_l hℳ y A := by
        rcases hValue with ⟨rfl, rfl⟩ | ⟨_, hValue⟩
        · exact ⟨hi, ha⟩
        · exact SecondOrderFunctionProperties.value_mem_l hℳ hf hValue
      exact (h x hxy.1 y hxy.2).mpr hValue
  · intro h x _ y _
    exact h x y

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  let n : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let A : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let f : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let i : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let g : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  .imp (SecondOrderObjectSyntax.map_m f n A) <| .imp (SecondOrderObjectSyntax.map_m g n A) <|
    .imp (SecondOrderObjectSyntax.member_m i n) <| .imp (SecondOrderObjectSyntax.member_m a A) <|
      .iff (formula_m n A f i a g) (PowerlessAssignmentUpdate.update_m f i a g)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hf hg hi ha
  have hf' := (map_formula_l η _ _ _).mp hf
  have hg' := (map_formula_l η _ _ _).mp hg
  exact (formula_l η _ _ _ _ _ _).trans
    ((update_iff_l hℳ hf' hg' hi ha).trans (PowerlessAssignmentUpdate.update_formula_l η _ _ _ _).symm)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentUpdateBounded
