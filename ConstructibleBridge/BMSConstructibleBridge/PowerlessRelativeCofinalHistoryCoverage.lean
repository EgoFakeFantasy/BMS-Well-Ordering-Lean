import BMSConstructibleBridge.PowerlessRelativeCofinalMemberDefRows
import BMSConstructibleBridge.PowerlessRelativeHierarchyAgreement

/-! # 同一原层历史的内部覆盖归纳

对象语言为纯隶属 ℒ，背景为原 Z₂。point 公式只量化实际历史图的值及
其全部成员；集合归纳来自原 WeakSetInduction，不使用外部序数良基性。
零步读取原基底覆盖，后继步消费同一 Sat 行算子，极限步读取原历史的并。

历史和行图的调用闭包、无序对及二元并闭包仍是实际操作接口；调用者须
在同一个可数程序像上证明这些闭包，不能把本模块当作低层可数性终局。
这里没有预供实际层的成员覆盖；每个层的全部成员由内部归纳取得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalHistoryCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def point_m {Γ Δ : SortContext ℒ} (H I a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.value_m (up H) (up a) (.bvar .here))
    (ThirdOrderTheory.subset_m (.bvar .here) (up I))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def point_l (H I a : Raw) : Prop :=
  ∀ A, SecondOrderFunctionObjects.value_l hℳ H a A →
    ∀ x, mem_l hℳ x A → mem_l hℳ x I

theorem point_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (H I a : Term ℒ Γ Δ .set) :
    (point_m H I a).satisfies η ↔ point_l (H.eval η) (I.eval η) (a.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, SecondOrderObjectSyntax.value_l hℳ,
    ThirdOrderSemantics.subset_formula_l, up, Term.eval_weakenBound]
  rfl

/-- 后继覆盖来自真实原 Def 行；历史的输出对象由实际历史调用取得。 -/
theorem step_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {β W α H I F a : Raw}
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hωW : mem_l hℳ ω.val W)
    (hHistory : PowerlessRelativeHierarchySemantics.history_l hℳ B α H W)
    (hBI : ∀ x, mem_l hℳ x B → mem_l hℳ x I)
    (hαI : ∀ x, mem_l hℳ x α → mem_l hℳ x I)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (hI : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I)
    (hF : ∀ s Z : Raw, value_l (ℳ := 𝒱) F s Z ↔ mem_l hℳ s W ∧ mem_l hℳ Z W ∧
      PowerlessRelativeLimitSatisfactionRowOperator.total_l (𝒩 := 𝒱) ω.val W G.val e.val s Z)
    (hCall : ∀ s Z : Raw, mem_l hℳ s I → value_l (ℳ := 𝒱) F s Z → mem_l hℳ Z I)
    (hGetter : ∀ b A : Raw, mem_l hℳ b I →
      SecondOrderFunctionObjects.value_l hℳ H b A → mem_l hℳ A I)
    (hPast : ∀ b, mem_l hℳ b a → point_l H I b) : point_l H I a := by
  intro A hA
  have ha := (SecondOrderFunctionProperties.value_mem_l hℳ hHistory.1 hA).1
  rcases hHistory.2 a A ⟨ha, hA⟩ with
    ⟨_hZero, hAB⟩ | ⟨b, C, hSucc, hC, hDef⟩ | ⟨_hLimitA, hUnion⟩
  · exact hAB.symm ▸ hBI
  · have hb := PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc
    have hBound := SecondOrderFunctionProperties.value_mem_l hℳ hHistory.1 hC
    exact PowerlessRelativeCofinalMemberDefRows.subset_l hBase K hLimit hW
      ω e t₁ t₂ t₃ Pair N Valid Translation G hCode hωW hBound.2 hDef
      hωI hI (hPast b hb C hC) (hGetter b C (hαI b hBound.1) hC) hF hCall
  · intro x hx
    obtain ⟨b, C, hb, hC, hxC⟩ := (hUnion x).mp hx
    exact hPast b hb C hC x hxC

/-- 同一纯 point 公式的原内部归纳覆盖全部历史输出。 -/
theorem subset_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {β W α H I F : Raw}
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hωW : mem_l hℳ ω.val W)
    (hHistory : PowerlessRelativeHierarchySemantics.history_l hℳ B α H W)
    (hBI : ∀ x, mem_l hℳ x B → mem_l hℳ x I)
    (hαI : ∀ x, mem_l hℳ x α → mem_l hℳ x I)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (hI : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I)
    (hF : ∀ s Z : Raw, value_l (ℳ := 𝒱) F s Z ↔ mem_l hℳ s W ∧ mem_l hℳ Z W ∧
      PowerlessRelativeLimitSatisfactionRowOperator.total_l (𝒩 := 𝒱) ω.val W G.val e.val s Z)
    (hCall : ∀ s Z : Raw, mem_l hℳ s I → value_l (ℳ := 𝒱) F s Z → mem_l hℳ Z I)
    (hGetter : ∀ b A : Raw, mem_l hℳ b I →
      SecondOrderFunctionObjects.value_l hℳ H b A → mem_l hℳ A I) :
    ∀ a, point_l H I a := by
  let η : Env 𝒱 [] [.set, .set] := Env.empty (M := 𝒱) |>.pushFree H |>.pushFree I
  let φ : Formula ℒ [] [.set, .set, .set] :=
    point_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  have hFormula (a : Raw) : φ.satisfies (η.pushFree a) ↔ point_l H I a :=
    point_formula_l (η.pushFree a) _ _ _
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ) φ η
    (fun a ih => (hFormula a).mpr (step_l hBase K hLimit hW
      ω e t₁ t₂ t₃ Pair N Valid Translation G hCode hωW hHistory hBI hαI hωI hI hF hCall hGetter
      (fun b hb => (hFormula b).mp (ih b hb))))
  exact fun a => (hFormula a).mp (hAll a)

/-- 任意原层见证与同一实际历史的值相等，故接收相同覆盖而不重选层。 -/
theorem level_l {α H W I a A : Raw}
    (hα : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α)
    (hHistory : PowerlessRelativeHierarchySemantics.history_l hℳ B α H W)
    (hCover : ∀ b, point_l H I b) (ha : mem_l hℳ a α)
    (hA : PowerlessRelativeHierarchySemantics.level_l hℳ B a A) :
    ∀ x, mem_l hℳ x A → mem_l hℳ x I := by
  obtain ⟨C, ⟨_hCW, hC⟩, _hUnique⟩ := hHistory.1.2 a ha
  have hEq := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hA
    ⟨α, H, W, hα, ha, hHistory, hC⟩
  exact hEq.symm ▸ hCover a C hC

#print axioms point_formula_l
#print axioms subset_l
#print axioms level_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalHistoryCoverage
