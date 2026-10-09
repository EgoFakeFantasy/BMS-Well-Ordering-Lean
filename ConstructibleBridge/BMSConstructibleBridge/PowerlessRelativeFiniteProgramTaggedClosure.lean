import BMSConstructibleBridge.PowerlessRelativeCofinalProgramGraphs
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramTaggedOperator
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramImageClosure

/-! # 同一实际程序像的逐图调用及基础操作闭包

原 Z₂、纯隶属语言。原程序像给有序对及组合算子的真实调用闭包；
标签本身进入 I 时，有序对指令产生 (标签,输入)，组合正文于是读取同一
实际函数图。图只作为 Class 参数，不须属于 I 或 W。输出的 Class 资格
由原图的 W 值域取得，不暗假定 I 传递或包含全部 W。

两种实际基础图因而给无序对及二元并闭包，历史调用图给原历史值的
成员性。这些性质保留同一个 I；调用者还须真正构造可数种子和程序像。
本模块不是最终 hSources 消去，也不把层覆盖或可数性作为既成结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramTaggedClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev Entry (Δ : SortContext ℒ) := Term ℒ [] Δ .set × Term ℒ [] Δ .set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 调用原图不要求原图∈I；只将标签及输入配成一个实际程序输入。 -/
theorem call_l {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ))
    (η : Env 𝒱 [] Δ) {B I x y : Raw} (p : Entry Δ)
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hClass : PowerlessRelativeClassCorrespondence.member_l hℳ B (W.eval η))
    (hBound : ∀ a, mem_l hℳ a I → mem_l hℳ a (W.eval η))
    (hPair : ∀ a b, mem_l hℳ a I → mem_l hℳ b I →
      ∃ s, mem_l hℳ s I ∧ ordered_l (ℳ := 𝒱) a b s)
    (hCall : ∀ s Z : Raw, mem_l hℳ s I → PowerlessRelativeClassCorrespondence.member_l hℳ B Z →
      (PowerlessRelativeFiniteProgramTaggedOperator.relation_m W F).satisfies
        ((η.pushFree s).pushFree Z) → mem_l hℳ Z I)
    (hp : p ∈ F) (hMap : map_l (ℳ := 𝒱) (p.2.eval η) (W.eval η) (W.eval η))
    (hTag : mem_l hℳ (p.1.eval η) I) (hx : mem_l hℳ x I)
    (hValue : value_l (ℳ := 𝒱) (p.2.eval η) x y) : mem_l hℳ y I := by
  obtain ⟨s, hsI, hs⟩ := hPair (p.1.eval η) x hTag hx
  have hyW := (SecondOrderFunctionProperties.value_mem_l hℳ hMap hValue).2
  apply hCall s y hsI (PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hClass hyW)
  exact (PowerlessRelativeFiniteProgramTaggedOperator.relation_formula_l W F η s y).mpr
    ⟨p, hp, x, hBound x hx, hs, hValue⟩

/-- 原像的有序对及调用闭包推出两项真实基础闭包，不以局部模型的判定替代。 -/
theorem basis_l {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ))
    (η : Env 𝒱 [] Δ) {B I : Raw} (p q : Entry Δ)
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hClass : PowerlessRelativeClassCorrespondence.member_l hℳ B (W.eval η))
    (hBound : ∀ a, mem_l hℳ a I → mem_l hℳ a (W.eval η))
    (hPair : ∀ a b, mem_l hℳ a I → mem_l hℳ b I →
      ∃ s, mem_l hℳ s I ∧ ordered_l (ℳ := 𝒱) a b s)
    (hCall : ∀ s Z : Raw, mem_l hℳ s I → PowerlessRelativeClassCorrespondence.member_l hℳ B Z →
      (PowerlessRelativeFiniteProgramTaggedOperator.relation_m W F).satisfies
        ((η.pushFree s).pushFree Z) → mem_l hℳ Z I)
    (hp : p ∈ F) (hq : q ∈ F)
    (hPMap : map_l (ℳ := 𝒱) (p.2.eval η) (W.eval η) (W.eval η))
    (hQMap : map_l (ℳ := 𝒱) (q.2.eval η) (W.eval η) (W.eval η))
    (hPTag : mem_l hℳ (p.1.eval η) I) (hQTag : mem_l hℳ (q.1.eval η) I)
    (hP : ∀ s Z : Raw, mem_l hℳ s (W.eval η) →
      PowerlessRelativeFiniteProgramBasicOperator.call_l (𝒩 := 𝒱) true (W.eval η) s Z →
        value_l (ℳ := 𝒱) (p.2.eval η) s Z)
    (hQ : ∀ s Z : Raw, mem_l hℳ s (W.eval η) →
      PowerlessRelativeFiniteProgramBasicOperator.call_l (𝒩 := 𝒱) false (W.eval η) s Z →
        value_l (ℳ := 𝒱) (q.2.eval η) s Z) :
    PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I := by
  have hBasic (b : Bool) (r : Entry Δ) (hr : r ∈ F)
      (hRMap : map_l (ℳ := 𝒱) (r.2.eval η) (W.eval η) (W.eval η))
      (hRTag : mem_l hℳ (r.1.eval η) I)
      (hRead : ∀ s Z : Raw, mem_l hℳ s (W.eval η) →
        PowerlessRelativeFiniteProgramBasicOperator.call_l (𝒩 := 𝒱) b (W.eval η) s Z →
          value_l (ℳ := 𝒱) (r.2.eval η) s Z) :
      ∀ A C Z : Raw, mem_l hℳ A I → mem_l hℳ C I →
        PowerlessRelativeFiniteProgramBasicOperator.operation_l (𝒩 := 𝒱) b A C Z → mem_l hℳ Z I := by
    intro A C Z hA hC hZ
    obtain ⟨s, hsI, hs⟩ := hPair A C hA hC
    apply call_l W F η r hBase hClass hBound hPair hCall hr hRMap hRTag hsI
    exact hRead s Z (hBound s hsI) ⟨A, C, hBound A hA, hBound C hC, hs, hZ⟩
  exact ⟨hBasic true p hp hPMap hPTag hP, hBasic false q hq hQMap hQTag hQ⟩

/-- 总化图保持原历史值，因此同一像也闭合于原历史调用。 -/
theorem history_l {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ))
    (η : Env 𝒱 [] Δ) {B I H : Raw} (p : Entry Δ)
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hClass : PowerlessRelativeClassCorrespondence.member_l hℳ B (W.eval η))
    (hBound : ∀ a, mem_l hℳ a I → mem_l hℳ a (W.eval η))
    (hPair : ∀ a b, mem_l hℳ a I → mem_l hℳ b I →
      ∃ s, mem_l hℳ s I ∧ ordered_l (ℳ := 𝒱) a b s)
    (hCall : ∀ s Z : Raw, mem_l hℳ s I → PowerlessRelativeClassCorrespondence.member_l hℳ B Z →
      (PowerlessRelativeFiniteProgramTaggedOperator.relation_m W F).satisfies
        ((η.pushFree s).pushFree Z) → mem_l hℳ Z I)
    (hp : p ∈ F) (hMap : map_l (ℳ := 𝒱) (p.2.eval η) (W.eval η) (W.eval η))
    (hTag : mem_l hℳ (p.1.eval η) I)
    (hRead : ∀ a A : Raw, mem_l hℳ a (W.eval η) →
      value_l (ℳ := 𝒱) H a A → value_l (ℳ := 𝒱) (p.2.eval η) a A) :
    ∀ a A : Raw, mem_l hℳ a I → value_l (ℳ := 𝒱) H a A → mem_l hℳ A I := by
  intro a A ha hA
  exact call_l W F η p hBase hClass hBound hPair hCall hp hMap hTag ha
    (hRead a A (hBound a ha) hA)

#print axioms call_l
#print axioms basis_l
#print axioms history_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramTaggedClosure
