import BMSConstructibleBridge.PowerlessRelativeFiniteProgramGraphOperator
import BMSConstructibleBridge.PowerlessRelativeFiniteHullAssignments

/-! # 无序对及二元并的真实有界程序算子

程序原生配对指令只构造有序对，不能据此宣称无序对或二元并闭包。
本模块将 (A,B) 编码为一个输入，输出实际 {A,B} 或 A∪B；两种正文
都是纯 Δ₀ 公式，任意 raw 输出唯一，并由实际非零极限层的闭包保层。
这里的 Bool 只索引两个外部公式实例，不模拟对象自然数或内部递归。

这些是可供标签组合及程序像闭包消费的真实算子。尚未装配同一可数
程序像，也不能仅凭算子单值、保层宣称低层可数性或最终 BMS 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBasicOperator

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev free₂ {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) :=
  (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set

def binary_m {Γ Δ : SortContext ℒ} (A B C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (membershipLevyBound.boundedForall A (SecondOrderObjectSyntax.member_m (.bvar .here) (up C))) <|
    .conj (membershipLevyBound.boundedForall B (SecondOrderObjectSyntax.member_m (.bvar .here) (up C)))
      (membershipLevyBound.boundedForall C (.disj
        (SecondOrderObjectSyntax.member_m (.bvar .here) (up A))
        (SecondOrderObjectSyntax.member_m (.bvar .here) (up B))))

theorem binary_delta_l {Γ Δ : SortContext ℒ} (A B C : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (binary_m A B C) :=
  .conj (.bounded_forall _ (.rel _ _))
    (.conj (.bounded_forall _ (.rel _ _)) (.bounded_forall _ (.disj (.rel _ _) (.rel _ _))))

theorem binary_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (A B C : Term ℒ Γ Δ .set) :
    (binary_m A B C).satisfies η ↔
      PowerlessRelativeFiniteHullAssignments.binary_l (A.eval η) (B.eval η) (C.eval η) := by
  simp only [binary_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  constructor
  · rintro ⟨hA, hB, hC⟩ x
    exact ⟨hC x, fun h => h.elim (hA x) (hB x)⟩
  · intro h
    exact ⟨fun x hx => (h x).mpr (Or.inl hx), fun x hx => (h x).mpr (Or.inr hx),
      fun x hx => (h x).mp hx⟩

def operation_m {Γ Δ : SortContext ℒ} (b : Bool) (A B C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  if b then PowerlessPairBounded.pair_m A B C else binary_m A B C

def operation_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (b : Bool)
    (A B C : carrier_l 𝒩) : Prop :=
  if b then pair_l A B C else PowerlessRelativeFiniteHullAssignments.binary_l A B C

theorem operation_delta_l {Γ Δ : SortContext ℒ} (b : Bool) (A B C : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (operation_m b A B C) := by
  cases b
  · exact binary_delta_l _ _ _
  · exact PowerlessPairBounded.pair_delta_l _ _ _

theorem operation_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (b : Bool) (η : Env 𝒩 Γ Δ) (A B C : Term ℒ Γ Δ .set) :
    (operation_m b A B C).satisfies η ↔ operation_l b (A.eval η) (B.eval η) (C.eval η) := by
  cases b
  · exact binary_formula_l η _ _ _
  · exact PowerlessPairBounded.pair_formula_l η _ _ _

def call_m {Γ Δ : SortContext ℒ} (b : Bool) (W s Z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists W <| membershipLevyBound.boundedExists (up W) <|
    .conj (PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (up (up s)))
      (operation_m b (.bvar (.there .here)) (.bvar .here) (up (up Z)))

def call_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (b : Bool) (W s Z : carrier_l 𝒩) : Prop :=
  ∃ A B, member_l 𝒩 A W ∧ member_l 𝒩 B W ∧ ordered_l A B s ∧ operation_l b A B Z

theorem call_delta_l {Γ Δ : SortContext ℒ} (b : Bool) (W s Z : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (call_m b W s Z) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
    (operation_delta_l b _ _ _)))

theorem call_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (b : Bool) (η : Env 𝒩 Γ Δ) (W s Z : Term ℒ Γ Δ .set) :
    (call_m b W s Z).satisfies η ↔ call_l b (W.eval η) (s.eval η) (Z.eval η) := by
  simp only [call_m, call_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
    operation_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  constructor
  · rintro ⟨A, hA, B, hB, hs, hZ⟩; exact ⟨A, B, hA, hB, hs, hZ⟩
  · rintro ⟨A, B, hA, hB, hs, hZ⟩; exact ⟨A, hA, B, hB, hs, hZ⟩

def relation_m {Δ : SortContext ℒ} (b : Bool) (W : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  call_m b (free₂ W) (.fvar (.there .here)) (.fvar .here)

theorem delta_l {Δ : SortContext ℒ} (b : Bool) (W : Term ℒ [] Δ .set) :
    Formula.IsDelta0 membershipLevyBound (relation_m b W) := call_delta_l b _ _ _

theorem relation_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (b : Bool) (W : Term ℒ [] Δ .set) (η : Env 𝒩 [] Δ) (s Z : carrier_l 𝒩) :
    (relation_m b W).satisfies ((η.pushFree s).pushFree Z) ↔ call_l b (W.eval η) s Z := by
  simpa only [relation_m, free₂, Term.eval_weakenFree, Term.eval,
    Env.pushFree_here, Env.pushFree_there] using
      call_formula_l b ((η.pushFree s).pushFree Z) (free₂ W)
        (.fvar (.there .here)) (.fvar .here)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => type_l hℳ

theorem unique_l (b : Bool) {W s Y Z : Raw}
    (hY : call_l (𝒩 := 𝒱) b W s Y) (hZ : call_l (𝒩 := 𝒱) b W s Z) : Y = Z := by
  obtain ⟨A, B, _hAW, _hBW, hs, hY⟩ := hY
  obtain ⟨C, D, _hCW, _hDW, hs', hZ⟩ := hZ
  obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hs hs').mp rfl
  cases b
  · exact SecondOrderQuotient.ext_l hℳ _ _ (fun x => (hY x).trans (hZ x).symm)
  · exact SecondOrderPairObjects.pair_unique_l hℳ hY hZ

/-- 二元并先作为实际无序对的并集保层，不使用 W 的完整分离。 -/
theorem member_l (b : Bool) {B β W s Z : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (hZ : call_l (𝒩 := 𝒱) b W s Z) : mem_l hℳ Z W := by
  obtain ⟨A, C, hAW, hCW, _hs, hZ⟩ := hZ
  cases b
  · obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ A C
    apply PowerlessRelativeLimitClosure.union_l hℳ hBase hLimit hW
      (PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hW hAW hCW hP)
    intro x
    refine (hZ x).trans ⟨?_, ?_⟩
    · rintro (hx | hx)
      · exact ⟨A, (hP A).mpr (Or.inl rfl), hx⟩
      · exact ⟨C, (hP C).mpr (Or.inr rfl), hx⟩
    · rintro ⟨Y, hYP, hx⟩
      rcases (hP Y).mp hYP with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
  · exact PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hW hAW hCW hZ

theorem functional_l {Δ : SortContext ℒ} (b : Bool) (W : Term ℒ [] Δ .set)
    (η : Env 𝒱 [] Δ) {B : Raw} :
    PowerlessRelativeFiniteProgramInstruction.functional_l (relation_m b W) η B := by
  intro s Y Z _ _ _ hY hZ
  exact unique_l b ((relation_formula_l b W η s Y).mp hY)
    ((relation_formula_l b W η s Z).mp hZ)

theorem closed_l {Δ : SortContext ℒ} (b : Bool) (W : Term ℒ [] Δ .set)
    (η : Env 𝒱 [] Δ) {B β : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β (W.eval η)) :
    PowerlessRelativeFiniteProgramLimitStep.closed_l (relation_m b W) η B (W.eval η) := by
  intro s Z _ _ hZ
  exact member_l b hBase hLimit hW ((relation_formula_l b W η s Z).mp hZ)

def schema_m {Δ : SortContext ℒ} (b : Bool) (B β W : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .conj (PowerlessRelativeFiniteProgramInstruction.functional_m (relation_m b W) B)
          (PowerlessRelativeFiniteProgramLimitStep.closed_m (relation_m b W) B W)

def sentence_m {Δ : SortContext ℒ} (b : Bool) (B β W : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m b B β W)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (b : Bool) (B β W : Term ℒ [] Δ .set) :
    (sentence_m b B β W).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeFiniteProgramInstruction.functional_formula_l K,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K,
    PowerlessBMSQuotientSubsetImageDerives.parameters_empty_l]
  intro η hBase hLimit hW
  exact ⟨functional_l b W η, closed_l b W η hBase hLimit hW⟩

theorem derives_m {Δ : SortContext ℒ} (b : Bool) (B β W : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m b B β W)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 b B β W)

#print axioms delta_l
#print axioms unique_l
#print axioms member_l
#print axioms functional_l
#print axioms closed_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBasicOperator
