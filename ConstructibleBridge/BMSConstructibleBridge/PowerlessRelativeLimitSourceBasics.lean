import BMSConstructibleBridge.PowerlessRelativeLimitClosure
import BMSConstructibleBridge.PowerlessRelativeParameters
import BMSConstructibleBridge.SecondOrderInfinityAxiom

/-! # 实际极限层成员子模型的六条基础公理

复用既有成员子模型与原公式相对化，不另造载体或满足关系。
层内的实际 ω 提供非空性与无穷见证；传递性处理外延、正则与
成员提升，极限层封闭性处理配对和并集。完整分离与 Collection
不在本文件的结论内；原闭句显式保留层值和 ω 的全部守卫。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSourceBasics

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β C ω : SecondOrderQuotient.type_l hℳ}
  (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
  (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
  (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
  (hω : SecondOrderOmega.omega_l hℳ ω) (hωC : mem_l hℳ ω C)

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "LevelModel" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) C (Exists.intro ω hωC)
local notation "CType" => PowerlessMemberStructure.type_l (ℳ := 𝒱) C

include hBase hC in
theorem extensionality_l : SecondOrderAxioms.extensionality_m.TrueIn LevelModel := by
  change ∀ a b : CType, (∀ z : CType, mem_l hℳ z.val a.val ↔ mem_l hℳ z.val b.val) → a = b
  intro a b hab
  apply Subtype.ext
  apply SecondOrderQuotient.ext_l hℳ
  intro z
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  exact ⟨fun hz => (hab ⟨z, hTrans a.val a.property z hz⟩).mp hz,
    fun hz => (hab ⟨z, hTrans b.val b.property z hz⟩).mpr hz⟩

include hBase hC hω in
theorem empty_l : SecondOrderAxioms.empty_m.TrueIn LevelModel := by
  obtain ⟨e, he, heω⟩ := hω.1.1
  change ∃ e : CType, ∀ z : CType, ¬mem_l hℳ z.val e.val
  exact ⟨⟨e, PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC ω hωC e heω⟩,
    fun z => he z.val⟩

include hBase hLimit hC in
theorem pairing_l : SecondOrderPairSet.formula_m.TrueIn LevelModel := by
  change ∀ a b : CType, ∃ p : CType, ∀ z : CType, mem_l hℳ z.val p.val ↔ z = a ∨ z = b
  intro a b
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.pair_exists_l hℳ a.val b.val
  refine ⟨⟨p, PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hC a.property b.property hp⟩,
    fun z => ?_⟩
  exact (hp z.val).trans (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)

include hBase hLimit hC in
theorem union_l : SecondOrderUnion.formula_m.TrueIn LevelModel := by
  change ∀ a : CType, ∃ b : CType, ∀ z : CType, mem_l hℳ z.val b.val ↔
    ∃ y : CType, mem_l hℳ y.val a.val ∧ mem_l hℳ z.val y.val
  intro a
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ a : SecondOrderQuotient.type_l hℳ, ∃ b, ∀ z,
    mem_l hℳ z b ↔ ∃ y, mem_l hℳ y a ∧ mem_l hℳ z y at hUnion
  obtain ⟨b, hb⟩ := hUnion a.val
  refine ⟨⟨b, PowerlessRelativeLimitClosure.union_l hℳ hBase hLimit hC a.property hb⟩, fun z => ?_⟩
  refine (hb z.val).trans ⟨?_, ?_⟩
  · rintro ⟨y, hya, hzy⟩
    exact ⟨⟨y, PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC a.val a.property y hya⟩, hya, hzy⟩
  · rintro ⟨y, hya, hzy⟩
    exact ⟨y.val, hya, hzy⟩

include hBase hC hω in
theorem infinity_l : SecondOrderInfinityAxiom.formula_m.TrueIn LevelModel := by
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  change ∃ w : CType, (∃ e : CType, (∀ z : CType, ¬mem_l hℳ z.val e.val) ∧ mem_l hℳ e.val w.val) ∧
    ∀ a : CType, mem_l hℳ a.val w.val → ∃ b : CType, mem_l hℳ b.val w.val ∧
      ∀ z : CType, mem_l hℳ z.val b.val ↔ mem_l hℳ z.val a.val ∨ z = a
  refine ⟨⟨ω, hωC⟩, ?_, ?_⟩
  · obtain ⟨e, he, heω⟩ := hω.1.1
    exact ⟨⟨e, hTrans ω hωC e heω⟩, fun z => he z.val, heω⟩
  · intro a ha
    obtain ⟨b, hb, hSucc⟩ := hω.1.2 a.val ha
    exact ⟨⟨b, hTrans ω hωC b hb⟩, hb, fun z =>
      (hSucc z.val).trans (or_congr Iff.rfl ⟨Subtype.ext, congrArg Subtype.val⟩)⟩

include hBase hC in
theorem foundation_l : SecondOrderFoundation.formula_m.TrueIn LevelModel := by
  change ∀ a : CType, (∃ b : CType, mem_l hℳ b.val a.val) →
    ∃ b : CType, mem_l hℳ b.val a.val ∧ ∀ z : CType, mem_l hℳ z.val b.val → ¬mem_l hℳ z.val a.val
  intro a ⟨b, hba⟩
  have hFoundation := SecondOrderFoundation.models_l hℳ
  change ∀ a : SecondOrderQuotient.type_l hℳ, (∃ b, mem_l hℳ b a) →
    ∃ b, mem_l hℳ b a ∧ ∀ z, mem_l hℳ z b → ¬mem_l hℳ z a at hFoundation
  obtain ⟨d, hda, hMin⟩ := hFoundation a.val ⟨b.val, hba⟩
  exact ⟨⟨d, PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC a.val a.property d hda⟩,
    hda, fun z hz => hMin z.val hz⟩

def basic_m : Sentence ℒ := .conj SecondOrderAxioms.extensionality_m <|
  .conj SecondOrderAxioms.empty_m <| .conj SecondOrderPairSet.formula_m <|
    .conj SecondOrderUnion.formula_m <| .conj SecondOrderInfinityAxiom.formula_m SecondOrderFoundation.formula_m

include hBase hLimit hC hω in
theorem basic_l : basic_m.TrueIn LevelModel :=
  ⟨extensionality_l hBase hC hωC, empty_l hBase hC hω hωC, pairing_l hBase hLimit hC hωC,
    union_l hBase hLimit hC hωC, infinity_l hBase hC hω hωC, foundation_l hBase hC hωC⟩

def guarded_m (φ : Sentence ℒ) : Sentence ℒ := Metatheory.Formula.forall_close <|
  let B : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let β := .fvar (.there .here)
  let C := .fvar (.there (.there .here))
  let ω := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (SecondOrderOmegaSyntax.omega_m ω) <|
          .imp (SecondOrderObjectSyntax.member_m ω C) <|
            PowerlessRelativeParameters.instance_m φ C (fun v => nomatch v)

theorem derives_m (φ : Sentence ℒ)
    (h : ∀ (𝒩 : FirstOrder.Structure.{0, 0, 0, 0} SecondOrderSyntax.signature_m)
      (h𝒩 : Theory.Models 𝒩 SecondOrderArithmetic.theory_m) (B β C ω : SecondOrderQuotient.type_l h𝒩)
      (_hBase : ∀ x, mem_l h𝒩 x B → ∀ y, mem_l h𝒩 y x → mem_l h𝒩 y B)
      (_hC : PowerlessRelativeHierarchySemantics.level_l h𝒩 B β C)
      (_hLimit : PowerlessRelativeHierarchySemantics.limit_l h𝒩 β)
      (_hω : SecondOrderOmega.omega_l h𝒩 ω) (hωC : mem_l h𝒩 ω C),
      φ.TrueIn (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l h𝒩) C ⟨ω, hωC⟩)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (guarded_m φ)) := by
  apply SecondOrderAxioms.interpretation_m
  intro 𝒩 h𝒩
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.level_formula_l K, PowerlessRelativeHierarchySemantics.limit_formula_l,
    SecondOrderOmegaSyntax.omega_l h𝒩, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  intro hBase hC hLimit hω hωC
  apply (PowerlessRelativeParameters.instance_l φ η
    (.fvar (.there (.there .here))) (fun v => nomatch v) Env.empty rfl (fun v => nomatch v)).mpr
  exact h 𝒩 h𝒩 _ _ _ _ hBase hC hLimit hω hωC

theorem basic_derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (guarded_m basic_m)) :=
  derives_m _ (fun _ _ _ _ _ _ hBase hC hLimit hω hωC => basic_l hBase hLimit hC hω hωC)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSourceBasics
