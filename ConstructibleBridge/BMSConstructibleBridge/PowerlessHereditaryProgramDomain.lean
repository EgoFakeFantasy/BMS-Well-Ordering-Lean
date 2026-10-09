import BMSConstructibleBridge.PowerlessHereditaryProduct
import BMSConstructibleBridge.PowerlessHereditaryFiniteSequences
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramDomain

/-! # 同一原有限程序码域及枚举图的遗传资格

纯隶属 ℒ，背景原 Z₂。先认同原 S 与已经实际构造的遗传有限序列集，
再由原 P=Seq(Q)×ω 的精确规格取得 P 的统一包络。原 U 是 Class 函数
图且映射 ω 到这个 P 时，整张原 U 由积母界取得遗传性，不是逐值断言。

Q 的遗传性仍是输入；没有把 ClassQ 偷换成遗传资格，也不更换原
Q/S/P/U。两个公开出口均为原核 Derives，不声称最终良序或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryProgramDomain

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => PowerlessRelativeClassStructure.structure_l hℳ B hBase

include hBase in
theorem member_l {ω Q S P : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hQ : PowerlessHereditaryClass.member_l hℳ B Q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l B ω Q S P) :
    PowerlessHereditaryClass.member_l hℳ B S ∧ PowerlessHereditaryClass.member_l hℳ B P := by
  have hωHC := PowerlessHereditaryOmega.member_l hℳ hBase hω
  let O : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨ω, PowerlessHereditaryClass.contained_l hℳ hBase hωHC⟩
  let X : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨Q, PowerlessHereditaryClass.contained_l hℳ hBase hQ⟩
  let T : PowerlessRelativeClassStructure.type_l hℳ B := ⟨S, hDomain.1⟩
  obtain ⟨T', hT', hEnvelope⟩ := PowerlessHereditaryFiniteSequences.exists_l
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr hω)
    ((PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) X).mp hQ)
  have hRead (f : PowerlessRelativeClassStructure.type_l hℳ B) :
      mem_l hℳ f.val T.val ↔ PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒩) O X f :=
    (hDomain.2.1 f.val).trans
      (PowerlessRelativeClassFiniteSequencesDerives.sequence_absolute_l (hBase := hBase) O X f).symm
  have hEq : T' = T := (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    T' T (fun f => (hT' f).trans (hRead f).symm)
  have hS : PowerlessHereditaryClass.member_l hℳ B S := by
    have hT'HC := (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) T').mpr hEnvelope
    simpa only [hEq] using hT'HC
  exact ⟨hS, PowerlessHereditaryProduct.member_l (hBase := hBase) hS hωHC hDomain.2.2.2⟩

include hBase in
/-- 给定同一个原 U 的实际 Class 资格和映射规格，取得整图遗传性。 -/
theorem enumeration_l {ω P U : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hP : PowerlessHereditaryClass.member_l hℳ B P)
    (hU : PowerlessRelativeClassCorrespondence.member_l hℳ B U)
    (hMap : map_l (ℳ := 𝒱) U ω P) :
    PowerlessHereditaryClass.member_l hℳ B U :=
  PowerlessHereditaryProduct.relation_l (hBase := hBase)
    (PowerlessHereditaryOmega.member_l hℳ hBase hω) hP hU hMap.1

def schema_m {Δ : SortContext ℒ} (B ω Q S P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessHereditaryClass.formula_m B Q) <|
        .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P)
          (.conj (PowerlessHereditaryClass.formula_m B S) (PowerlessHereditaryClass.formula_m B P))

def enumeration_schema_m {Δ : SortContext ℒ} (B ω P U : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessHereditaryClass.formula_m B P) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B U) <|
          .imp (SecondOrderObjectSyntax.map_m U ω P) (PowerlessHereditaryClass.formula_m B U)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω Q S P : Term ℒ [] Δ .set) :
    (Metatheory.Formula.forall_close (schema_m B ω Q S P)).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessHereditaryClass.formula_l K,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K]
  intro η hBase hω hQ hDomain
  exact member_l (hBase := hBase) hω hQ hDomain

theorem enumeration_models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω P U : Term ℒ [] Δ .set) :
    (Metatheory.Formula.forall_close (enumeration_schema_m B ω P U)).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [enumeration_schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessHereditaryClass.formula_l K, PowerlessRelativeHierarchySemantics.class_formula_l K,
    map_formula_l]
  intro η hBase hω hP hU hMap
  exact enumeration_l (hBase := hBase) hω hP hU hMap

theorem derives_m {Δ : SortContext ℒ} (B ω Q S P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close (schema_m B ω Q S P))) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B ω Q S P)

theorem enumeration_derives_m {Δ : SortContext ℒ} (B ω P U : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close (enumeration_schema_m B ω P U))) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => enumeration_models_l h𝒩 B ω P U)

#print axioms member_l
#print axioms enumeration_l
#print axioms derives_m
#print axioms enumeration_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryProgramDomain
