import BMSConstructibleBridge.PowerlessRelativeClassLegacyMemberDefAssembly
import BMSConstructibleBridge.PowerlessRelativeClassInjectionEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassOntoCountability

/-! # 类内可数母集的原 Def 闭包及对象推导

单射必须是实际 Class 对象。非空分支将其带默认值反转为实际枚举，再
消费已装配的原 Def 精确 Class 呈现；空分支使用配对闭包。结论针对任意
原 Def 见证，不替换原 global_m，也不将母集的任意子集自动放入 Class。

公开闭句经同一原商图翻译回到原 Z₂ Derives。这是有类内可数性前提的
原 Def 闭包定理，不证明全部截断层可数，不收集历史，也不是最终 BMS。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyDefClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

theorem class_l (K : source_coding_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {ω A H : SecondOrderQuotient.type_l hℳ} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hCountable : PowerlessRelativeOrdinalCutoff.countable_l B ω A)
    (hDef : SecondOrderMemberDef.spec_l hℳ A H) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B H := by
  rcases hDef with ⟨_hEmpty, hPair⟩ | hDef
  · exact PowerlessRelativeClassPair.pair_l hℳ hBase hA hA hPair
  · obtain ⟨d, hd⟩ := SecondOrderMemberDef.nonempty_member_l hℳ hDef
    let A' : type_l hℳ B := ⟨A, hA⟩
    let d' : type_l hℳ B := ⟨d,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hA hd⟩
    let ω' : type_l hℳ B := ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
      (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
    have hΩ := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mpr hω
    obtain ⟨R, hRClass, hRMap, hInjective⟩ := hCountable
    let R' : type_l hℳ B := ⟨R, hRClass⟩
    have hMap : map_l (ℳ := structure_l hℳ B hBase) R' A' ω' :=
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) R' A' ω').mpr hRMap
    have hInj : ∀ x y i : type_l hℳ B,
        value_l (ℳ := structure_l hℳ B hBase) R' x i →
          value_l (ℳ := structure_l hℳ B hBase) R' y i → x = y := by
      intro x y i hxi hyi
      exact Subtype.ext (hInjective x.val y.val i.val
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R' x i).mp hxi)
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R' y i).mp hyi))
    obtain ⟨U, hU, hOnto, _hRead⟩ :=
      PowerlessRelativeClassInjectionEnumeration.exists_l (hBase := hBase) hMap hInj (d := d') hd
    have hURaw : map_l (ℳ := RawModel) U.val ω A := by
      change SecondOrderFunctionObjects.map_l hℳ U.val ω A
      exact (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) U ω' A').mp hU
    have hOntoRaw : ∀ y, mem_l hℳ y A →
        ∃ i, mem_l hℳ i ω ∧ value_l (ℳ := RawModel) U.val i y := by
      intro y hy
      let y' : type_l hℳ B := ⟨y,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hA hy⟩
      obtain ⟨i, hi, hiy⟩ := hOnto y' hy
      exact ⟨i.val, hi, (PowerlessRelativeClassFunctionAbsolute.value_l
        (hBase := hBase) U i y').mp hiy⟩
    obtain ⟨Y, hY⟩ := PowerlessRelativeClassLegacyMemberDefAssembly.exists_l
      (hBase := hBase) (ω := ω') (A := A') (U := U) hΩ hURaw hOntoRaw
    exact PowerlessRelativeClassLegacyMemberDef.class_l hY (Or.inr hDef)

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let H : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let A := .fvar (.there .here)
  let ω := .fvar (.there (.there .here))
  let B := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
        .imp (PowerlessRelativeOrdinalCutoff.countable_m B ω A) <|
          .imp (PowerlessMemberDefSyntax.global_m A H) (PowerlessRelativeHierarchySyntax.class_m B H)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn RawModel := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, PowerlessMemberDefDerives.formula_l K, Term.eval]
  intro η hBase hω hA hCountable hDef
  exact class_l K hBase hω hA hCountable hDef

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms class_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyDefClosure
