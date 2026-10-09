import BMSConstructibleBridge.PowerlessLegacyMemberDefWellOrderAmbient
import BMSConstructibleBridge.PowerlessMemberDefDerives

/-! # 原 Def 保持环境良序的原 Z₂ 对象推导

句子中母集、Def 输出及非空子集量词均在环境商取值。配对与传递
超集将母集和给定序图置于共同基点；类内设施只构造新的实际序图。
空母集分支按原定义输出单元素集。结论通过原图翻译回到 Derives，
不替代相对层的规范相容或最终固定行 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefWellOrder

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem exists_l {A P D : SecondOrderQuotient.type_l hℳ}
    (hP : wellOrder_l (ℳ := SecondOrderQuotient.structure_l hℳ) A P)
    (hD : SecondOrderMemberDef.spec_l hℳ A D) :
    ∃ L : SecondOrderQuotient.type_l hℳ,
      wellOrder_l (ℳ := SecondOrderQuotient.structure_l hℳ) D L := by
  rcases hD with ⟨_, hPair⟩ | hD
  · obtain ⟨e, he⟩ := SecondOrderQuotient.empty_l hℳ
    have hNoEdge x y : ¬value_l (ℳ := SecondOrderQuotient.structure_l hℳ) e x y := by
      rintro ⟨p, hp, _⟩
      exact he p hp
    have hSingleton x (hx : mem_l hℳ x D) : x = A :=
      ((hPair x).mp hx).elim id id
    refine ⟨e, fun x _ => hNoEdge x x, ?_, ?_, ?_⟩
    · intro x y z _ hxy _
      exact (hNoEdge x y hxy).elim
    · intro x y hxy
      exact Or.inr (Or.inl ((hSingleton x hxy.1).trans (hSingleton y hxy.2).symm))
    · intro U hU
      obtain ⟨x, hx⟩ := hU.2
      exact ⟨x, hx, fun y _ => hNoEdge y x⟩
  · obtain ⟨A₀, a, ha, V, E, I, Q, R, T, F, H, hA, hPresentation, hH⟩ := hD
    obtain ⟨C, hC⟩ := SecondOrderPairObjects.pair_exists_l hℳ A P
    have hSup := SecondOrderTransitiveSuperset.models_l hℳ
    change ∀ C : SecondOrderQuotient.type_l hℳ, ∃ B,
      (∀ x, mem_l hℳ x C → mem_l hℳ x B) ∧
        ∀ x y, mem_l hℳ x B → mem_l hℳ y x → mem_l hℳ y B at hSup
    obtain ⟨B, hCB, hTrans⟩ := hSup C
    have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B :=
      fun x hx y hy => hTrans x y hx hy
    let A' : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨A, PowerlessRelativeClassCorrespondence.base_l hℳ hBase (hCB A ((hC A).mpr (Or.inl rfl)))⟩
    let P' : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨P, PowerlessRelativeClassCorrespondence.base_l hℳ hBase (hCB P ((hC P).mpr (Or.inr rfl)))⟩
    obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
    let ω : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
        (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
    have hΩ := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr K.omega_spec
    obtain ⟨L, hL⟩ := PowerlessLegacyMemberDefWellOrderAmbient.exists_l
      (hBase := hBase) (A := A') (P := P') hΩ hP hPresentation hA.symm
    exact ⟨L.val, hH ▸ hL⟩

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let A : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let P : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let D : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m A P) <|
    .imp (PowerlessMemberDefSyntax.global_m A D) <|
      .existsE .set (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m
        (D.weakenBound SetTheory.SetSort.set) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessMemberDefDerives.formula_l K, Term.eval_weakenBound, Term.eval]
  exact fun hP hD => exists_l hP hD

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefWellOrder
