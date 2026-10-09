import BMSConstructibleBridge.PowerlessRawLegacyNumericReading
import BMSConstructibleBridge.PowerlessCodedHistoryDataReading
import BMSConstructibleBridge.PowerlessMemberDefImageRawReading
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryUnique
import BMSConstructibleBridge.PowerlessRelativeCofinalDefGraph

/-! # 任意完整捕获包的原 Def 与原历史认同

对象语言为纯隶属 ℒ，背景及正式推导为原 num/set Z₂。给定完整点
资格中的 P/F/V/Q/G/D/U/f 全部保持不变；只用其实际原商规格恢复
原 Def、零／后继／极限历史和原层资格，不要求这些图属于 Class。
空母集与非空母集分开处理，双向图读数覆盖全部 raw 输出。

对象恢复原则明确保留 ω 及完整点资格。它不是完整源 Collection、
逐候选源存在性或最终无额外前提的 H 行良序定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRawCodedHistoryReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 仅用实际指标上的查询读数识别每个 raw 行；不要求查询图干净。 -/
private theorem rows_l {ω e N Q z R S I J C r : type_l hℳ}
    (hData : PowerlessMemberDefImageCoverage.spec_l (𝒩 := 𝒱) ω e N Q z R S I J C)
    (hRows : PowerlessRelativeClassRowOrderCanonical.family_l (ℳ₀ := 𝒱) J z C r) :
    ∀ Z, mem_l hℳ Z r ↔ ∃ j, mem_l hℳ j J ∧
      ∀ x, mem_l hℳ x Z ↔ mem_l hℳ x z ∧
        PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω z S I R j x := by
  have hRow (j : type_l hℳ) (hj : mem_l hℳ j J) (Z : type_l hℳ) :
      PowerlessRelativeClassRowFamily.row_l (ℳ₀ := 𝒱) z C j Z ↔
        ∀ x, mem_l hℳ x Z ↔ mem_l hℳ x z ∧
          PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω z S I R j x := by
    have hPoint (x : type_l hℳ) :
        (mem_l hℳ x z ∧ value_l (ℳ := 𝒱) C j x) ↔
          (mem_l hℳ x z ∧ PowerlessRelativeClassSatisfactionAllSlots.query_l
            (ℳ₀ := 𝒱) ω z S I R j x) :=
      and_congr_right (fun hx => hData.2.2.2 j hj x hx)
    exact ⟨fun h x => (h x).trans (hPoint x), fun h x => (h x).trans (hPoint x).symm⟩
  intro Z
  exact (hRows Z).trans
    ⟨fun ⟨j, hj, h⟩ => ⟨j, hj, (hRow j hj Z).mp h⟩,
      fun ⟨j, hj, h⟩ => ⟨j, hj, (hRow j hj Z).mpr h⟩⟩

section Reading

variable (K : source_coding_l hℳ)
  {B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : type_l hℳ}
  (hω : ω = K.omega)
  (h : PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
    B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G)

include hω h

/-- 同一 D 的任意实际输出满足原 Def；空分支不调用非空呈现。 -/
theorem image_l {z r : type_l hℳ} (hValue : value_l (ℳ := 𝒱) D z r) :
    SecondOrderMemberDef.spec_l hℳ z r := by
  classical
  obtain ⟨_ha, _hf, _hx, _hB, hωU, hStatic, hG, hD, hNumeric, _hA, _hLight,
    hFinite, hTrans, hClosed⟩ := h
  obtain ⟨hzU, _hrU, hChecker⟩ := (hD.2 z r).mp hValue
  rcases hChecker with ⟨hEmpty, hPair⟩ | ⟨hNonempty, hImage⟩
  · exact Or.inl ⟨hEmpty, hPair⟩
  · obtain ⟨he, ht₁, ht₂, ht₃, hN, hP, hPair, hF⟩ :=
      PowerlessRawStaticCodingReading.reading_l K hω hStatic
    obtain ⟨_ht₄, hLegacy⟩ := PowerlessRawLegacyNumericReading.reading_l K hω hStatic hNumeric
    obtain ⟨V₀, hV₀, _⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
    obtain ⟨C₀, hC₀, _⟩ := SecondOrderLegacyFormulaTranslation.exists_l hℳ
    have hQ := (hLegacy V₀ hV₀).2 C₀ hC₀
    obtain ⟨R, S, I, J, C, _hR, _hS, _hI, _hJ, _hC, _hValue, hSat, hData, hRows⟩ :=
      PowerlessCodedHistoryDataReading.image_l K hω hTrans hClosed hωU hzU
        hStatic hG hFinite hImage
    have hz : ∃ t, mem_l hℳ t z := by
      by_contra hn
      exact hNonempty (fun t ht => hn ⟨t, ht⟩)
    exact Or.inr (PowerlessMemberDefImageRawReading.identify_l K hω he ht₁ ht₂ ht₃
      hN hP hPair hF hQ hC₀ hSat hData hz (rows_l hData hRows))

/-- 输出不预先限制于 U；反向由同一 D 的全域性及原 Def 唯一性取得。 -/
theorem graph_l : PowerlessRelativeCofinalDefGraph.graph_l (hℳ := hℳ) U D := by
  have hD := h.2.2.2.2.2.2.2.1
  refine ⟨hD.1, ?_⟩
  intro z r
  constructor
  · intro hValue
    exact ⟨((hD.2 z r).mp hValue).1, image_l K hω h hValue⟩
  · rintro ⟨hz, hOriginal⟩
    obtain ⟨s, hs, _⟩ := hD.1.2 z hz
    have hEq := SecondOrderMemberDef.unique_l hℳ hOriginal (image_l K hω h hs.2)
    exact hEq.symm ▸ hs.2

/-- 完整轻量历史回到原 Def 后继历史，所有图与极限并保持不变。 -/
theorem history_l : PowerlessRelativeHierarchySemantics.history_l hℳ B A f U := by
  have hLight := h.2.2.2.2.2.2.2.2.2.2.1
  have hGraph : ∀ z r, value_l (ℳ := 𝒱) D z r ↔
      mem_l hℳ z U ∧ SecondOrderMemberDef.spec_l hℳ z r := by
    intro z r
    exact (graph_l K hω h).2 z r
  exact PowerlessHierarchyLightHistoryUnique.to_original_l hℳ
    (B := B) (D := D) (W := U) (α := A) (C := U) (f := f) hGraph
    ((PowerlessHierarchyLightHistory.reading_l hℳ).mp hLight)

/-- 指定同一阶段、输出及其成员取得原层与原相对类资格。 -/
theorem level_l : PowerlessRelativeHierarchySemantics.level_l hℳ B a y ∧
    PowerlessRelativeClassCorrespondence.member_l hℳ B x := by
  have hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B a y :=
    ⟨A, f, U, h.2.2.2.2.2.2.2.2.2.1, h.1, history_l K hω h, h.2.1⟩
  exact ⟨hLevel, a, y, hLevel, h.2.2.1⟩

end Reading

def result_m {Γ Δ : SortContext ℒ} (B x a y A U D f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeCofinalDefGraph.graph_m U D) <|
    .conj (PowerlessRelativeHierarchySyntax.history_m B A f U) <|
      .conj (PowerlessRelativeHierarchySyntax.level_m B a y)
        (PowerlessRelativeHierarchySyntax.class_m B x)

def schema_m {Δ : SortContext ℒ}
    (B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (PowerlessCodedHistoryCoverageSyntax.point_m B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G)
      (result_m B x a y A U D f)

def sentence_m {Δ : SortContext ℒ}
    (B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ}
    (B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : Term ℒ [] Δ .set) :
    (sentence_m B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
      (SecondOrderQuotient.structure_l hℳ)) :=
    ⟨SecondOrderQuotient.ext_l hℳ⟩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, result_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    PowerlessCodedHistoryCoverageSyntax.point_formula_l hExt,
    PowerlessRelativeCofinalDefGraph.graph_formula_l K,
    PowerlessRelativeHierarchySemantics.history_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K]
  intro hΩ hPoint
  have hωEq := SecondOrderOmega.unique_l hℳ hΩ K.omega_spec
  have hLevel := level_l K hωEq hPoint
  exact ⟨graph_l K hωEq hPoint, history_l K hωEq hPoint, hLevel.1, hLevel.2⟩

theorem derives_m {Δ : SortContext ℒ}
    (B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ hℳ => models_l hℳ B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G)

#print axioms image_l
#print axioms graph_l
#print axioms history_l
#print axioms level_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRawCodedHistoryReading
