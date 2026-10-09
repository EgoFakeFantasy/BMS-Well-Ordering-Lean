import BMSConstructibleBridge.PowerlessRelativeCutoffHistoryCoverage
import BMSConstructibleBridge.PowerlessRelativeMemberStaticAbsolute
import BMSConstructibleBridge.PowerlessMemberSatisfactionFunctionAbsolute
import BMSConstructibleBridge.PowerlessMemberDefFunctionAbsolute
import BMSConstructibleBridge.PowerlessMemberOrdinalAbsolute
import BMSConstructibleBridge.PowerlessRelativeCofinalLegacyNumericReading
import BMSConstructibleBridge.PowerlessMemberLegacyNumericAbsolute

/-! # 任意源对象的前史与同一母层内完整编码包

沿任意 x∈W 的实际较早前史选择同一个 U，取得其原共尾 Def 编码包。
原旧翻译图 Q 与完整 Sat 图 G 均作为实际对象保留；G∈W 使用两次
严格后继预算，不从 G∈Def²(U) 猜测 G∈U。十一个编码对象及实际 ω
都在 MemberW 中，七个前史对象亦作为同一实际成员见证返回。原完整
静态规格、完整 Sat 与 Def 检查器图规格，以及同一轻量前史，
均在同一 MemberW 成立；原完整 Def／历史证书仍保留在原点规格中。

这是统一捕获步骤所需的源存在性装配，不假定任意 W 对象属于同一个
较早 U，也不重新选取共同域 I。尚须构造并捕获完整覆盖矩阵；本模块
没有完成全局弱凝聚、Collection 或最终无条件 Z₂ 良序推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffHistoryCodedCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  PowerlessRelativeClassStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 所有实际编码对象位于母层；完整原包与母层静态包指向同一对象。 -/
theorem exists_l (K : source_coding_l hℳ) {B ω Ω W x : type_l hℳ}
    (hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hBW : mem_l hℳ B W) (hx : mem_l hℳ x W) :
    ∃ a y A β U D f :
        PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W,
      PowerlessRelativeCutoffHistoryCoverage.point_l B ω Ω W x
        a.val y.val A.val β.val U.val D.val f.val ∧
      ∃ ω₀ e t₁ t₂ t₃ P N F Q G t₄ V :
          PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W,
        ∃ C : SecondOrderModel.set_l ℳ, ω₀.val = ω ∧
          PowerlessRelativeCofinalDefCoding.spec_l (W := U.val) hBase K
            (PowerlessRelativeMemberStaticAbsolute.class_l hW ω₀)
            (PowerlessRelativeMemberStaticAbsolute.class_l hW e)
            (PowerlessRelativeMemberStaticAbsolute.class_l hW t₁)
            (PowerlessRelativeMemberStaticAbsolute.class_l hW t₂)
            (PowerlessRelativeMemberStaticAbsolute.class_l hW t₃)
            (PowerlessRelativeMemberStaticAbsolute.class_l hW P)
            (PowerlessRelativeMemberStaticAbsolute.class_l hW N)
            (PowerlessRelativeMemberStaticAbsolute.class_l hW F)
            (PowerlessRelativeMemberStaticAbsolute.class_l hW Q)
            (PowerlessRelativeMemberStaticAbsolute.class_l hW G) C ∧
          PowerlessSatisfactionExistenceSyntax.static_l
            (𝒩 := PowerlessMemberStructure.structure_l
              (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨x, hx⟩)
            ω₀ e t₁ t₂ t₃ P N F ∧
          PowerlessMemberSatisfactionFunctionAbsolute.spec_l
            (𝒩 := PowerlessMemberStructure.structure_l
              (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨x, hx⟩)
            ω₀ e t₁ t₂ t₃ P N F U G ∧
          PowerlessMemberDefFunctionAbsolute.spec_l
            (𝒩 := PowerlessMemberStructure.structure_l
              (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨x, hx⟩)
            ω₀ e N Q U G D ∧
          PowerlessLegacyNumericSyntax.spec_l
            (𝒩 := PowerlessMemberStructure.structure_l
              (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨x, hx⟩)
            ω₀ e t₁ t₂ t₃ t₄ P N V Q ∧
          SetTheory.Structure.IsOrdinal
            (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
              (PowerlessMemberStructure.structure_l
                (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨x, hx⟩)) A ∧
          PowerlessHierarchyLightHistory.holds_l
            (𝒩 := PowerlessMemberStructure.structure_l
              (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨x, hx⟩)
            ⟨B, hBW⟩ D A U f ∧
          ∀ z : PowerlessMemberStructure.type_l
              (ℳ := SecondOrderQuotient.structure_l hℳ) W,
            member_l (PowerlessMemberStructure.structure_l
              (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨x, hx⟩) z U →
            ∀ r : PowerlessMemberStructure.type_l
                (ℳ := SecondOrderQuotient.structure_l hℳ) W,
              PowerlessFiniteSequencesSyntax.sequence_l
                (ℳ := PowerlessMemberStructure.structure_l
                  (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨x, hx⟩) ω₀ z r →
              member_l (PowerlessMemberStructure.structure_l
                (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨x, hx⟩) r U := by
  obtain ⟨a, y, A, β, U, D, f, hPoint⟩ :=
    PowerlessRelativeCutoffHistoryCoverage.exists_l K hBase hω hΩ hW hBW hx
  have h := hPoint
  obtain ⟨haW, hyW, hAW, hβW, hUW, hDW, hfW,
    _haA, _haΩ, hAΩ, hβΩ, _hAβ, hLimit, hCofinal, hU, _hBU, _hxU, hωU,
    hGraph, _hf, hLight, _hCapture, _hyLevel, _hy, _hxy⟩ := h
  let ω' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨ω, ⟨β, U, hU, hωU⟩⟩
  have hωEq : ω'.val = K.omega := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨e, t₁, t₂, t₃, P, N, F, Q, G, C, hCoding⟩ :=
    PowerlessRelativeCofinalDefCoding.exists_l hBase K hLimit hU hCofinal ω' hωU hωEq
  obtain ⟨t₄, V, ht₄U, hVU, hNumericRaw⟩ :=
    PowerlessRelativeCofinalLegacyNumericReading.exists_l
      hBase K hLimit hU hωU hCoding
  have hOuter := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  have hGW := PowerlessRelativeCofinalDefGraph.satisfaction_member_l K hBase
    hLimit hU hOuter hW hβΩ hωU hCoding
  have hSub := PowerlessRelativeLevelClosure.subset_l hℳ hBase hβΩ hU hW
  let ω₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    ⟨ω, hSub ω hωU⟩
  let e₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    ⟨e.val, hSub e.val hCoding.e_mem⟩
  let t₁₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    ⟨t₁.val, hSub t₁.val hCoding.tag₁_mem⟩
  let t₂₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    ⟨t₂.val, hSub t₂.val hCoding.tag₂_mem⟩
  let t₃₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    ⟨t₃.val, hSub t₃.val hCoding.tag₃_mem⟩
  let P₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    ⟨P.val, hSub P.val hCoding.pair_mem⟩
  let N₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    ⟨N.val, hSub N.val hCoding.numbers_mem⟩
  let F₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    ⟨F.val, hSub F.val hCoding.validity_mem⟩
  let Q₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    ⟨Q.val, hSub Q.val hCoding.translation_mem⟩
  let G₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W := ⟨G.val, hGW⟩
  let t₄₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    ⟨t₄.val, hSub t₄.val ht₄U⟩
  let V₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    ⟨V.val, hSub V.val hVU⟩
  let a₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W := ⟨a, haW⟩
  let y₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W := ⟨y, hyW⟩
  let A₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W := ⟨A, hAW⟩
  let β₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W := ⟨β, hβW⟩
  let U₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W := ⟨U, hUW⟩
  let D₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W := ⟨D, hDW⟩
  let f₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W := ⟨f, hfW⟩
  have hStatic : PowerlessSatisfactionExistenceSyntax.static_l
      (𝒩 := PowerlessMemberStructure.structure_l
        (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨x, hx⟩)
      ω₀ e₀ t₁₀ t₂₀ t₃₀ P₀ N₀ F₀ :=
    PowerlessRelativeMemberStaticAbsolute.spec_l K hBase hOuter hW
      (PowerlessRelativeCutoffInnerLimits.cofinal_l K hBase hω hΩ) hωEq hCoding.static
  have hTrans : PowerlessNaturalOrder.transitive_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    fun z t hz ht => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW z hz t ht
  have hNumeric := (PowerlessMemberLegacyNumericAbsolute.spec_l
    (ℳ := SecondOrderQuotient.structure_l hℳ) (W := W) (hW := ⟨x, hx⟩)
    hTrans ω₀ e₀ t₁₀ t₂₀ t₃₀ t₄₀ P₀ N₀ V₀ Q₀).mpr hNumericRaw
  have hSat := PowerlessMemberSatisfactionFunctionAbsolute.graph_l
    (ℳ := SecondOrderQuotient.structure_l hℳ) (W := W) (hW := ⟨x, hx⟩)
    hTrans ω₀ e₀ t₁₀ t₂₀ t₃₀ P₀ N₀ F₀ U₀ G₀ hCoding.sat_map hCoding.sat_read
  have hDefRaw (z r : type_l hℳ) :
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) D z r ↔
        mem_l hℳ z U ∧ mem_l hℳ r U ∧
          PowerlessMemberDefImageBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
            ω e.val N.val Q.val U G.val z r := by
    constructor
    · intro hz
      obtain ⟨hzU, hDef⟩ := (hGraph.2 z r).mp hz
      exact ⟨hzU, (SecondOrderFunctionProperties.value_mem_l hℳ hGraph.1 hz).2,
        (PowerlessMemberDefImageBoundedReading.checkeriff_l
          hBase K hLimit hU hωU hCoding hzU).mpr hDef⟩
    · rintro ⟨hzU, _hrU, hCheck⟩
      exact (hGraph.2 z r).mpr ⟨hzU,
        (PowerlessMemberDefImageBoundedReading.checkeriff_l
          hBase K hLimit hU hωU hCoding hzU).mp hCheck⟩
  have hDef := PowerlessMemberDefFunctionAbsolute.graph_l
    (ℳ := SecondOrderQuotient.structure_l hℳ) (W := W) (hW := ⟨x, hx⟩)
    hTrans ω₀ e₀ N₀ Q₀ U₀ G₀ D₀ hGraph.1 hDefRaw
  let B₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    ⟨B, hBW⟩
  let η : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨x, hx⟩)
      [] [.set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree f₀ |>.pushFree U₀ |>.pushFree A₀ |>.pushFree D₀ |>.pushFree B₀
  have hLightAbsolute : PowerlessHierarchyLightHistory.holds_l
      (𝒩 := PowerlessMemberStructure.structure_l
        (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨x, hx⟩) B₀ D₀ A₀ U₀ f₀ ↔
      PowerlessHierarchyLightHistory.holds_l
        (𝒩 := SecondOrderQuotient.structure_l hℳ) B D A U f := by
    let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
      PowerlessHierarchyLightHistory.formula_m
        (.fvar .here)
        (.fvar (.there .here))
        (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there (.there (.there .here)))))
    have hφ : Formula.IsDelta0 StabilityFrame.membershipLevyBound φ :=
      PowerlessHierarchyLightHistory.delta_l _ _ _ _ _
    have h := PowerlessMemberBounded.formula_l
      (fun z hz t ht => hTrans z t hz ht) hφ η
    simpa only [φ, PowerlessHierarchyLightHistory.formula_l, Term.eval,
      Env.pushFree_here, Env.pushFree_there, PowerlessRelativization.env_l, η,
      B₀, D₀, A₀, U₀, f₀] using h
  have hLightMember := hLightAbsolute.mpr ((PowerlessHierarchyLightHistory.reading_l hℳ).mpr hLight)
  have hA : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
        (SecondOrderQuotient.structure_l hℳ)) A := by
    apply SetTheory.Structure.IsOrdinal.mem hΩ.1
    exact hAΩ
  have hAMember := PowerlessMemberOrdinalAbsolute.ordinal_l
    (ℳ := SecondOrderQuotient.structure_l hℳ) (W := W) (hW := ⟨x, hx⟩) hTrans A₀ hA
  have hFinite := PowerlessMemberSatisfactionFunctionAbsolute.coverage_l
    (ℳ := SecondOrderQuotient.structure_l hℳ) (W := W) (hW := ⟨x, hx⟩)
    hTrans ω₀ U₀ hCoding.coverage
  exact ⟨a₀, y₀, A₀, β₀, U₀, D₀, f₀, hPoint,
    ω₀, e₀, t₁₀, t₂₀, t₃₀, P₀, N₀, F₀, Q₀, G₀, t₄₀, V₀,
    C, rfl, hCoding, hStatic, hSat, hDef, hNumeric, hAMember, hLightMember, hFinite⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffHistoryCodedCoverage
