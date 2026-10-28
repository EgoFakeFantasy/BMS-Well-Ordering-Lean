import BMSConstructibleBridge.PowerlessRelativeCofinalNormalizedSatisfaction
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionFunction
import BMSConstructibleBridge.PowerlessRelativeLimitLegacySyntaxGraphs
import BMSConstructibleBridge.PowerlessRelativeLimitLegacyImageIndices
import BMSConstructibleBridge.PowerlessRelativeLimitSelectedSatisfactionRows
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAbsolute

/-! # 共尾极限层的原 Def 检查器实际编码整包

背景为原 SecondOrderArithmetic.theory_m，辅助图及检查器使用纯隶属语言 ℒ。
同一 K、实际非零共尾极限层 W 和实际 ω∈W 给出层内静态编码包、旧翻译
的完整数字图，以及一张实际 Class 规范 Sat 函数 W→W。整张 Sat 函数图
只要求属于 Class，绝不把它的全局存在误认为 G∈W。

给定这张函数的任意 raw 输出，实际取得同一 W 内的 Seq、Idx、I、Q，
完整读数覆盖全部 raw 指标和元素。W 仅作为有限赋值的覆盖母界，不假定
Seq(ω,W)∈W。反向 Sat 绝对性也在本文件实际证明，供原 Def 的求值保持
使用；不存在最终保持性、枚举、可数性或历史前提占位。

全部对象见证保留 Prop，无 Collection、外部 ω 标准性、外部良基性或
Type 选择。这里只装配指定层的真实语义数据；Def 函数图、长前缀图及
对应原 Derives 的构造由调用端继续，不宣称 BMS 终局已经完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalDefCoding

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β W : SecondOrderQuotient.type_l hℳ}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 指定实际 Sat 的完整 raw 规格读回实际 Class，不替换该图或选择更新数据。 -/
theorem sat_class_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {ω A e t₁ t₂ t₃ Pair Valid Seq Sat : type_l hℳ B}
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val A.val Seq.val)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := RawModel)
      ω.val A.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val Sat.val) :
    PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase)
      ω A e t₁ t₂ t₃ Pair Valid Sat := by
  refine ⟨?_, ?_, ?_⟩
  · intro c f hValue
    obtain ⟨hc, L, hL, hValid, hMap⟩ := hSat.1 c.val f.val
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Sat c f).mp hValue)
    let L' : type_l hℳ B := ⟨L,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hL⟩
    exact ⟨hc, L', hL,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Valid c L').mpr hValid,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f L' A).mpr hMap⟩
  · intro f hValue
    exact hSat.2.1 f.val
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Sat e f).mp hValue)
  · intro c L f hc hL hMap a b
    have hBranches := hSat.2.2 c.val L.val f.val hc hL
      ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f L A).mp hMap) a.val b.val
    have hValue := PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Sat c f
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hConstructor ha hb
      exact hValue.trans ((hBranches.1
        (PowerlessRelativeClassConstructorBounds.constructor_to_ambient_l (hBase := hBase) hω hConstructor)
        ha hb).trans (PowerlessRelativeClassEvaluationAbsolute.member_l (hBase := hBase) f a b).symm)
    · intro hConstructor ha hb
      exact hValue.trans ((hBranches.2.1
        (PowerlessRelativeClassConstructorBounds.constructor_to_ambient_l (hBase := hBase) hω hConstructor)
        ha hb).trans (PowerlessRelativeClassEvaluationAbsolute.equal_l (hBase := hBase) f a b).symm)
    · intro hConstructor ha hb
      have haRaw := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Valid a L).mp ha
      have hbRaw := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Valid b L).mp hb
      exact hValue.trans ((hBranches.2.2.1
        (PowerlessRelativeClassConstructorBounds.constructor_to_ambient_l (hBase := hBase) hω hConstructor)
        haRaw hbRaw).trans (not_congr (and_congr
          (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Sat a f).symm
          (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Sat b f).symm)))
    · intro hConstructor ha hb
      have hbRaw := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Valid b L).mp hb
      exact hValue.trans ((hBranches.2.2.2
        (PowerlessRelativeClassConstructorBounds.constructor_to_ambient_l (hBase := hBase) hω hConstructor)
        ha hbRaw).trans (PowerlessRelativeClassEvaluationAbsolute.exists_l
          (hBase := hBase) ω A Seq Sat f a b hSeq).symm)

/-- 命名字段均为真实规格证书；没有把实际对象见证抽成宿主数据函数。 -/
structure spec_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) (ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    (C : SecondOrderModel.set_l ℳ) : Prop where
  omega_eq : ω.val = K.omega
  e_mem : mem_l hℳ e.val W
  tag₁_mem : mem_l hℳ t₁.val W
  tag₂_mem : mem_l hℳ t₂.val W
  tag₃_mem : mem_l hℳ t₃.val W
  pair_mem : mem_l hℳ Pair.val W
  numbers_mem : mem_l hℳ N.val W
  validity_mem : mem_l hℳ Valid.val W
  translation_mem : mem_l hℳ Translation.val W
  static : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := structure_l hℳ B hBase)
    ω e t₁ t₂ t₃ Pair N Valid
  legacy_translation : SecondOrderLegacyFormulaTranslation.spec_l C
  translation_numeric : ∀ n s, value_l (ℳ := RawModel) Translation.val (code_l K n) (code_l K s) ↔
    SecondOrderPairing.relation_l C n s
  sat_map : map_l (ℳ := RawModel) G.val W W
  sat_read : ∀ a r : SecondOrderQuotient.type_l hℳ,
    value_l (ℳ := RawModel) G.val a r ↔ mem_l hℳ a W ∧ mem_l hℳ r W ∧
      PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := RawModel)
        ω.val a e.val N.val Pair.val W W t₁.val t₂.val t₃.val Valid.val r
  coverage : ∀ a : SecondOrderQuotient.type_l hℳ, mem_l hℳ a W → ∀ f,
    PowerlessFiniteSequencesSyntax.sequence_l (ℳ := RawModel) ω.val a f → mem_l hℳ f W
  sat_class : ∀ A Seq Sat : type_l hℳ B, mem_l hℳ A.val W →
    PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val A.val Seq.val →
    value_l (ℳ := RawModel) G.val A.val Sat.val →
      PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase)
        ω A e t₁ t₂ t₃ Pair Valid Sat
  witnesses : ∀ a r : SecondOrderQuotient.type_l hℳ,
    mem_l hℳ a W → value_l (ℳ := RawModel) G.val a r →
      mem_l hℳ r W ∧ ∃ Seq Idx I Q : type_l hℳ B,
        mem_l hℳ Seq.val W ∧ mem_l hℳ Idx.val W ∧ mem_l hℳ I.val W ∧ mem_l hℳ Q.val W ∧
          PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val a Seq.val ∧
          (∀ t : SecondOrderQuotient.type_l hℳ, mem_l hℳ t Idx.val ↔
            ∃ q f : SecondOrderQuotient.type_l hℳ, mem_l hℳ q ω.val ∧ mem_l hℳ f Seq.val ∧
              ordered_l (ℳ := RawModel) q f t) ∧
          (∀ j : SecondOrderQuotient.type_l hℳ, mem_l hℳ j I.val ↔
            PowerlessLegacyImageIndicesBounded.select_l (𝒩 := RawModel)
              ω.val e.val N.val Translation.val a Seq.val Idx.val j) ∧
          (∀ j x : SecondOrderQuotient.type_l hℳ, value_l (ℳ := RawModel) Q.val j x ↔
            mem_l hℳ j I.val ∧ mem_l hℳ x a ∧
              PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := RawModel)
                ω.val a Seq.val Idx.val r j x)

private abbrev parameters_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set]

private abbrev entry_m (v : Variable parameters_m .set) : Term ℒ [] parameters_m .set := .fvar v

/-- 固定 K 的全部数据实际取得；G 是 Class 图，不声称 G∈W。 -/
theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ)
    (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    (ω : type_l hℳ B) (hωW : mem_l hℳ ω.val W) (hωEq : ω.val = K.omega) :
    ∃ e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B,
      ∃ C : SecondOrderModel.set_l ℳ, spec_l (W := W) hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G C := by
  obtain ⟨e, t₁, t₂, t₃, Pair, N, Valid, heW, ht₁W, ht₂W, ht₃W, hPairW, hNW,
    hValidW, hStatic, hTotal⟩ := PowerlessRelativeCofinalNormalizedSatisfaction.exists_l
      (hBase := hBase) K hLimit hW hCofinal ω hωW hωEq
  obtain ⟨he, ht₁, ht₂, ht₃, hN, hPairMap, hPair, hValidReading⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l (hBase := hBase) K hωEq hStatic
  have hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr (hωEq.symm ▸ K.omega_spec)
  have hωRaw : SecondOrderOmega.omega_l hℳ ω.val := hωEq.symm ▸ K.omega_spec
  let ηω : Env RawModel [] [.set] := Env.empty.pushFree ω.val
  have hωPure : omega_l (ℳ := RawModel) ω.val :=
    (omega_formula_l ηω (.fvar .here)).mp
      ((SecondOrderOmegaSyntax.omega_l hℳ ηω (.fvar .here)).mpr hωRaw)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  have hCoverage (a : SecondOrderQuotient.type_l hℳ) (ha : mem_l hℳ a W)
      (f : SecondOrderQuotient.type_l hℳ)
      (hf : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := RawModel) ω.val a f) : mem_l hℳ f W := by
    obtain ⟨L, hL, hMap⟩ := hf
    exact PowerlessRelativeLimitFiniteMaps.subset_member_l hℳ hBase hLimit hW K
      (hωEq ▸ hωW) (fun x hx => hTrans a ha x hx) (hωEq ▸ hL) hMap
  obtain ⟨V₄, hV₄, _hV₄Unique⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  let WC : type_l hℳ B := ⟨W, PowerlessRelativeLevelClosure.class_l hℳ hBase hW⟩
  let ηTail : Env (structure_l hℳ B hBase) [] [.set, .set, .set] :=
    (((Env.empty).pushFree Valid).pushFree t₃).pushFree t₂
  let η : Env (structure_l hℳ B hBase) [] parameters_m :=
    (((((ηTail.pushFree t₁).pushFree WC).pushFree Pair).pushFree N).pushFree e).pushFree ω
  let w := entry_m .here
  let z := entry_m (.there .here)
  let n := entry_m (.there (.there .here))
  let p := entry_m (.there (.there (.there .here)))
  let c := entry_m (.there (.there (.there (.there .here))))
  let x := entry_m (.there (.there (.there (.there (.there .here)))))
  let y := entry_m (.there (.there (.there (.there (.there (.there .here))))))
  let d := entry_m (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let v := entry_m (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  have hCoverageK (A : type_l hℳ B) (hAW : mem_l hℳ A.val W) (f : SecondOrderQuotient.type_l hℳ)
      (hf : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := RawModel) K.omega A.val f) : mem_l hℳ f W := by
    apply hCoverage A.val hAW f
    simpa only [hωEq] using hf
  obtain ⟨G, hGMap, hGRead⟩ := PowerlessRelativeClassSatisfactionFunction.exists_l
    (hBase := hBase) K η w z n p c c x y d v WC hωEq he ht₁ ht₂ ht₃ hN hPairMap
      hCoverageK hPair hV₄ (hValidReading V₄ hV₄) hTotal
  obtain ⟨V₅, hV₅, _hV₅Unique⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  obtain ⟨C, hC, _hCUnique⟩ := SecondOrderLegacyFormulaTranslation.exists_l hℳ
  obtain ⟨_OldValid, Translation, _hOldValidW, hTranslationW,
    _hOldValidRaw, _hOldValidNumeric, _hTranslationRaw, hTranslationNumeric⟩ :=
    PowerlessRelativeLimitLegacySyntaxGraphs.exists_l (hBase := hBase) K hLimit hW
      hΩ hωEq hωW hNW hPairW hN hPairMap hPair hV₅ hC
  have heEmpty : ∀ a, ¬mem_l hℳ a e.val :=
    (PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp hStatic.1.1
  have hNω : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val ω.val N.val := by
    simpa only [hωEq] using hN
  have hPairω : map_l (ℳ := RawModel) Pair.val ω.val ω.val := by
    simpa only [hωEq] using hPairMap
  have hRawRead (a r : SecondOrderQuotient.type_l hℳ) (ha : mem_l hℳ a W)
      (hValue : value_l (ℳ := RawModel) G.val a r) : mem_l hℳ r W ∧
        ∃ S, mem_l hℳ S W ∧ PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val a S ∧
          PowerlessSatisfactionSpecification.spec_l (𝒩 := RawModel)
            ω.val a e.val t₁.val t₂.val t₃.val Pair.val Valid.val r ∧
          PowerlessSatisfactionGraphClean.holds_l (𝒩 := RawModel) ω.val S r := by
    obtain ⟨_ha, hr, hNorm⟩ := (hGRead a r).mp hValue
    exact ⟨hr, (PowerlessSatisfactionNormalizedMatrix.spec_iff_of_coverage_l
      hωPure heEmpty hNω hPairω (hCoverage a ha)).mp hNorm⟩
  refine ⟨e, t₁, t₂, t₃, Pair, N, Valid, Translation, G, C, ?_⟩
  refine {
    omega_eq := hωEq
    e_mem := heW
    tag₁_mem := ht₁W
    tag₂_mem := ht₂W
    tag₃_mem := ht₃W
    pair_mem := hPairW
    numbers_mem := hNW
    validity_mem := hValidW
    translation_mem := hTranslationW
    static := hStatic
    legacy_translation := hC
    translation_numeric := hTranslationNumeric
    sat_map := hGMap
    sat_read := hGRead
    coverage := hCoverage
    sat_class := ?_
    witnesses := ?_ }
  · intro A Seq Sat hAW hSeq hValue
    obtain ⟨_hr, _S, _hSW, _hSeq, hSat, _hClean⟩ := hRawRead A.val Sat.val hAW hValue
    exact sat_class_l hBase hωRaw hSeq hSat
  · intro a r ha hValue
    obtain ⟨hr, s, hsW, hSeq, _hSat, _hClean⟩ := hRawRead a r ha hValue
    let A : type_l hℳ B := ⟨a, ⟨β, W, hW, ha⟩⟩
    let Sat : type_l hℳ B := ⟨r, ⟨β, W, hW, hr⟩⟩
    let Seq : type_l hℳ B := ⟨s, ⟨β, W, hW, hsW⟩⟩
    obtain ⟨Idx, I, hIdxW, hIW, hIdx, hI⟩ := PowerlessRelativeLimitLegacyImageIndices.exists_l
      hBase hLimit hW ω e N Translation A Seq hωW heW hNW hTranslationW ha hsW
    obtain ⟨Q, hQW, hQ⟩ := PowerlessRelativeLimitSelectedSatisfactionRows.query_exists_l
      hBase hLimit hW ω A Seq Idx Sat I hωW ha hsW hIdxW hr hIW
    exact ⟨hr, Seq, Idx, I, Q, hsW, hIdxW, hIW, hQW, hSeq, hIdx, hI, hQ⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalDefCoding
