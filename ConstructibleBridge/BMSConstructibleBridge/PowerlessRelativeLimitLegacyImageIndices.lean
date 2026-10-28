import BMSConstructibleBridge.PowerlessLegacyImageIndicesBounded
import BMSConstructibleBridge.PowerlessRelativeLimitProduct
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparation

/-! # 指定非零极限层内的完整旧翻译像指标

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m。给定同一
指定非零极限层 W 中的实际 Class 参数，先以全 raw 积规格构造 Idx 与
J，再用层内 Δ₀ 分离取得 I。Idx、I 的成员界是真正的原商 W 成员界，
不把全局 Class 构图或任意母集子集性质冒充层内闭包。

全部 raw 指标的最终 iff 精确使用原 selector，不多加 J 母界守卫：selector
自己的 (l,t) 坐标已经保证该守卫。这里只要求给定 Seq 对象属于 W，绝不
假定 Seq(ω,W) 属于 W。旧合法性、数字图及 Seq 的正确性留给调用端。

所有见证保留 Prop。本文件只给固定层内的语义辅助构造，不宣称已经取得
共同参数层、统一枚举历史或最终原 Derives/BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitLegacyImageIndices

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessLegacyImageIndicesBounded (select_m select_l select_delta_l select_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β W : SecondOrderQuotient.type_l hℳ}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

private abbrev parameters_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set]

/-- 先有全 raw 实际积，再以指定极限层的积成员界取得 Class 身份。 -/
private theorem product_exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    (X Y : type_l hℳ B) (hXW : mem_l hℳ X.val W) (hYW : mem_l hℳ Y.val W) :
    ∃ P : type_l hℳ B, mem_l hℳ P.val W ∧
      ∀ p : SecondOrderQuotient.type_l hℳ, mem_l hℳ p P.val ↔
        ∃ x y : SecondOrderQuotient.type_l hℳ, mem_l hℳ x X.val ∧ mem_l hℳ y Y.val ∧
          ordered_l (ℳ := RawModel) x y p := by
  obtain ⟨P, hP⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (Δ := []) .truth
    (Env.empty (M := RawModel)) X.val Y.val
  have hProduct : ∀ p, mem_l hℳ p P ↔ ∃ x y,
      mem_l hℳ x X.val ∧ mem_l hℳ y Y.val ∧ SecondOrderPairObjects.ordered_l hℳ x y p := by
    simpa only [Formula.satisfies, true_and] using hP
  have hPW := PowerlessRelativeLimitProduct.member_l hBase hLimit hW hXW hYW hProduct
  have hPClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hW) hPW
  exact ⟨⟨P, hPClass⟩, hPW, hProduct⟩

/-- 给定已在 W 内的 Idx，全部 raw 筛选指标仍在同一 W，且无额外母积守卫。 -/
theorem exists_for_index_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    (ω e N F A Seq Idx : type_l hℳ B)
    (hωW : mem_l hℳ ω.val W) (heW : mem_l hℳ e.val W) (hNW : mem_l hℳ N.val W)
    (hFW : mem_l hℳ F.val W) (hAW : mem_l hℳ A.val W)
    (hSeqW : mem_l hℳ Seq.val W) (hIdxW : mem_l hℳ Idx.val W) :
    ∃ I : type_l hℳ B, mem_l hℳ I.val W ∧
      ∀ j : SecondOrderQuotient.type_l hℳ, mem_l hℳ j I.val ↔
        select_l (𝒩 := RawModel) ω.val e.val N.val F.val A.val Seq.val Idx.val j := by
  obtain ⟨J, hJW, hJ⟩ := product_exists_l hBase hLimit hW ω Idx hωW hIdxW
  let η : Env RawModel [] parameters_m :=
    ((((((Env.empty.pushFree Idx.val).pushFree Seq.val).pushFree A.val).pushFree F.val).pushFree N.val).pushFree e.val).pushFree ω.val
  let w : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there .here)
  let z : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there (.there .here))
  let n : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there (.there (.there .here)))
  let g : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there (.there (.there (.there .here))))
  let a : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let s : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let t : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let φ : Formula ℒ [] (.set :: parameters_m) := select_m w z n g a s t (.fvar .here)
  have hφ : Formula.IsDelta0 membershipLevyBound φ := select_delta_l _ _ _ _ _ _ _ _
  have hParams : ∀ q (v : Variable parameters_m q), mem_l hℳ (η.freeVal v) W := by
    intro q v
    cases q
    cases v with
    | here => exact hωW
    | there v => cases v with
      | here => exact heW
      | there v => cases v with
        | here => exact hNW
        | there v => cases v with
          | here => exact hFW
          | there v => cases v with
            | here => exact hAW
            | there v => cases v with
              | here => exact hSeqW
              | there v => cases v with
                | here => exact hIdxW
                | there v => nomatch v
  obtain ⟨I, hIW, hSlice⟩ := PowerlessRelativeLimitDeltaSeparation.exists_l
    hBase hLimit hW hφ η hJW hParams
  have hIClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hW) hIW
  have hFormula (j : SecondOrderQuotient.type_l hℳ) : φ.satisfies (η.pushFree j) ↔
      select_l (𝒩 := RawModel) ω.val e.val N.val F.val A.val Seq.val Idx.val j :=
    select_formula_l (η.pushFree j) w z n g a s t (.fvar .here)
  refine ⟨⟨I, hIClass⟩, hIW, fun j => (hSlice j).trans ?_⟩
  constructor
  · exact fun h => (hFormula j).mp h.2
  · intro hSelected
    have hCoordinates := hSelected
    obtain ⟨l, hl, t₀, ht, _q, _hq, _f, _hf, hPair, _⟩ := hCoordinates
    exact ⟨(hJ j).mpr ⟨l, t₀, hl, ht, hPair⟩, (hFormula j).mpr hSelected⟩

/-- 完整原商积与原 selector 的逐成员 iff；只使用给定实际 Class 参数及其 W 界。 -/
theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    (ω e N F A Seq : type_l hℳ B)
    (hωW : mem_l hℳ ω.val W) (heW : mem_l hℳ e.val W) (hNW : mem_l hℳ N.val W)
    (hFW : mem_l hℳ F.val W) (hAW : mem_l hℳ A.val W) (hSeqW : mem_l hℳ Seq.val W) :
    ∃ Idx I : type_l hℳ B, mem_l hℳ Idx.val W ∧ mem_l hℳ I.val W ∧
      (∀ t : SecondOrderQuotient.type_l hℳ, mem_l hℳ t Idx.val ↔
        ∃ q f : SecondOrderQuotient.type_l hℳ, mem_l hℳ q ω.val ∧ mem_l hℳ f Seq.val ∧
          ordered_l (ℳ := RawModel) q f t) ∧
      ∀ j : SecondOrderQuotient.type_l hℳ, mem_l hℳ j I.val ↔
        select_l (𝒩 := RawModel) ω.val e.val N.val F.val A.val Seq.val Idx.val j := by
  obtain ⟨Idx, hIdxW, hIdx⟩ := product_exists_l hBase hLimit hW ω Seq hωW hSeqW
  obtain ⟨I, hIW, hI⟩ := exists_for_index_l hBase hLimit hW ω e N F A Seq Idx
    hωW heW hNW hFW hAW hSeqW hIdxW
  exact ⟨Idx, I, hIdxW, hIW, hIdx, hI⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitLegacyImageIndices
