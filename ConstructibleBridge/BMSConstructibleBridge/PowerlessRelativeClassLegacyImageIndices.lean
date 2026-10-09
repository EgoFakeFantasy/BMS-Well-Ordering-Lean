import BMSConstructibleBridge.PowerlessLegacyImageIndicesBounded
import BMSConstructibleBridge.PowerlessRelativeClassProduct
import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation

/-! # 旧四标签翻译像的实际 Class 行指标集

先构造 Idx=ω×Seq(A) 与 J=ω×Idx，再在 J 内作实际 Δ₀ 分离。全部参数
都是已给定的 Class 对象，原 raw 枚举 U 不进入 AST 或类内环境；不要求 A
可数，也不使用最终 Def 闭包作为输入。完整原商指标的读数由有界绝对性
及实际有序对的 Class 闭包恢复，而不是把 raw 量词缩为 Class 量词。

本文件只构造受限翻译像指标。原 F、Seq 的正确性、Sat 行的精确读数和
原 Def 对象的认同仍由调用端接续；不宣称共同枚举族、一般 Collection
或 BMS 终局已经取得。对象分离模式沿已有原 Z₂ Derives 接口使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyImageIndices

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessLegacyImageIndicesBounded (select_m select_l select_delta_l select_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase
local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

private abbrev parameters_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set]

include hBase in
/-- 给定内层指标母集后，外层积中的受限翻译像有全部 raw 指标的精确读数。 -/
theorem exists_for_index_l (ω e N F A Seq Idx : type_l hℳ B) :
    ∃ I : type_l hℳ B, ∀ j : SecondOrderQuotient.type_l hℳ,
      mem_l hℳ j I.val ↔ select_l (𝒩 := RawModel)
        ω.val e.val N.val F.val A.val Seq.val Idx.val j := by
  obtain ⟨J, hJ⟩ := PowerlessRelativeClassProduct.exists_l hBase ω Idx
  let η : Env ClassModel [] parameters_m :=
    ((((((Env.empty.pushFree Idx).pushFree Seq).pushFree A).pushFree F).pushFree N).pushFree e).pushFree ω
  let w : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there .here)
  let z : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there (.there .here))
  let n : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there (.there (.there .here)))
  let g : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there (.there (.there (.there .here))))
  let a : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let s : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let t : Term ℒ [] (.set :: parameters_m) .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let φ : Formula ℒ [] (.set :: parameters_m) := select_m w z n g a s t (.fvar .here)
  have hφ : Formula.IsDelta0 membershipLevyBound φ := select_delta_l _ _ _ _ _ _ _ _
  obtain ⟨I, hI⟩ := PowerlessRelativeClassDeltaSeparation.exists_l hφ η J
  have hClassFormula (j : type_l hℳ B) : φ.satisfies (η.pushFree j) ↔
      select_l (𝒩 := ClassModel) ω e N F A Seq Idx j :=
    select_formula_l (η.pushFree j) w z n g a s t (.fvar .here)
  have hRawFormula (j : type_l hℳ B) :
      φ.satisfies (PowerlessRelativeClassRelativization.env_l (η.pushFree j)) ↔
      select_l (𝒩 := RawModel) ω.val e.val N.val F.val A.val Seq.val Idx.val j.val :=
    select_formula_l (PowerlessRelativeClassRelativization.env_l (η.pushFree j)) w z n g a s t (.fvar .here)
  have hAbsolute (j : type_l hℳ B) : φ.satisfies (η.pushFree j) ↔
      select_l (𝒩 := RawModel) ω.val e.val N.val F.val A.val Seq.val Idx.val j.val :=
    (PowerlessRelativeClassBounded.formula_l hφ (η.pushFree j)).trans (hRawFormula j)
  have hRead (j : type_l hℳ B) : mem_l hℳ j.val I.val ↔
      select_l (𝒩 := RawModel) ω.val e.val N.val F.val A.val Seq.val Idx.val j.val := by
    refine (hI j).trans ?_
    constructor
    · exact fun h => (hAbsolute j).mp h.2
    · intro hSelected
      have hClassSelected := (hClassFormula j).mp ((hAbsolute j).mpr hSelected)
      obtain ⟨l, hl, t₀, ht, _q, _hq, _f, _hf, hPair, _⟩ := hClassSelected
      exact ⟨(hJ j).mpr ⟨l, t₀, hl, ht, hPair⟩, (hAbsolute j).mpr hSelected⟩
  refine ⟨I, fun j => ⟨?_, ?_⟩⟩
  · intro hj
    let j' : type_l hℳ B := ⟨j,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase I.property hj⟩
    exact (hRead j').mp hj
  · intro hSelected
    have hCoordinates := hSelected
    obtain ⟨l, hl, t₀, ht, _q, _hq, _f, _hf, hPair, _⟩ := hCoordinates
    have hlClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hl
    have htClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Idx.property ht
    have hjClass := PowerlessRelativeClassPair.ordered_l hℳ hBase hlClass htClass hPair
    let j' : type_l hℳ B := ⟨j, hjClass⟩
    exact (hRead j').mpr hSelected

/-- 只给 Class Seq 参数即可实际构造 ω×Seq 的母集及受限指标，不消费 Def 结论。 -/
theorem exists_l (ω e N F A Seq : type_l hℳ B) :
    ∃ Idx I : type_l hℳ B,
      (∀ t : type_l hℳ B, mem_l hℳ t.val Idx.val ↔ ∃ q f : type_l hℳ B,
        mem_l hℳ q.val ω.val ∧ mem_l hℳ f.val Seq.val ∧
          ordered_l (ℳ := ClassModel) q f t) ∧
      ∀ j : SecondOrderQuotient.type_l hℳ, mem_l hℳ j I.val ↔
        select_l (𝒩 := RawModel) ω.val e.val N.val F.val A.val Seq.val Idx.val j := by
  obtain ⟨Idx, hIdx⟩ := PowerlessRelativeClassProduct.exists_l hBase ω Seq
  obtain ⟨I, hI⟩ := exists_for_index_l (hBase := hBase) ω e N F A Seq Idx
  exact ⟨Idx, I, hIdx, hI⟩

#print axioms exists_for_index_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyImageIndices
