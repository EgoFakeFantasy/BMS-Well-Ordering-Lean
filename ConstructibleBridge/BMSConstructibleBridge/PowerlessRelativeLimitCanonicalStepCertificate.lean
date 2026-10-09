import BMSConstructibleBridge.PowerlessRelativeLimitCanonicalStepReading
import BMSConstructibleBridge.PowerlessRelativeLimitCanonicalIndex

/-! # 原规范候选的实际同层有界证书

对象语言为纯隶属 ℒ，背景为原 Z₂ 模型的相对 Class。已有原候选可由
实际 Def 与固定 Sat 的认同给出；本模块不重新假设最终良序结论。原候选
辅助图未必在指定 C 中，故重新构造无垃圾指标及查询图，以全部 raw 读数
对齐。精确行覆盖随后产生 C 内的同一规范行序与完整末端扩张。

这里消去的是有限辅助对象的层界，不是跨层历史或枚举族。输入原候选的
存在应由已有 CanonicalMemberDefStep.of_spec_l 在最终调用端填入，不能作为
最终 closed_m H 的新增前提。完整对象推导仍由长历史与源模型装配完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitCanonicalStepCertificate

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒞" => structure_l hℳ B hBase

private theorem clean_l {X Y R : SecondOrderQuotient.type_l hℳ}
    {χ : SecondOrderQuotient.type_l hℳ → SecondOrderQuotient.type_l hℳ → Prop}
    (hR : PowerlessRelativeLimitCanonicalIndex.graph_l (𝒩 := 𝒱) X Y R χ) :
    PowerlessRelationBounded.clean_l (𝒩 := 𝒱) R X Y := by
  intro p hp
  obtain ⟨x, y, hx, hy, hxy, _⟩ := (hR p).mp hp
  exact ⟨x, y, hx, hy, hxy⟩

variable (hBase)

theorem exists_l {β C : SecondOrderQuotient.type_l hℳ}
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (ω A P Sat D : type_l hℳ B)
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hωC : mem_l hℳ ω.val C) (hAC : mem_l hℳ A.val C)
    (hPC : mem_l hℳ P.val C) (hSatC : mem_l hℳ Sat.val C)
    (hDC : mem_l hℳ D.val C) (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (hCandidate : ∃ L, PowerlessRelativeClassCanonicalOrderStep.candidate_l
      (hBase := hBase) ω A P Sat D L) :
    ∃ E : type_l hℳ B, mem_l hℳ E.val C ∧
      PowerlessCanonicalOrderCandidateBounded.holds_l (𝒩 := 𝒱)
        C ω.val A.val P.val Sat.val D.val E.val ∧
      PowerlessRelativeClassCanonicalOrderStep.step_l (hBase := hBase) ω A P Sat D E ∧
      wellOrder_l (ℳ := 𝒱) D.val E.val := by
  obtain ⟨S, I, J, N, T, K, U, hSC, hIC, hJC, hNC, hTC, hKC, hUC,
    hSpec, hIndex, hU⟩ := PowerlessRelativeLimitCanonicalIndex.exists_l hℳ
      hBase hLimit hC hω hωC hAC hPC hP
  have hCoverage : ∀ f, PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱)
      ω.val A.val f → mem_l hℳ f C := by
    obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
    have hωEq := SecondOrderOmega.unique_l hℳ hω K₀.omega_spec
    rintro f ⟨n, hn, hf⟩
    rw [hωEq] at hn
    exact PowerlessRelativeLimitFiniteMaps.member_l hℳ hBase hLimit hC K₀
      (hωEq ▸ hωC) hAC hn hf
  obtain ⟨hS, hI, hJ, hN, hT, hK, hURead⟩ := hSpec
  have hSpec' : PowerlessRelativeLimitCanonicalIndex.spec_l ω.val A.val P.val S I J N T K U :=
    ⟨hS, hI, hJ, hN, hT, hK, hURead⟩
  obtain ⟨hNRead, hTRead, hKRead, hURead'⟩ := PowerlessRelativeLimitCanonicalIndex.reading_l hSpec'
  have hRawIndex : PowerlessCanonicalIndexBounded.rawspec_l ω.val A.val P.val S I J N T K U :=
    ⟨hS, hI, hJ, clean_l hN, clean_l hT, clean_l hK, clean_l hURead,
      hNRead, hTRead, hKRead, hURead'⟩
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    PowerlessRelativeClassSatisfactionAllSlots.query_m
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set] :=
    ((((Env.empty.pushFree Sat.val).pushFree I).pushFree S).pushFree A.val).pushFree ω.val
  have hParams : ∀ s (v : Variable [SetTheory.SetSort.set, .set, .set, .set, .set] s),
      mem_l hℳ (η.freeVal v) C := by
    intro s v
    cases v with
    | here => exact hωC
    | there v => cases v with
      | here => exact hAC
      | there v => cases v with
        | here => exact hSC
        | there v => cases v with
          | here => exact hIC
          | there v => cases v with
            | here => exact hSatC
            | there v => nomatch v
  obtain ⟨Q, hQC, hQ⟩ := PowerlessRelativeLimitRelationalGraph.exists_member_l
    hBase hLimit hC (PowerlessRelativeClassSatisfactionAllSlots.query_delta_l _ _ _ _ _ _ _)
      η hJC hAC hParams
  have hClean : PowerlessRelationBounded.clean_l (𝒩 := 𝒱) Q J A.val := by
    intro p hp
    obtain ⟨j, x, hj, hx, hPair, _⟩ := (hQ p).mp hp
    exact ⟨j, x, hj, hx, hPair⟩
  have hφ j x : φ.satisfies ((η.pushFree x).pushFree j) ↔
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω.val A.val S I Sat.val j x :=
    PowerlessRelativeClassSatisfactionAllSlots.query_formula_l _ _ _ _ _ _ _ _
  have hRead j x : value_l (ℳ := 𝒱) Q j x ↔ mem_l hℳ j J ∧ mem_l hℳ x A.val ∧
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω.val A.val S I Sat.val j x :=
    (PowerlessRelativeLimitRelationalGraph.values_of_members_l hQ j x).trans
      (and_congr Iff.rfl (and_congr Iff.rfl (hφ j x)))
  obtain ⟨L₀, S₀, I₀, J₀, U₀, Q₀, Y₀, hIndex₀, hRead₀, hFamily₀, _, hSubset₀, _⟩ := hCandidate
  have hΩ : omega_l (ℳ := 𝒞) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr hω
  have hEqual := SecondOrderCanonicalIndexUnique.unique_l hIndex
    (PowerlessCanonicalIndexAbsolute.spec_absolute_l (hBase := hBase) hΩ hIndex₀)
  have hQValues j x : value_l (ℳ := 𝒱) Q₀.val j x ↔ value_l (ℳ := 𝒱) Q j x := by
    rw [hRead₀, hRead, hEqual.1, hEqual.2.1, hEqual.2.2.1]
  have hCover : ∀ x, mem_l hℳ x D.val → ∃ j, mem_l hℳ j J ∧
      PowerlessRelativeClassRowFamily.row_l (ℳ₀ := 𝒱) A.val Q j x := by
    intro x hx
    obtain ⟨j, hj, hRow⟩ := (SecondOrderRowOrderCanonical.family_ambient_l
      (hBase := hBase) hFamily₀ x).mp (hSubset₀ x hx)
    exact ⟨j, hEqual.2.2.1.symm ▸ hj,
      (PowerlessRelativeClassRowOrderCanonical.row_congr_l hQValues j x).mp hRow⟩
  have hCClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hC
  let J' : type_l hℳ B := ⟨J, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCClass hJC⟩
  let U' : type_l hℳ B := ⟨U, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCClass hUC⟩
  let Q' : type_l hℳ B := ⟨Q, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCClass hQC⟩
  obtain ⟨Y, L, E, hYC, hLC, hEC, hFamily, hGraph, _, hExtension, _⟩ :=
    PowerlessRelativeLimitCanonicalRowExtension.exists_l hBase hLimit hC
      J' U' A Q' P D hJC hUC hAC hQC hPC hDC hU hP hCover
  have hDY : subset_l (ℳ := 𝒱) D.val Y.val := fun x hx => (hFamily x).mpr (hCover x hx)
  have hData := (PowerlessCanonicalOrderCandidateBounded.reading_l hCoverage).mpr
    (show PowerlessCanonicalOrderCandidateBounded.rawspec_l
      ω.val A.val P.val Sat.val D.val E.val S I J N T K U Q Y.val L.val from
      ⟨hRawIndex, hClean, hRead, hFamily, hGraph, hDY, hExtension⟩)
  have hBounded : PowerlessCanonicalOrderCandidateBounded.holds_l (𝒩 := 𝒱)
      C ω.val A.val P.val Sat.val D.val E.val :=
    ⟨S, hSC, I, hIC, J, hJC, N, hNC, T, hTC, K, hKC, U, hUC,
      Q, hQC, Y.val, hYC, L.val, hLC, hData⟩
  obtain ⟨_, E', hEq, hStep, hOrder⟩ := PowerlessRelativeLimitCanonicalStepReading.reading_l
    hBase hLimit hC ω A P Sat D hω hωC hAC hPC hDC hP hBounded
  have hEEq : E' = E := Subtype.ext hEq
  exact ⟨E, hEC, hBounded, hEEq ▸ hStep, hOrder⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitCanonicalStepCertificate
