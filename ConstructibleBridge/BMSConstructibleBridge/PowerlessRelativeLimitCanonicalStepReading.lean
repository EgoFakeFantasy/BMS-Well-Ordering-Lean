import BMSConstructibleBridge.PowerlessCanonicalOrderCandidateBounded
import BMSConstructibleBridge.PowerlessRelativeLimitCanonicalRowExtension
import BMSConstructibleBridge.PowerlessRelativeLimitFiniteMaps
import BMSConstructibleBridge.SecondOrderCanonicalIndexUnique
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalOrderStep

/-! # 实际极限层中有界规范后继证书的可靠性

对象语言为纯隶属 ℒ，背景为原 Z₂ 模型及其图商。独立有限函数覆盖界
恢复候选的完整 raw 指标规格，再与真实规范指标认同。良序性由已经证明的
实际规范构造取得，而非列为候选证书的前提。全部十个辅助对象确实属于 C。

精确行族和两张完整序图分别按成员规格认同原实际构造；由此取得任意 raw
输出 E 的 C 成员性及原 Class 后继关系。本模块不构造长历史或枚举族，
也不以该语义辅助结论替代最终 Derives Z₂ closed_m H。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitCanonicalStepReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒞" => structure_l hℳ B hBase

private theorem row_absolute_l (A Q i y : type_l hℳ B) :
    PowerlessRelativeClassRowFamily.row_l (ℳ₀ := 𝒞) A Q i y ↔
      PowerlessRelativeClassRowFamily.row_l (ℳ₀ := 𝒱) A.val Q.val i.val y.val := by
  let η : Env 𝒞 [] [.set, .set, .set, .set] :=
    (((Env.empty.pushFree y).pushFree i).pushFree Q).pushFree A
  let a : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let q : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let k : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let z : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  exact (PowerlessRelativeClassRowFamily.row_formula_l η a q k z).symm.trans
    ((PowerlessRelativeClassBounded.formula_l
      (PowerlessRelativeClassRowFamily.row_delta_l a q k z) η).trans
      (PowerlessRelativeClassRowFamily.row_formula_l
        (PowerlessRelativeClassRelativization.env_l η) a q k z))

variable (hBase)

/-- 原后继关系无需 A⊆D；旧序初段的推论才消费该另行证明的包含关系。 -/
theorem reading_l {β C E : SecondOrderQuotient.type_l hℳ}
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (ω A P Sat D : type_l hℳ B)
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hωC : mem_l hℳ ω.val C) (hAC : mem_l hℳ A.val C)
    (hPC : mem_l hℳ P.val C)
    (hDC : mem_l hℳ D.val C) (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (hCandidate : PowerlessCanonicalOrderCandidateBounded.holds_l (𝒩 := 𝒱)
      C ω.val A.val P.val Sat.val D.val E) :
    mem_l hℳ E C ∧ ∃ E' : type_l hℳ B, E'.val = E ∧
      PowerlessRelativeClassCanonicalOrderStep.step_l (hBase := hBase) ω A P Sat D E' ∧
      wellOrder_l (ℳ := 𝒱) D.val E := by
  obtain ⟨S, hSC, I, hIC, J, hJC, N, hNC, T, hTC, K, hKC,
    U, hUC, Q, hQC, Y, hYC, L, hLC, hData⟩ := hCandidate
  have hCoverage : ∀ f, PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱)
      ω.val A.val f → mem_l hℳ f C := by
    obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
    have hωEq := SecondOrderOmega.unique_l hℳ hω K₀.omega_spec
    rintro f ⟨n, hn, hf⟩
    rw [hωEq] at hn
    exact PowerlessRelativeLimitFiniteMaps.member_l hℳ hBase hLimit hC K₀
      (hωEq ▸ hωC) hAC hn hf
  have hRaw := (PowerlessCanonicalOrderCandidateBounded.reading_l hCoverage).mp hData
  have hIndex := PowerlessCanonicalIndexBounded.canonical_spec_l hCoverage hData.1
  have hCClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hC
  have inClass : ∀ x, mem_l hℳ x C →
      PowerlessRelativeClassCorrespondence.member_l hℳ B x :=
    fun x hx => PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCClass hx
  let S' : type_l hℳ B := ⟨S, inClass S hSC⟩
  let I' : type_l hℳ B := ⟨I, inClass I hIC⟩
  let J' : type_l hℳ B := ⟨J, inClass J hJC⟩
  let U' : type_l hℳ B := ⟨U, inClass U hUC⟩
  let Q' : type_l hℳ B := ⟨Q, inClass Q hQC⟩
  let Y' : type_l hℳ B := ⟨Y, inClass Y hYC⟩
  let L' : type_l hℳ B := ⟨L, inClass L hLC⟩
  have hΩ : omega_l (ℳ := 𝒞) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr hω
  obtain ⟨S₀, I₀, J₀, U₀, hIndex₀, hOrder₀⟩ :=
    PowerlessRelativeClassSatisfactionIndexCanonical.exists_l (hBase := hBase) hΩ hP
  have hEqual := SecondOrderCanonicalIndexUnique.unique_l hIndex
    (PowerlessCanonicalIndexAbsolute.spec_absolute_l (hBase := hBase) hΩ hIndex₀)
  have hSEq : S₀ = S' := Subtype.ext hEqual.1.symm
  have hIEq : I₀ = I' := Subtype.ext hEqual.2.1.symm
  have hJEq : J₀ = J' := Subtype.ext hEqual.2.2.1.symm
  have hUEq : U₀ = U' := Subtype.ext hEqual.2.2.2.symm
  rw [hSEq, hIEq, hJEq, hUEq] at hIndex₀
  have hUOrder : wellOrder_l (ℳ := 𝒱) J U := by
    rw [hEqual.2.2.1, hEqual.2.2.2]
    exact hOrder₀
  have hFamily : PowerlessRelativeClassRowOrderCanonical.family_l (ℳ₀ := 𝒞) J' A Q' Y' := by
    intro y
    constructor
    · intro hy
      obtain ⟨i, hi, hRow⟩ := (hRaw.family y.val).mp hy
      let i' : type_l hℳ B := ⟨i,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase J'.property hi⟩
      exact ⟨i', hi, (row_absolute_l (hBase := hBase) A Q' i' y).mpr hRow⟩
    · rintro ⟨i, hi, hRow⟩
      exact (hRaw.family y.val).mpr
        ⟨i.val, hi, (row_absolute_l (hBase := hBase) A Q' i y).mp hRow⟩
  obtain ⟨Y₀, L₀, E₀, _, _, hE₀C, hFamily₀, hGraph₀, hYOrder₀, hEGraph₀, hEOrder₀⟩ :=
    PowerlessRelativeLimitCanonicalRowExtension.exists_l hBase hLimit hC
      J' U' A Q' P D hJC hUC hAC hQC hPC hDC hUOrder hP
      (fun x hx => (hRaw.family x).mp (hRaw.subset x hx))
  have hYEq : Y₀.val = Y := SecondOrderQuotient.ext_l hℳ _ _
    (fun y => (hFamily₀ y).trans (hRaw.family y).symm)
  rw [hYEq] at hGraph₀ hYOrder₀
  have hLEq : L₀.val = L := PowerlessRelativeClassRowOrderCanonical.graph_unique_l hGraph₀ hRaw.rowGraph
  rw [hLEq] at hEGraph₀ hYOrder₀
  have hEEq : E₀.val = E := SecondOrderWellOrderEndExtensionUnique.unique_l hEGraph₀ hRaw.extension
  have hEC : mem_l hℳ E C := hEEq ▸ hE₀C
  let E' : type_l hℳ B := ⟨E, inClass E hEC⟩
  refine ⟨hEC, E', rfl, ?_, hEEq ▸ hEOrder₀⟩
  exact ⟨L', ⟨S', I', J', U', Q', Y', hIndex₀, hRaw.queryRead,
    hFamily, hRaw.rowGraph, hRaw.subset, hYOrder₀⟩, hRaw.extension⟩

#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitCanonicalStepReading
