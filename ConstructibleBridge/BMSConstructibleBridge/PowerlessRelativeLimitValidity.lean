import BMSConstructibleBridge.PowerlessRelativeLimitRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeClassValidity

/-! # 给定非零极限层中的实际合法性图

先在固定层内对 ω × ω 的有界查询构图，再复用同一 K、T、V 的合法性
读取桥。所有查询坐标均为原商对象；不要求内部合法码外部标准，也不把
原二阶 V 转成该层的集合成员。全有限证书母集 N 的规格和层成员仍显式保留。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitValidity

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β C : type_l hℳ}

/-- 纯查询图的固定层存在性不预设编码参数的语义正确性。 -/
theorem query_exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {ω e N T t₁ t₂ t₃ : type_l hℳ}
    (hωC : mem_l hℳ ω C) (heC : mem_l hℳ e C) (hNC : mem_l hℳ N C)
    (hTC : mem_l hℳ T C) (ht₁C : mem_l hℳ t₁ C)
    (ht₂C : mem_l hℳ t₂ C) (ht₃C : mem_l hℳ t₃ C) :
    ∃ F, mem_l hℳ F C ∧ ∀ c l : type_l hℳ,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F c l ↔
        PowerlessFormulaValidityBounded.query_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
          ω e N T t₁ t₂ t₃ c l := by
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set, .set, .set, .set, .set] :=
    (((((((Env.empty).pushFree t₃).pushFree t₂).pushFree t₁).pushFree T).pushFree N).pushFree e).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let s : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let t : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let b : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let d : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  have hParams : ∀ q (v : Variable [SetTheory.SetSort.set, .set, .set, .set, .set, .set, .set] q),
      mem_l hℳ (η.freeVal v) C := by
    intro q v
    cases v with
    | here => exact hωC
    | there v => cases v with
      | here => exact heC
      | there v => cases v with
        | here => exact hNC
        | there v => cases v with
          | here => exact hTC
          | there v => cases v with
            | here => exact ht₁C
            | there v => cases v with
              | here => exact ht₂C
              | there v => cases v with
                | here => exact ht₃C
                | there v => nomatch v
  obtain ⟨F, hFC, hF⟩ := PowerlessRelativeLimitRelationalGraph.exists_l hBase hLimit hC
    (PowerlessFormulaValidityGraph.matrix_delta_l w z s t a b d) η hωC hωC hParams
  refine ⟨F, hFC, fun c l => ?_⟩
  have h := (hF c l).trans (and_congr Iff.rfl (and_congr Iff.rfl
    (PowerlessFormulaValidityGraph.matrix_formula_l η w z s t a b d c l)))
  change value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F c l ↔
    mem_l hℳ c ω ∧ mem_l hℳ l ω ∧
      PowerlessFormulaValidityBounded.query_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω e N T t₁ t₂ t₃ c l at h
  exact h.trans ⟨And.right ∘ And.right, fun hQuery => ⟨hQuery.1, hQuery.2.1, hQuery⟩⟩

/-- 同一固定层图读取原内部合法性关系；不重新选择编码或图见证。 -/
theorem exists_l (K : source_coding_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {ω e N T t₁ t₂ t₃ : type_l hℳ}
    (hωC : mem_l hℳ ω C) (heC : mem_l hℳ e C) (hNC : mem_l hℳ N C)
    (hTC : mem_l hℳ T C) (ht₁C : mem_l hℳ t₁ C)
    (ht₂C : mem_l hℳ t₂ C) (ht₃C : mem_l hℳ t₃ C)
    (hωEq : ω = K.omega) (he : e = code_l K (SecondOrderModel.zero_l ℳ))
    (ht : PowerlessEvaluationTags.tags_l (ℳ := SecondOrderQuotient.structure_l hℳ) e t₁ t₂ t₃)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hN : PowerlessFiniteSequencesSyntax.spec_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N) :
    ∃ F, mem_l hℳ F C ∧ ∀ c l : type_l hℳ,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F c l ↔
        PowerlessRelationalCodeValidity.valid_l K V c l := by
  obtain ⟨F, hFC, hF⟩ := query_exists_l hBase hLimit hC hωC heC hNC hTC ht₁C ht₂C ht₃C
  let lift (x : type_l hℳ) (hx : mem_l hℳ x C) : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨x, ⟨β, C, hC, hx⟩⟩
  let ω' := lift ω hωC
  let e' := lift e heC
  let N' := lift N hNC
  let T' := lift T hTC
  let t₁' := lift t₁ ht₁C
  let t₂' := lift t₂ ht₂C
  let t₃' := lift t₃ ht₃C
  have hωRaw : SecondOrderOmega.omega_l hℳ ω := by
    simpa only [hωEq] using K.omega_spec
  have hωClass : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) ω' :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mpr hωRaw
  have htClass : PowerlessEvaluationTags.tags_l
      (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) e' t₁' t₂' t₃' :=
    ⟨(PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e').mpr ht.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e' t₁').mpr ht.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₁' t₂').mpr ht.2.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₂' t₃').mpr ht.2.2.2⟩
  refine ⟨F, hFC, fun c l => ?_⟩
  exact (hF c l).trans (PowerlessRelativeClassValidity.query_iff_l
    (hBase := hBase) (ω := ω') (e := e') (N := N') (T := T')
    (t₁ := t₁') (t₂ := t₂') (t₃ := t₃')
    K hωClass hωEq he htClass hT hSpec hV hN c l)

#print axioms query_exists_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitValidity
