import BMSConstructibleBridge.PowerlessSatisfactionNormalizedMatrix
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessRelativeClassBounded
import BMSConstructibleBridge.PowerlessRelativeClassValueCoordinates

/-! # 共同层内规范 Sat 见证的实际 Class 函数

固定同一编码包与合法赋值的共同母界，用纯 Δ₀ 规范矩阵检查输入域和输出 Sat。
若每个域已有共同层内见证，原 Δ₀ 图存在和规范对象唯一性给出一张实际
Class 函数，精确读数覆盖全部原商坐标。没有使用 Collection 或 Type 选择。

共同层内总性在接口中明确保留，须由实际层界另证。本模块不从逐域
存在推出共同界，不构造枚举前史，也不是最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionFunction

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev lift_m {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => structure_l hℳ B hBase

private theorem term_value_l {Γ Δ : SortContext ℒ} (η : Env ClassModel Γ Δ)
    (t : Term ℒ Γ Δ .set) :
    t.eval (PowerlessRelativeClassRelativization.env_l η) = (t.eval η).val := by
  match t with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app f _ => nomatch f

private theorem env_here_l {Γ Δ : SortContext ℒ} (η : Env ClassModel Γ Δ)
    (x : type_l hℳ B) :
    (PowerlessRelativeClassRelativization.env_l (η.pushFree (sort := SetTheory.SetSort.set) x)).freeVal
      .here = x.val := rfl

private theorem env_there_l {Γ Δ : SortContext ℒ} (η : Env ClassModel Γ Δ)
    (x : type_l hℳ B) (v : Variable Δ .set) :
    (PowerlessRelativeClassRelativization.env_l (η.pushFree (sort := SetTheory.SetSort.set) x)).freeVal
      (.there v) = (PowerlessRelativeClassRelativization.env_l η).freeVal v := rfl

/-- 层内总性是实际存在见证的假设，不是新源公理或宿主选择函数。 -/
theorem exists_l {Δ : SortContext ℒ} (K : source_coding_l hℳ)
    (η : Env ClassModel [] Δ) (ω e N T M D t₁ t₂ t₃ F : Term ℒ [] Δ .set)
    (C : type_l hℳ B)
    (hω : (ω.eval η).val = K.omega) (he : (e.eval η).val = code_l K (numeral_l ℳ 0))
    (ht₁ : (t₁.eval η).val = code_l K (numeral_l ℳ 1))
    (ht₂ : (t₂.eval η).val = code_l K (numeral_l ℳ 2))
    (ht₃ : (t₃.eval η).val = code_l K (numeral_l ℳ 3))
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) K.omega K.omega (N.eval η).val)
    (hT : map_l (ℳ := RawModel) (T.eval η).val K.omega K.omega)
    (hCoverage : ∀ A : type_l hℳ B, mem_l hℳ A.val C.val → ∀ f,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := RawModel) K.omega A.val f →
        mem_l hℳ f (M.eval η).val)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K (T.eval η).val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hF : ∀ c L, value_l (ℳ := RawModel) (F.eval η).val c L ↔
      PowerlessRelationalCodeValidity.valid_l K V c L)
    (hTotal : ∀ A : type_l hℳ B, mem_l hℳ A.val C.val → ∃ R : type_l hℳ B,
      mem_l hℳ R.val (D.eval η).val ∧
      PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := RawModel)
        (ω.eval η).val A.val (e.eval η).val (N.eval η).val (T.eval η).val
        (M.eval η).val (D.eval η).val (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val
        (F.eval η).val R.val) :
    ∃ G : type_l hℳ B, map_l (ℳ := RawModel) G.val C.val (D.eval η).val ∧
      ∀ a r : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := RawModel) G.val a r ↔ mem_l hℳ a C.val ∧ mem_l hℳ r (D.eval η).val ∧
          PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := RawModel)
            (ω.eval η).val a (e.eval η).val (N.eval η).val (T.eval η).val
            (M.eval η).val (D.eval η).val (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val
            (F.eval η).val r := by
  let φ : Formula ℒ [] (.set :: .set :: Δ) :=
    PowerlessSatisfactionNormalizedMatrix.formula_m (lift_m ω) (.fvar .here)
      (lift_m e) (lift_m N) (lift_m T) (lift_m M) (lift_m D)
      (lift_m t₁) (lift_m t₂) (lift_m t₃) (lift_m F) (.fvar (.there .here))
  have hφ : Formula.IsDelta0 membershipLevyBound φ :=
    PowerlessSatisfactionNormalizedMatrix.delta_l _ _ _ _ _ _ _ _ _ _ _ _
  have hRead (A R : type_l hℳ B) : φ.satisfies ((η.pushFree R).pushFree A) ↔
      PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := RawModel)
        (ω.eval η).val A.val (e.eval η).val (N.eval η).val (T.eval η).val
        (M.eval η).val (D.eval η).val (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val
        (F.eval η).val R.val := by
    have h := (PowerlessRelativeClassBounded.formula_l hφ ((η.pushFree R).pushFree A)).trans
      (PowerlessSatisfactionNormalizedMatrix.formula_l
        (PowerlessRelativeClassRelativization.env_l ((η.pushFree R).pushFree A))
        (lift_m ω) (.fvar .here) (lift_m e) (lift_m N) (lift_m T) (lift_m M) (lift_m D)
        (lift_m t₁) (lift_m t₂) (lift_m t₃) (lift_m F) (.fvar (.there .here)))
    simpa only [term_value_l, lift_m, Term.eval_weakenFree, Term.eval,
      env_here_l, env_there_l, Env.pushFree_here, Env.pushFree_there] using h
  have hTotal' (A : type_l hℳ B) (hA : mem_l hℳ A.val C.val) :
      ∃! R : type_l hℳ B, mem_l hℳ R.val (D.eval η).val ∧
        φ.satisfies ((η.pushFree R).pushFree A) := by
    obtain ⟨R, hRD, hR⟩ := hTotal A hA
    refine ⟨R, ⟨hRD, (hRead A R).mpr hR⟩, ?_⟩
    intro R' hR'
    have hNorm := (hRead A R').mp hR'.2
    rw [hω, he, ht₁, ht₂, ht₃] at hR hNorm
    exact Subtype.ext (PowerlessSatisfactionNormalizedMatrix.unique_of_coverage_l K
      hN hT (hCoverage A hA) hPair hV hF hNorm hR)
  obtain ⟨G, hG, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l hφ η C (D.eval η) hTotal'
  refine ⟨G, (PowerlessRelativeClassFunctionAbsolute.map_l G C (D.eval η)).mp hG, ?_⟩
  have hClassRead (A R : type_l hℳ B) :=
    (PowerlessRelativeClassFunctionAbsolute.value_l G A R).symm.trans
      ((hValue A R).trans (and_congr Iff.rfl (and_congr Iff.rfl (hRead A R))))
  intro a r
  constructor
  · intro hValueRaw
    obtain ⟨ha, hr⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase G hValueRaw
    exact (hClassRead ⟨a, ha⟩ ⟨r, hr⟩).mp hValueRaw
  · rintro ⟨ha, hr, hNorm⟩
    let A : type_l hℳ B := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase C.property ha⟩
    let R : type_l hℳ B := ⟨r, PowerlessRelativeClassCorrespondence.transitive_l
      hℳ hBase (D.eval η).property hr⟩
    exact (hClassRead A R).mpr ⟨ha, hr, hNorm⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionFunction
