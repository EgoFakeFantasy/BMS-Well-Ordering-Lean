import BMSConstructibleBridge.SecondOrderGraphFormulaRelation
import BMSConstructibleBridge.SecondOrderFunctionLaws
import BMSConstructibleBridge.SecondOrderEvaluationFixedPoint
import BMSConstructibleBridge.SecondOrderEvaluationEquations
import BMSConstructibleBridge.SecondOrderDefinableFamily
import BMSConstructibleBridge.PowerlessFormulaValidityReading

/-! # 指定实际枚举的原求值与行族证书

在给定实际 raw 映射 U 下，两个纯集合公式理解原数值相等图和成员图；
K.less 的内部良基根覆盖全部原数，原映射的值唯一性使读数适用于任意
给定 raw 输出。再用原理解取得全数域 D、递归求值 T 与精确行族 F₀。

所有原实数及证书均在 Prop 存在量词中保留，不选择模型、函数值或实数
作为 Type 数据。这里不要求 U、Q、R、T 或 F₀ 属于 Class，不替换指定 U
为旧正规化枚举，不更改原 presentation；给定 E 也无须增加正确性前提。
本模块是原 EnumeratedMemberDef 接线的语义辅助，不是最终原 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEnumeratedEvaluation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderModel (num_l set_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def equality_m {Γ Δ : SortContext ℒ} (U i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .conj
    (SecondOrderObjectSyntax.value_m (up₂ U) (up₂ i) (.bvar (.there .here)))
    (.conj (SecondOrderObjectSyntax.value_m (up₂ U) (up₂ j) (.bvar .here))
      (.equal (.bvar (.there .here)) (.bvar .here)))

def membership_m {Γ Δ : SortContext ℒ} (U i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .conj
    (SecondOrderObjectSyntax.value_m (up₂ U) (up₂ i) (.bvar (.there .here)))
    (.conj (SecondOrderObjectSyntax.value_m (up₂ U) (up₂ j) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here)))

theorem equality_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (U i j : Term ℒ Γ Δ .set) :
    (equality_m U i j).satisfies η ↔
      ∃ x y, value_l (ℳ := 𝒩) (U.eval η) (i.eval η) x ∧
        value_l (ℳ := 𝒩) (U.eval η) (j.eval η) y ∧ x = y := by
  simp only [equality_m, Formula.satisfies, value_formula_l,
    up, up₂, Term.eval_weakenBound, Term.eval]
  rfl

theorem membership_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (U i j : Term ℒ Γ Δ .set) :
    (membership_m U i j).satisfies η ↔
      ∃ x y, value_l (ℳ := 𝒩) (U.eval η) (i.eval η) x ∧
        value_l (ℳ := 𝒩) (U.eval η) (j.eval η) y ∧ member_l 𝒩 x y := by
  simp only [membership_m, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, up₂, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 原数域、原子图、求值图和行族全部匹配给定 U，且只保留 Prop 存在见证。 -/
theorem exists_l (K : source_coding_l hℳ) {A U : SecondOrderQuotient.type_l hℳ}
    (hU : map_l (ℳ := RawModel) U K.omega A) (E : set_l ℳ) :
    ∃ D Q R T F₀ : set_l ℳ,
      (∀ n, SecondOrderModel.mem_l n D) ∧
      (∀ i j x y, value_l (ℳ := RawModel) U (code_l K i) x →
        value_l (ℳ := RawModel) U (code_l K j) y →
          (SecondOrderPairing.relation_l Q i j ↔ x = y)) ∧
      (∀ i j x y, value_l (ℳ := RawModel) U (code_l K i) x →
        value_l (ℳ := RawModel) U (code_l K j) y →
          (SecondOrderPairing.relation_l R i j ↔ member_l RawModel x y)) ∧
      SecondOrderEvaluationEquations.spec_l E D Q R T ∧
        SecondOrderDefinableFamily.spec_l E D T F₀ := by
  let η : Env RawModel [] [.set] := (Env.empty).pushFree U
  let φQ : Formula ℒ [] [.set, .set, .set] := equality_m
    (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  let φR : Formula ℒ [] [.set, .set, .set] := membership_m
    (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  obtain ⟨Q, hQ⟩ := SecondOrderGraphFormulaRelation.exists_l hℳ φQ η K.less K.less
  obtain ⟨R, hR⟩ := SecondOrderGraphFormulaRelation.exists_l hℳ φR η K.less K.less
  have hQRead (i j : num_l ℳ) : SecondOrderPairing.relation_l Q i j ↔
      ∃ x y, value_l (ℳ := RawModel) U (code_l K i) x ∧
        value_l (ℳ := RawModel) U (code_l K j) y ∧ x = y := by
    have h := hQ i j (SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec i)
      (SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec j)
    change SecondOrderPairing.relation_l Q i j ↔
      φQ.satisfies ((η.pushFree (code_l K j)).pushFree (code_l K i)) at h
    exact h.trans (equality_formula_l _ _ _ _)
  have hRRead (i j : num_l ℳ) : SecondOrderPairing.relation_l R i j ↔
      ∃ x y, value_l (ℳ := RawModel) U (code_l K i) x ∧
        value_l (ℳ := RawModel) U (code_l K j) y ∧ member_l RawModel x y := by
    have h := hR i j (SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec i)
      (SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec j)
    change SecondOrderPairing.relation_l R i j ↔
      φR.satisfies ((η.pushFree (code_l K j)).pushFree (code_l K i)) at h
    exact h.trans (membership_formula_l _ _ _ _)
  have hUoriginal : SecondOrderFunctionObjects.map_l hℳ U K.omega A := hU
  obtain ⟨D, hD⟩ := SecondOrderModel.comprehension_l hℳ
    (Formula.truth : Formula SecondOrderSyntax.signature_m [] [.num]) rfl Env.empty
  obtain ⟨T, hT, _⟩ := SecondOrderEvaluationFixedPoint.exists_l hℳ E D Q R
  obtain ⟨F₀, hF₀, _⟩ := SecondOrderDefinableFamily.exists_l hℳ E D T
  refine ⟨D, Q, R, T, F₀, (fun n => (hD n).mpr trivial), ?_, ?_, hT, hF₀⟩
  · intro i j x y hix hjy
    constructor
    · intro hij
      obtain ⟨a, b, hia, hjb, hab⟩ := (hQRead i j).mp hij
      have ha := SecondOrderFunctionLaws.value_unique_l hℳ hUoriginal hia hix
      have hb := SecondOrderFunctionLaws.value_unique_l hℳ hUoriginal hjb hjy
      exact ha.symm.trans (hab.trans hb)
    · intro hxy
      exact (hQRead i j).mpr ⟨x, y, hix, hjy, hxy⟩
  · intro i j x y hix hjy
    constructor
    · intro hij
      obtain ⟨a, b, hia, hjb, hab⟩ := (hRRead i j).mp hij
      have ha := SecondOrderFunctionLaws.value_unique_l hℳ hUoriginal hia hix
      have hb := SecondOrderFunctionLaws.value_unique_l hℳ hUoriginal hjb hjy
      simpa only [ha, hb] using hab
    · intro hxy
      exact (hRRead i j).mpr ⟨x, y, hix, hjy, hxy⟩

#print axioms equality_formula_l
#print axioms membership_formula_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEnumeratedEvaluation
