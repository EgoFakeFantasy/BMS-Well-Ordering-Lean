import BMSConstructibleBridge.PowerlessRelativeFiniteHullDefImage
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapse
import BMSConstructibleBridge.PowerlessMemberCollapseTransport
import BMSConstructibleBridge.PowerlessMemberDefImageCoverage

/-! # 实际成员坍缩后的 Def 像检查与全部候选行

同一实际 H:I→T 先运输完整检查器，随后只对已证传递的 T 使用
纯 Δ₀ 绝对性。所有数据见证和指标覆盖因此成为原商中的真实证书。
原商外延性恢复全部 raw 候选行的精确规格，不把候选限制在 T。
指定局部母域的传递性和真实闭包还恢复全部内部赋值与全部原商指标。
这尚不识别目标行查询为原 Def，也不证明非传递 I 的 global_m。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseDefImage

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteHullDefImage (context_m matrix_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 八个实际图值只给关系证书，不从 H 抽取 Type 层映射。 -/
theorem model_l {I T H : type_l hℳ} {Δ Ε : SortContext ℒ}
    (hI : ∃ x, mem_l hℳ x I) (hT : ∃ x, mem_l hℳ x T)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) I hI) context_m Δ)
    (ξ : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT) context_m Ε)
    (h : ∀ v : Variable context_m .set,
      PowerlessMemberCollapseTransport.relation_l H (η.boundVal v) (ξ.boundVal v)) :
    (matrix_m Δ).satisfies η ↔
      (matrix_m Ε).satisfies (PowerlessRelativization.env_l ξ) := by
  -- 矩阵不读取自由参数；保留实际绑定值，避免为无用参数选择坍缩像。
  let η₀ : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) I hI) context_m [] :=
    { boundVal := η.boundVal, freeVal := fun v => nomatch v }
  let ξ₀ : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT) context_m [] :=
    { boundVal := ξ.boundVal, freeVal := fun v => nomatch v }
  have hEnv : PowerlessMemberCollapseTransport.environments_related_l
      (PowerlessMemberCollapseTransport.relation_l H) η₀ ξ₀ := by
    constructor
    · exact h
    · intro v
      nomatch v
  have hTransport := PowerlessMemberCollapseTransport.member_l
    (hI := hI) (hT := hT) H hH.2.1 hH.2.2.1 hH.2.2.2.2.1 hH.2.2.2.2.2
      (matrix_m []) η₀ ξ₀ hEnv
  have hReadI := (PowerlessRelativeFiniteHullDefImage.formula_l η).trans
    (PowerlessRelativeFiniteHullDefImage.formula_l η₀).symm
  have hReadT := (PowerlessRelativeFiniteHullDefImage.formula_l ξ₀).trans
    (PowerlessRelativeFiniteHullDefImage.formula_l ξ).symm
  exact hReadI.trans (hTransport.trans (hReadT.trans (PowerlessMemberBounded.formula_l hH.1
    (PowerlessRelativeFiniteHullDefImage.delta_l Ε) ξ)))

/-- 八个实际图值逐次在 Prop 中取得，不把像环境或 H 的图值抽为数据函数。 -/
theorem exists_l {I T H : type_l hℳ} {Δ : SortContext ℒ}
    (hI : ∃ x, mem_l hℳ x I) (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) I hI) context_m Δ)
    (h : (matrix_m Δ).satisfies η) :
    ∃ hT : ∃ x, mem_l hℳ x T,
      ∃ ξ : (Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT) context_m []),
        (∀ v : Variable context_m .set,
          PowerlessMemberCollapseTransport.relation_l H (η.boundVal v) (ξ.boundVal v)) ∧
          (matrix_m []).satisfies (PowerlessRelativization.env_l ξ) := by
  have hT : ∃ x, mem_l hℳ x T := by
    obtain ⟨a, ha⟩ := hI
    obtain ⟨b, hb, _⟩ := hH.2.1.2 a ha
    exact ⟨b, hb.1⟩
  obtain ⟨a₇, h₇, _⟩ := hH.2.1.2
    (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.here))))))))).val
    (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.here))))))))).property
  obtain ⟨a₆, h₆, _⟩ := hH.2.1.2
    (η.boundVal (.there (.there (.there (.there (.there (.there (.here)))))))).val
    (η.boundVal (.there (.there (.there (.there (.there (.there (.here)))))))).property
  obtain ⟨a₅, h₅, _⟩ := hH.2.1.2
    (η.boundVal (.there (.there (.there (.there (.there (.here))))))).val
    (η.boundVal (.there (.there (.there (.there (.there (.here))))))).property
  obtain ⟨a₄, h₄, _⟩ := hH.2.1.2
    (η.boundVal (.there (.there (.there (.there (.here)))))).val
    (η.boundVal (.there (.there (.there (.there (.here)))))).property
  obtain ⟨a₃, h₃, _⟩ := hH.2.1.2
    (η.boundVal (.there (.there (.there (.here))))).val
    (η.boundVal (.there (.there (.there (.here))))).property
  obtain ⟨a₂, h₂, _⟩ := hH.2.1.2
    (η.boundVal (.there (.there (.here)))).val
    (η.boundVal (.there (.there (.here)))).property
  obtain ⟨a₁, h₁, _⟩ := hH.2.1.2
    (η.boundVal (.there (.here))).val
    (η.boundVal (.there (.here))).property
  obtain ⟨a₀, h₀, _⟩ := hH.2.1.2
    (η.boundVal (.here)).val
    (η.boundVal (.here)).property
  let ξ : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT) context_m [] :=
    PowerlessRelativeFiniteHullDefImage.env_l Env.empty
      ⟨a₇, h₇.1⟩ ⟨a₆, h₆.1⟩ ⟨a₅, h₅.1⟩ ⟨a₄, h₄.1⟩
      ⟨a₃, h₃.1⟩ ⟨a₂, h₂.1⟩ ⟨a₁, h₁.1⟩ ⟨a₀, h₀.1⟩
  have hξ : ∀ v : Variable context_m .set,
      PowerlessMemberCollapseTransport.relation_l H (η.boundVal v) (ξ.boundVal v) := by
    intro v
    cases v with
    | here => exact h₀.2
    | there v =>
      cases v with
      | here => exact h₁.2
      | there v =>
        cases v with
        | here => exact h₂.2
        | there v =>
          cases v with
          | here => exact h₃.2
          | there v =>
            cases v with
            | here => exact h₄.2
            | there v =>
              cases v with
              | here => exact h₅.2
              | there v =>
                cases v with
                | here => exact h₆.2
                | there v =>
                  cases v with
                  | here => exact h₇.2
                  | there v => nomatch v
  exact ⟨hT, ξ, hξ, (model_l hI hT hH η ξ hξ).mp h⟩

/-- 非空分支的原商全部原查询行，不仅是已经属于 T 的候选行。 -/
theorem rows_l {ω e N F U G A D : type_l hℳ}
    (h : PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒱) ω e N F U G A D)
    (hA : ∃ x, mem_l hℳ x A) :
    ∃ Sat Seq Idx J Q : type_l hℳ,
      mem_l hℳ Sat U ∧ mem_l hℳ Seq U ∧ mem_l hℳ Idx U ∧ mem_l hℳ J U ∧ mem_l hℳ Q U ∧
        value_l (ℳ := 𝒱) G A Sat ∧
          PowerlessMemberDefImageBounded.data_l (𝒩 := 𝒱) ω e N F U A Sat Seq Idx J Q ∧
            ∀ Z : type_l hℳ, mem_l hℳ Z D ↔
              ∃ j : type_l hℳ, mem_l hℳ j J ∧
                ∀ x : type_l hℳ, mem_l hℳ x Z ↔ mem_l hℳ x A ∧
                  PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω A Seq Idx Sat j x := by
  rcases h with ⟨hEmpty, _⟩ | ⟨_, hImage⟩
  · obtain ⟨x, hx⟩ := hA
    exact False.elim (hEmpty x hx)
  · obtain ⟨Sat, hSat, Seq, hSeq, Idx, hIdx, J, hJ, Q, hQ, hG, hData, hRows⟩ := hImage
    have hFamily := (SecondOrderRowFamilyBounded.family_iff_l hℳ).mp hRows
    refine ⟨Sat, Seq, Idx, J, Q, hSat, hSeq, hIdx, hJ, hQ, hG, hData, fun Z => ?_⟩
    refine (hFamily Z).trans ⟨?_, ?_⟩
    · rintro ⟨j, hj, hRow⟩
      exact ⟨j, hj, fun x => (hRow x).trans
        (and_congr_right (fun hx => hData.2.2.2 j hj x hx))⟩
    · rintro ⟨j, hj, hRow⟩
      exact ⟨j, hj, fun x => (hRow x).trans
        (and_congr_right (fun hx => (hData.2.2.2 j hj x hx).symm))⟩

/-- 同一局部母域像中的全部原查询行，同时保留完整 Seq 与全部 raw 指标。 -/
theorem collapse_rows_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {I T H U V e N F G A D : type_l hℳ}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hI : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I)
    (hU : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) U)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) U)
    (hUI : mem_l hℳ U I) (hUV : SecondOrderFunctionObjects.value_l hℳ H U V)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (hω : mem_l hℳ K.omega I) (hωU : mem_l hℳ K.omega U)
    (hAV : mem_l hℳ A V)
    (h : PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒱) K.omega e N F V G A D)
    (hA : ∃ x, mem_l hℳ x A) :
    ∃ R S P J Q : type_l hℳ,
      mem_l hℳ R V ∧ mem_l hℳ S V ∧ mem_l hℳ P V ∧ mem_l hℳ J V ∧ mem_l hℳ Q V ∧
        value_l (ℳ := 𝒱) G A R ∧
          PowerlessMemberDefImageBounded.data_l (𝒩 := 𝒱) K.omega e N F V A R S P J Q ∧
            PowerlessMemberDefImageCoverage.spec_l (𝒩 := 𝒱) K.omega e N F A R S P J Q ∧
              ∀ Z : type_l hℳ, mem_l hℳ Z D ↔
                ∃ j : type_l hℳ, mem_l hℳ j J ∧
                  ∀ x : type_l hℳ, mem_l hℳ x Z ↔ mem_l hℳ x A ∧
                    PowerlessRelativeClassSatisfactionAllSlots.query_l
                      (ℳ₀ := 𝒱) K.omega A S P R j x := by
  obtain ⟨R, S, P, J, Q, hR, hS, hP, hJ, hQ, hG, hData, hRows⟩ := rows_l h hA
  exact ⟨R, S, P, J, Q, hR, hS, hP, hJ, hQ, hG, hData,
    PowerlessMemberDefImageCoverage.collapse_l K hH hI hU hTrans hUI hUV
      hωI hω hωU hAV hP hData, hRows⟩

#print axioms model_l
#print axioms exists_l
#print axioms rows_l
#print axioms collapse_rows_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseDefImage
