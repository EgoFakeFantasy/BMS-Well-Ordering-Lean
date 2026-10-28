import BMSConstructibleBridge.PowerlessRelativeCutoffLocalDefGraph
import BMSConstructibleBridge.PowerlessRelativeCutoffInnerLimits
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryBudgetSyntax
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryBudgetProvider
import BMSConstructibleBridge.PowerlessRelativeOrdinalBudgetCountability

/-! # 截断内的局部轻量前史预算起点

纯隶属 ℒ 对象句经原图翻译回到原 Z₂ 的普通 Derives。局部图
D:U→U、U 和基集 B 已是 W=LΩ[B] 的真实成员时，实际构造
ξ∈Ω 的非零极限起始层 C，同时容纳 B、D、U 及指标序数 A。
原规范尾函数随后产生同一真实预算 Q，其完整预算字段和全部
实际轻量前史的预算层成员界一起保留在对象结论中。对同一规范图
的全部实际输出证明严格低于 Ω，不把任意预算证书的字段误当可数性。

这里以局部 U 而非整体 W 作前史陪域。严格尾界来自真实 Class
二维尾图及可数性证明；配合预算总性可将给定完整前史放入 W。
实际前史存在由调用端建设，不声称完整 Collection 或 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffHistoryBudget

open Logic FirstOrder SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def bounds_l (Ω Q : type_l hℳ) : Prop :=
  ∀ a δ, ThirdOrderSemantics.value_l (ℳ := 𝒱) Q a δ → mem_l hℳ δ Ω

/-- 同一预算在目标指标有值，严格尾界把真实完整历史送入截断层。 -/
theorem member_l {B Ω W U D β Q A f : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hBudget : PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ B D U β Q)
    (hBound : bounds_l Ω Q)
    (hPoint : PowerlessHierarchyLightHistoryBudgetInduction.point_l hℳ B D U Q A)
    (hAβ : mem_l hℳ A β) (hf : PowerlessHierarchyLightHistory.history_l hℳ B D A U f) :
    mem_l hℳ f W := by
  obtain ⟨δ, hQδ⟩ := hBudget.total A hAβ
  obtain ⟨E, hE⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase
    (hBudget.output_ordinal A δ hQδ)
  exact (PowerlessRelativeLevelClosure.subset_l hℳ hBase (hBound A δ hQδ) hE hW) f
    (hPoint δ E f hQδ hE hf)

/-- 先前层的共同参数界实际低于 Ω，预算图本身仍只需为 raw 图。 -/
theorem exists_l (K : source_coding_l hℳ) {B ω Ω W U D A : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hBW : mem_l hℳ B W) (hUW : mem_l hℳ U W) (hDW : mem_l hℳ D W)
    (hGraph : PowerlessRelativeCofinalDefGraph.graph_l U D) (hAΩ : mem_l hℳ A Ω) :
    ∃ ξ C Q : type_l hℳ, mem_l hℳ ξ Ω ∧
      PowerlessRelativeHierarchySemantics.limit_l hℳ ξ ∧
        PowerlessRelativeHierarchySemantics.level_l hℳ B ξ C ∧
          mem_l hℳ B C ∧ mem_l hℳ D C ∧ mem_l hℳ U C ∧ mem_l hℳ A C ∧
            PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ B D U A Q ∧
              bounds_l Ω Q ∧
                ∀ a, PowerlessHierarchyLightHistoryBudgetInduction.point_l hℳ B D U Q a := by
  have hA : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) A := by
    apply SetTheory.Structure.IsOrdinal.mem hΩ.1
    exact hAΩ
  have hAW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW A hAΩ
  have hOuter := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  let η : Env 𝒱 [] [.set, .set, .set, .set] :=
    (((Env.empty.pushFree A).pushFree U).pushFree D).pushFree B
  have hParams : ∀ s (v : Variable ([.set, .set, .set, .set] : SortContext ℒ) s),
      mem_l hℳ (η.freeVal v) W := by
    intro s v
    cases s
    match v with
    | .here => exact hBW
    | .there .here => exact hDW
    | .there (.there .here) => exact hUW
    | .there (.there (.there .here)) => exact hAW
  obtain ⟨a, c, haΩ, hc, _hUc, hValues⟩ :=
    PowerlessRelativeLimitParameterBounds.exists_l hBase hOuter hW η hUW hParams
  obtain ⟨ξ, hξ, haξ, hξΩ, hLimit⟩ :=
    PowerlessRelativeCutoffInnerLimits.exists_l K hBase hω hΩ haΩ
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hξ
  have hLift := PowerlessRelativeLevelClosure.subset_l hℳ hBase haξ hc hC
  have hBC : mem_l hℳ B C := hLift B (hValues _ .here)
  have hDC : mem_l hℳ D C := hLift D (hValues _ (.there .here))
  have hUC : mem_l hℳ U C := hLift U (hValues _ (.there (.there .here)))
  have hAC : mem_l hℳ A C := hLift A (hValues _ (.there (.there (.there .here))))
  obtain ⟨Ξ, hΞ⟩ := SecondOrderQuotient.surj_l hℳ ξ
  obtain ⟨S, hSGraph⟩ := SecondOrderValidRootGraph.exists_l hℳ Ξ.real
  have hS (n : SecondOrderModel.num_l ℳ) : SecondOrderDomain.wf_l S n :=
    SecondOrderValidRootGraph.wf_l hSGraph n
  have hEq : SecondOrderOrdinalBudgetOrder.base_l hℳ hS Ξ.root = ξ :=
    ((SecondOrderQuotient.eq_iff_l hℳ Ξ ⟨S, Ξ.root, hS Ξ.root⟩).mpr
      (SecondOrderValidRootGraph.agrees_l hℳ hSGraph Ξ.root Ξ.wf)).symm.trans hΞ
  obtain ⟨A₀, hA₀⟩ := SecondOrderQuotient.surj_l hℳ A
  have hOrdinal : SetTheory.Structure.IsOrdinal (SecondOrderOrdinalBudgetOrder.quotient_l hℳ)
      (mk_l hℳ A₀) := hA₀.symm ▸ hA
  have hAStart : mem_l hℳ (mk_l hℳ A₀) C := hA₀.symm ▸ hAC
  let two : SecondOrderModel.num_l ℳ :=
    SecondOrderModel.succ_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))
  obtain ⟨Q₀, N, R, G, hQ₀, hN, hR, hG, _Y, Q, _hMap, hRead⟩ :=
    SecondOrderOrdinalBudgetFunction.exists_l hℳ S Ξ.root hS A₀ two
  have hBudget₀ := PowerlessHierarchyLightHistoryBudgetProvider.budget_of_tail_l hℳ hBase
    A₀ hOrdinal hS hQ₀ hN hR hG hEq hLimit hC hBC hDC hUC hAStart hRead
  have hBudget : PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ B D U A Q := by
    simpa only [hA₀] using hBudget₀
  have hΩK : PowerlessRelativeOrdinalCutoff.first_l B K.omega Ω :=
    (SecondOrderOmega.unique_l hℳ hω K.omega_spec) ▸ hΩ
  have hBound : bounds_l Ω Q := by
    intro a δ haδ
    obtain ⟨n, hn, _, hδ⟩ := (hRead a δ).mp haδ
    have hTail := PowerlessRelativeOrdinalBudgetCountability.below_l (hBase := hBase)
      K A₀ hQ₀ hN hR hG hS hOrdinal (hEq.symm ▸ hξ) (hEq.symm ▸ hLimit)
      hΩK (hA₀.symm ▸ hAΩ) (hEq.symm ▸ hξΩ) n two hn
    exact hδ.symm ▸ hTail
  exact ⟨ξ, C, Q, hξΩ, hLimit, hC, hBC, hDC, hUC, hAC, hBudget, hBound,
    PowerlessHierarchyLightHistoryBudgetInduction.bounded_l hℳ K hBase hGraph.2 hBudget⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))

def bounds_m {Γ Δ : SortContext ℒ} (Ω Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .imp
    (value_m (up (up Q)) (.bvar (.there .here)) (.bvar .here))
    (member_m (.bvar .here) (up (up Ω)))

theorem bounds_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (Ω Q : Term ℒ Γ Δ .set) :
    (bounds_m Ω Q).satisfies η ↔ bounds_l (Ω.eval η) (Q.eval η) := by
  simp only [bounds_m, bounds_l, Formula.satisfies, ThirdOrderSemantics.value_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def result_m {Γ Δ : SortContext ℒ} (B Ω U D A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let ξ : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let C : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let Q : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .conj (member_m ξ (up₃ Ω)) <|
      .conj (PowerlessRelativeHierarchySyntax.limit_m ξ) <|
        .conj (PowerlessRelativeHierarchySyntax.level_m (up₃ B) ξ C) <|
          .conj (member_m (up₃ B) C) <| .conj (member_m (up₃ D) C) <|
            .conj (member_m (up₃ U) C) <| .conj (member_m (up₃ A) C) <|
              .conj (PowerlessHierarchyLightHistoryBudgetSyntax.budget_m
                (up₃ B) (up₃ D) (up₃ U) (up₃ A) Q) <|
                .conj (bounds_m (up₃ Ω) Q) <| .forallE .set <|
                  PowerlessHierarchyLightHistoryBudgetInduction.point_m
                  (up (up₃ B)) (up (up₃ D)) (up (up₃ U)) (up Q) (.bvar .here)

theorem result_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B Ω U D A : Term ℒ Γ Δ .set) :
    (result_m B Ω U D A).satisfies η ↔ ∃ ξ C Q : type_l hℳ,
      mem_l hℳ ξ (Ω.eval η) ∧ PowerlessRelativeHierarchySemantics.limit_l hℳ ξ ∧
        PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) ξ C ∧
          mem_l hℳ (B.eval η) C ∧ mem_l hℳ (D.eval η) C ∧
            mem_l hℳ (U.eval η) C ∧ mem_l hℳ (A.eval η) C ∧
              PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ
                (B.eval η) (D.eval η) (U.eval η) (A.eval η) Q ∧
                  bounds_l (Ω.eval η) Q ∧
                    ∀ a, PowerlessHierarchyLightHistoryBudgetInduction.point_l hℳ
                    (B.eval η) (D.eval η) (U.eval η) Q a := by
  simp only [result_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessHierarchyLightHistoryBudgetSyntax.budget_formula_l K,
    bounds_formula_l,
    PowerlessHierarchyLightHistoryBudgetInduction.point_formula_l hℳ K,
    member_m, Arguments.eval, up₃, up, Term.eval_weakenBound, Term.eval,
    SecondOrderQuotient.structure_l]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let Ω := .fvar (.there (.there .here))
  let W := .fvar (.there (.there (.there .here)))
  let U := .fvar (.there (.there (.there (.there .here))))
  let D := .fvar (.there (.there (.there (.there (.there .here)))))
  let A := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
          .imp (member_m B W) <| .imp (member_m U W) <| .imp (member_m D W) <|
            .imp (PowerlessRelativeCofinalDefGraph.graph_m U D) <|
              .imp (member_m A Ω) (result_m B Ω U D A)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeCofinalDefGraph.graph_formula_l K, result_formula_l K,
    member_m, Arguments.eval, Term.eval, SecondOrderQuotient.structure_l]
  exact fun hBase hω hΩ hW hBW hUW hDW hGraph hAΩ =>
    exists_l K hBase hω hΩ hW hBW hUW hDW hGraph hAΩ

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffHistoryBudget
