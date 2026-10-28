import BMSConstructibleBridge.PowerlessRelativeCutoffLocalHistoryBudget

/-! # 首 Ω 层中任意对象的实际较早前史覆盖

对象语言为纯隶属 ℒ，背景为原 Z₂，正式出口仍是原推导核的图翻译句。
对每个 x∈W，先在原极限层取得 x∈Lₐ[B]，再把该阶段放入严格较早
的实际前史。前史值的原层唯一性识别同一个输出，不把 x∈U 误用为
x 属于指定前史的某个阶段。所有七个实际见证均有 W 成员证据；f
保留原同见证捕获证书，完整原 Def 后继与精确极限并没有替换。

这是源 W 中的统一存在式，不声称见证已属于某个共同域 I。后续须
在同一反射族中捕获该式并读回原规格；全局弱凝聚、Collection、
无首 Ω 分支和最终 hSources 仍未完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffHistoryCoverage

open Logic FirstOrder SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₇ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  up (up (up (up (up (up (up t))))))

/-- 原前史点、全部实际成员界和原捕获证书，均指向同一组见证。 -/
def point_l (B ω Ω W x a y A β U D f : type_l hℳ) : Prop :=
  mem_l hℳ a W ∧ mem_l hℳ y W ∧ mem_l hℳ A W ∧ mem_l hℳ β W ∧
  mem_l hℳ U W ∧ mem_l hℳ D W ∧ mem_l hℳ f W ∧
  mem_l hℳ a A ∧ mem_l hℳ a Ω ∧ mem_l hℳ A Ω ∧ mem_l hℳ β Ω ∧ mem_l hℳ A β ∧
  PowerlessRelativeHierarchySemantics.limit_l hℳ β ∧
  PowerlessRelativeCofinalLimitBounds.cofinal_l β ∧
  PowerlessRelativeHierarchySemantics.level_l hℳ B β U ∧
  mem_l hℳ B U ∧ mem_l hℳ x U ∧ mem_l hℳ ω U ∧
  PowerlessRelativeCofinalDefGraph.graph_l U D ∧
  PowerlessRelativeHierarchySemantics.history_l hℳ B A f U ∧
  PowerlessHierarchyLightHistory.history_l hℳ B D A U f ∧
  PowerlessRelativeCutoffLocalHistoryBudget.capture_l hℳ B D A U W f ∧
  PowerlessRelativeHierarchySemantics.level_l hℳ B a y ∧
  SecondOrderFunctionObjects.value_l hℳ f a y ∧ mem_l hℳ x y

def point_m {Γ Δ : SortContext ℒ} (B ω Ω W x a y A β U D f : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ :=
  .conj (member_m a W) <| .conj (member_m y W) <| .conj (member_m A W) <|
  .conj (member_m β W) <| .conj (member_m U W) <| .conj (member_m D W) <|
  .conj (member_m f W) <| .conj (member_m a A) <| .conj (member_m a Ω) <|
  .conj (member_m A Ω) <| .conj (member_m β Ω) <| .conj (member_m A β) <|
  .conj (PowerlessRelativeHierarchySyntax.limit_m β) <|
  .conj (PowerlessRelativeCofinalLimitBounds.cofinal_m β) <|
  .conj (PowerlessRelativeHierarchySyntax.level_m B β U) <|
  .conj (member_m B U) <| .conj (member_m x U) <| .conj (member_m ω U) <|
  .conj (PowerlessRelativeCofinalDefGraph.graph_m U D) <|
  .conj (PowerlessRelativeHierarchySyntax.history_m B A f U) <|
  .conj (PowerlessHierarchyLightHistory.formula_m B D A U f) <|
  .conj (PowerlessRelativeCutoffLocalHistoryBudget.capture_m B D A U W f) <|
  .conj (PowerlessRelativeHierarchySyntax.level_m B a y) <|
  .conj (value_m f a y) (member_m x y)

theorem point_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (B ω Ω W x a y A β U D f : Term ℒ Γ Δ .set) :
    (point_m B ω Ω W x a y A β U D f).satisfies η ↔
      point_l (B.eval η) (ω.eval η) (Ω.eval η) (W.eval η) (x.eval η)
        (a.eval η) (y.eval η) (A.eval η) (β.eval η) (U.eval η) (D.eval η) (f.eval η) := by
  simp only [point_m, point_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeCofinalLimitBounds.cofinal_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeCofinalDefGraph.graph_formula_l K,
    PowerlessRelativeHierarchySemantics.history_formula_l K,
    PowerlessHierarchyLightHistory.reading_formula_l hℳ,
    PowerlessRelativeCutoffLocalHistoryBudget.capture_formula_l hℳ,
    ThirdOrderSemantics.value_formula_l, member_m, Arguments.eval,
    SecondOrderQuotient.structure_l]
  rfl

def result_m {Γ Δ : SortContext ℒ} (B ω Ω W x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
  .existsE .set <| .existsE .set <| .existsE .set <|
  let f : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
  let D := .bvar (.there .here)
  let U := .bvar (.there (.there .here))
  let β := .bvar (.there (.there (.there .here)))
  let A := .bvar (.there (.there (.there (.there .here))))
  let y := .bvar (.there (.there (.there (.there (.there .here)))))
  let a := .bvar (.there (.there (.there (.there (.there (.there .here))))))
  point_m (up₇ B) (up₇ ω) (up₇ Ω) (up₇ W) (up₇ x) a y A β U D f

theorem result_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B ω Ω W x : Term ℒ Γ Δ .set) :
    (result_m B ω Ω W x).satisfies η ↔ ∃ a y A β U D f : type_l hℳ,
      point_l (B.eval η) (ω.eval η) (Ω.eval η) (W.eval η) (x.eval η) a y A β U D f := by
  simp only [result_m, Formula.satisfies, point_formula_l K, up₇, up,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

/-- 任意源对象由同一个真实前史点覆盖；所有见证实际位于 W。 -/
theorem exists_l (K : source_coding_l hℳ) {B ω Ω W x : type_l hℳ}
    (hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hBW : mem_l hℳ B W) (hx : mem_l hℳ x W) :
    ∃ a y A β U D f : type_l hℳ, point_l B ω Ω W x a y A β U D f := by
  have hOuter := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  obtain ⟨a, c, haΩ, hc, hxc⟩ :=
    (PowerlessRelativeLimitClosure.value_l hℳ hBase hOuter hW x).mp hx
  obtain ⟨A, hAΩ, haA⟩ := hOuter.2 a haΩ
  obtain ⟨β, U, D, hβΩ, hAβ, hLimit, hCofinal, hU, hUW, hBU, hxU, hωU,
    hDW, hGraph, _hParams, ⟨f, hf, hLight, hfW, hCapture⟩, _hBudget⟩ :=
    PowerlessRelativeCutoffLocalHistoryBudget.exists_l K hBase hω hΩ hW hBW hx hAΩ
      Env.empty (fun _ v => nomatch v)
  have hA : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) A := by
    apply SetTheory.Structure.IsOrdinal.mem hΩ.1
    exact hAΩ
  obtain ⟨y, ⟨hyU, hy⟩, _hUnique⟩ := hf.1.2 a haA
  have hyLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B a y :=
    ⟨A, f, U, hA, haA, hf, hy⟩
  have hcy := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hc hyLevel
  have haW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW a haΩ
  have hAW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW A hAΩ
  have hβW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW β hβΩ
  have hyW := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW U hUW y hyU
  exact ⟨a, y, A, β, U, D, f, haW, hyW, hAW, hβW, hUW, hDW, hfW,
    haA, haΩ, hAΩ, hβΩ, hAβ, hLimit, hCofinal, hU, hBU, hxU, hωU, hGraph,
    hf, hLight, hCapture, hyLevel, hy, hcy ▸ hxc⟩

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let Ω := .fvar (.there (.there .here))
  let W := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
  .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
  .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
  .imp (member_m B W) <| .forallE .set <| .imp (member_m (.bvar .here) (up W))
    (result_m (up B) (up ω) (up Ω) (up W) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K, result_formula_l K,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    SecondOrderQuotient.structure_l, Env.pushBound_bound_here]
  exact fun hBase hω hΩ hW hBW x hx => exists_l K hBase hω hΩ hW hBW hx

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffHistoryCoverage
