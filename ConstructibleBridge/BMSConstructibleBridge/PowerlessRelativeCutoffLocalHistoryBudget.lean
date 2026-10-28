import BMSConstructibleBridge.PowerlessRelativeCutoffHistoryBudget
import BMSConstructibleBridge.PowerlessRelativeLayerHistoryPrefix
import BMSConstructibleBridge.PowerlessRelativeFiniteHullHistory

/-! # 同一局部 Def 图与严格较早前史预算的共同对象存在

纯隶属 ℒ 的外部有限参数模式，经原图翻译取得原 Z₂ Derives。
从实际截断、候选 X 和指标 A∈Ω 构造同一 β/U/D，其中 A∈β，
实际限制出 A 上的原／轻量历史，再以该 D 的完整 Def 读数构造预算。
不把前一模块的 U、D、图规格、历史或
预算证书加回用户前提；全部存在量词共用同一装配环境。

输出保留严格较早起点、全部实际预算输出低于 Ω，并将同一真实
原／轻量前史放入外层 W。此同一前史还可被两式有限元素性捕获，
但完整 Def 截迹、最终 hSources 和 Collection 未闭合。
预算域取 β 而非 A：A∈β 才保证同一 Q 在 A 上有预算值，避免
只覆盖 A 的前驱而无法给完整 A 历史读出成员界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffLocalHistoryBudget

open Logic FirstOrder SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₃ {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) := up (up (up t))

private def binding_m {Γ Θ : SortContext ℒ} (I W : Term ℒ Γ Θ .set) :
    Substitution ℒ [] [.set, .set] Γ Θ :=
  .map (fun v => nomatch v) (fun {s} v => match s with
    | .set => match v with
      | .here => I
      | .there .here => W)

/-- 域参数代入两式原公式族；不把 I 或 W 假设为域内对象。 -/
def elementary_m {Γ Θ : SortContext ℒ} (I W : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  (PowerlessRelativeFiniteElementarity.form_m
    (PowerlessRelativeFiniteHullHistory.family_m []) (.fvar .here) (.fvar (.there .here))
      (fun v => nomatch v)).substitute (binding_m I W)

theorem elementary_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Θ : SortContext ℒ} (η : Env 𝒩 Γ Θ) (I W : Term ℒ Γ Θ .set) :
    (elementary_m I W).satisfies η ↔
      (PowerlessRelativeFiniteElementarity.form_m (PowerlessRelativeFiniteHullHistory.family_m [])
        (.fvar .here) (.fvar (.there .here)) (fun v => nomatch v)).satisfies
          ((Env.empty.pushFree (W.eval η)).pushFree (I.eval η)) := by
  rw [elementary_m, Formula.satisfies_substitute]
  have hη : η.pullback (binding_m I W) =
      (Env.empty.pushFree (W.eval η)).pushFree (I.eval η) := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => nomatch v
  rw [hη]

def capture_m {Γ Θ : SortContext ℒ} (B D A U W f : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .forallE .set <|
    let I : Term ℒ (.set :: Γ) Θ .set := .bvar .here
    .imp (ThirdOrderTheory.subset_m I (up W)) <|
      .imp (member_m (up B) I) <| .imp (member_m (up D) I) <|
        .imp (member_m (up A) I) <| .imp (member_m (up U) I) <|
          .imp (elementary_m I (up W)) (member_m (up f) I)

def capture_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B D A U W f : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ I, ThirdOrderSemantics.subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I W →
    SecondOrderQuotient.mem_l hℳ B I → SecondOrderQuotient.mem_l hℳ D I →
      SecondOrderQuotient.mem_l hℳ A I → SecondOrderQuotient.mem_l hℳ U I →
        (PowerlessRelativeFiniteElementarity.form_m (PowerlessRelativeFiniteHullHistory.family_m [])
          (.fvar .here) (.fvar (.there .here)) (fun v => nomatch v)).satisfies
            ((Env.empty.pushFree W).pushFree I) → SecondOrderQuotient.mem_l hℳ f I

theorem capture_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Θ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Θ)
    (B D A U W f : Term ℒ Γ Θ .set) :
    (capture_m B D A U W f).satisfies η ↔
      capture_l hℳ (B.eval η) (D.eval η) (A.eval η) (U.eval η) (W.eval η) (f.eval η) := by
  simp only [capture_m, capture_l, Formula.satisfies, ThirdOrderSemantics.subset_formula_l,
    elementary_formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    SecondOrderQuotient.structure_l]
  rfl

def history_m {Γ Θ : SortContext ℒ} (B A U D W : Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .existsE .set <| .conj
    (PowerlessRelativeHierarchySyntax.history_m (up B) (up A) (.bvar .here) (up U)) <|
    .conj (PowerlessHierarchyLightHistory.formula_m (up B) (up D) (up A) (up U) (.bvar .here))
      (.conj (member_m (.bvar .here) (up W))
        (capture_m (up B) (up D) (up A) (up U) (up W) (.bvar .here)))

theorem history_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} (K : source_coding_l hℳ)
    {Γ Θ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Θ)
    (B A U D W : Term ℒ Γ Θ .set) :
    (history_m B A U D W).satisfies η ↔ ∃ f : SecondOrderQuotient.type_l hℳ,
      PowerlessRelativeHierarchySemantics.history_l hℳ (B.eval η) (A.eval η) f (U.eval η) ∧
        PowerlessHierarchyLightHistory.history_l hℳ
          (B.eval η) (D.eval η) (A.eval η) (U.eval η) f ∧
            SecondOrderQuotient.mem_l hℳ f (W.eval η) ∧
              capture_l hℳ (B.eval η) (D.eval η) (A.eval η) (U.eval η) (W.eval η) f := by
  simp only [history_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.history_formula_l K,
    PowerlessHierarchyLightHistory.reading_formula_l hℳ, capture_formula_l hℳ, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval, SecondOrderQuotient.structure_l]
  rfl

def result_m {Γ Θ Δ : SortContext ℒ} (B ω Ω W X A : Term ℒ Γ Θ .set)
    (τ : VariableSubstitution ℒ Δ Γ Θ) : Formula ℒ Γ Θ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let β : Term ℒ (.set :: .set :: .set :: Γ) Θ .set := .bvar (.there (.there .here))
    let U : Term ℒ (.set :: .set :: .set :: Γ) Θ .set := .bvar (.there .here)
    let D : Term ℒ (.set :: .set :: .set :: Γ) Θ .set := .bvar .here
    .conj (member_m β (up₃ Ω)) <| .conj (member_m (up₃ A) β) <|
      .conj (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .conj (PowerlessRelativeCofinalLimitBounds.cofinal_m β) <|
          .conj (PowerlessRelativeHierarchySyntax.level_m (up₃ B) β U) <|
            .conj (member_m U (up₃ W)) <| .conj (member_m (up₃ B) U) <|
              .conj (member_m (up₃ X) U) <|
              .conj (member_m (up₃ ω) U) <| .conj (member_m D (up₃ W)) <|
                .conj (PowerlessRelativeCofinalDefGraph.graph_m U D) <|
                  .conj (parameters_m Δ U (fun v => up₃ (τ v))) <|
                    .conj (history_m (up₃ B) (up₃ A) U D (up₃ W))
                      (PowerlessRelativeCutoffHistoryBudget.result_m (up₃ B) (up₃ Ω) U D β)

def schema_m {Θ Δ : SortContext ℒ} (B ω Ω W X A : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
          .imp (member_m B W) <| .imp (member_m X W) <| .imp (member_m A Ω) <|
            .imp (parameters_m Δ W τ) (result_m B ω Ω W X A τ)

def sentence_m {Θ Δ : SortContext ℒ} (B ω Ω W X A : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω Ω W X A τ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 两个实际较早序数具有同一个严格较大的共尾极限界。 -/
private theorem common_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {B ω Ω a b : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (haΩ : SecondOrderQuotient.mem_l hℳ a Ω) (hbΩ : SecondOrderQuotient.mem_l hℳ b Ω) :
    ∃ γ : SecondOrderQuotient.type_l hℳ,
      SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
        (SecondOrderQuotient.structure_l hℳ)) γ ∧
      SecondOrderQuotient.mem_l hℳ γ Ω ∧ SecondOrderQuotient.mem_l hℳ a γ ∧
        SecondOrderQuotient.mem_l hℳ b γ ∧ PowerlessRelativeHierarchySemantics.limit_l hℳ γ ∧
          PowerlessRelativeCofinalLimitBounds.cofinal_l γ := by
  have ha : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) a := by
    apply SetTheory.Structure.IsOrdinal.mem hΩ.1
    exact haΩ
  have hb : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) b := by
    apply SetTheory.Structure.IsOrdinal.mem hΩ.1
    exact hbΩ
  rcases SecondOrderOrdinalComparison.compare_l hℳ ha hb with h | h | h
  · obtain ⟨γ, hγ, hγΩ, hbγ, hLimit, hCofinal⟩ :=
      PowerlessRelativeCutoffCofinalLimits.exists_l K hBase hω hΩ hbΩ
    exact ⟨γ, hγ, hγΩ, h.symm ▸ hbγ, hbγ, hLimit, hCofinal⟩
  · obtain ⟨γ, hγ, hγΩ, hbγ, hLimit, hCofinal⟩ :=
      PowerlessRelativeCutoffCofinalLimits.exists_l K hBase hω hΩ hbΩ
    exact ⟨γ, hγ, hγΩ, hγ.transitive b hbγ a h, hbγ, hLimit, hCofinal⟩
  · obtain ⟨γ, hγ, hγΩ, haγ, hLimit, hCofinal⟩ :=
      PowerlessRelativeCutoffCofinalLimits.exists_l K hBase hω hΩ haΩ
    exact ⟨γ, hγ, hγΩ, haγ, hγ.transitive a haγ b h, hLimit, hCofinal⟩

/-- 实际较早前史、严格成员界与同见证捕获证书；对象出口复用此证明。 -/
theorem exists_l {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    (K : source_coding_l hℳ) {B ω Ω W X A : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hBW : SecondOrderQuotient.mem_l hℳ B W) (hX : SecondOrderQuotient.mem_l hℳ X W)
    (hAΩ : SecondOrderQuotient.mem_l hℳ A Ω)
    {Δ : SortContext ℒ} (ν : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (hParams : ∀ s (v : Variable Δ s), SecondOrderQuotient.mem_l hℳ (ν.freeVal v) W) :
    ∃ β U D : SecondOrderQuotient.type_l hℳ,
      SecondOrderQuotient.mem_l hℳ β Ω ∧ SecondOrderQuotient.mem_l hℳ A β ∧
        PowerlessRelativeHierarchySemantics.limit_l hℳ β ∧
        PowerlessRelativeCofinalLimitBounds.cofinal_l β ∧
        PowerlessRelativeHierarchySemantics.level_l hℳ B β U ∧
        SecondOrderQuotient.mem_l hℳ U W ∧ SecondOrderQuotient.mem_l hℳ B U ∧
        SecondOrderQuotient.mem_l hℳ X U ∧ SecondOrderQuotient.mem_l hℳ ω U ∧
        SecondOrderQuotient.mem_l hℳ D W ∧ PowerlessRelativeCofinalDefGraph.graph_l U D ∧
        (∀ s (v : Variable Δ s), SecondOrderQuotient.mem_l hℳ (ν.freeVal v) U) ∧
        (∃ f : SecondOrderQuotient.type_l hℳ,
          PowerlessRelativeHierarchySemantics.history_l hℳ B A f U ∧
          PowerlessHierarchyLightHistory.history_l hℳ B D A U f ∧
          SecondOrderQuotient.mem_l hℳ f W ∧ capture_l hℳ B D A U W f) ∧
        ∃ ξ C Q : SecondOrderQuotient.type_l hℳ,
          SecondOrderQuotient.mem_l hℳ ξ Ω ∧ PowerlessRelativeHierarchySemantics.limit_l hℳ ξ ∧
          PowerlessRelativeHierarchySemantics.level_l hℳ B ξ C ∧
          SecondOrderQuotient.mem_l hℳ B C ∧ SecondOrderQuotient.mem_l hℳ D C ∧
          SecondOrderQuotient.mem_l hℳ U C ∧ SecondOrderQuotient.mem_l hℳ β C ∧
          PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ B D U β Q ∧
          PowerlessRelativeCutoffHistoryBudget.bounds_l Ω Q ∧
          ∀ a, PowerlessHierarchyLightHistoryBudgetInduction.point_l hℳ B D U Q a := by
  have hAll : ∀ s (v : Variable (.set :: Δ) s),
      SecondOrderQuotient.mem_l hℳ ((ν.pushFree B).freeVal v) W := by
    intro s v
    cases s
    cases v with
    | here => exact hBW
    | there v => exact hParams _ v
  obtain ⟨β, U, _D, hβΩ, _hInner, _hCofinal, hU, _hUW, hXU, hωU, _hDW, _hGraph, hValues⟩ :=
    PowerlessRelativeCutoffLocalDefGraph.exists_l K hBase hω hΩ hW hX
      (ν.pushFree B) hAll
  obtain ⟨γ, hγ, hγΩ, hβγ, hAγ, hInner, hCofinal⟩ :=
    common_l hℳ K hBase hω hΩ hβΩ hAΩ
  obtain ⟨V, hV⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hγ
  have hLift := PowerlessRelativeLevelClosure.subset_l hℳ hBase hβγ hU hV
  have hVW := PowerlessRelativeLevelClosure.members_l hℳ hBase hγΩ hV hW
  have hωV := hLift ω hωU
  have hKωV : SecondOrderQuotient.mem_l hℳ K.omega V :=
    (SecondOrderOmega.unique_l hℳ hω K.omega_spec) ▸ hωV
  obtain ⟨F, hFW, hGraph⟩ := PowerlessRelativeCofinalDefGraph.exists_l K
    hBase hInner hV hCofinal hKωV
    (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hW hγΩ
  obtain ⟨ξ, C, Q, hξΩ, hLimit, hC, hBC, hDC, hVC, hγC, hBudget, hBound, hPoint⟩ :=
    PowerlessRelativeCutoffHistoryBudget.exists_l K
      hBase hω hΩ hW hBW hVW hFW hGraph hγΩ
  refine ⟨γ, V, F, hγΩ, hAγ, hInner, hCofinal, hV, hVW,
    hLift B (hValues _ .here), hLift X hXU, hωV, hFW, hGraph,
    (fun _ v => hLift (ν.freeVal v) (hValues _ (.there v))), ?_, ?_⟩
  · obtain ⟨f, hf, hLight⟩ := PowerlessRelativeLayerHistoryPrefix.exists_l hBase hV hAγ hGraph
    have hfW := PowerlessRelativeCutoffHistoryBudget.member_l hBase hW
      hBudget hBound (hPoint A) hAγ hLight
    refine ⟨f, hf, hLight, hfW, ?_⟩
    intro I hIW hBI hDI hAI hUI h
    let ζ : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set] :=
      (Env.empty.pushFree W).pushFree I
    exact PowerlessRelativeFiniteHullHistory.member_l hℳ (Δ := [])
      (I₀ := I) (W₀ := W) (B := B) (D := F) (A := A) (U := V) (f := f)
      ζ (.fvar .here) (.fvar (.there .here))
      (fun v => nomatch v) Env.empty (fun v => nomatch v) (fun v => nomatch v)
      rfl rfl (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW)
      hIW hBI hDI hAI hUI h hGraph (SetTheory.Structure.IsOrdinal.mem hΩ.1 hAΩ) hf hfW
  · exact ⟨ξ, C, Q, hξΩ, hLimit, hC, hBC, hDC, hVC, hγC, hBudget, hBound, hPoint⟩

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (B ω Ω W X A : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) :
    (sentence_m B ω Ω W X A τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, result_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeCofinalLimitBounds.cofinal_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeCofinalDefGraph.graph_formula_l K, parameters_formula_l,
    history_formula_l K,
    PowerlessRelativeCutoffHistoryBudget.result_formula_l K,
    member_m, Arguments.eval, up₃, up, Term.eval_weakenBound, Term.eval,
    SecondOrderQuotient.structure_l]
  intro hBase hω hΩ hW hBW hX hAΩ hParams
  let ν : Env (SecondOrderQuotient.structure_l hℳ) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (τ v).eval η }
  exact exists_l K hBase hω hΩ hW hBW hX hAΩ ν hParams

theorem derives_m {Θ Δ : SortContext ℒ} (B ω Ω W X A : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω Ω W X A τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω Ω W X A τ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffLocalHistoryBudget
