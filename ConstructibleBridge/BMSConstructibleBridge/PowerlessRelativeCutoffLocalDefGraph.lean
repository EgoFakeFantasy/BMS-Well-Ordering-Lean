import BMSConstructibleBridge.PowerlessRelativeCutoffCofinalLimits
import BMSConstructibleBridge.PowerlessRelativeCutoffLimit
import BMSConstructibleBridge.PowerlessRelativeCofinalDefGraph
import BMSConstructibleBridge.PowerlessRelativeLimitParameterBounds
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives

/-! # 截断内同时容纳有限参数的局部 Def 图

对象语言是纯隶属 ℒ，背景是原 Z₂，出口为原图翻译的普通 Derives。
给定实际首不可数 Ω、W=LΩ[B] 和 X∈W，从原内部层次构造同一
β∈Ω、U=Lβ[B] 与 D∈W。U 同时包含 X、ω 和全部原有限参数；
β 为非零共尾极限，D 是完整原 Def 的 U→U 图，不预供较早层、
编码包或图的存在性。外部有限上下文仍只是模式索引。

这里消去局部图的存在守卫，不证明任意长前史属于 W，也不把
局部 U→U 图改称整体 W→W 图或完整源模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffLocalDefGraph

open Logic FirstOrder SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 原有限参数和候选共用一个较早层；所有存在见证只在 Prop 中装配。 -/
theorem exists_l (K : source_coding_l hℳ) {B ω Ω W X : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : level_l hℳ B Ω W) (hX : mem_l hℳ X W)
    {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) W) :
    ∃ β U D : type_l hℳ, mem_l hℳ β Ω ∧ limit_l hℳ β ∧
      PowerlessRelativeCofinalLimitBounds.cofinal_l β ∧ level_l hℳ B β U ∧
        mem_l hℳ U W ∧ mem_l hℳ X U ∧ mem_l hℳ ω U ∧ mem_l hℳ D W ∧
          PowerlessRelativeCofinalDefGraph.graph_l U D ∧
            ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) U := by
  have hOuter := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW ω
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ)
  have hAll : ∀ s (v : Variable (.set :: Δ) s),
      mem_l hℳ ((η.pushFree ω).freeVal v) W := by
    intro s v
    cases s
    cases v with
    | here => exact hωW
    | there v => exact hParams _ v
  obtain ⟨a, c, haΩ, hc, hXc, hValues⟩ :=
    PowerlessRelativeLimitParameterBounds.exists_l hBase hOuter hW (η.pushFree ω) hX hAll
  obtain ⟨β, hβ, hβΩ, haβ, hInner, hCofinal⟩ :=
    PowerlessRelativeCutoffCofinalLimits.exists_l K hBase hω hΩ haΩ
  obtain ⟨U, hU⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hβ
  have hLift := PowerlessRelativeLevelClosure.subset_l hℳ hBase haβ hc hU
  have hωU : mem_l hℳ ω U := hLift ω (hValues _ .here)
  have hKωU : mem_l hℳ K.omega U :=
    (SecondOrderOmega.unique_l hℳ hω K.omega_spec) ▸ hωU
  obtain ⟨D, hDW, hGraph⟩ := PowerlessRelativeCofinalDefGraph.exists_l K
    hBase hInner hU hCofinal hKωU hOuter hW hβΩ
  exact ⟨β, U, D, hβΩ, hInner, hCofinal, hU,
    PowerlessRelativeLevelClosure.members_l hℳ hBase hβΩ hU hW,
    hLift X hXc, hωU, hDW, hGraph,
    fun _ v => hLift (η.freeVal v) (hValues _ (.there v))⟩

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 三个绑定槽依次为 β、U、D；参数始终指向原 Δ，而非装配槽。 -/
def result_m {Γ Θ Δ : SortContext ℒ} (B ω Ω W X : Term ℒ Γ Θ .set)
    (τ : VariableSubstitution ℒ Δ Γ Θ) : Formula ℒ Γ Θ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let β : Term ℒ (.set :: .set :: .set :: Γ) Θ .set := .bvar (.there (.there .here))
    let U : Term ℒ (.set :: .set :: .set :: Γ) Θ .set := .bvar (.there .here)
    let D : Term ℒ (.set :: .set :: .set :: Γ) Θ .set := .bvar .here
    .conj (member_m β (up (up (up Ω)))) <|
      .conj (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .conj (PowerlessRelativeCofinalLimitBounds.cofinal_m β) <|
          .conj (PowerlessRelativeHierarchySyntax.level_m (up (up (up B))) β U) <|
            .conj (member_m U (up (up (up W)))) <|
              .conj (member_m (up (up (up X))) U) <|
                .conj (member_m (up (up (up ω))) U) <|
                  .conj (member_m D (up (up (up W)))) <|
                    .conj (PowerlessRelativeCofinalDefGraph.graph_m U D)
                      (parameters_m Δ U (fun v => up (up (up (τ v)))))

theorem result_formula_l (K : source_coding_l hℳ) {Γ Θ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Θ) (B ω Ω W X : Term ℒ Γ Θ .set)
    (τ : VariableSubstitution ℒ Δ Γ Θ) :
    (result_m B ω Ω W X τ).satisfies η ↔
      ∃ β U D : type_l hℳ, mem_l hℳ β (Ω.eval η) ∧ limit_l hℳ β ∧
        PowerlessRelativeCofinalLimitBounds.cofinal_l β ∧ level_l hℳ (B.eval η) β U ∧
          mem_l hℳ U (W.eval η) ∧ mem_l hℳ (X.eval η) U ∧ mem_l hℳ (ω.eval η) U ∧
            mem_l hℳ D (W.eval η) ∧ PowerlessRelativeCofinalDefGraph.graph_l U D ∧
              ∀ s (v : Variable Δ s), mem_l hℳ ((τ v).eval η) U := by
  simp only [result_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeCofinalLimitBounds.cofinal_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeCofinalDefGraph.graph_formula_l K, parameters_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    SecondOrderQuotient.structure_l]
  rfl

def schema_m {Θ Δ : SortContext ℒ} (B ω Ω W X : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
          .imp (member_m X W) <| .imp (parameters_m Δ W τ)
            (result_m B ω Ω W X τ)

def sentence_m {Θ Δ : SortContext ℒ} (B ω Ω W X : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω Ω W X τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (B ω Ω W X : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) :
    (sentence_m B ω Ω W X τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K, parameters_formula_l,
    result_formula_l K, member_m, Arguments.eval]
  intro hBase hω hΩ hW hX hParams
  let ν : Env (SecondOrderQuotient.structure_l hℳ) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (τ v).eval η }
  exact exists_l K hBase hω hΩ hW hX ν hParams

theorem derives_m {Θ Δ : SortContext ℒ} (B ω Ω W X : Term ℒ [] Θ .set)
    (τ : VariableSubstitution ℒ Δ [] Θ) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω Ω W X τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω Ω W X τ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffLocalDefGraph
