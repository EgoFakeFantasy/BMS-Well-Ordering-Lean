import BMSConstructibleBridge.PowerlessRelativeCofinalSatisfaction
import BMSConstructibleBridge.PowerlessRelativeLimitSatisfactionSyntax

/-! # 消去早期层与赋值集见证的原 Z₂ 对象模式

只保留原商外层及明确的极限阶段共尾守卫。早期层和 S 在模型证明中
实际构造，不进入对象前提；原 T/N/F 和完整 Sat 正文保持不变。
共尾层存在性已由 SecondOrderCofinalLimitDerives 单独证明；本模式不宣称
任意普通极限层已满足该条件。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalSatisfactionDerives

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitSatisfactionSyntax
  (sourceStatic_m sourceStatic_formula_l sourceSat_m sourceSat_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev context_m (Δ : SortContext ℒ) : SortContext ℒ := .set :: .set :: .set :: Δ
private abbrev base_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set := .fvar .here
private abbrev stage_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set := .fvar (.there .here)
private abbrev layer_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set := .fvar (.there (.there .here))

private def tail_m {Γ Δ : SortContext ℒ} : VariableSubstitution ℒ Δ Γ (context_m Δ)
  | _, v => .fvar (.there (.there (.there v)))

private def one_m {Δ : SortContext ℒ} : VariableSubstitution ℒ (.set :: Δ) [.set] (context_m Δ)
  | _, .here => .bvar .here
  | _, .there v => tail_m v

private def two_m {Δ : SortContext ℒ} : VariableSubstitution ℒ (.set :: .set :: Δ) [.set, .set] (context_m Δ)
  | _, .here => .bvar .here
  | _, .there .here => .bvar (.there .here)
  | _, .there (.there v) => tail_m v

def schema_m {Δ : SortContext ℒ} (ω e N T A t₁ t₂ t₃ : Term ℒ [] Δ .set) : Formula ℒ [] (context_m Δ) :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m base_m) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m base_m stage_m layer_m) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m stage_m) <|
        .imp (PowerlessRelativeCofinalLimitBounds.cofinal_m stage_m) <|
          .imp (PowerlessRelativeLimitDeltaSeparationDerives.parameters_m Δ layer_m tail_m) <|
            .imp (PowerlessRelativeClassInstantiation.formula_m base_m (SecondOrderOmegaSyntax.omega_m ω) tail_m) <|
              .forallE .set <| .imp (member_m (.bvar .here) layer_m) <|
                .imp (PowerlessRelativeClassInstantiation.formula_m base_m (sourceStatic_m ω e N T t₁ t₂ t₃) one_m) <|
                  .existsE .set <| .conj (member_m (.bvar .here) layer_m)
                    (PowerlessRelativeClassInstantiation.formula_m base_m (sourceSat_m ω e T A t₁ t₂ t₃) two_m)

def sentence_m {Δ : SortContext ℒ} (ω e N T A t₁ t₂ t₃ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω e N T A t₁ t₂ t₃)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω e N T A t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    (sentence_m ω e N T A t₁ t₂ t₃).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ρ hBase hC hLimit hCofinal hParams hω
  let B := base_m.eval ρ
  let β := stage_m.eval ρ
  let C := layer_m.eval ρ
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ ρ base_m).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K ρ base_m stage_m layer_m).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l ρ stage_m).mp hLimit
  have hCofinal' := (PowerlessRelativeCofinalLimitBounds.cofinal_formula_l ρ stage_m).mp hCofinal
  have hParams' := (PowerlessRelativeLimitDeltaSeparationDerives.parameters_formula_l Δ ρ layer_m tail_m).mp hParams
  let η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase') [] Δ :=
    ⟨(fun v => nomatch v), fun {s} v => match s with
      | .set => ⟨(tail_m v).eval ρ, ⟨β, C, hC', hParams' _ v⟩⟩⟩
  have hη : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v).val C := by
    intro s v
    cases s
    exact hParams' _ v
  have hω' := (PowerlessRelativeClassInstantiation.formula_l K (SecondOrderOmegaSyntax.omega_m ω)
    η ρ base_m tail_m rfl (fun _ => rfl)).mp hω
  have hωClass := (omega_formula_l η ω).mp hω'
  intro F hFC hStatic
  let F' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨F, ⟨β, C, hC', hFC⟩⟩
  have hStatic' := (PowerlessRelativeClassInstantiation.formula_l K
    (sourceStatic_m ω e N T t₁ t₂ t₃) (η.pushFree F') (ρ.pushBound F) base_m one_m rfl
    (by intro v; cases v <;> rfl)).mp hStatic
  have hStaticClass := (sourceStatic_formula_l η ω e N T t₁ t₂ t₃ F').mp hStatic'
  obtain ⟨R, hRC, hSat⟩ := PowerlessRelativeCofinalSatisfaction.exists_l (F := F')
    hC' hLimit' hCofinal' η ω e N T A t₁ t₂ t₃ hη hωClass hFC hStaticClass
  refine ⟨R.val, hRC, ?_⟩
  apply (PowerlessRelativeClassInstantiation.formula_l K (sourceSat_m ω e T A t₁ t₂ t₃)
    ((η.pushFree F').pushFree R) ((ρ.pushBound F).pushBound R.val) base_m two_m rfl ?_).mpr
  · exact (sourceSat_formula_l η ω e T A t₁ t₂ t₃ F' R).mpr hSat
  · intro v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

theorem derives_m {Δ : SortContext ℒ} (ω e N T A t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω e N T A t₁ t₂ t₃)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω e N T A t₁ t₂ t₃)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalSatisfactionDerives
