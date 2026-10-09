import BMSConstructibleBridge.PowerlessRelativeCofinalSatisfactionDerives
import BMSConstructibleBridge.PowerlessRelativeCutoffInnerLimits
import BMSConstructibleBridge.PowerlessRelativeCutoffLimit
import BMSConstructibleBridge.PowerlessRelativeCofinalSatisfactionForDomain

/-! # 首个类内不可数截止层的原 Z₂ 求值模式

原商中的 ω 与首个类内不可数 Ω 代替显式极限、共尾前提。给定编码包
和求值域仍须实际属于截止层；本模式取得其中的 Sat，不声称已经证明
截止层的完整 Separation／Collection 或任意行数 BMS 的终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSatisfactionDerives

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitSatisfactionSyntax
  (sourceStatic_m sourceStatic_formula_l sourceSat_m sourceSat_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

/-- 固定截止层内先取得整套编码，再给其中每个域取得 Sat；对象模式见下。 -/
theorem coding_exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} (K : source_coding_l hℳ)
    {B ω Ω C : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω C) :
    ∃ w e t₁ t₂ t₃ T N F : PowerlessRelativeClassStructure.type_l hℳ B,
      w.val = ω ∧ mem_l hℳ w.val C ∧
        mem_l hℳ e.val C ∧ mem_l hℳ t₁.val C ∧ mem_l hℳ t₂.val C ∧ mem_l hℳ t₃.val C ∧
          mem_l hℳ T.val C ∧ mem_l hℳ N.val C ∧ mem_l hℳ F.val C ∧
            PowerlessSatisfactionExistenceSyntax.static_l
              (𝒩 := PowerlessRelativeClassStructure.structure_l hℳ B hBase) w e t₁ t₂ t₃ T N F ∧
              ∀ A : PowerlessRelativeClassStructure.type_l hℳ B, mem_l hℳ A.val C →
                ∃ R : PowerlessRelativeClassStructure.type_l hℳ B, mem_l hℳ R.val C ∧
                  PowerlessSatisfactionSpecification.spec_l
                    (𝒩 := PowerlessRelativeClassStructure.structure_l hℳ B hBase) w A e t₁ t₂ t₃ T F R := by
  have hωC := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω C hC ω
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ)
  let w : PowerlessRelativeClassStructure.type_l hℳ B := ⟨ω, Ω, C, hC, hωC⟩
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨e, t₁, t₂, t₃, T, N, F, h⟩ := PowerlessRelativeCofinalSatisfactionForDomain.exists_l
    (hBase := hBase) K (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ) hC
    (PowerlessRelativeCutoffInnerLimits.cofinal_l K hBase hω hΩ) w hωC hωEq
  exact ⟨w, e, t₁, t₂, t₃, T, N, F, rfl, hωC, h⟩

private abbrev context_m (Δ : SortContext ℒ) : SortContext ℒ := .set :: .set :: .set :: .set :: Δ
private abbrev base_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set := .fvar .here
private abbrev stage_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set := .fvar (.there .here)
private abbrev layer_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set := .fvar (.there (.there .here))
private abbrev ambientOmega_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set :=
  .fvar (.there (.there (.there .here)))

private def tail_m {Γ Δ : SortContext ℒ} : VariableSubstitution ℒ Δ Γ (context_m Δ)
  | _, v => .fvar (.there (.there (.there (.there v))))

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
      .imp (SecondOrderOmegaSyntax.omega_m ambientOmega_m) <|
        .imp (PowerlessRelativeOrdinalCutoff.first_m base_m ambientOmega_m stage_m) <|
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
  intro ρ hBase hC hAmbientOmega hΩ hParams hω
  let B := base_m.eval ρ
  let Ω := stage_m.eval ρ
  let C := layer_m.eval ρ
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ ρ base_m).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K ρ base_m stage_m layer_m).mp hC
  have hAmbientOmega' := (SecondOrderOmegaSyntax.omega_l hℳ ρ ambientOmega_m).mp hAmbientOmega
  have hΩ' := (PowerlessRelativeOrdinalCutoff.first_formula_l K ρ base_m ambientOmega_m stage_m).mp hΩ
  have hLimit := PowerlessRelativeCutoffLimit.limit_l K hBase' hAmbientOmega' hΩ'
  have hCofinal := PowerlessRelativeCutoffInnerLimits.cofinal_l K hBase' hAmbientOmega' hΩ'
  have hParams' := (PowerlessRelativeLimitDeltaSeparationDerives.parameters_formula_l Δ ρ layer_m tail_m).mp hParams
  let η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase') [] Δ :=
    ⟨(fun v => nomatch v), fun {s} v => match s with
      | .set => ⟨(tail_m v).eval ρ, ⟨Ω, C, hC', hParams' _ v⟩⟩⟩
  have hη : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v).val C := by
    intro s v
    cases s
    exact hParams' _ v
  have hω' := (PowerlessRelativeClassInstantiation.formula_l K (SecondOrderOmegaSyntax.omega_m ω)
    η ρ base_m tail_m rfl (fun _ => rfl)).mp hω
  have hωClass := (omega_formula_l η ω).mp hω'
  intro F hFC hStatic
  let F' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨F, ⟨Ω, C, hC', hFC⟩⟩
  have hStatic' := (PowerlessRelativeClassInstantiation.formula_l K
    (sourceStatic_m ω e N T t₁ t₂ t₃) (η.pushFree F') (ρ.pushBound F) base_m one_m rfl
    (by intro v; cases v <;> rfl)).mp hStatic
  have hStaticClass := (sourceStatic_formula_l η ω e N T t₁ t₂ t₃ F').mp hStatic'
  obtain ⟨R, hRC, hSat⟩ := PowerlessRelativeCofinalSatisfaction.exists_l (F := F')
    hC' hLimit hCofinal η ω e N T A t₁ t₂ t₃ hη hωClass hFC hStaticClass
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
#print axioms coding_exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSatisfactionDerives
