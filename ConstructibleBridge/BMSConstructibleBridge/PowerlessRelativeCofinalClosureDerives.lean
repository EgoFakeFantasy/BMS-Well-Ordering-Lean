import BMSConstructibleBridge.PowerlessRelativeCofinalClosure
import BMSConstructibleBridge.PowerlessRelativeLimitSatisfactionSyntax

/-! # 共同共尾层与完整 Sat 收纳的原 Z₂ 对象模式

外部有限参数和 F 只需属于相对并类；β、C、R 由对象存在量词实际给出。
层关系与成员收纳仍在原商读取，仅 ω、static 和 Sat 正文作类相对化。
自由参数包括给定 A，不将逐 A 的存在量词错误地移到 A 量词之前。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalClosureDerives

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitSatisfactionSyntax
  (sourceStatic_m sourceStatic_formula_l sourceSat_m sourceSat_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private def classParameters_m {Γ Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B : Term ℒ Γ Ε .set) (σ : VariableSubstitution ℒ Δ Γ Ε) : Formula ℒ Γ Ε :=
  match Δ with
  | [] => .truth
  | .set :: Δ => .conj (PowerlessRelativeHierarchySyntax.class_m B (σ .here))
      (classParameters_m Δ B (fun v => σ (.there v)))

private theorem classParameters_formula_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} (K : source_coding_l hℳ)
    {Γ Ε : SortContext ℒ} (Δ : SortContext ℒ) (ρ : Env (SecondOrderQuotient.structure_l hℳ) Γ Ε)
    (B : Term ℒ Γ Ε .set) (σ : VariableSubstitution ℒ Δ Γ Ε) :
    (classParameters_m Δ B σ).satisfies ρ ↔ ∀ s (v : Variable Δ s),
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval ρ) ((σ v).eval ρ) := by
  induction Δ with
  | nil =>
      constructor
      · intro _ _ v; nomatch v
      · intro _; trivial
  | cons s Δ ih =>
      cases s
      change (_ ∧ (classParameters_m Δ B (fun v => σ (.there v))).satisfies ρ) ↔ _
      rw [PowerlessRelativeHierarchySemantics.class_formula_l K, ih]
      constructor
      · rintro ⟨hHead, hTail⟩ t v
        cases t
        cases v with
        | here => exact hHead
        | there v => exact hTail _ v
      · intro h
        exact ⟨h _ .here, fun _ v => h _ (.there v)⟩

private abbrev context_m (Δ : SortContext ℒ) : SortContext ℒ := .set :: Δ
private abbrev base_m {Γ Δ : SortContext ℒ} : Term ℒ Γ (context_m Δ) .set := .fvar .here

private def tail_m {Γ Δ : SortContext ℒ} : VariableSubstitution ℒ Δ Γ (context_m Δ)
  | _, v => .fvar (.there v)

private def one_m {Δ : SortContext ℒ} : VariableSubstitution ℒ (.set :: Δ) [.set] (context_m Δ)
  | _, .here => .bvar .here
  | _, .there v => tail_m v

/-- 输出量词依次引入 β、C、R；原 F 因而处于第四个绑定槽。 -/
private def output_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set, .set, .set, .set] (context_m Δ)
  | _, .here => .bvar .here
  | _, .there .here => .bvar (.there (.there (.there .here)))
  | _, .there (.there v) => tail_m v

private abbrev stage_m {Δ : SortContext ℒ} : Term ℒ [.set, .set, .set, .set] (context_m Δ) .set :=
  .bvar (.there (.there .here))
private abbrev layer_m {Δ : SortContext ℒ} : Term ℒ [.set, .set, .set, .set] (context_m Δ) .set :=
  .bvar (.there .here)

private def witnesses_m {Δ : SortContext ℒ} (ω e T A t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Formula ℒ [.set] (context_m Δ) :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    .conj (PowerlessRelativeHierarchySyntax.level_m base_m stage_m layer_m) <|
      .conj (PowerlessRelativeHierarchySyntax.limit_m stage_m) <|
        .conj (PowerlessRelativeCofinalLimitBounds.cofinal_m stage_m) <|
          .conj (member_m (.bvar (.there (.there (.there .here)))) layer_m) <|
            .conj (PowerlessRelativeLimitDeltaSeparationDerives.parameters_m Δ layer_m tail_m) <|
              .conj (member_m (.bvar .here) layer_m)
                (PowerlessRelativeClassInstantiation.formula_m base_m
                  (sourceSat_m ω e T A t₁ t₂ t₃) output_m)

def schema_m {Δ : SortContext ℒ} (ω e N T A t₁ t₂ t₃ : Term ℒ [] Δ .set) : Formula ℒ [] (context_m Δ) :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m base_m) <|
    .imp (classParameters_m Δ base_m tail_m) <|
      .imp (PowerlessRelativeClassInstantiation.formula_m base_m (SecondOrderOmegaSyntax.omega_m ω) tail_m) <|
        .forallE .set <| .imp (PowerlessRelativeHierarchySyntax.class_m base_m (.bvar .here)) <|
          .imp (PowerlessRelativeClassInstantiation.formula_m base_m (sourceStatic_m ω e N T t₁ t₂ t₃) one_m)
            (witnesses_m ω e T A t₁ t₂ t₃)

def sentence_m {Δ : SortContext ℒ} (ω e N T A t₁ t₂ t₃ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω e N T A t₁ t₂ t₃)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω e N T A t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    (sentence_m ω e N T A t₁ t₂ t₃).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ρ hBase hParams hω
  let B := base_m.eval ρ
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ ρ base_m).mp hBase
  have hParams' := (classParameters_formula_l K Δ ρ base_m tail_m).mp hParams
  let η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase') [] Δ :=
    ⟨(fun v => nomatch v), fun {s} v => match s with
      | .set => ⟨(tail_m v).eval ρ, hParams' _ v⟩⟩
  have hω' := (PowerlessRelativeClassInstantiation.formula_l K (SecondOrderOmegaSyntax.omega_m ω)
    η ρ base_m tail_m rfl (fun _ => rfl)).mp hω
  have hωClass := (omega_formula_l η ω).mp hω'
  intro F hF hStatic
  have hF' := (PowerlessRelativeHierarchySemantics.class_formula_l K (ρ.pushBound F) base_m (.bvar .here)).mp hF
  let F' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨F, hF'⟩
  have hStatic' := (PowerlessRelativeClassInstantiation.formula_l K
    (sourceStatic_m ω e N T t₁ t₂ t₃) (η.pushFree F') (ρ.pushBound F) base_m one_m rfl
    (by intro v; cases v <;> rfl)).mp hStatic
  have hStaticClass := (sourceStatic_formula_l η ω e N T t₁ t₂ t₃ F').mp hStatic'
  obtain ⟨β, C, R, hC, hLimit, hCofinal, hFC, hParamsC, hRC, hSat⟩ :=
    PowerlessRelativeCofinalClosure.satisfaction_l (F := F') η ω e N T A t₁ t₂ t₃ hωClass hStaticClass
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [.set, .set, .set, .set] (context_m Δ) :=
    (((ρ.pushBound F).pushBound β).pushBound C).pushBound R.val
  refine ⟨β, C, R.val, ?_, ?_, ?_, hFC, ?_, hRC, ?_⟩
  · exact (PowerlessRelativeHierarchySemantics.level_formula_l K ξ base_m stage_m layer_m).mpr hC
  · exact (PowerlessRelativeHierarchySemantics.limit_formula_l ξ stage_m).mpr hLimit
  · exact (PowerlessRelativeCofinalLimitBounds.cofinal_formula_l ξ stage_m).mpr hCofinal
  · apply (PowerlessRelativeLimitDeltaSeparationDerives.parameters_formula_l Δ ξ layer_m tail_m).mpr
    intro s v
    cases s
    exact hParamsC _ v
  · apply (PowerlessRelativeClassInstantiation.formula_l K (sourceSat_m ω e T A t₁ t₂ t₃)
      ((η.pushFree F').pushFree R) ξ base_m output_m rfl ?_).mpr
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

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalClosureDerives
