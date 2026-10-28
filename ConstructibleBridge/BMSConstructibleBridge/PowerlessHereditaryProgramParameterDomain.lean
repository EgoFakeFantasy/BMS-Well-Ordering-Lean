import BMSConstructibleBridge.PowerlessHereditaryParameterEnvelope
import BMSConstructibleBridge.PowerlessClassProgramEnvelopeDomain

/-! # 从原遗传参数构造实际分离程序母域

纯隶属 ℒ，背景原 Z₂。原有限参数 Δ 在装配上下文 Ε 中经指定项解释；
先构造含基底、ω 和全部原参数的可数传递 D/F，再构造另一套
C=D∪{D}、G、Q、S、P。调用者不再预供 D/F 或新程序母域。
原数码 U 及求值元数据若需纳入，只能在 Δ 中显式列为遗传参数。

公开出口为原核 Derives。遗传性及标签 Class 资格仍是明确前提；
本文件不证明原求值参数的遗传性，也不冒称最终 BMS 良序完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryProgramParameterDomain

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up t)

def conclusion_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω t₀ t₁ t₂ : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Formula ℒ [] Ε :=
  .existsE .set <| .existsE .set <|
    let D := .bvar (.there .here)
    let F := .bvar .here
    .conj (PowerlessHereditaryClass.body_m (up₂ B) (up₂ B) D F (up₂ ω)) <|
      .conj (SecondOrderObjectSyntax.member_m (up₂ ω) D) <|
        .conj (PowerlessRelativeClassParameterSeed.members_m Δ D (fun v => up₂ (τ v)))
          (PowerlessClassProgramEnvelopeDomain.conclusion_m
            (up₂ B) (up₂ ω) D (up₂ t₀) (up₂ t₁) (up₂ t₂))

def schema_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω t₀ t₁ t₂ : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessHereditaryClass.formula_m B B) <|
        .imp (PowerlessHereditaryParameterEnvelope.parameters_m Δ B τ) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B t₀) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B t₁) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B t₂)
                (conclusion_m Δ B ω t₀ t₁ t₂ τ)

def sentence_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω t₀ t₁ t₂ : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Δ B ω t₀ t₁ t₂ τ)

universe v

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, v} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Ε : SortContext ℒ}
    (Δ : SortContext ℒ) (B ω t₀ t₁ t₂ : Term ℒ [] Ε .set)
    (τ : VariableSubstitution ℒ Δ [] Ε) :
    (sentence_m Δ B ω t₀ t₁ t₂ τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessHereditaryClass.formula_l K, PowerlessHereditaryParameterEnvelope.parameters_formula_l K,
    PowerlessHereditaryClass.body_formula_l K,
    PowerlessRelativeClassParameterSeed.members_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hω hB hParams h₀ h₁ h₂
  obtain ⟨D, F, hEnvelope, hωD, hMembers⟩ :=
    PowerlessHereditaryParameterEnvelope.exists_l hBase hω hB Δ η τ hParams
  obtain ⟨C, G, Q, S, P, hDomain⟩ := PowerlessClassProgramEnvelopeDomain.exists_l
    hBase hω hEnvelope.1 hEnvelope.2.1 hEnvelope.2.2.2.2.2.1
    hEnvelope.2.2.2.2.2.2 h₀ h₁ h₂
  refine ⟨D, F, hEnvelope, hωD, hMembers, ?_⟩
  simp only [PowerlessClassProgramEnvelopeDomain.conclusion_formula_l K,
    Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  exact ⟨C, G, Q, S, P, hDomain⟩

theorem derives_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω t₀ t₁ t₂ : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Δ B ω t₀ t₁ t₂ τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 Δ B ω t₀ t₁ t₂ τ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryProgramParameterDomain
