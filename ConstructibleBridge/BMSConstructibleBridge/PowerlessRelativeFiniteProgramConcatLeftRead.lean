import BMSConstructibleBridge.PowerlessRelativeFiniteProgramPrefixLength
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramWordConcat

/-! # 实际拼接词保留左程序的全部真实输出

从原 concat 矩阵读取同一加法图、实际新词与新长度。长度不减和
前缀读数同余都由该矩阵证明，随后调用内部历史保持；不把两项
作为未验证的额外接口前提，也不以缺省输出冒充真实 run。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConcatLeftRead

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeFiniteProgramExecution (relation_m)
open PowerlessRelativeFiniteProgramOutput (run_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_m tags_m)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_pushBound_l parameters_empty_l at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e a t₀ t₁ t₂ n w m z Q A c v k : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (SecondOrderObjectSyntax.map_m w n Q) <| .imp (tags_m t₀ t₁ t₂) <|
              .imp (functional_m φ B) <| .imp (SecondOrderObjectSyntax.member_m n ω) <|
                .imp (PowerlessRelativeFiniteProgramWordConcat.concat_m B ω e n w m z Q A c v)
                  (PowerlessRelativeFiniteProgramPrefixLength.result_m φ B C ω w v e t₀ t₁ t₂ a n c k)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e a t₀ t₁ t₂ n w m z Q A c v k : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω e a t₀ t₁ t₂ n w m z Q A c v k)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e a t₀ t₁ t₂ n w m z Q A c v k : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω e a t₀ t₁ t₂ n w m z Q A c v k).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, PowerlessRelativeFiniteProgramPrefixLength.result_m,
    PowerlessDefinableFiniteTraceDerives.zero_m, tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l, map_formula_l,
    PowerlessRelativeFiniteProgramWordConcat.concat_formula_l K, run_formula_l K, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hw hTags hFunctional hn hConcat y hy
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  have hnK := hωEq ▸ hn
  obtain ⟨hc, hnc⟩ := PowerlessRelativeFiniteProgramWordConcat.length_l K hωEq he hnK hConcat
  have hAgree := PowerlessRelativeFiniteProgramWordConcat.prefix_l K hωEq he hnK hConcat
  have hv := hConcat.2.2.2.2.2.2.1
  exact PowerlessRelativeFiniteProgramPrefixLength.run_transfer_l K φ η
    B C ω w n v c Q e t₀ t₁ t₂ a n c k hBase hC hω he hInitial hw hv hTags hFunctional
      hn (hωEq.symm ▸ hc) hnc hAgree hy

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e a t₀ t₁ t₂ n w m z Q A c v k : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω e a t₀ t₁ t₂ n w m z Q A c v k)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω e a t₀ t₁ t₂ n w m z Q A c v k)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConcatLeftRead
