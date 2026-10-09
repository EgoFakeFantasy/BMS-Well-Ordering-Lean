import BMSConstructibleBridge.PowerlessRelativeFiniteProgramConcatTrace
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramOutput

/-! # 实际拼接词保留右程序的全部真实输出

右输出坐标沿同一加法图平移；该图同时用于父坐标重编号与词拼接。
先证明新坐标确在新长度内，构造原执行关系的实际历史，再消费同步
内部归纳。输出保持不是单步相容性的假设，也不使用缺省总化分支。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConcatRightRead

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramExecution (relation_m)
open PowerlessRelativeFiniteProgramOutput (run_m run_l run_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_m functional_l tags_m)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem run_transfer_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω e t₀ t₁ t₂ a n w m z Q A r c v k l : Term ℒ [] Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l
      (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hz : map_l (ℳ := 𝒱) (z.eval η) (m.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η))
    (hn : mem_l hℳ (n.eval η) (ω.eval η)) (hm : mem_l hℳ (m.eval η) (ω.eval η))
    (hJoined : PowerlessRelativeFiniteProgramConcat.joined_l
      (B.eval η) (C.eval η) (ω.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
        (n.eval η) (w.eval η) (m.eval η) (z.eval η) (Q.eval η) (A.eval η)
          (r.eval η) (c.eval η) (v.eval η))
    (hkl : value_l (ℳ := 𝒱) (A.eval η) (k.eval η) (l.eval η)) {y : type_l hℳ}
    (hy : run_l (relation_m φ B C ω z e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (m.eval η) (k.eval η) y) :
    run_l (relation_m φ B C ω v e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (c.eval η) (l.eval η) y := by
  obtain ⟨S, D, F, s, E, f, _, _, hF, hs, hValid, hfy⟩ := hy
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hnK := hωEq ▸ hn
  have hmK := hωEq ▸ hm
  have hA : map_l (ℳ := 𝒱) (A.eval η) K.omega K.omega := hωEq ▸ hJoined.2.2.1
  have hmc := hJoined.2.2.2.2.1
  have hkM := (SecondOrderFunctionProperties.value_mem_l hℳ hValid.2.2.2.2.2 hfy).1
  obtain ⟨a₀, ha₀⟩ := numberCode_surjective_l K ⟨n.eval η, hnK⟩
  have ha₀Eq : (numberCode_l K a₀).val = n.eval η := congrArg Subtype.val ha₀
  have hIteration : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega
      (e.eval η) (numberCode_l K a₀).val (A.eval η) := by
    simpa only [hωEq, ha₀Eq] using hJoined.2.2.2.1
  have hlC := (SecondOrderFiniteConcatArithmetic.order_l K a₀ he hIteration hA hkl hmc).mp hkM
  have hc := (PowerlessRelativeFiniteProgramWordConcat.length_l K hωEq he hnK hJoined.2).1
  have hv := hJoined.2.2.2.2.2.2.2.1
  obtain ⟨y', T, G, H, t, J, g, hGC, hHC, hH, ht, htValid, _⟩ :=
    PowerlessRelativeFiniteProgramOutput.run_exists_l K φ η
      B C ω v c Q e t₀ t₁ t₂ a c l hBase hC hω he hInitial hv hTags hFunctional
        (hωEq.symm ▸ hc) hlC
  have hState := PowerlessRelativeFiniteProgramConcatTrace.values_l K φ η
    B C ω e t₀ t₁ t₂ a n w m z Q A r c v hBase hC hωEq he hInitial hz hTags
      hFunctional hnK hmK hJoined hF hH (m.eval η) hmK
  have hRead := hState (c.eval η) s t E f J g hmc hs ht hValid.1 htValid.1
  exact ⟨T, G, H, t, J, g, hGC, hHC, hH, ht, htValid, (hRead _ _ hkl y).mp hfy⟩

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a m z c v k l : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .imp
    (run_m (relation_m φ B C ω z e t₀ t₁ t₂) B ω e a m k (.bvar .here))
    (run_m (relation_m φ B C ω v e t₀ t₁ t₂) B ω e a c l (.bvar .here))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q A r c v k l : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (SecondOrderObjectSyntax.map_m z m Q) <| .imp (tags_m t₀ t₁ t₂) <|
              .imp (functional_m φ B) <| .imp (SecondOrderObjectSyntax.member_m n ω) <|
                .imp (SecondOrderObjectSyntax.member_m m ω) <|
                  .imp (PowerlessRelativeFiniteProgramConcat.joined_m B C ω e t₀ t₁ t₂ n w m z Q A r c v) <|
                    .imp (SecondOrderObjectSyntax.value_m A k l)
                      (result_m φ B C ω e t₀ t₁ t₂ a m z c v k l)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q A r c v k l : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω e t₀ t₁ t₂ a n w m z Q A r c v k l)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q A r c v k l : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω e t₀ t₁ t₂ a n w m z Q A r c v k l).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, PowerlessDefinableFiniteTraceDerives.zero_m, tags_m, functional_m,
    Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l, map_formula_l, value_formula_l,
    PowerlessRelativeFiniteProgramConcat.joined_formula_l K, run_formula_l K, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hz hTags hFunctional hn hm hJoined hkl y hy
  exact run_transfer_l K φ η B C ω e t₀ t₁ t₂ a n w m z Q A r c v k l
    hBase hC hω he hInitial hz hTags hFunctional hn hm hJoined hkl hy

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q A r c v k l : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω e t₀ t₁ t₂ a n w m z Q A r c v k l)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω e t₀ t₁ t₂ a n w m z Q A r c v k l)

#print axioms run_transfer_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConcatRightRead
