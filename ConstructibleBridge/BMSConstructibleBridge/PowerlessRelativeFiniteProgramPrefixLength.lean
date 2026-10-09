import BMSConstructibleBridge.PowerlessRelativeFiniteProgramPersistentRead
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramPrefix

/-! # 增大执行长度后保留程序前缀的真实输出

先把短历史传给前缀相同的新词，再由不同长度历史的共同坐标唯一性
识别长历史中的中间状态，最后用持久存储读数传到长历史末态。
结论是原 run 的保持，不是仅缺省总化的输出，也不假定无限历史存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramPrefixLength

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramExecution (relation_m relation_formula_l)
open PowerlessRelativeFiniteProgramOutput (run_m run_l run_formula_l)
open PowerlessRelativeFiniteProgramPrefix (agree_m agree_l agree_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_m functional_l tags_m)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_pushBound_l parameters_empty_l at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem member_transitive_l (K : source_coding_l hℳ) {m n k : type_l hℳ}
    (hm : mem_l hℳ m K.omega) (hnm : mem_l hℳ n m) (hkn : mem_l hℳ k n) :
    mem_l hℳ k m := by
  obtain ⟨b, hb⟩ := numberCode_surjective_l K ⟨m, hm⟩
  have hbEq : (numberCode_l K b).val = m := congrArg Subtype.val hb
  obtain ⟨a, hab, ha⟩ := SecondOrderFiniteEnumerationRoots.member_number_l K b n (hbEq.symm ▸ hnm)
  obtain ⟨c, hca, hc⟩ := SecondOrderFiniteEnumerationRoots.member_number_l K a k (ha.symm ▸ hkn)
  exact hbEq ▸ hc ▸ (numberCode_mem_iff_lt_l K c b).mpr (SecondOrderOrder.trans_l hℳ hca hab)

theorem run_transfer_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w N v M Q e t₀ t₁ t₂ a n m k : Term ℒ [] Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (N.eval η) (Q.eval η))
    (hv : map_l (ℳ := 𝒱) (v.eval η) (M.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η))
    (hn : mem_l hℳ (n.eval η) (ω.eval η)) (hm : mem_l hℳ (m.eval η) (ω.eval η))
    (hnm : mem_l hℳ (n.eval η) (m.eval η) ∨ n.eval η = m.eval η)
    (hAgree : agree_l (n.eval η) (w.eval η) (v.eval η)) {y : type_l hℳ}
    (hy : run_l (relation_m φ B C ω w e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) y) :
    run_l (relation_m φ B C ω v e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (m.eval η) (k.eval η) y := by
  obtain ⟨S, D, F, s, E, f, _, _, hTrace, hs, hValid, hfy⟩ := hy
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hnK : mem_l hℳ (n.eval η) K.omega := hωEq ▸ hn
  have hmK : mem_l hℳ (m.eval η) K.omega := hωEq ▸ hm
  have hkN := (SecondOrderFunctionProperties.value_mem_l hℳ hValid.2.2.2.2.2 hfy).1
  have hkM : mem_l hℳ (k.eval η) (m.eval η) := by
    rcases hnm with h | h
    · exact member_transitive_l K hmK h hkN
    · exact h ▸ hkN
  obtain ⟨z, T, G, H, t, J, g, hGC, hHC, hLong, ht, htValid, _⟩ :=
    PowerlessRelativeFiniteProgramOutput.run_exists_l K φ η
      B C ω v M Q e t₀ t₁ t₂ a m k hBase hC hω he hInitial hv hTags hFunctional hm hkM
  have hShort := PowerlessRelativeFiniteProgramPrefix.trace_transfer_l K φ η
    B C ω w N Q v e t₀ t₁ t₂ a n hBase hC hωEq he hInitial hw hTags hFunctional hnK hAgree hTrace
  have hnT := (hLong.1 (n.eval η)).mpr hnm
  obtain ⟨r, hr, _⟩ := hLong.2.1.2 (n.eval η) hnT
  have heEq : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := by
    apply SecondOrderQuotient.ext_l hℳ
    intro x
    exact iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x)
  have hUnique : ∀ x y z, (relation_m φ B C ω v e t₀ t₁ t₂).satisfies ((η.pushFree x).pushFree y) →
      (relation_m φ B C ω v e t₀ t₁ t₂).satisfies ((η.pushFree x).pushFree z) → y = z := by
    intro x y z hy hz
    obtain ⟨t, _, hUnique⟩ := PowerlessRelativeFiniteProgramStep.exists_unique_l
      φ η hBase hC hv hTags hFunctional x
    exact (hUnique y ((relation_formula_l K φ η B C ω v e t₀ t₁ t₂ x y).mp hy)).trans
      (hUnique z ((relation_formula_l K φ η B C ω v e t₀ t₁ t₂ x z).mp hz)).symm
  have hsr := PowerlessDefinableFiniteTraceUnique.overlap_values_l K
    (relation_m φ B C ω v e t₀ t₁ t₂) η hnK hmK heEq hShort hLong hUnique
      (n.eval η) s r hs hr.2
  have hOldRead : PowerlessRelativeFiniteProgramPersistentRead.read_l H (n.eval η) (k.eval η) y :=
    ⟨r, E, f, hr.2, hsr ▸ hValid.1, hfy⟩
  have hEndRead := PowerlessRelativeFiniteProgramPersistentRead.values_l K φ η
    B C ω v M Q e t₀ t₁ t₂ a m hBase hC hωEq he hInitial hv hTags hFunctional hmK hLong
      (n.eval η) (m.eval η) (k.eval η) y t hnm ht hOldRead
  have hgy := (PowerlessRelativeFiniteProgramPersistentRead.read_iff_l hLong.2.1 ht htValid.1).mp hEndRead
  exact ⟨T, G, H, t, J, g, hGC, hHC, hLong, ht, htValid, hgy⟩

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w v e t₀ t₁ t₂ a n m k : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .imp
    (run_m (relation_m φ B C ω w e t₀ t₁ t₂) B ω e a n k (.bvar .here))
    (run_m (relation_m φ B C ω v e t₀ t₁ t₂) B ω e a m k (.bvar .here))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N v M Q e t₀ t₁ t₂ a n m k : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
          .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
            .imp (SecondOrderObjectSyntax.map_m w N Q) <|
              .imp (SecondOrderObjectSyntax.map_m v M Q) <|
                .imp (tags_m t₀ t₁ t₂) <| .imp (functional_m φ B) <|
                  .imp (SecondOrderObjectSyntax.member_m n ω) <|
                    .imp (SecondOrderObjectSyntax.member_m m ω) <|
                      .imp (.disj (SecondOrderObjectSyntax.member_m n m) (.equal n m)) <|
                        .imp (agree_m n w v) (result_m φ B C ω w v e t₀ t₁ t₂ a n m k)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N v M Q e t₀ t₁ t₂ a n m k : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w N v M Q e t₀ t₁ t₂ a n m k)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω w N v M Q e t₀ t₁ t₂ a n m k : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω w N v M Q e t₀ t₁ t₂ a n m k).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, PowerlessDefinableFiniteTraceDerives.zero_m,
    tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l, map_formula_l, agree_formula_l,
    run_formula_l K, at_formula_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hw hv hTags hFunctional hn hm hnm hAgree y hy
  exact run_transfer_l K φ η B C ω w N v M Q e t₀ t₁ t₂ a n m k
    hBase hC hω he hInitial hw hv hTags hFunctional hn hm hnm hAgree hy

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N v M Q e t₀ t₁ t₂ a n m k : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w N v M Q e t₀ t₁ t₂ a n m k)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω w N v M Q e t₀ t₁ t₂ a n m k)

#print axioms run_transfer_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramPrefixLength
