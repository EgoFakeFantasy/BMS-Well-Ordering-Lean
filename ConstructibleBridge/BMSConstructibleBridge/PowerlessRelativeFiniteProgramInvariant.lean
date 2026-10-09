import BMSConstructibleBridge.PowerlessRelativeFiniteProgramExecution

/-! # 每个内部执行坐标的实际存储域不变式

从空状态开始的原执行历史，在坐标 i 的状态恰有干净图 f:i→D，
计数、陪域、存储图均属于 Class。归纳谓词是下面 point_m 的原 AST；
不是宿主 Nat 归纳，也不把任意内部程序当作外部有限项树。
最终对象句同时保留历史存在、历史图唯一及全部坐标的不变式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramInvariant

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramExecution (relation_m relation_formula_l)
open PowerlessRelativeFiniteProgramStep (valid_m valid_l valid_formula_l record_m record_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_m functional_l tags_m)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l at_formula_l)
open PowerlessDefinableFiniteTrace (trace_m trace_l trace_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₃ t)
private abbrev up₇ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₅ t)

def point_m {Δ : SortContext ℒ} (B ω F : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: Δ) :=
  .forallE .set <|
    .imp (SecondOrderObjectSyntax.value_m (up (F.weakenFree SetTheory.SetSort.set))
      (up (.fvar .here)) (.bvar .here)) <|
      .existsE .set <| .existsE .set <|
        valid_m (up₃ (B.weakenFree SetTheory.SetSort.set))
          (up₃ (ω.weakenFree SetTheory.SetSort.set)) (up₃ (.fvar .here))
            (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem point_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (η : Env 𝒱 [] Δ) (B ω F : Term ℒ [] Δ .set) (i : type_l hℳ) :
    (point_m B ω F).satisfies (η.pushFree i) ↔
      ∀ s, value_l (ℳ := 𝒱) (F.eval η) i s →
        ∃ D f, valid_l (B.eval η) (ω.eval η) i D f s := by
  simp only [point_m, Formula.satisfies, value_formula_l, valid_formula_l K,
    up₃, up₂, up, Term.eval_weakenFree, Term.eval_weakenBound, Term.eval,
    Env.pushFree_here]
  rfl

theorem induction_derives_m {Δ : SortContext ℒ} (B ω F : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (SecondOrderArithmetic.induction_m (GraphTranslation.form_m (point_m B ω F))) :=
  GraphTranslation.induction_m (point_m B ω F)

private theorem predecessor_l (K : source_coding_l hℳ) {n S : type_l hℳ}
    (hn : mem_l hℳ n K.omega) (hS : PowerlessNatural.successor_l (ℳ := 𝒱) n S)
    (k : SecondOrderModel.num_l ℳ)
    (hk : mem_l hℳ (numberCode_l K (SecondOrderModel.succ_l k)).val S) :
    mem_l hℳ (numberCode_l K k).val n := by
  obtain ⟨l, hl⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have hlEq : (numberCode_l K l).val = n := congrArg Subtype.val hl
  have hSEq : S = (numberCode_l K (SecondOrderModel.succ_l l)).val :=
    SecondOrderQuotient.ext_l hℳ S _ (fun x =>
      (hS x).trans (hlEq ▸ PowerlessBMSQuotientSuccessor.successor_l K l x).symm)
  rw [hSEq] at hk
  have hlt := (SecondOrderOrder.succ_iff_l hℳ k l).mp
    ((numberCode_mem_iff_lt_l K _ _).mp hk)
  exact hlEq ▸ (numberCode_mem_iff_lt_l K k l).mpr hlt

theorem values_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) {S D F : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (N.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) (hn : mem_l hℳ (n.eval η) K.omega)
    (hF : trace_l (relation_m φ B C ω w e t₀ t₁ t₂) η (e.eval η) (a.eval η) (n.eval η) S D F) :
    ∀ i s, value_l (ℳ := 𝒱) F i s → ∃ E g, valid_l (B.eval η) (ω.eval η) i E g s := by
  let ξ : Env 𝒱 [] (.set :: Δ) := η.pushFree F
  let B' := B.weakenFree SetTheory.SetSort.set
  let ω' := ω.weakenFree SetTheory.SetSort.set
  let F' : Term ℒ [] (.set :: Δ) .set := .fvar .here
  have hRead (i : type_l hℳ) : (point_m B' ω' F').satisfies (ξ.pushFree i) ↔
      ∀ s, value_l (ℳ := 𝒱) F i s → ∃ E g, valid_l (B.eval η) (ω.eval η) i E g s := by
    simpa only [ξ, B', ω', F', Term.eval_weakenFree, Term.eval, Env.pushFree_here] using
      point_formula_l K ξ B' ω' F' i
  have heEq : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := by
    apply SecondOrderQuotient.ext_l hℳ
    intro x
    exact iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x)
  have h := PowerlessBMSQuotientInduction.induction_l K (point_m B' ω' F') ξ ?_ ?_
  · intro i s hs
    have hiS := (SecondOrderFunctionProperties.value_mem_l hℳ hF.2.1 hs).1
    have hiω : mem_l hℳ i K.omega := by
      rcases (hF.1 i).mp hiS with hi | hi
      · exact SecondOrderOmegaTransitive.member_l hℳ K.omega_spec hn hi
      · exact hi.symm ▸ hn
    obtain ⟨k, hk⟩ := numberCode_surjective_l K ⟨i, hiω⟩
    have hkEq : (numberCode_l K k).val = i := congrArg Subtype.val hk
    have hPoint := (hRead _).mp (h k)
    rw [hkEq] at hPoint
    exact hPoint s hs
  · apply (hRead _).mpr
    intro s hs
    rw [← heEq] at hs
    have hsa := SecondOrderFunctionProperties.value_unique_l hℳ hF.2.1 hs hF.2.2.1
    subst s
    rw [← heEq]
    exact ⟨e.eval η, e.eval η, hω.symm ▸ PowerlessRelativeFiniteProgramStep.initial_l K hBase he hInitial⟩
  · intro k hPrevious
    apply (hRead _).mpr
    intro t ht
    have hjS := (SecondOrderFunctionProperties.value_mem_l hℳ hF.2.1 ht).1
    have hkN := predecessor_l K hn hF.1 k hjS
    have hkS := (hF.1 (numberCode_l K k).val).mpr (Or.inl hkN)
    obtain ⟨s, hs, _⟩ := hF.2.1.2 (numberCode_l K k).val hkS
    obtain ⟨E, g, hValid⟩ := (hRead _).mp hPrevious s hs.2
    have hSuccessor := PowerlessBMSQuotientSuccessor.successor_l K k
    have hRelation := hF.2.2.2 (numberCode_l K k).val
      (numberCode_l K (SecondOrderModel.succ_l k)).val s t hkN hSuccessor hs.2 ht
    have hStep := (relation_formula_l K φ η B C ω w e t₀ t₁ t₂ s t).mp hRelation
    rw [hω] at hValid hStep
    obtain ⟨_, T, G, r, _, _, hT, hNext⟩ := PowerlessRelativeFiniteProgramStep.transition_l
      K φ η hBase hC hw hTags hFunctional hValid hStep
    have hTEq : T = (numberCode_l K (SecondOrderModel.succ_l k)).val :=
      SecondOrderQuotient.ext_l hℳ T _ (fun x => (hT x).trans (hSuccessor x).symm)
    exact ⟨G, r, hω.symm ▸ hTEq ▸ hNext⟩

def conclusion_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let ψ := relation_m φ B C ω w e t₀ t₁ t₂
  .forallE .set <| .forallE .set <| .forallE .set <|
    .imp (trace_m ψ (up₃ e) (up₃ a) (up₃ n)
      (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)) <|
      .forallE .set <| .forallE .set <|
        .imp (SecondOrderObjectSyntax.value_m (.bvar (.there (.there .here)))
          (.bvar (.there .here)) (.bvar .here)) <|
          .existsE .set <| .existsE .set <|
            valid_m (up₇ B) (up₇ ω) (.bvar (.there (.there (.there .here))))
              (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here)))

theorem conclusion_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) :
    (conclusion_m φ B C ω w e t₀ t₁ t₂ a n).satisfies η ↔
      ∀ S D F, trace_l (relation_m φ B C ω w e t₀ t₁ t₂) η
        (e.eval η) (a.eval η) (n.eval η) S D F →
          ∀ i s, value_l (ℳ := 𝒱) F i s → ∃ E g, valid_l (B.eval η) (ω.eval η) i E g s := by
  simp only [conclusion_m, Formula.satisfies, trace_formula_l, value_formula_l,
    valid_formula_l K, parameters_pushBound_l, parameters_empty_l,
    up₇, up₅, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <| .imp (record_m e e e a) <|
          .imp (SecondOrderObjectSyntax.map_m w N Q) <| .imp (tags_m t₀ t₁ t₂) <|
            .imp (functional_m φ B) <| .imp (SecondOrderObjectSyntax.member_m n ω) <|
              .conj (PowerlessRelativeFiniteProgramExecution.result_m φ B C ω w e t₀ t₁ t₂ a n)
                (conclusion_m φ B C ω w e t₀ t₁ t₂ a n)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w N Q e t₀ t₁ t₂ a n)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω w N Q e t₀ t₁ t₂ a n).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  have hExecution := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeFiniteProgramExecution.models_l h𝒩 φ B C ω w N Q e t₀ t₁ t₂ a n) η
  simp only [schema_m, PowerlessRelativeFiniteProgramExecution.schema_m,
    PowerlessDefinableFiniteTraceDerives.zero_m, tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    record_formula_l, map_formula_l, conclusion_formula_l K, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there] at hExecution ⊢
  intro hBase hC hω he hInitial hw hTags hFunctional hn
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  exact ⟨hExecution hBase hC hω he hInitial hw hTags hFunctional hn,
    fun _ _ _ hF => values_l K φ η B C ω w N Q e t₀ t₁ t₂ a n
      hBase hC hωEq he hInitial hw hTags hFunctional (hωEq ▸ hn) hF⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w N Q e t₀ t₁ t₂ a n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω w N Q e t₀ t₁ t₂ a n)

#print axioms induction_derives_m
#print axioms values_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramInvariant
