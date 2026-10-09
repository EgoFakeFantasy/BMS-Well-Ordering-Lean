import BMSConstructibleBridge.PowerlessRelativeFiniteProgramConcat
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramRelocationInitial
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramInvariant

/-! # 拼接右段与原程序的实际历史同步

归纳变量是模型内部坐标。加法图、两张原历史和存储图均为实际集合；
归纳正文只比较原状态编码与全部平移父坐标上的读数，不假定未来值
存在，也不把内部程序长度换成宿主 Nat。对象出口消费实际 joined
及实际 trace 矩阵，不预设整个右段已具有输出保持性质。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConcatTrace

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramStep (record_m record_l record_formula_l valid_l)
open PowerlessRelativeFiniteProgramExecution (relation_m relation_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_m functional_l tags_m)
open PowerlessRelativeFiniteProgramRelocationComputed (reading_m reading_l reading_formula_l)
open PowerlessDefinableFiniteTrace (trace_m trace_l trace_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₇ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ (up₃ t))

def state_m {Γ Δ : SortContext ℒ} (A F H j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
      let i : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there (.there (.there (.there .here))))))
      let s := .bvar (.there (.there (.there (.there (.there .here)))))
      let t := .bvar (.there (.there (.there (.there .here))))
      let D := .bvar (.there (.there (.there .here)))
      let f := .bvar (.there (.there .here))
      let E := .bvar (.there .here)
      let g := .bvar .here
      .imp (SecondOrderObjectSyntax.value_m (up₇ A) (up₇ j) i) <|
        .imp (SecondOrderObjectSyntax.value_m (up₇ F) (up₇ j) s) <|
          .imp (SecondOrderObjectSyntax.value_m (up₇ H) i t) <|
            .imp (record_m (up₇ j) D f s) <|
              .imp (record_m i E g t) (reading_m (up₇ A) f g)

def point_m {Δ : SortContext ℒ} (A F H : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: Δ) :=
  state_m (A.weakenFree SetTheory.SetSort.set) (F.weakenFree SetTheory.SetSort.set)
    (H.weakenFree SetTheory.SetSort.set) (.fvar .here)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def state_l (A F H j : type_l hℳ) : Prop :=
  ∀ i s t D f E g, value_l (ℳ := 𝒱) A j i → value_l (ℳ := 𝒱) F j s →
    value_l (ℳ := 𝒱) H i t → record_l j D f s → record_l i E g t → reading_l A f g

theorem state_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (A F H j : Term ℒ Γ Δ .set) :
    (state_m A F H j).satisfies η ↔ state_l (A.eval η) (F.eval η) (H.eval η) (j.eval η) := by
  simp only [state_m, state_l, Formula.satisfies, value_formula_l, record_formula_l,
    reading_formula_l, up₇, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem point_formula_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ)
    (A F H : Term ℒ [] Δ .set) (j : type_l hℳ) :
    (point_m A F H).satisfies (η.pushFree j) ↔
      state_l (A.eval η) (F.eval η) (H.eval η) j := by
  simp only [point_m, state_formula_l, Term.eval_weakenFree, Term.eval, Env.pushFree_here]

theorem induction_derives_m {Δ : SortContext ℒ} (A F H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (SecondOrderArithmetic.induction_m (GraphTranslation.form_m (point_m A F H))) :=
  GraphTranslation.induction_m (point_m A F H)

private theorem predecessor_l (K : source_coding_l hℳ) {n S i j : type_l hℳ}
    (hn : mem_l hℳ n K.omega) (hi : mem_l hℳ i K.omega)
    (hS : PowerlessNatural.successor_l (ℳ := 𝒱) n S)
    (hij : PowerlessNatural.successor_l (ℳ := 𝒱) i j) (hj : mem_l hℳ j S) :
    mem_l hℳ i n := by
  obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨i, hi⟩
  obtain ⟨b, hb⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have haEq : (numberCode_l K a).val = i := congrArg Subtype.val ha
  have hbEq : (numberCode_l K b).val = n := congrArg Subtype.val hb
  have hjEq : j = (numberCode_l K (SecondOrderModel.succ_l a)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x =>
      (hij x).trans (haEq ▸ PowerlessBMSQuotientSuccessor.successor_l K a x).symm)
  have hSEq : S = (numberCode_l K (SecondOrderModel.succ_l b)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x =>
      (hS x).trans (hbEq ▸ PowerlessBMSQuotientSuccessor.successor_l K b x).symm)
  rw [hjEq, hSEq] at hj
  exact haEq ▸ hbEq ▸ (numberCode_mem_iff_lt_l K a b).mpr
    ((SecondOrderOrder.succ_iff_l hℳ a b).mp ((numberCode_mem_iff_lt_l K _ _).mp hj))

theorem values_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω e t₀ t₁ t₂ a n w m z Q A r c v : Term ℒ [] Δ .set)
    {S D F T E H : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hz : map_l (ℳ := 𝒱) (z.eval η) (m.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η))
    (hn : mem_l hℳ (n.eval η) K.omega) (hm : mem_l hℳ (m.eval η) K.omega)
    (hJoined : PowerlessRelativeFiniteProgramConcat.joined_l
      (B.eval η) (C.eval η) (ω.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
        (n.eval η) (w.eval η) (m.eval η) (z.eval η) (Q.eval η) (A.eval η)
          (r.eval η) (c.eval η) (v.eval η))
    (hF : trace_l (relation_m φ B C ω z e t₀ t₁ t₂) η
      (e.eval η) (a.eval η) (m.eval η) S D F)
    (hH : trace_l (relation_m φ B C ω v e t₀ t₁ t₂) η
      (e.eval η) (a.eval η) (c.eval η) T E H) :
    ∀ j, mem_l hℳ j K.omega → state_l (A.eval η) F H j := by
  have hA : map_l (ℳ := 𝒱) (A.eval η) K.omega K.omega := hω ▸ hJoined.2.2.1
  have hIteration : PowerlessAddition.iteration_l (ℳ := 𝒱)
      K.omega (e.eval η) (n.eval η) (A.eval η) := hω ▸ hJoined.2.2.2.1
  obtain ⟨Y, hIterationMap, hZero, hNext⟩ := hIteration
  have hLength := PowerlessRelativeFiniteProgramWordConcat.length_l K hω he hn hJoined.2
  have hc := hLength.1
  have hv := hJoined.2.2.2.2.2.2.2.1
  have hValidF := PowerlessRelativeFiniteProgramInvariant.values_l K φ η
    B C ω z m Q e t₀ t₁ t₂ a m hBase hC hω he hInitial hz hTags hFunctional hm hF
  have hValidH := PowerlessRelativeFiniteProgramInvariant.values_l K φ η
    B C ω v c Q e t₀ t₁ t₂ a c hBase hC hω he hInitial hv hTags hFunctional hc hH
  obtain ⟨t, ht, _⟩ := hH.2.1.2 (n.eval η) ((hH.1 (n.eval η)).mpr hLength.2)
  obtain ⟨J, g, hValid⟩ := hValidH (n.eval η) t ht.2
  have hInjective := (PowerlessRelativeFiniteProgramRelocationInitial.properties_l
    K he hn hA ⟨Y, hIterationMap, hZero, hNext⟩ hValid.2.2.2.2.2).1
  let ξ : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree H).pushFree F).pushFree (A.eval η)
  let A' : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let F' : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let H' : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  have hPoint (j : type_l hℳ) : (point_m A' F' H').satisfies (ξ.pushFree j) ↔
      state_l (A.eval η) F H j := by
    simpa only [ξ, A', F', H', Term.eval, Env.pushFree_here, Env.pushFree_there] using
      point_formula_l ξ A' F' H' j
  have heEq : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false (he x)
      (PowerlessBMSQuotientSuccessor.zero_l K x))
  have h := PowerlessBMSQuotientInduction.induction_l K (point_m A' F' H') ξ ?_ ?_
  · intro j hj
    obtain ⟨k, hk⟩ := numberCode_surjective_l K ⟨j, hj⟩
    have hkEq : (numberCode_l K k).val = j := congrArg Subtype.val hk
    exact hkEq ▸ (hPoint _).mp (h k)
  · apply (hPoint _).mpr
    rw [← heEq]
    intro i s t G f J g hi hs ht hRecordF hRecordH
    have hiEq := SecondOrderFunctionProperties.value_unique_l hℳ hA hi hZero
    subst i
    have hsEq := SecondOrderFunctionProperties.value_unique_l hℳ hF.2.1 hs hF.2.2.1
    subst s
    obtain ⟨_, _, hfEq⟩ := PowerlessRelativeFiniteProgramStep.record_coordinates_l hRecordF hInitial
    subst f
    obtain ⟨J', g', hValid⟩ := hValidH _ t ht
    obtain ⟨_, hJEq, hgEq⟩ := PowerlessRelativeFiniteProgramStep.record_coordinates_l hRecordH hValid.1
    have hg : map_l (ℳ := 𝒱) g (n.eval η) J := by
      simpa only [← hJEq, ← hgEq] using hValid.2.2.2.2.2
    exact (PowerlessRelativeFiniteProgramRelocationInitial.properties_l
      K he hn hA ⟨Y, hIterationMap, hZero, hNext⟩ hg).2.2
  · intro k hPrevious
    apply (hPoint _).mpr
    intro i' s' t' G' f' J' g' hAi' hs' ht' hRecordF' hRecordH'
    have hSuccessor := PowerlessBMSQuotientSuccessor.successor_l K k
    have hkω : mem_l hℳ (numberCode_l K k).val K.omega := (numberCode_l K k).property
    have hkM := predecessor_l K hm hkω hF.1 hSuccessor
      (SecondOrderFunctionProperties.value_mem_l hℳ hF.2.1 hs').1
    obtain ⟨i, hi, _⟩ := hA.2 (numberCode_l K k).val hkω
    have hiω := hi.1
    have hSuccessorI := (PowerlessAddition.step_formula_l K.omega i i').mp
      (hNext (numberCode_l K k).val (numberCode_l K (SecondOrderModel.succ_l k)).val
        i i' hkω hSuccessor hi.2 hAi')
    have hiC := predecessor_l K hc hiω hH.1 hSuccessorI
      (SecondOrderFunctionProperties.value_mem_l hℳ hH.2.1 ht').1
    obtain ⟨s, hs, _⟩ := hF.2.1.2 (numberCode_l K k).val
      ((hF.1 (numberCode_l K k).val).mpr (Or.inl hkM))
    obtain ⟨t, ht, _⟩ := hH.2.1.2 i ((hH.1 i).mpr (Or.inl hiC))
    obtain ⟨G, f, hValidF'⟩ := hValidF _ s hs.2
    obtain ⟨J, g, hValidH'⟩ := hValidH i t ht.2
    have hRead := (hPoint _).mp hPrevious i s t G f J g hi.2 hs.2 ht.2 hValidF'.1 hValidH'.1
    have hStepF := (relation_formula_l K φ η B C ω z e t₀ t₁ t₂ s s').mp
      (hF.2.2.2 (numberCode_l K k).val (numberCode_l K (SecondOrderModel.succ_l k)).val
        s s' hkM hSuccessor hs.2 hs')
    have hStepH := (relation_formula_l K φ η B C ω v e t₀ t₁ t₂ t t').mp
      (hH.2.2.2 i i' t t' hiC hSuccessorI ht.2 ht')
    rw [hω] at hValidF' hValidH' hStepF hStepH
    obtain ⟨q, S', D', fNext, hq, hStoreF, _, hNextF⟩ :=
      PowerlessRelativeFiniteProgramStep.transition_l K φ η
        hBase hC hz hTags hFunctional hValidF' hStepF
    obtain ⟨q', T', E', gNext, hq', hStoreH, _, hNextH⟩ :=
      PowerlessRelativeFiniteProgramStep.transition_l K φ η
        hBase hC hv hTags hFunctional hValidH' hStepH
    obtain ⟨q₀, hq₀, _⟩ := hz.2 (numberCode_l K k).val hkM
    have hqValue : value_l (ℳ := 𝒱) (z.eval η) (numberCode_l K k).val q := by
      rcases hq with hq | hq
      · exact hq
      · exact (hq.1 ⟨q₀, hq₀.2⟩).elim
    obtain ⟨q₁, hq₁, _⟩ := hJoined.1.2.1.2 (numberCode_l K k).val hkM
    obtain ⟨q₂, hq₂, hRelocation⟩ := (hJoined.1.2.2 _ q₁).mp hq₁.2
    have hqq₂ := SecondOrderFunctionProperties.value_unique_l hℳ hz hqValue hq₂
    subst q₂
    have hq₁Value := (PowerlessRelativeFiniteProgramWordConcat.suffix_l
      K hω he hn hJoined.2 hkM hi.2 q₁).mpr hq₁.2
    have hq'Value : value_l (ℳ := 𝒱) (v.eval η) i q' := by
      rcases hq' with hq' | hq'
      · exact hq'
      · exact (hq'.1 ⟨q₁, hq₁Value⟩).elim
    have hqq₁ := SecondOrderFunctionProperties.value_unique_l hℳ hv hq'Value hq₁Value
    subst q'
    have hNextRead := PowerlessRelativeFiniteProgramRelocationStore.stores_l
      φ η hBase hC hValidF'.2.2.2.1 hValidF'.2.2.2.2.2 hA hInjective hi.2
        hTags hFunctional (hω ▸ hRelocation) hRead hStoreF hStoreH
    obtain ⟨_, _, hfNextEq⟩ :=
      PowerlessRelativeFiniteProgramStep.record_coordinates_l hNextF.1 hRecordF'
    obtain ⟨_, _, hgNextEq⟩ :=
      PowerlessRelativeFiniteProgramStep.record_coordinates_l hNextH.1 hRecordH'
    exact hfNextEq ▸ hgNextEq ▸ hNextRead

def result_m {Γ Δ : SortContext ℒ} (ω A F H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up ω))
    (state_m (up A) (up F) (up H) (.bvar .here))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q A r c v S D F T E H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <| .imp (record_m e e e a) <|
          .imp (SecondOrderObjectSyntax.map_m z m Q) <| .imp (tags_m t₀ t₁ t₂) <|
            .imp (functional_m φ B) <| .imp (SecondOrderObjectSyntax.member_m n ω) <|
              .imp (SecondOrderObjectSyntax.member_m m ω) <|
                .imp (PowerlessRelativeFiniteProgramConcat.joined_m B C ω e t₀ t₁ t₂ n w m z Q A r c v) <|
                  .imp (trace_m (relation_m φ B C ω z e t₀ t₁ t₂) e a m S D F) <|
                    .imp (trace_m (relation_m φ B C ω v e t₀ t₁ t₂) e a c T E H)
                      (result_m ω A F H)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q A r c v S D F T E H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω e t₀ t₁ t₂ a n w m z Q A r c v S D F T E H)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q A r c v S D F T E H : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω e t₀ t₁ t₂ a n w m z Q A r c v S D F T E H).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, PowerlessDefinableFiniteTraceDerives.zero_m, tags_m, functional_m,
    Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    record_formula_l, map_formula_l, PowerlessRelativeFiniteProgramConcat.joined_formula_l K,
    trace_formula_l, state_formula_l, parameters_pushBound_l, parameters_empty_l, at_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hz hTags hFunctional hn hm hJoined hF hH j hj
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  exact values_l K φ η B C ω e t₀ t₁ t₂ a n w m z Q A r c v hBase hC hωEq he hInitial
    hz hTags hFunctional (hωEq ▸ hn) (hωEq ▸ hm) hJoined hF hH j (hωEq ▸ hj)

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω e t₀ t₁ t₂ a n w m z Q A r c v S D F T E H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω e t₀ t₁ t₂ a n w m z Q A r c v S D F T E H)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B C ω e t₀ t₁ t₂ a n w m z Q A r c v S D F T E H)

#print axioms induction_derives_m
#print axioms values_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConcatTrace
