import BMSConstructibleBridge.PowerlessRelativeFiniteProgramInvariant

/-! # 实际内部执行历史的持久存储读数

读数来自同一历史中的实际状态与存储图，不用缺省输出代替。
原公式归纳证明较早状态的读数保留到全部后续状态，覆盖非标准长度。
本模块的对象出口供程序拼接的完整输出保持使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramPersistentRead

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramStep (record_m record_l valid_l)
open PowerlessRelativeFiniteProgramExecution (relation_m relation_formula_l)
open PowerlessDefinableFiniteTrace (trace_m trace_l trace_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_m functional_l tags_m)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ t)

def read_m {Γ Δ : SortContext ℒ} (F i k y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let s : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let D := .bvar (.there .here)
    let f := .bvar .here
    .conj (SecondOrderObjectSyntax.value_m (up₃ F) (up₃ i) s) <|
      .conj (record_m (up₃ i) D f s) (SecondOrderObjectSyntax.value_m f (up₃ k) (up₃ y))

def point_m {Δ : SortContext ℒ} (F k y : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: Δ) :=
  .forallE .set <|
    .imp (SecondOrderObjectSyntax.value_m (up (F.weakenFree SetTheory.SetSort.set))
      (up (.fvar .here)) (.bvar .here)) <|
      .forallE .set <|
        let j : Term ℒ [.set, .set] (.set :: Δ) .set := up₂ (.fvar .here)
        let i := .bvar .here
        let F' := up₂ (F.weakenFree SetTheory.SetSort.set)
        let k' := up₂ (k.weakenFree SetTheory.SetSort.set)
        let y' := up₂ (y.weakenFree SetTheory.SetSort.set)
        .imp (.disj (SecondOrderObjectSyntax.member_m i j) (.equal i j)) <|
          .imp (read_m F' i k' y') (read_m F' j k' y')

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def read_l (F i k y : type_l hℳ) : Prop :=
  ∃ s D f, value_l (ℳ := 𝒱) F i s ∧ record_l i D f s ∧ value_l (ℳ := 𝒱) f k y

theorem read_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (F i k y : Term ℒ Γ Δ .set) :
    (read_m F i k y).satisfies η ↔ read_l (F.eval η) (i.eval η) (k.eval η) (y.eval η) := by
  simp only [read_m, read_l, Formula.satisfies, value_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l, up₃, up₂, up,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem point_formula_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ)
    (F k y : Term ℒ [] Δ .set) (j : type_l hℳ) :
    (point_m F k y).satisfies (η.pushFree j) ↔
      ∀ t, value_l (ℳ := 𝒱) (F.eval η) j t → ∀ i,
        (mem_l hℳ i j ∨ i = j) → read_l (F.eval η) i (k.eval η) (y.eval η) →
          read_l (F.eval η) j (k.eval η) (y.eval η) := by
  simp only [point_m, Formula.satisfies, value_formula_l, read_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₂, up,
    Term.eval_weakenBound, Term.eval_weakenFree, Term.eval, Env.pushFree_here]
  rfl

theorem read_iff_l {F S E i s D f k y : type_l hℳ}
    (hF : map_l (ℳ := 𝒱) F S E) (hs : value_l (ℳ := 𝒱) F i s)
    (hRecord : record_l i D f s) : read_l F i k y ↔ value_l (ℳ := 𝒱) f k y := by
  constructor
  · rintro ⟨t, G, g, ht, hRecord', hy⟩
    have hts := SecondOrderFunctionProperties.value_unique_l hℳ hF ht hs
    subst t
    obtain ⟨_, _, hgf⟩ := PowerlessRelativeFiniteProgramStep.record_coordinates_l hRecord' hRecord
    exact hgf ▸ hy
  · intro hy
    exact ⟨s, D, f, hs, hRecord, hy⟩

private theorem predecessor_bound_l (K : source_coding_l hℳ) {n S : type_l hℳ}
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
  exact hlEq ▸ (numberCode_mem_iff_lt_l K k l).mpr
    ((SecondOrderOrder.succ_iff_l hℳ k l).mp ((numberCode_mem_iff_lt_l K _ _).mp hk))

theorem values_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) {S D F : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (N.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) (hn : mem_l hℳ (n.eval η) K.omega)
    (hF : trace_l (relation_m φ B C ω w e t₀ t₁ t₂) η
      (e.eval η) (a.eval η) (n.eval η) S D F) :
    ∀ i j k y t, (mem_l hℳ i j ∨ i = j) → value_l (ℳ := 𝒱) F j t →
      read_l F i k y → read_l F j k y := by
  have hValid := PowerlessRelativeFiniteProgramInvariant.values_l K φ η
    B C ω w N Q e t₀ t₁ t₂ a n hBase hC hω he hInitial hw hTags hFunctional hn hF
  intro i j k y t hij ht hRead
  let ξ : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree y).pushFree k).pushFree F
  let F' : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let k' : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let y' : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  have hPoint (j : type_l hℳ) : (point_m F' k' y').satisfies (ξ.pushFree j) ↔
      ∀ t, value_l (ℳ := 𝒱) F j t → ∀ i,
        (mem_l hℳ i j ∨ i = j) → read_l F i k y → read_l F j k y := by
    simpa only [ξ, F', k', y', Term.eval, Env.pushFree_here, Env.pushFree_there] using
      point_formula_l ξ F' k' y' j
  have h := PowerlessBMSQuotientInduction.induction_l K (point_m F' k' y') ξ ?_ ?_
  · obtain ⟨_, _, hjValid⟩ := hValid j t ht
    have hjω : mem_l hℳ j K.omega := hω ▸ hjValid.2.1
    obtain ⟨l, hl⟩ := numberCode_surjective_l K ⟨j, hjω⟩
    have hlEq : (numberCode_l K l).val = j := congrArg Subtype.val hl
    exact (hPoint j).mp (hlEq ▸ h l) t ht i hij hRead
  · apply (hPoint _).mpr
    intro s hs i hi hRead
    rcases hi with hi | rfl
    · exact (PowerlessBMSQuotientSuccessor.zero_l K i hi).elim
    · exact hRead
  · intro l hPrevious
    apply (hPoint _).mpr
    intro t ht i hi hRead
    rcases hi with hi | rfl
    · have hjS := (SecondOrderFunctionProperties.value_mem_l hℳ hF.2.1 ht).1
      have hlN := predecessor_bound_l K hn hF.1 l hjS
      have hlS := (hF.1 (numberCode_l K l).val).mpr (Or.inl hlN)
      obtain ⟨s, hs, _⟩ := hF.2.1.2 _ hlS
      have hiPrevious := (PowerlessBMSQuotientSuccessor.successor_l K l i).mp hi
      have hOld := (hPoint _).mp hPrevious s hs.2 i hiPrevious hRead
      obtain ⟨E, g, hsValid⟩ := hValid _ s hs.2
      have hgy := (read_iff_l hF.2.1 hs.2 hsValid.1).mp hOld
      have hRelation := hF.2.2.2 (numberCode_l K l).val
        (numberCode_l K (SecondOrderModel.succ_l l)).val s t hlN
        (PowerlessBMSQuotientSuccessor.successor_l K l) hs.2 ht
      have hStep := (relation_formula_l K φ η B C ω w e t₀ t₁ t₂ s t).mp hRelation
      rw [hω] at hsValid hStep
      obtain ⟨q, T, G, f, _, hStore, hT, hNext⟩ := PowerlessRelativeFiniteProgramStep.transition_l
        K φ η hBase hC hw hTags hFunctional hsValid hStep
      obtain ⟨z, _, _, _, _, _, _, _, hStoreRead⟩ := hStore
      have hTY : T = (numberCode_l K (SecondOrderModel.succ_l l)).val :=
        SecondOrderQuotient.ext_l hℳ T _ (fun x =>
          (hT x).trans (PowerlessBMSQuotientSuccessor.successor_l K l x).symm)
      exact ⟨t, G, f, ht, hTY ▸ hNext.1, (hStoreRead k y).mpr (Or.inl hgy)⟩
    · exact hRead

def result_m {Γ Δ : SortContext ℒ} (F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let i : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set :=
      .bvar (.there (.there (.there .here)))
    let j := .bvar (.there (.there .here))
    let k := .bvar (.there .here)
    let y := .bvar .here
    .imp (.disj (SecondOrderObjectSyntax.member_m i j) (.equal i j)) <|
      .imp (.existsE .set (SecondOrderObjectSyntax.value_m (up (up₄ F)) (up j) (.bvar .here))) <|
        .imp (read_m (up₄ F) i k y) (read_m (up₄ F) j k y)

def conclusion_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    .imp (trace_m (relation_m φ B C ω w e t₀ t₁ t₂) (up₃ e) (up₃ a) (up₃ n)
      (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
      (result_m (.bvar .here))

theorem conclusion_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B C ω w e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) :
    (conclusion_m φ B C ω w e t₀ t₁ t₂ a n).satisfies η ↔
      ∀ S D F, trace_l (relation_m φ B C ω w e t₀ t₁ t₂) η
        (e.eval η) (a.eval η) (n.eval η) S D F →
          ∀ i j k y, (mem_l hℳ i j ∨ i = j) → (∃ t, value_l (ℳ := 𝒱) F j t) →
            read_l F i k y → read_l F j k y := by
  simp only [conclusion_m, result_m, Formula.satisfies, trace_formula_l, read_formula_l,
    value_formula_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₄, up₃, up₂, up,
    Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <| .imp (record_m e e e a) <|
          .imp (SecondOrderObjectSyntax.map_m w N Q) <| .imp (tags_m t₀ t₁ t₂) <|
            .imp (functional_m φ B) <| .imp (SecondOrderObjectSyntax.member_m n ω)
              (conclusion_m φ B C ω w e t₀ t₁ t₂ a n)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w N Q e t₀ t₁ t₂ a n)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω w N Q e t₀ t₁ t₂ a n).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, PowerlessDefinableFiniteTraceDerives.zero_m, tags_m, functional_m,
    Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l, map_formula_l, conclusion_formula_l,
    PowerlessBMSQuotientSubsetImageDerives.at_formula_l, parameters_pushBound_l,
    parameters_empty_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hω he hInitial hw hTags hFunctional hn S D F hF i j k y hij ht hRead
  obtain ⟨t, ht⟩ := ht
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  exact values_l K φ η B C ω w N Q e t₀ t₁ t₂ a n
    hBase hC hωEq he hInitial hw hTags hFunctional (hωEq ▸ hn) hF i j k y t hij ht hRead

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ a n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w N Q e t₀ t₁ t₂ a n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω w N Q e t₀ t₁ t₂ a n)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramPersistentRead
