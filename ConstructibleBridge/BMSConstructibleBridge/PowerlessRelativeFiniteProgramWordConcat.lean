import BMSConstructibleBridge.PowerlessRelativeFiniteProgramWordAppend
import BMSConstructibleBridge.PowerlessRelativeClassAdditionGraph
import BMSConstructibleBridge.PowerlessRelativeLimitFiniteMaps
import BMSConstructibleBridge.PowerlessAdditionIterationSyntax
import BMSConstructibleBridge.SecondOrderFiniteConcatArithmetic
import BMSConstructibleBridge.SecondOrderDefinableRelationImage

/-! # 原 Z₂ 中实际有限指令词的拼接

先在给定陪域上的有界乘积中构造实际关系图，用内部加法分段证明它
是干净映射，再以共同极限层有限图定理取得 Class 成员性。没有使用
完整 Collection 或假定新词存在。此处只是词拼接；右词的父坐标重编号
及两次执行的读数保持另行证明，不把本结论误报为程序求值闭包。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramWordConcat

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def body_m {Γ Δ : SortContext ℒ} (n w m z A i q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (SecondOrderObjectSyntax.member_m i n) (SecondOrderObjectSyntax.value_m w i q))
    (.existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up m)) <|
      .conj (SecondOrderObjectSyntax.value_m (up A) (.bvar .here) (up i))
        (SecondOrderObjectSyntax.value_m (up z) (.bvar .here) (up q)))

def reading_m {Γ Δ : SortContext ℒ} (n w m z A v : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .iff
    (SecondOrderObjectSyntax.value_m (up₂ v) (.bvar (.there .here)) (.bvar .here))
    (body_m (up₂ n) (up₂ w) (up₂ m) (up₂ z) (up₂ A) (.bvar (.there .here)) (.bvar .here))

def concat_m {Γ Δ : SortContext ℒ} (B ω e n w m z Q A c v : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.class_m B A) <|
    .conj (SecondOrderObjectSyntax.map_m A ω ω) <|
      .conj (PowerlessAdditionIterationSyntax.formula_m ω e n A) <|
        .conj (SecondOrderObjectSyntax.value_m A m c) <|
          .conj (PowerlessRelativeHierarchySyntax.class_m B c) <|
            .conj (PowerlessRelativeHierarchySyntax.class_m B v) <|
              .conj (SecondOrderObjectSyntax.map_m v c Q) (reading_m n w m z A v)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def body_l (n w m z A i q : type_l hℳ) : Prop :=
  (mem_l hℳ i n ∧ value_l (ℳ := 𝒱) w i q) ∨
    ∃ j, mem_l hℳ j m ∧ value_l (ℳ := 𝒱) A j i ∧ value_l (ℳ := 𝒱) z j q

def concat_l (B ω e n w m z Q A c v : type_l hℳ) : Prop :=
  PowerlessRelativeClassCorrespondence.member_l hℳ B A ∧
    map_l (ℳ := 𝒱) A ω ω ∧ PowerlessAddition.iteration_l (ℳ := 𝒱) ω e n A ∧
      value_l (ℳ := 𝒱) A m c ∧ PowerlessRelativeClassCorrespondence.member_l hℳ B c ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ B v ∧ map_l (ℳ := 𝒱) v c Q ∧
          ∀ i q, value_l (ℳ := 𝒱) v i q ↔ body_l n w m z A i q

theorem body_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (n w m z A i q : Term ℒ Γ Δ .set) :
    (body_m n w m z A i q).satisfies η ↔
      body_l (n.eval η) (w.eval η) (m.eval η) (z.eval η) (A.eval η) (i.eval η) (q.eval η) := by
  simp only [body_m, body_l, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem concat_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω e n w m z Q A c v : Term ℒ Γ Δ .set) :
    (concat_m B ω e n w m z Q A c v).satisfies η ↔
      concat_l (B.eval η) (ω.eval η) (e.eval η) (n.eval η) (w.eval η) (m.eval η)
        (z.eval η) (Q.eval η) (A.eval η) (c.eval η) (v.eval η) := by
  simp only [concat_m, concat_l, reading_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassCorrespondence.member_l, PowerlessAdditionIterationSyntax.formula_l,
    map_formula_l, value_formula_l, body_formula_l, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]

/-- 对任意原商有限图给出类成员性，不把原图的 Class 性列为假设。 -/
theorem finite_class_l (K : source_coding_l hℳ) {B Q n f : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ B K.omega)
    (hQC : PowerlessRelativeClassCorrespondence.member_l hℳ B Q)
    (hn : mem_l hℳ n K.omega) (hf : map_l (ℳ := 𝒱) f n Q) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B f := by
  obtain ⟨α, C, hC, hωC, hQC⟩ := PowerlessRelativeClassBounds.common_l hℳ hBase hωC hQC
  obtain ⟨β, hβ, hαβ, hNoMax⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ α
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hC)
  obtain ⟨D, hD⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hβ
  have hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β := ⟨⟨α, hαβ⟩, hNoMax⟩
  have hωD := PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hC hD K.omega hωC
  have hQD := PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hC hD Q hQC
  exact ⟨β, D, hD, PowerlessRelativeLimitFiniteMaps.member_l hℳ hBase hLimit hD K hωD hQD hn hf⟩

theorem given_exists_l (K : source_coding_l hℳ) {B e n w m z Q A : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ B K.omega)
    (hQC : PowerlessRelativeClassCorrespondence.member_l hℳ B Q)
    (he : ∀ x, ¬mem_l hℳ x e) (hn : mem_l hℳ n K.omega) (hm : mem_l hℳ m K.omega)
    (hw : map_l (ℳ := 𝒱) w n Q) (hz : map_l (ℳ := 𝒱) z m Q)
    (hAC : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hMap : map_l (ℳ := 𝒱) A K.omega K.omega)
    (hIteration : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega e n A) :
    ∃ c v, concat_l B K.omega e n w m z Q A c v := by
  obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨n, hn⟩
  obtain ⟨b, hb⟩ := numberCode_surjective_l K ⟨m, hm⟩
  have haEq : (numberCode_l K a).val = n := congrArg Subtype.val ha
  have hbEq : (numberCode_l K b).val = m := congrArg Subtype.val hb
  rw [← haEq] at hIteration
  let c := (numberCode_l K (SecondOrderModel.add_l a b)).val
  have hcω : mem_l hℳ c K.omega := (numberCode_l K (SecondOrderModel.add_l a b)).property
  have hcC := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωC hcω
  have hValue : value_l (ℳ := 𝒱) A m c := hbEq ▸
    (SecondOrderFiniteConcatArithmetic.read_l K a he hIteration hMap b c).mpr rfl
  have hBounds (i q : type_l hℳ) (h : body_l n w m z A i q) : mem_l hℳ i c ∧ mem_l hℳ q Q := by
    rcases h with ⟨hi, hq⟩ | ⟨j, hj, hji, hq⟩
    · have hi' : mem_l hℳ i (numberCode_l K a).val := haEq.symm ▸ hi
      exact ⟨SecondOrderFiniteConcatArithmetic.prefix_l K a b hi',
        (SecondOrderFunctionProperties.value_mem_l hℳ hw hq).2⟩
    · obtain ⟨i', hi', hji'⟩ := SecondOrderFiniteConcatArithmetic.shifted_l K a b
        he hIteration hMap (hbEq.symm ▸ hj)
      have hiEq := SecondOrderFunctionProperties.value_unique_l hℳ hMap hji hji'
      exact ⟨hiEq.symm ▸ hi', (SecondOrderFunctionProperties.value_mem_l hℳ hz hq).2⟩
  have hTotal (i : type_l hℳ) (hi : mem_l hℳ i c) : ∃ q, body_l n w m z A i q := by
    rcases SecondOrderFiniteConcatArithmetic.segment_l K a b he hIteration hMap hi with hi | ⟨j, hj, hji⟩
    · obtain ⟨q, hq, _⟩ := hw.2 i (haEq ▸ hi)
      exact ⟨q, Or.inl ⟨haEq ▸ hi, hq.2⟩⟩
    · obtain ⟨q, hq, _⟩ := hz.2 j (hbEq ▸ hj)
      exact ⟨q, Or.inr ⟨j, hbEq ▸ hj, hji, hq.2⟩⟩
  have hUnique (i q r : type_l hℳ) (hq : body_l n w m z A i q)
      (hr : body_l n w m z A i r) : q = r := by
    rcases hq with ⟨hi, hq⟩ | ⟨j, _, hji, hq⟩
    · rcases hr with ⟨_, hr⟩ | ⟨k, _, hki, _⟩
      · exact SecondOrderFunctionProperties.value_unique_l hℳ hw hq hr
      · exact (SecondOrderFiniteConcatArithmetic.lower_l K a he hIteration hMap hki
          (haEq.symm ▸ hi)).elim
    · rcases hr with ⟨hi, _⟩ | ⟨k, _, hki, hr⟩
      · exact (SecondOrderFiniteConcatArithmetic.lower_l K a he hIteration hMap hji
          (haEq.symm ▸ hi)).elim
      · have hjk := SecondOrderFiniteConcatArithmetic.cancel_l K a he hIteration hMap hji hki
        subst k
        exact SecondOrderFunctionProperties.value_unique_l hℳ hz hq hr
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set] :=
    (((((Env.empty).pushFree A).pushFree z).pushFree m).pushFree w).pushFree n
  let φ : Formula ℒ [] (.set :: .set :: [.set, .set, .set, .set, .set]) :=
    body_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar .here) (.fvar (.there .here))
  obtain ⟨v, hGraph⟩ := SecondOrderDefinableRelationImage.exists_l hℳ φ η c Q
  have hSpec : ∀ p, mem_l hℳ p v ↔ ∃ i q, mem_l hℳ i c ∧ mem_l hℳ q Q ∧
      body_l n w m z A i q ∧ ordered_l (ℳ := 𝒱) i q p := by
    intro p
    simpa only [φ, body_formula_l, η, Term.eval, Env.pushFree, Assignment.push_here, Assignment.push_there,
      SecondOrderPairObjects.ordered_l,
      SecondOrderPairObjects.pair_l, ThirdOrderSemantics.ordered_l, ThirdOrderSemantics.pair_l,
      ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using hGraph p
  have hRead (i q : type_l hℳ) : value_l (ℳ := 𝒱) v i q ↔ body_l n w m z A i q := by
    constructor
    · rintro ⟨p, hp, hOrdered⟩
      obtain ⟨i', q', _, _, hBody, hOrdered'⟩ := (hSpec p).mp hp
      obtain ⟨hiEq, hqEq⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hOrdered hOrdered').mp rfl
      subst i'
      subst q'
      exact hBody
    · intro hBody
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ i q
      exact ⟨p, (hSpec p).mpr ⟨i, q, (hBounds i q hBody).1, (hBounds i q hBody).2, hBody, hp⟩, hp⟩
  have hv : map_l (ℳ := 𝒱) v c Q := by
    constructor
    · intro p hp
      obtain ⟨i, q, hi, hq, _, hp⟩ := (hSpec p).mp hp
      exact ⟨i, q, hi, hq, hp⟩
    · intro i hi
      obtain ⟨q, hq⟩ := hTotal i hi
      exact ⟨q, ⟨(hBounds i q hq).2, (hRead i q).mpr hq⟩,
        fun r hr => hUnique i r q ((hRead i r).mp hr.2) hq⟩
  have hvC := finite_class_l K hBase hωC hQC hcω hv
  refine ⟨c, v, hAC, hMap, ?_, hValue, hcC, hvC, hv, hRead⟩
  simpa only [haEq] using hIteration

theorem exists_l (K : source_coding_l hℳ) {B e n w m z Q : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ B K.omega)
    (hQC : PowerlessRelativeClassCorrespondence.member_l hℳ B Q)
    (he : ∀ x, ¬mem_l hℳ x e) (hn : mem_l hℳ n K.omega) (hm : mem_l hℳ m K.omega)
    (hw : map_l (ℳ := 𝒱) w n Q) (hz : map_l (ℳ := 𝒱) z m Q) :
    ∃ A c v, concat_l B K.omega e n w m z Q A c v := by
  obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have haEq : (numberCode_l K a).val = n := congrArg Subtype.val ha
  obtain ⟨A, hIteration, hMap⟩ := PowerlessBMSQuotientArithmetic.additionIteration_exists_l K a
  have hAC := PowerlessRelativeClassAdditionGraph.member_l (hBase := hBase) K
    (a := (numberCode_l K a).val) (numberCode_l K a).property hIteration hMap
  have heEq : (numberCode_l K (SecondOrderModel.zero_l ℳ)).val = e :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false
      (PowerlessBMSQuotientSuccessor.zero_l K x) (he x))
  rw [heEq, haEq] at hIteration
  obtain ⟨c, v, hConcat⟩ := given_exists_l K hBase hωC hQC he hn hm hw hz hAC hMap hIteration
  exact ⟨A, c, v, hConcat⟩

theorem prefix_l (K : source_coding_l hℳ) {B ω e n w m z Q A c v : type_l hℳ}
    (hω : ω = K.omega) (he : ∀ x, ¬mem_l hℳ x e) (hn : mem_l hℳ n K.omega)
    (hConcat : concat_l B ω e n w m z Q A c v) :
    PowerlessRelativeFiniteProgramPrefix.agree_l n w v := by
  obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have haEq : (numberCode_l K a).val = n := congrArg Subtype.val ha
  have hMap : map_l (ℳ := 𝒱) A K.omega K.omega := hω ▸ hConcat.2.1
  have hIteration : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega e (numberCode_l K a).val A := by
    simpa only [hω, haEq] using hConcat.2.2.1
  intro i hi q
  constructor
  · intro hq
    exact (hConcat.2.2.2.2.2.2.2 i q).mpr (Or.inl ⟨hi, hq⟩)
  · intro hq
    rcases (hConcat.2.2.2.2.2.2.2 i q).mp hq with ⟨_, hq⟩ | ⟨j, _, hji, _⟩
    · exact hq
    · exact (SecondOrderFiniteConcatArithmetic.lower_l K a he hIteration hMap hji
        (haEq.symm ▸ hi)).elim

theorem suffix_l (K : source_coding_l hℳ) {B ω e n w m z Q A c v j i : type_l hℳ}
    (hω : ω = K.omega) (he : ∀ x, ¬mem_l hℳ x e) (hn : mem_l hℳ n K.omega)
    (hConcat : concat_l B ω e n w m z Q A c v)
    (hj : mem_l hℳ j m) (hji : value_l (ℳ := 𝒱) A j i) (q : type_l hℳ) :
    value_l (ℳ := 𝒱) v i q ↔ value_l (ℳ := 𝒱) z j q := by
  obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have haEq : (numberCode_l K a).val = n := congrArg Subtype.val ha
  have hMap : map_l (ℳ := 𝒱) A K.omega K.omega := hω ▸ hConcat.2.1
  have hIteration : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega e (numberCode_l K a).val A := by
    simpa only [hω, haEq] using hConcat.2.2.1
  constructor
  · intro hq
    rcases (hConcat.2.2.2.2.2.2.2 i q).mp hq with ⟨hi, _⟩ | ⟨k, _, hki, hq⟩
    · exact (SecondOrderFiniteConcatArithmetic.lower_l K a he hIteration hMap hji
        (haEq.symm ▸ hi)).elim
    · have hjk := SecondOrderFiniteConcatArithmetic.cancel_l K a he hIteration hMap hji hki
      exact hjk.symm ▸ hq
  · intro hq
    exact (hConcat.2.2.2.2.2.2.2 i q).mpr (Or.inr ⟨j, hj, hji, hq⟩)

/-- 实际拼接长度属于内部 ω，且不短于左词；不借用完整 Collection 的加法图。 -/
theorem length_l (K : source_coding_l hℳ) {B ω e n w m z Q A c v : type_l hℳ}
    (hω : ω = K.omega) (he : ∀ x, ¬mem_l hℳ x e) (hn : mem_l hℳ n K.omega)
    (hConcat : concat_l B ω e n w m z Q A c v) :
    mem_l hℳ c K.omega ∧ (mem_l hℳ n c ∨ n = c) := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  have hMap : map_l (ℳ := 𝒱) A K.omega K.omega := hω ▸ hConcat.2.1
  have hmc := hConcat.2.2.2.1
  have hBounds := SecondOrderFunctionProperties.value_mem_l hℳ hMap hmc
  obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨n, hn⟩
  obtain ⟨b, hb⟩ := numberCode_surjective_l K ⟨m, hBounds.1⟩
  have haEq : (numberCode_l K a).val = n := congrArg Subtype.val ha
  have hbEq : (numberCode_l K b).val = m := congrArg Subtype.val hb
  have hIteration : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega e (numberCode_l K a).val A := by
    simpa only [hω, haEq] using hConcat.2.2.1
  have hcEq := (SecondOrderFiniteConcatArithmetic.read_l K a he hIteration hMap b c).mp
    (hbEq.symm ▸ hmc)
  refine ⟨hBounds.2, ?_⟩
  have hLe : a ≤ a + b := le_add_of_nonneg_right (SecondOrderAlgebra.zero_le_l hℳ b)
  rcases lt_or_eq_of_le hLe with h | h
  · exact Or.inl (haEq ▸ hcEq.symm ▸ (numberCode_mem_iff_lt_l K a (a + b)).mpr h)
  · exact Or.inr (haEq.symm.trans ((congrArg (fun k => (numberCode_l K k).val) h).trans hcEq.symm))

def schema_m {Δ : SortContext ℒ} (B ω e n w m z Q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
          .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
            .imp (SecondOrderObjectSyntax.member_m n ω) <|
              .imp (SecondOrderObjectSyntax.member_m m ω) <|
                .imp (SecondOrderObjectSyntax.map_m w n Q) <|
                  .imp (SecondOrderObjectSyntax.map_m z m Q) <|
                    .existsE .set <| .existsE .set <| .existsE .set <|
                      concat_m (up₃ B) (up₃ ω) (up₃ e) (up₃ n) (up₃ w) (up₃ m) (up₃ z) (up₃ Q)
                        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def sentence_m {Δ : SortContext ℒ} (B ω e n w m z Q : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω e n w m z Q)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω e n w m z Q : Term ℒ [] Δ .set) :
    (sentence_m B ω e n w m z Q).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, PowerlessDefinableFiniteTraceDerives.zero_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    concat_formula_l K, map_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hω hωC hQC he hn hm hw hz
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  obtain ⟨A, c, v, hConcat⟩ := exists_l K hBase (hωEq ▸ hωC) hQC he
    (hωEq ▸ hn) (hωEq ▸ hm) hw hz
  exact ⟨A, c, v, hωEq.symm ▸ hConcat⟩

theorem derives_m {Δ : SortContext ℒ} (B ω e n w m z Q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω e n w m z Q)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B ω e n w m z Q)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramWordConcat
