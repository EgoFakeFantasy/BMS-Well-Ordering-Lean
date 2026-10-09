import BMSConstructibleBridge.PowerlessDefinableFiniteTraceDerives
import BMSConstructibleBridge.PowerlessRelativeLimitFunctionAppend

/-! # 同一极限层中的实际内部有限轨迹

原矩阵只须在 W 上有 W 见证。初值、每个内部自然数长度的域、
陪域和历史图均留在同一 W；归纳是原 Z₂ 公式实例。矩阵参数
不必属于 W，不要求 W 完整分离、Collection 或无限轨迹集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitDefinableFiniteTrace

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_l parameters_pushBound_l parameters_empty_l)
open PowerlessDefinableFiniteTrace (trace_l trace_m trace_formula_l lift_m lift_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def finite_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (W e a n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let S : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let D := .bvar (.there .here)
    let f := .bvar .here
    .conj (SecondOrderObjectSyntax.member_m S (up₃ W)) <|
      .conj (SecondOrderObjectSyntax.member_m D (up₃ W)) <|
        .conj (SecondOrderObjectSyntax.member_m f (up₃ W))
          (trace_m φ (up₃ e) (up₃ a) (up₃ n) S D f)

def point_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (W e a : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: Δ) :=
  finite_m (lift_m φ) (W.weakenFree SetTheory.SetSort.set)
    (e.weakenFree SetTheory.SetSort.set) (a.weakenFree SetTheory.SetSort.set) (.fvar .here)

theorem finite_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ) (W e a n : Term ℒ Γ Δ .set) :
    (finite_m φ W e a n).satisfies η ↔ ∃ S D f,
      member_l 𝒩 S (W.eval η) ∧ member_l 𝒩 D (W.eval η) ∧ member_l 𝒩 f (W.eval η) ∧
        trace_l φ (parameters_l η) (e.eval η) (a.eval η) (n.eval η) S D f := by
  simp only [finite_m, Formula.satisfies, trace_formula_l, parameters_pushBound_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

theorem point_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (W e a : Term ℒ [] Δ .set)
    (n : carrier_l 𝒩) : (point_m φ W e a).satisfies (η.pushFree n) ↔ ∃ S D f,
      member_l 𝒩 S (W.eval η) ∧ member_l 𝒩 D (W.eval η) ∧ member_l 𝒩 f (W.eval η) ∧
        trace_l φ η (e.eval η) (a.eval η) n S D f := by
  simp only [point_m, finite_formula_l, parameters_empty_l, Term.eval_weakenFree,
    Term.eval, trace_l, lift_formula_l, Env.pushFree_here]

theorem induction_derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (W e a : Term ℒ [] Δ .set) : Derives SecondOrderArithmetic.theory_m []
      (SecondOrderArithmetic.induction_m (GraphTranslation.form_m (point_m φ W e a))) :=
  GraphTranslation.induction_m (point_m φ W e a)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B β W e a : Term ℒ [] Δ .set)
    (hB : ∀ x, mem_l hℳ x (B.eval η) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η))
    (hβ : limit_l hℳ (β.eval η)) (hW : level_l hℳ (B.eval η) (β.eval η) (W.eval η))
    (hωW : mem_l hℳ K.omega (W.eval η)) (ha : mem_l hℳ (a.eval η) (W.eval η))
    (he : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hφ : ∀ x, mem_l hℳ x (W.eval η) → ∃ y, mem_l hℳ y (W.eval η) ∧
      φ.satisfies ((η.pushFree x).pushFree y)) (n : SecondOrderModel.num_l ℳ) :
    ∃ S D f, mem_l hℳ S (W.eval η) ∧ mem_l hℳ D (W.eval η) ∧ mem_l hℳ f (W.eval η) ∧
      trace_l φ η (e.eval η) (a.eval η) (numberCode_l K n).val S D f := by
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW
  have hNumber (i : SecondOrderModel.num_l ℳ) : mem_l hℳ (numberCode_l K i).val (W.eval η) :=
    hTrans K.omega hωW _ (numberCode_l K i).property
  have h := PowerlessBMSQuotientInduction.induction_l K (point_m φ W e a) η ?_ ?_
  · exact (point_formula_l φ η W e a _).mp (h n)
  · apply (point_formula_l φ η W e a _).mpr
    let z := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
    let S := (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val
    have hS := PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.zero_l ℳ)
    have hz := PowerlessBMSQuotientSuccessor.zero_l K
    obtain ⟨D, hD⟩ := SecondOrderPairObjects.pair_exists_l hℳ (a.eval η) (a.eval η)
    have hDW := PowerlessRelativeLimitClosure.pair_l hℳ hB hβ hW ha ha hD
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ z (a.eval η)
    have hpW := PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW (hNumber _) ha hp
    obtain ⟨f, hf⟩ := SecondOrderPairObjects.pair_exists_l hℳ p p
    have hfW := PowerlessRelativeLimitClosure.pair_l hℳ hB hβ hW hpW hpW hf
    have hSingleton := SecondOrderFunctionAppend.singleton_l hℳ
      (fun x => (hS x).trans (or_iff_right (hz x)))
      ((hD (a.eval η)).mpr (Or.inl rfl)) hp
      (fun q => by simpa only [or_self] using hf q)
    exact ⟨S, D, f, hNumber _, hDW, hfW, hS, hSingleton.1,
      (hSingleton.2 _ _).mpr ⟨he, rfl⟩, fun i _ _ _ hi => (hz i hi).elim⟩
  · intro i hPrevious
    obtain ⟨S, D, f, hSW, hDW, hfW, hF⟩ := (point_formula_l φ η W e a _).mp hPrevious
    have hSEq : S = (numberCode_l K (SecondOrderModel.succ_l i)).val :=
      SecondOrderQuotient.ext_l hℳ _ _ (fun x => (hF.1 x).trans
        (PowerlessBMSQuotientSuccessor.successor_l K i x).symm)
    obtain ⟨z, hz, _⟩ := hF.2.1.2 _ ((hF.1 _).mpr (Or.inr rfl))
    obtain ⟨d, hdW, hd⟩ := hφ z (hTrans D hDW z hz.1)
    obtain ⟨T, E, g, hTW, hEW, hgW, hT, _, hG, hRead⟩ :=
      PowerlessRelativeLimitFunctionAppend.exists_l hB hβ hW hfW hSW hDW hSW hdW hF.2.1
        (fun hSS => SecondOrderNaturalCases.asymmetry_l hℳ hSS hSS)
    apply (point_formula_l φ η W e a _).mpr
    rw [← hSEq]
    exact ⟨T, E, g, hTW, hEW, hgW, PowerlessDefinableFiniteTrace.extension_l K φ η
      (n := (numberCode_l K i).val) (numberCode_l K i).property hF hG hT hRead hz.2 hd⟩

def total_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up W)) <|
    .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ W))
      (at_m φ (.bvar (.there .here)) (.bvar .here))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β W ω e a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (SecondOrderOmegaSyntax.omega_m ω) <|
          .imp (SecondOrderObjectSyntax.member_m ω W) <|
            .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
              .imp (SecondOrderObjectSyntax.member_m a W) <|
                .imp (total_m φ W) <| .imp (SecondOrderObjectSyntax.member_m n ω)
                  (finite_m φ W e a n)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β W ω e a n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β W ω e a n)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B β W ω e a n : Term ℒ [] Δ .set) :
    (sentence_m φ B β W ω e a n).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, total_m, PowerlessDefinableFiniteTraceDerives.zero_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    SecondOrderOmegaSyntax.omega_l, finite_formula_l, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₂, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hB hβ hW hω hωW he ha hφ hn
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.eval η, hωEq ▸ hn⟩
  have hi' : (numberCode_l K i).val = n.eval η := congrArg Subtype.val hi
  have he' : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l h𝒩 _ _ (fun x => iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  rw [← hi']
  exact exists_l K φ η B β W e a hB hβ hW (hωEq ▸ hωW) ha he' hφ i

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β W ω e a n : Term ℒ [] Δ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β W ω e a n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B β W ω e a n)

#print axioms induction_derives_m
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitDefinableFiniteTrace
