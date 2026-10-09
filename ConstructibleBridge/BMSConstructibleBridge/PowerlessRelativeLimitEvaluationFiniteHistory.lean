import BMSConstructibleBridge.PowerlessEvaluationFiniteHistory
import BMSConstructibleBridge.PowerlessRelativeLimitEvaluationStep

/-! # 同一极限层内全部内部有限求值历史

归纳公式显式量化历史集合，沿原 Z₂ 图翻译归纳覆盖全部内部数，包括
非标准长度。后继步用同层分离得到新列，再把单点图并入旧历史；全程
没有调用完整源理论、幂集或 Collection，也没有抽取 Type 选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationFiniteHistory

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def template_m {Δ : SortContext ℒ} (ω e T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  let w (t : Term ℒ [] Δ .set) := up ((t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set)
  .existsE .set <| .conj
    (SecondOrderObjectSyntax.member_m (.bvar .here) (up (.fvar (.there .here))))
    (PowerlessEvaluationFiniteHistory.formula_m (up (.fvar (.there .here)))
      (w ω) (w e) (w T) (w A) (w t₁) (w t₂) (w t₃) (w S) (.bvar .here) (up (.fvar .here)))

theorem template_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 [] Δ) (ω e T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) (C n : carrier_l 𝒩) :
    (template_m ω e T A S t₁ t₂ t₃).satisfies ((η.pushFree C).pushFree n) ↔
      ∃ F, member_l 𝒩 F C ∧ PowerlessEvaluationFiniteHistory.trace_l C
        (ω.eval η) (e.eval η) (T.eval η) (A.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (S.eval η) F n := by
  simp only [template_m, Formula.satisfies, PowerlessEvaluationFiniteHistory.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval_weakenFree, Term.eval]
  rfl

theorem induction_derives_m {Δ : SortContext ℒ} (ω e T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (SecondOrderArithmetic.induction_m (GraphTranslation.form_m (template_m ω e T A S t₁ t₂ t₃))) :=
  GraphTranslation.induction_m (template_m ω e T A S t₁ t₂ t₃)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C : type_l hℳ}

/-- 为当前历史与索引扩充环境，原静态参数仍在同一层中。 -/
theorem column_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C)
    (hSC : mem_l hℳ (S.eval η) C)
    (hω : omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η))
    (he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η))
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η) (ω.eval η) (N.eval η))
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) (T.eval η) (ω.eval η) (ω.eval η))
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η) (A.eval η) (S.eval η))
    {F n : type_l hℳ} (hFC : mem_l hℳ F C) (hnC : mem_l hℳ n C) :
    ∃ Y, mem_l hℳ Y C ∧ PowerlessEvaluationStep.step_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η) (e.eval η) (T.eval η) (A.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (S.eval η) F n Y := by
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] (.set :: .set :: Δ) := (η.pushFree n).pushFree F
  let w (t : Term ℒ [] Δ .set) := (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
  have hParams' : ∀ s (v : Variable (.set :: .set :: Δ) s), mem_l hℳ (ξ.freeVal v) C := by
    intro s v
    cases s
    cases v with
    | here => exact hFC
    | there v =>
        cases v with
        | here => exact hnC
        | there v => exact hParams _ v
  have hSC' : mem_l hℳ ((w S).eval ξ) C := by simpa only [ξ, w, Term.eval_weakenFree] using hSC
  have hω' : omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) ((w ω).eval ξ) := by
    simpa only [ξ, w, Term.eval_weakenFree] using hω
  have he' : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) ((w e).eval ξ) := by
    simpa only [ξ, w, Term.eval_weakenFree] using he
  have hN' : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ((w ω).eval ξ) ((w ω).eval ξ) ((w N).eval ξ) := by simpa only [ξ, w, Term.eval_weakenFree] using hN
  have hT' : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) ((w T).eval ξ) ((w ω).eval ξ) ((w ω).eval ξ) := by
    simpa only [ξ, w, Term.eval_weakenFree] using hT
  have hS' : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ((w ω).eval ξ) ((w A).eval ξ) ((w S).eval ξ) := by simpa only [ξ, w, Term.eval_weakenFree] using hS
  obtain ⟨Y, hYC, hY⟩ := PowerlessRelativeLimitEvaluationStep.exists_l hBase hLimit hC ξ
    (w ω) (w e) (w N) (w T) (w A) (w S) (w t₁) (w t₂) (w t₃)
    (.fvar .here) (.fvar (.there .here)) hParams' hSC' hω' he' hN' hT' hS'
  refine ⟨Y, hYC, ?_⟩
  simpa only [ξ, w, Term.eval_weakenFree, Term.eval, Env.pushFree_here, Env.pushFree_there] using hY

theorem exists_l (K : source_coding_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C) (hωC : mem_l hℳ K.omega C)
    {Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C)
    (hSC : mem_l hℳ (S.eval η) C)
    (hωEq : ω.eval η = K.omega)
    (heEq : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η) (ω.eval η) (N.eval η))
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) (T.eval η) (ω.eval η) (ω.eval η))
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η) (A.eval η) (S.eval η))
    (i : SecondOrderModel.num_l ℳ) :
    ∃ F, mem_l hℳ F C ∧ PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C (ω.eval η) (e.eval η) (T.eval η) (A.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (S.eval η)
      F (numberCode_l K i).val := by
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hω : omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) (ω.eval η) := hωEq.symm ▸ K.omega_spec
  have he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η) :=
    heEq.symm ▸ PowerlessBMSQuotientSuccessor.zero_l K
  have h := PowerlessBMSQuotientInduction.induction_l K (template_m ω e T A S t₁ t₂ t₃) (η.pushFree C) ?_ ?_
  · exact (template_formula_l η ω e T A S t₁ t₂ t₃ C _).mp (h i)
  · apply (template_formula_l η ω e T A S t₁ t₂ t₃ C _).mpr
    exact ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val,
      hTrans K.omega hωC (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
        (numberCode_l K (SecondOrderModel.zero_l ℳ)).property,
      PowerlessEvaluationFiniteHistory.empty_l (PowerlessBMSQuotientSuccessor.zero_l K)⟩
  · intro j hF
    obtain ⟨F, hFC, hF⟩ := (template_formula_l η ω e T A S t₁ t₂ t₃ C _).mp hF
    let n := (numberCode_l K j).val
    have hnC := hTrans K.omega hωC n (numberCode_l K j).property
    obtain ⟨Y, hYC, hY⟩ := column_l hBase hLimit hC η ω e N T A S t₁ t₂ t₃
      hParams hSC hω he hN hT hS hFC hnC
    have hm := PowerlessBMSQuotientSuccessor.successor_l K j
    obtain ⟨G, hGC, hG, hRead⟩ := PowerlessRelativeLimitFunctionExtension.exists_l hℳ
      hBase hLimit hC hFC hnC hYC hF.1 (fun hnn => SecondOrderNaturalCases.asymmetry_l hℳ hnn hnn) hYC hm
    apply (template_formula_l η ω e T A S t₁ t₂ t₃ C _).mpr
    exact ⟨G, hGC, PowerlessEvaluationFiniteHistory.extension_l hF hG hm hRead hY⟩

#print axioms induction_derives_m
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitEvaluationFiniteHistory
