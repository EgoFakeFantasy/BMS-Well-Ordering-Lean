import BMSConstructibleBridge.PowerlessHereditaryRealRequest
import BMSConstructibleBridge.PowerlessBMSQuotientSuccessor

/-! # 带根请求存在性的原 Z₂ 对象推导

以纯 ℒ 表达传递基底、ω、零、后继与有限序列界；遗传对象的请求
存在性经原图翻译返回同一 Derives 核。语义输入覆盖任意原 Z₂ 模型，
不添加源模型的 Separation 或 Collection 假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealRequestDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def support_m {Γ Δ : SortContext ℒ} (ω e o S : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderOmegaSyntax.omega_m ω) <|
    .conj (PowerlessRelativeHierarchySyntax.empty_m e) <|
      .conj (PowerlessRelativeHierarchySyntax.successor_m e o) (PowerlessFiniteSequencesSyntax.spec_m ω ω S)

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let e := .fvar (.there (.there .here))
  let o := .fvar (.there (.there (.there .here)))
  let S := .fvar (.there (.there (.there (.there .here))))
  let X := .fvar (.there (.there (.there (.there (.there .here)))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (support_m ω e o S) <| .imp (PowerlessHereditaryClass.formula_m B X) <|
      .existsE .set (PowerlessHereditaryRealRequest.formula_m (up B) (up ω) (up e) (up o) (up S) (up X) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem support_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (ω e o S : Term ℒ Γ Δ .set) :
    (support_m ω e o S).satisfies η ↔
      SecondOrderOmega.omega_l hℳ (ω.eval η) ∧
        PowerlessRelativeHierarchySemantics.empty_l hℳ (e.eval η) ∧
          PowerlessRelativeHierarchySemantics.successor_l hℳ (e.eval η) (o.eval η) ∧
            PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) (ω.eval η) (ω.eval η) (S.eval η) := by
  simp only [support_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeHierarchySemantics.empty_formula_l,
    PowerlessRelativeHierarchySemantics.successor_formula_l, PowerlessFiniteSequencesSyntax.spec_formula_l]

/-- 支撑参数由原商外延性归一化，而非完整无幂集集合论模型假设。 -/
theorem normalize_l (K : source_coding_l hℳ) {ω e o : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) (he : PowerlessRelativeHierarchySemantics.empty_l hℳ e)
    (ho : PowerlessRelativeHierarchySemantics.successor_l hℳ e o) :
    ω = K.omega ∧ e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val ∧
      o = (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val := by
  have he' : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  refine ⟨SecondOrderOmega.unique_l hℳ hω K.omega_spec, he', ?_⟩
  subst e
  exact SecondOrderQuotient.ext_l hℳ _ _
    (fun x => (ho x).trans (PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.zero_l ℳ) x).symm)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    support_formula_l, PowerlessHereditaryClass.formula_l K, PowerlessHereditaryRealRequest.formula_l K,
    up, Term.eval_weakenBound, Term.eval]
  intro hBase ⟨hω, he, ho, hS⟩ hX
  obtain ⟨hωEq, heEq, hoEq⟩ := normalize_l K hω he ho
  rw [hωEq] at hS
  obtain ⟨V, hV⟩ := PowerlessHereditaryRealRequest.exists_l (hBase := hBase) K hS hX
  refine ⟨V, ?_⟩
  rw [hωEq, heEq, hoEq]
  exact hV

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms normalize_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealRequestDerives
