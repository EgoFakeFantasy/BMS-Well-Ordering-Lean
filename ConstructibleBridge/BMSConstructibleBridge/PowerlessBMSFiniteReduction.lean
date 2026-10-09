import BMSConstructibleBridge.PowerlessBMSObjectProof
import BMSConstructibleBridge.PowerlessBMSQuotientTranslation
import BMSConstructibleBridge.PowerlessBMSQuotientAxioms
import BMSConstructibleBridge.PowerlessBMSQuotientReals
import BMSConstructibleBridge.SecondOrderCompleteness

/-!
# 从原 BMS 对象证明的有限支持回到 Z₂ 原目标

算术翻译回读与目标候选实数覆盖在任意 Z₂ 模型中实际成立。剩余条件可以是
同一图商满足一份支持原证明的有限公理列表，而不必先验证完整 PowerlessTheory。
本文件不证明该有限支持的模型条件；尤其不把 Collection 隐藏在新定义中。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSFiniteReduction

open Logic FirstOrder ThirdOrderSemantics
open PowerlessBMSQuotientCoding PowerlessBMSQuotientTranslation

set_option autoImplicit false

attribute [local implicit_reducible] SecondOrderQuotient.structure_l PowerlessArithmetic.structure_l

universe u

variable {M : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

/-- 任意算术闭句的纯集合闭包在商中的真值可回读到实际商算术结构。 -/
theorem closure_l (C : source_coding_l hM) (φ : Sentence SecondOrderSyntax.signature_m)
    (h : (PowerlessBMSObjectProof.closure_m φ).TrueIn (SecondOrderQuotient.structure_l hM)) :
    φ.TrueIn (arithmetic_l C) := by
  have hBody := (PowerlessBMSObjectProof.closure_formula_l φ).mp h C.omega
    (numberCode_l C (SecondOrderModel.zero_l M)).val
    (PowerlessBMSQuotientOmega.omega_l hM C.omega_spec)
    (PowerlessBMSQuotientSuccessor.zero_l C)
  exact (PowerlessBMSQuotientTranslation.formula_l C Env.empty
    (((Env.empty (M := SecondOrderQuotient.structure_l hM)).pushBound C.omega).pushBound
      (numberCode_l C (SecondOrderModel.zero_l M)).val)
    (.bvar (.there .here)) (.bvar .here) (fun v => nomatch v) (fun v => nomatch v)
    rfl rfl (fun v => nomatch v) (fun v => nomatch v) φ).mp hBody

/-- 候选实数代表与实际算术对应将原具体闭句从商算术搬回目标模型。 -/
theorem closed_transfer_l (C : source_coding_l hM) (H : Nat)
    (h : (SecondOrderConcreteFormula.closed_m H).TrueIn (arithmetic_l C)) :
    (SecondOrderConcreteFormula.closed_m H).TrueIn M := by
  obtain ⟨φ, hφ, hpure⟩ := SecondOrderConcreteFormula.closed_pure_m H
  rw [hφ] at h ⊢
  change ∀ X : M.Carrier .set, φ.satisfies ((Env.empty (M := M)).pushBound X)
  intro X
  obtain ⟨A, hA⟩ := representative_exists_l C X
  let D := PowerlessBMSQuotientMultiplication.correspondence_l C
  apply (SecondOrderPureTransfer.formula_l D φ hpure
    ((Env.empty (M := arithmetic_l C)).pushBound A) ((Env.empty (M := M)).pushBound X) ?_).mp (h A)
  constructor
  · intro s v
    cases v with
    | here => exact hA
    | there v => nomatch v
  · intro s v
    nomatch v

/-- 纯集合闭句回读为原固定高度目标；没有候选覆盖或运算对应的附加假设。 -/
theorem closed_of_sentence_l (hℳ : Theory.Models M SecondOrderArithmetic.theory_m) (H : Nat)
    (h : (PowerlessBMSObjectProof.sentence_m H).TrueIn (SecondOrderQuotient.structure_l hℳ)) :
    (SecondOrderConcreteFormula.closed_m H).TrueIn M := by
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  exact closed_transfer_l C H (closure_l C (SecondOrderConcreteFormula.closed_m H) h)

/-- 原固定高度句在两个算术结构间双向保持，而非只从源真值推出目标真值。 -/
theorem closed_iff_l (C : source_coding_l hM) (H : Nat) :
    (SecondOrderConcreteFormula.closed_m H).TrueIn (arithmetic_l C) ↔
      (SecondOrderConcreteFormula.closed_m H).TrueIn M := by
  refine ⟨closed_transfer_l C H, fun h => ?_⟩
  obtain ⟨φ, hφ, hpure⟩ := SecondOrderConcreteFormula.closed_pure_m H
  rw [hφ] at h ⊢
  change ∀ A : (arithmetic_l C).Carrier .set,
    φ.satisfies ((Env.empty (M := arithmetic_l C)).pushBound A)
  intro A
  obtain ⟨X, hAX⟩ := PowerlessBMSQuotientReals.trace_exists_l C A
  let D := PowerlessBMSQuotientMultiplication.correspondence_l C
  apply (SecondOrderPureTransfer.formula_l D φ hpure
    ((Env.empty (M := arithmetic_l C)).pushBound A) ((Env.empty (M := M)).pushBound X) ?_).mpr (h X)
  constructor
  · intro s v
    cases v with
    | here => exact hAX
    | there v => nomatch v
  · intro s v
    nomatch v

/-- 只需指定有限支持在全部原 Z₂ 模型的图商中成立，即可得到原目标的对象推导。
支持的满足性仍为待证明前提，并不由有限性自动推出。 -/
theorem derives_of_finite_models_m (H : Nat)
    (S : Derives.FiniteTheorySupport PowerlessTheory.theory_m [] (PowerlessBMSObjectProof.sentence_m H))
    (hModels : ∀ (M : FirstOrder.Structure.{0, 0, 0, 0} SecondOrderSyntax.signature_m)
      (hM : Theory.Models M SecondOrderArithmetic.theory_m),
      Theory.Models (SecondOrderQuotient.structure_l hM) (Theory.ofList S.sentences)) :
    Derives SecondOrderArithmetic.theory_m [] (SecondOrderConcreteFormula.closed_m H) := by
  apply SecondOrderCompleteness.derives_m
  intro M hM
  apply closed_of_sentence_l hM H
  exact S.derivation.sound (hModels M hM) Env.empty (fun _ h => nomatch h)

/-- 有限支持与其目标保持接口的存在性；不通过选择固定未知支持。 -/
theorem finite_reduction_m (H : Nat) :
    ∃ Γ : List (Sentence ℒ), (∀ φ ∈ Γ, PowerlessTheory.theory_m φ) ∧
      ((∀ (M : FirstOrder.Structure.{0, 0, 0, 0} SecondOrderSyntax.signature_m)
        (hM : Theory.Models M SecondOrderArithmetic.theory_m),
        Theory.Models (SecondOrderQuotient.structure_l hM) (Theory.ofList Γ)) →
        Derives SecondOrderArithmetic.theory_m [] (SecondOrderConcreteFormula.closed_m H)) := by
  obtain ⟨S⟩ := PowerlessBMSObjectProof.finite_m H
  exact ⟨S.sentences, S.subset, derives_of_finite_models_m H S⟩

/-- 原证明有限支持中的非收集公理已实际解释；剩余前提仅为出现的收集实例。
这并不保证原图商能满足这些实例，也不把它们添加到 Z₂ 的公理中。 -/
theorem collection_reduction_m (H : Nat) :
    ∃ Γ : List (Sentence ℒ), (∀ φ ∈ Γ, PowerlessTheory.theory_m φ) ∧
      ((∀ (M : FirstOrder.Structure.{0, 0, 0, 0} SecondOrderSyntax.signature_m)
        (hM : Theory.Models M SecondOrderArithmetic.theory_m), ∀ φ ∈ Γ,
        PowerlessBMSQuotientAxioms.collection_m φ →
        φ.TrueIn (SecondOrderQuotient.structure_l hM)) →
        Derives SecondOrderArithmetic.theory_m [] (SecondOrderConcreteFormula.closed_m H)) := by
  obtain ⟨S⟩ := PowerlessBMSObjectProof.finite_m H
  refine ⟨S.sentences, S.subset, fun h => derives_of_finite_models_m H S ?_⟩
  intro M hM
  exact PowerlessBMSQuotientAxioms.finite_models_l hM S.sentences S.subset (h M hM)

#print axioms closure_l
#print axioms closed_transfer_l
#print axioms closed_of_sentence_l
#print axioms closed_iff_l
#print axioms derives_of_finite_models_m
#print axioms finite_reduction_m
#print axioms collection_reduction_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSFiniteReduction
