import BMSConstructibleBridge.PowerlessDefinableFiniteTrace

/-! # 可定义有限轨迹模式的原 Z₂ 对象推导

每个外部有限二元矩阵实例给出纯隶属句与原 `Derives`。目标显式要求
矩阵总性；结论是每个内部长度的有限历史存在，不是无限依赖选择。
后续 Skolem 调用必须先用规范最小元及缺省分支证明同一矩阵的总性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableFiniteTraceDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessBMSQuotientSubsetImageDerives (at_m at_formula_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def zero_m {Γ Δ : SortContext ℒ} (e : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up e))

theorem zero_formula_l {𝒱 : FirstOrder.Structure ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (e : Term ℒ Γ Δ .set) :
    (zero_m e).satisfies η ↔ PowerlessNatural.zero_l (e.eval η) := by
  simp only [zero_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def total_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ Γ Δ :=
  .forallE .set <| .existsE .set <| at_m φ (.bvar (.there .here)) (.bvar .here)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (zero_m e) <|
    .imp (total_m φ) <| .imp (SecondOrderObjectSyntax.member_m n ω)
      (PowerlessDefinableFiniteTrace.finite_m φ e a n)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e a n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ ω e a n)

theorem schema_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) (ω e a n : Term ℒ [] Δ .set) :
    (schema_m φ ω e a n).satisfies η ↔
      (SecondOrderOmega.omega_l hℳ (ω.eval η) →
        PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η) →
        (∀ x, ∃ y, φ.satisfies ((η.pushFree x).pushFree y)) →
        SecondOrderQuotient.mem_l hℳ (n.eval η) (ω.eval η) →
        ∃ S D f, PowerlessDefinableFiniteTrace.trace_l φ η
          (e.eval η) (a.eval η) (n.eval η) S D f) := by
  simp only [schema_m, zero_m, total_m, Formula.satisfies,
    SecondOrderOmegaSyntax.omega_l, PowerlessDefinableFiniteTrace.finite_formula_l,
    at_formula_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ω e a n : Term ℒ [] Δ .set) :
    (sentence_m φ ω e a n).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  apply (schema_formula_l hℳ φ η ω e a n).mpr
  intro hω he hTotal hn
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  rw [SecondOrderOmega.unique_l hℳ hω K.omega_spec] at hn
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.eval η, hn⟩
  have hi' : (numberCode_l K i).val = n.eval η := congrArg Subtype.val hi
  have he' : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := by
    apply SecondOrderQuotient.ext_l hℳ
    intro x
    exact iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x)
  rw [← hi']
  exact PowerlessDefinableFiniteTrace.exists_l K φ η e a he' hTotal i

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e a n : Term ℒ [] Δ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ ω e a n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ ω e a n)

#print axioms schema_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableFiniteTraceDerives
