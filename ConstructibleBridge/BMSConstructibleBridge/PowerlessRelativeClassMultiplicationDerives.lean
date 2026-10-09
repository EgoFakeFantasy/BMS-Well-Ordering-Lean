import BMSConstructibleBridge.PowerlessRelativeClassMultiplicationAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassRelativization

/-! # 整条类内乘法图的原 Z₂ 对象推导

对象句覆盖每个内部左因子与内部右因子。其逐点规格使用原乘法迭代定义，
不把宿主数运算或有限轨迹检查式作为最终对象公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassMultiplicationDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (ω e a F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up ω)) <|
    .forallE .set <| .iff
      (SecondOrderObjectSyntax.value_m (up (up F)) (.bvar (.there .here)) (.bvar .here))
      (PowerlessMultiplication.multiplication_m (up (up ω)) (up (up e)) (up (up a))
        (.bvar (.there .here)) (.bvar .here))

theorem body_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e a F : Term ℒ Γ Δ .set) : (body_m ω e a F).satisfies η ↔
      ∀ b, member_l 𝒩 b (ω.eval η) → ∀ c, value_l (ℳ := 𝒩) (F.eval η) b c ↔
        PowerlessMultiplication.multiplication_l (ℳ := 𝒩) (ω.eval η) (e.eval η) (a.eval η) b c := by
  simp only [body_m, Formula.satisfies, value_formula_l, PowerlessMultiplication.multiplication_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def sentence_m : Sentence ℒ := .forallE .set <| .forallE .set <| .forallE .set <|
  .imp (SecondOrderOmegaSyntax.omega_m (.bvar (.there (.there .here)))) <|
    .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here)
      (.bvar (.there (.there .here)))))) <|
      .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there .here)))) <|
        .existsE .set <| .conj
          (SecondOrderObjectSyntax.map_m (.bvar .here) (.bvar (.there (.there (.there .here))))
            (.bvar (.there (.there (.there .here)))))
          (body_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
            (.bvar (.there .here)) (.bvar .here))

theorem sentence_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} : sentence_m.TrueIn 𝒩 ↔
    ∀ ω e a : carrier_l 𝒩, omega_l (ℳ := 𝒩) ω → (∀ x, ¬member_l 𝒩 x e) → member_l 𝒩 a ω →
      ∃ F, map_l (ℳ := 𝒩) F ω ω ∧ ∀ b, member_l 𝒩 b ω → ∀ c,
        value_l (ℳ := 𝒩) F b c ↔ PowerlessMultiplication.multiplication_l (ℳ := 𝒩) ω e a b c := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, omega_formula_l, map_formula_l,
    body_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  rfl

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply sentence_l.mpr
  intro ω e a hω he ha
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  have heEq : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := SecondOrderQuotient.ext_l hℳ _ _
    (fun x => iff_of_false ((PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp he x)
      (PowerlessBMSQuotientSuccessor.zero_l K x))
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a.val, hωEq ▸ ha⟩
  have haEq : a.val = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
  obtain ⟨_, F, _, hF, hGraph⟩ := PowerlessRelativeClassMultiplicationAbsolute.graph_l
    (hBase := hBase) K i hωEq heEq haEq
  refine ⟨F, hF.1, fun b hb c => ?_⟩
  obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b.val, hωEq ▸ hb⟩
  have hbEq : b.val = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
  have hMul := PowerlessRelativeClassMultiplicationAbsolute.instance_l (hBase := hBase) K
    (ω := ω) (e := e) (a := a) (b := b) (c := c) hωEq heEq haEq hbEq
  constructor
  · intro hValue
    apply hMul.mpr
    have hValue' := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F b c).mp hValue
    rw [hbEq] at hValue'
    exact (hGraph j c.val).mp hValue'
  · intro hMul'
    apply (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F b c).mpr
    change value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val b.val c.val
    rw [hbEq]
    exact (hGraph j c.val).mpr (hMul.mp hMul')

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassMultiplicationDerives
