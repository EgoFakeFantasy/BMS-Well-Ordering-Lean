import BMSConstructibleBridge.PowerlessRelativeClassBoundedArithmetic

/-! # 统一有界运算参数存在的原 Z₂ 推导

每个相对类有同一个有限序列集 S，使两个 Δ₀ 检查式与原无限迭代加乘关系
逐点等价。此对象句不要求整类满足 Collection，也不提供最终 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBoundedArithmeticDerives

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (ω e S : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  membershipLevyBound.boundedForall ω <| membershipLevyBound.boundedForall (up ω) <|
    .forallE .set <| .conj
      (.iff (PowerlessBoundedAddition.formula_m (w ω) (w e) (w S)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
        (PowerlessAdditionSyntax.addition_m (w ω) (w e)
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)))
      (.iff (PowerlessBoundedMultiplication.formula_m (w ω) (w e) (w S)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
        (PowerlessMultiplication.multiplication_m (w ω) (w e)
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)))

theorem body_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S : Term ℒ Γ Δ .set) : (body_m ω e S).satisfies η ↔
      ∀ a, member_l 𝒩 a (ω.eval η) → ∀ b, member_l 𝒩 b (ω.eval η) → ∀ c,
        (PowerlessBoundedAddition.holds_l (𝒩 := 𝒩) (ω.eval η) (e.eval η) (S.eval η) a b c ↔
          PowerlessAddition.addition_l (ℳ := 𝒩) (ω.eval η) (e.eval η) a b c) ∧
        (PowerlessBoundedMultiplication.holds_l (𝒩 := 𝒩) (ω.eval η) (e.eval η) (S.eval η) a b c ↔
          PowerlessMultiplication.multiplication_l (ℳ := 𝒩) (ω.eval η) (e.eval η) a b c) := by
  simp only [body_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedAddition.formula_l,
    PowerlessAdditionSyntax.addition_formula_l, PowerlessBoundedMultiplication.formula_l,
    PowerlessMultiplication.multiplication_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def sentence_m : Sentence ℒ := .forallE .set <| .forallE .set <|
  .imp (SecondOrderOmegaSyntax.omega_m (.bvar (.there .here))) <|
    .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))))) <|
      .existsE .set <| .conj
        (PowerlessFiniteSequencesSyntax.spec_m (.bvar (.there (.there .here)))
          (.bvar (.there (.there .here))) (.bvar .here))
        (body_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, omega_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, body_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval]
  intro ω e hω he
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  have heEq : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := SecondOrderQuotient.ext_l hℳ _ _
    (fun x => iff_of_false ((PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp he x)
      (PowerlessBMSQuotientSuccessor.zero_l K x))
  obtain ⟨S, hS₀, hSClass⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l
    (hBase := hBase) (ω := ω) (X := ω) hω
  have hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega S.val := by
    simpa only [hωEq] using hS₀
  refine ⟨S, hSClass, fun a ha b hb c => ?_⟩
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a.val, hωEq ▸ ha⟩
  obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b.val, hωEq ▸ hb⟩
  have haEq : a.val = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
  have hbEq : b.val = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
  exact ⟨PowerlessRelativeClassBoundedArithmetic.addition_l (hBase := hBase) K
    (ω := ω) (e := e) (S := S) (a := a) (b := b) (c := c) hS hωEq heEq haEq hbEq,
    PowerlessRelativeClassBoundedArithmetic.multiplication_l (hBase := hBase) K
      (ω := ω) (e := e) (S := S) (a := a) (b := b) (c := c) hS hωEq heEq haEq hbEq⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBoundedArithmeticDerives
