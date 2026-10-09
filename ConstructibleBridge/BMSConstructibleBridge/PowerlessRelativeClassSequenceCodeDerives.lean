import BMSConstructibleBridge.PowerlessRelativeClassSequenceCode
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives
import BMSConstructibleBridge.PowerlessNaturalStep

/-! # 类内有限函数编码存在的原 Z₂ 推导

对象语言只有隶属和相等；背景为原 SecondOrderArithmetic.theory_m，经已有
图翻译与相对类守卫回传原 Derives 核。此句不包含最终 BMS 良序结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceCodeDerives

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (ω e S one two : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  membershipLevyBound.boundedForall ω <| .forallE .set <| .imp
    (PowerlessMapBounded.formula_m (.bvar .here) (.bvar (.there .here)) (up (up ω)))
    (membershipLevyBound.boundedExists (up (up ω)) <|
      PowerlessBoundedSequenceCode.formula_m (w ω) (w e) (w S) (w one) (w two)
        (.bvar (.there (.there .here))) (.bvar .here) (.bvar (.there .here)))

theorem body_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S one two : Term ℒ Γ Δ .set) : (body_m ω e S one two).satisfies η ↔
      ∀ n, member_l 𝒩 n (ω.eval η) → ∀ f, map_l (ℳ := 𝒩) f n (ω.eval η) →
        ∃ c, member_l 𝒩 c (ω.eval η) ∧ PowerlessBoundedSequenceCode.holds_l
          (𝒩 := 𝒩) (ω.eval η) (e.eval η) (S.eval η) (one.eval η) (two.eval η) n c f := by
  simp only [body_m, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessMapBounded.formula_l, PowerlessBoundedSequenceCode.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def sentence_m : Sentence ℒ := .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
  .imp (SecondOrderOmegaSyntax.omega_m (.bvar (.there (.there (.there .here))))) <|
    .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m
      (.bvar .here) (.bvar (.there (.there (.there .here))))))) <|
      .imp (PowerlessNaturalStep.successor_m (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
        .imp (PowerlessNaturalStep.successor_m (.bvar (.there .here)) (.bvar .here)) <|
          .existsE .set <| .conj
            (PowerlessFiniteSequencesSyntax.spec_m (.bvar (.there (.there (.there (.there .here)))))
              (.bvar (.there (.there (.there (.there .here))))) (.bvar .here))
            (body_m (.bvar (.there (.there (.there (.there .here)))))
              (.bvar (.there (.there (.there .here)))) (.bvar .here)
              (.bvar (.there (.there .here))) (.bvar (.there .here)))

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, omega_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, body_l, PowerlessNaturalStep.successor_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  intro ω e one two hω he hone htwo
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  have heEq : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := SecondOrderQuotient.ext_l hℳ _ _
    (fun x => iff_of_false ((PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp he x)
      (PowerlessBMSQuotientSuccessor.zero_l K x))
  have hone₀ : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) e.val one.val :=
    (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e one).mp hone
  rw [heEq] at hone₀
  have honeEq : one.val = (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val :=
    PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) hone₀
      (PowerlessBMSQuotientSuccessor.successor_l K _)
  have htwo₀ : PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) one.val two.val :=
    (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) one two).mp htwo
  rw [honeEq] at htwo₀
  have htwoEq : two.val = (numberCode_l K (SecondOrderModel.succ_l
      (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))).val :=
    PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) htwo₀
      (PowerlessBMSQuotientSuccessor.successor_l K _)
  obtain ⟨S, hS₀, hSClass⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l
    (hBase := hBase) (ω := ω) (X := ω) hω
  have hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega S.val := by
    simpa only [hωEq] using hS₀
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  exact ⟨S, hSClass, fun n hn f hf => PowerlessRelativeClassSequenceCode.exists_l
    (hBase := hBase) K (ω := ω) (e := e) (S := S) (one := one) (two := two) (n := n) (f := f)
      hS hE hωEq heEq honeEq htwoEq hn hf⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceCodeDerives
