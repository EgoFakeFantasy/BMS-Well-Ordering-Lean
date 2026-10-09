import BMSConstructibleBridge.PowerlessRelativeClassAdditionGraph
import BMSConstructibleBridge.PowerlessAdditionIterationSyntax
import BMSConstructibleBridge.PowerlessRelativeClassRelativization

/-! # 相对并类中整条加法迭代图的原 Z₂ 推导

对象句断言每个内部自然数初值有整个 ω 长图，而非外部标准有限实例。
类模型验证仅作中间步骤；交付接口是原二阶算术推导核的 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassAdditionDerives

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct
  SecondOrderQuotient.structure_l PowerlessRelativeClassStructure.structure_l

universe u

def sentence_m : Sentence ℒ :=
  .forallE .set (.forallE .set (.forallE .set
    (.imp (SecondOrderOmegaSyntax.omega_m (.bvar (.there (.there .here))))
      (.imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m
        (.bvar .here) (.bvar (.there (.there .here))))))
        (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there .here))))
          (.existsE .set (.conj
            (SecondOrderObjectSyntax.map_m (.bvar .here)
              (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there (.there .here)))))
            (PowerlessAdditionIterationSyntax.formula_m (.bvar (.there (.there (.there .here))))
              (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)))))))))

theorem sentence_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} : sentence_m.TrueIn 𝒩 ↔
    ∀ ω e a : carrier_l 𝒩, omega_l (ℳ := 𝒩) ω → (∀ x, ¬member_l 𝒩 x e) → member_l 𝒩 a ω →
      ∃ F, map_l (ℳ := 𝒩) F ω ω ∧ PowerlessAddition.iteration_l (ℳ := 𝒩) ω e a F := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies,
    omega_formula_l, map_formula_l, PowerlessAdditionIterationSyntax.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  rfl

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B) :
    sentence_m.TrueIn (PowerlessRelativeClassStructure.structure_l hℳ B hBase) := by
  apply sentence_l.mpr
  intro ω e a hω he ha
  exact PowerlessRelativeClassAdditionGraph.exists_l (hBase := hBase) hω he ha

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassAdditionDerives
