import BMSConstructibleBridge.SecondOrderMemberDefArithmetic
import BMSConstructibleBridge.PowerlessBMSQuotientArithmeticTransfer

/-!
# Def 算术证书的原核对象推导

任意相等图与成员图参数均有合法性、幂、全数域、求值和切片的同一证书。
纯集合闭包也由原 Z₂ 推导；这不是母集 Def 的存在唯一性或 BMS 良序终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefArithmeticDerives

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

private def parameters_m : VariableSubstitution signature_m
    [.set, .set, .set, .set, .set, .set, .set] [.set, .set, .set, .set, .set, .set, .set] []
  | _, .here => .bvar (.there (.there (.there (.there .here))))
  | _, .there .here => .bvar (.there (.there (.there .here)))
  | _, .there (.there .here) => .bvar (.there (.there .here))
  | _, .there (.there (.there .here)) => .bvar (.there (.there (.there (.there (.there (.there .here))))))
  | _, .there (.there (.there (.there .here))) => .bvar (.there (.there (.there (.there (.there .here)))))
  | _, .there (.there (.there (.there (.there .here)))) => .bvar (.there .here)
  | _, .there (.there (.there (.there (.there (.there .here))))) => .bvar .here

private def body_m : Formula signature_m [.set, .set, .set, .set, .set, .set, .set] [] :=
  SecondOrderMemberDefArithmetic.formula_m.substitute
    (show Substitution signature_m [] [.set, .set, .set, .set, .set, .set, .set]
      [.set, .set, .set, .set, .set, .set, .set] [] from .map (fun v => nomatch v) parameters_m)

def sentence_m : Sentence signature_m :=
  .forallE .set <| .forallE .set <| .existsE .set <| .existsE .set <|
    .existsE .set <| .existsE .set <| .existsE .set body_m

theorem pure_m : language_m sentence_m = true := by
  change language_m body_m = true
  refine (SecondOrderSubstitution.form_subst_m SecondOrderMemberDefArithmetic.formula_m _ _ ?_ ?_).trans
    SecondOrderMemberDefArithmetic.pure_m
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => cases v with
            | here => rfl
            | there v => cases v with
              | here => rfl
              | there v => cases v with
                | here => rfl
                | there v => nomatch v

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ := by
  intro Q R
  obtain ⟨V, hV, _⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  obtain ⟨D, hD⟩ := comprehension_l hℳ (Formula.truth : Formula signature_m [] [.num]) rfl Env.empty
  have hDomain : ∀ n, mem_l n D := fun n => (hD n).mpr trivial
  obtain ⟨T, hT, _⟩ := SecondOrderEvaluationFixedPoint.exists_l hℳ E D Q R
  obtain ⟨F, hF, _⟩ := SecondOrderDefinableFamily.exists_l hℳ E D T
  refine ⟨V, E, D, T, F, ?_⟩
  rw [body_m, Formula.satisfies_substitute]
  unfold SecondOrderMemberDefArithmetic.formula_m
  exact (SecondOrderMemberDefArithmetic.packet_formula_l _ _ _ _ _ _ _ _).mpr
    ⟨hV, hE, hDomain, hT, hF⟩

theorem derives_m : Derives theory_m [] sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => models_l hℳ)

def pure_sentence_m : Sentence ℒ := PowerlessBMSObjectProof.closure_m sentence_m

theorem pure_derives_m : Derives theory_m [] (GraphTranslation.form_m pure_sentence_m) :=
  PowerlessBMSQuotientArithmeticTransfer.derives_m sentence_m pure_m derives_m

#print axioms derives_m
#print axioms pure_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefArithmeticDerives
