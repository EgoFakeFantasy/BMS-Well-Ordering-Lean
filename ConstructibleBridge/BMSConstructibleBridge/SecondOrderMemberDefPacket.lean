import BMSConstructibleBridge.SecondOrderMemberDefArithmetic
import BMSConstructibleBridge.SecondOrderMemberRelations

/-! # 给定原图和正规化参数的唯一 Def 实数证书

这里的存在唯一性针对实际模型实数，而不是图商对象；原图可以任意，
不预先假定它良基。全部证书在 Prop 中绑定，不抽取 Type 层选择函数。
这是构造全域原图操作的辅助步骤，还不是相对层次或 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefPacket

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderMemberNormalizer (value_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

structure spec_l (A : set_l ℳ) (r a : num_l ℳ) (V E D Q R T F : set_l ℳ) : Prop where
  formula_codes : SecondOrderInternalFormulaSyntax.spec_l V
  powers : SecondOrderBinaryPowers.spec_l E
  domain : ∀ n, mem_l n D
  equality : ∀ n m, relation_l Q n m ↔
    SecondOrderBisimulation.eq_l A A (value_l A r a n) (value_l A r a m)
  membership : ∀ n m, relation_l R n m ↔ ∃ b, relation_l A b (value_l A r a m) ∧
    SecondOrderBisimulation.eq_l A A (value_l A r a n) b
  evaluation : SecondOrderEvaluationEquations.spec_l E D Q R T
  family : SecondOrderDefinableFamily.spec_l E D T F

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : set_l ℳ) (r a : num_l ℳ) :
    ∃ V E D Q R T F, spec_l A r a V E D Q R T F := by
  obtain ⟨Q, R, hQ, hR⟩ := SecondOrderMemberRelations.exists_l hℳ A r a
  obtain ⟨D, hD⟩ := comprehension_l hℳ (Formula.truth : Formula signature_m [] [.num]) rfl Env.empty
  obtain ⟨V, hV, _⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  obtain ⟨T, hT, _⟩ := SecondOrderEvaluationFixedPoint.exists_l hℳ E D Q R
  obtain ⟨F, hF, _⟩ := SecondOrderDefinableFamily.exists_l hℳ E D T
  exact ⟨V, E, D, Q, R, T, F, hV, hE, fun n => (hD n).mpr trivial, hQ, hR, hT, hF⟩

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {A : set_l ℳ} {r a : num_l ℳ}
    {V E D Q R T F V' E' D' Q' R' T' F' : set_l ℳ}
    (h : spec_l A r a V E D Q R T F) (h' : spec_l A r a V' E' D' Q' R' T' F') :
    V = V' ∧ E = E' ∧ D = D' ∧ Q = Q' ∧ R = R' ∧ T = T' ∧ F = F' := by
  obtain ⟨W, _, hWV⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  have hV : V = V' := (hWV V h.formula_codes).trans (hWV V' h'.formula_codes).symm
  have hE : E = E' := SecondOrderPowers.unique_l hℳ h.powers h'.powers
  have hD : D = D' := SecondOrderModel.ext_l hℳ D D'
    (fun n => iff_of_true (h.domain n) (h'.domain n))
  have hQ : Q = Q' := SecondOrderRelations.ext_l hℳ Q Q'
    (fun n m => (h.equality n m).trans (h'.equality n m).symm)
  have hR : R = R' := SecondOrderRelations.ext_l hℳ R R'
    (fun n m => (h.membership n m).trans (h'.membership n m).symm)
  subst V' E' D' Q' R'
  obtain ⟨U, _, hUT⟩ := SecondOrderEvaluationFixedPoint.exists_l hℳ E D Q R
  have hT : T = T' := (hUT T h.evaluation).trans (hUT T' h'.evaluation).symm
  subst T'
  obtain ⟨G, _, hGF⟩ := SecondOrderDefinableFamily.exists_l hℳ E D T
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, (hGF F h.family).trans (hGF F' h'.family).symm⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefPacket
