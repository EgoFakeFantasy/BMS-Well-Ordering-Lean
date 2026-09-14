import BMSConstructibleBridge.SecondOrderPairLayer
import BMSConstructibleBridge.SecondOrderPairObjects

/-!
# 统一 Kuratowski 有序对层

连续两层统一配对得到所有旧根对的有序对表示。根数的实际纯算术模板与
同一模型中的配对值核验，供后续内部函数图选择使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrderedLayer

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

noncomputable def root_l (a b : num_l ℳ) : num_l ℳ :=
  SecondOrderPairLayer.pair_l (SecondOrderPairLayer.pair_l a a) (SecondOrderPairLayer.pair_l a b)

theorem wf_l (hℳ : Theory.Models ℳ theory_m) (R G H : set_l ℳ)
    (hG : SecondOrderPairLayer.spec_l R G) (hH : SecondOrderPairLayer.spec_l G H)
    (a b : num_l ℳ) (ha : SecondOrderDomain.wf_l R a) (hb : SecondOrderDomain.wf_l R b) :
    SecondOrderDomain.wf_l H (root_l a b) :=
  SecondOrderPairLayer.pair_wf_l hℳ G H hH _ _
    (SecondOrderPairLayer.pair_wf_l hℳ R G hG a a ha ha)
    (SecondOrderPairLayer.pair_wf_l hℳ R G hG a b ha hb)

noncomputable def code_l (hℳ : Theory.Models ℳ theory_m) (R G H : set_l ℳ)
    (hG : SecondOrderPairLayer.spec_l R G) (hH : SecondOrderPairLayer.spec_l G H)
    (a b : num_l ℳ) (ha : SecondOrderDomain.wf_l R a) (hb : SecondOrderDomain.wf_l R b) :
    SecondOrderGraph.code_l ℳ := ⟨H, root_l a b, wf_l hℳ R G H hG hH a b ha hb⟩

private theorem pair_spec (hℳ : Theory.Models ℳ theory_m) (R G : set_l ℳ)
    (hG : SecondOrderPairLayer.spec_l R G) (a b : num_l ℳ)
    (ha : SecondOrderDomain.wf_l R a) (hb : SecondOrderDomain.wf_l R b) :
    SecondOrderPairObjects.pair_l hℳ
      (SecondOrderQuotient.mk_l hℳ ⟨R, a, ha⟩) (SecondOrderQuotient.mk_l hℳ ⟨R, b, hb⟩)
      (SecondOrderQuotient.mk_l hℳ (SecondOrderPairLayer.code_l hℳ R G hG a b ha hb)) := by
  intro d
  obtain ⟨D, rfl⟩ := SecondOrderQuotient.surj_l hℳ d
  exact (SecondOrderPairLayer.mem_l hℳ R G hG a b ha hb D).trans
    (or_congr (SecondOrderQuotient.eq_iff_l hℳ D ⟨R, a, ha⟩).symm
      (SecondOrderQuotient.eq_iff_l hℳ D ⟨R, b, hb⟩).symm)

theorem ordered_l (hℳ : Theory.Models ℳ theory_m) (R G H : set_l ℳ)
    (hG : SecondOrderPairLayer.spec_l R G) (hH : SecondOrderPairLayer.spec_l G H)
    (a b : num_l ℳ) (ha : SecondOrderDomain.wf_l R a) (hb : SecondOrderDomain.wf_l R b) :
    SecondOrderPairObjects.ordered_l hℳ
      (SecondOrderQuotient.mk_l hℳ ⟨R, a, ha⟩) (SecondOrderQuotient.mk_l hℳ ⟨R, b, hb⟩)
      (SecondOrderQuotient.mk_l hℳ (code_l hℳ R G H hG hH a b ha hb)) :=
  ⟨_, _, pair_spec hℳ R G hG a a ha ha, pair_spec hℳ R G hG a b ha hb,
    pair_spec hℳ G H hH _ _ _ _⟩

private def one {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons (Term.app (σ := signature_m) .zero .nil) .nil)

/-- 自由槽位为左根、右根、输出根；五个中间值均为数量词。 -/
def template_m : Formula signature_m [] [.num, .num, .num] :=
  .existsE .num <| .existsE .num <| .existsE .num <| .existsE .num <| .existsE .num <|
    .conj (PrimitiveFormulas.pair_m (.fvar .here) (.fvar .here)
      (.bvar (.there (.there (.there (.there .here))))))
      (.conj (PrimitiveFormulas.pair_m one (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there (.there .here)))))
        (.conj (PrimitiveFormulas.pair_m (.fvar .here) (.fvar (.there .here)) (.bvar (.there (.there .here))))
          (.conj (PrimitiveFormulas.pair_m one (.bvar (.there (.there .here))) (.bvar (.there .here)))
            (.conj (PrimitiveFormulas.pair_m (.bvar (.there (.there (.there .here))))
              (.bvar (.there .here)) (.bvar .here))
              (PrimitiveFormulas.pair_m one (.bvar .here) (.fvar (.there (.there .here))))))))

private def bind {Γ Δ : SortContext signature_m} (a b c : Term signature_m Γ Δ .num) :
    Substitution signature_m [] [.num, .num, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => a
    | .there .here => b
    | .there (.there .here) => c)

def formula_m {Γ Δ : SortContext signature_m} (a b c : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := template_m.substitute (bind a b c)

theorem pure_m {Γ Δ : SortContext signature_m} (a b c : Term signature_m Γ Δ .num)
    (ha : pure_term_m a = true) (hb : pure_term_m b = true) (hc : pure_term_m c = true) :
    language_m (formula_m a b c) = true := by
  refine (SecondOrderSubstitution.form_subst_m template_m _ _ ?_ ?_).trans (pure_language_m _ rfl)
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact ha
    | .there .here => exact hb
    | .there (.there .here) => exact hc

theorem template_l (η : Env ℳ [] [.num, .num, .num]) :
    Formula.satisfies η template_m ↔ root_l (η.freeVal .here) (η.freeVal (.there .here)) =
      η.freeVal (.there (.there .here)) := by
  simp only [template_m, Formula.satisfies, SecondOrderPairing.formula_l]
  change (∃ x s y t z,
    value_l (η.freeVal .here) (η.freeVal .here) = x ∧ value_l (succ_l (zero_l ℳ)) x = s ∧
    value_l (η.freeVal .here) (η.freeVal (.there .here)) = y ∧ value_l (succ_l (zero_l ℳ)) y = t ∧
    value_l s t = z ∧ value_l (succ_l (zero_l ℳ)) z = η.freeVal (.there (.there .here))) ↔ _
  constructor
  · rintro ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, h⟩

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (a b c : Term signature_m Γ Δ .num) :
    Formula.satisfies η (formula_m a b c) ↔ root_l (a.eval η) (b.eval η) = c.eval η := by
  rw [formula_m, Formula.satisfies_substitute, template_l]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrderedLayer
