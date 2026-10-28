import BMSConstructibleBridge.SecondOrderGraphFormulaRelation

/-!
# 带双侧根域护栏的可定义关系

无效根被实际理解公式排除，而不是只在定理使用时外加有效性前提。
该接口用于将可定义类关系变为模型内部的双模拟候选见证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphFormulaGuard

open Logic FirstOrder SecondOrderSyntax GraphTranslation

set_option autoImplicit false

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (R S : SecondOrderModel.set_l ℳ) :
    ∃ F : SecondOrderModel.set_l ℳ, ∀ n m,
      SecondOrderPairing.relation_l F n m ↔
        ∃ (hn : SecondOrderDomain.wf_l R n) (hm : SecondOrderDomain.wf_l S m),
          φ.satisfies ((η.pushFree (SecondOrderQuotient.mk_l hℳ ⟨S, m, hm⟩)).pushFree
            (SecondOrderQuotient.mk_l hℳ ⟨R, n, hn⟩)) := by
  obtain ⟨E, hE⟩ := SecondOrderGraphFormulaRelation.exists_l hℳ φ η R S
  let ψ : Formula signature_m [] [.num, .num, .set, .set, .set] :=
    .conj (domain_m (.fvar (.there (.there .here))) (.fvar .here))
      (.conj (domain_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here)))
        (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here)))))
          (.fvar .here) (.fvar (.there .here))))
  have hψ : SecondOrderArithmetic.language_m ψ = true := by
    change (_ && (_ && _)) = true
    rw [domain_pure_m _ _ rfl rfl, domain_pure_m _ _ rfl rfl]
    exact SecondOrderArithmetic.pure_language_m _ (GraphSyntax.edge_pure_m _ _ _ rfl rfl rfl)
  obtain ⟨F, hF⟩ := SecondOrderRelations.comprehension_l hℳ ψ hψ
    ((((Env.empty (M := ℳ)).pushFree E).pushFree S).pushFree R)
  refine ⟨F, fun n m => (hF n m).trans ?_⟩
  simp only [ψ, Formula.satisfies, SecondOrderInterpretation.domain_l, SecondOrderPairing.edge_l]
  change (SecondOrderDomain.wf_l R n ∧ SecondOrderDomain.wf_l S m ∧
    SecondOrderPairing.relation_l E n m) ↔ _
  constructor
  · rintro ⟨hn, hm, h⟩
    exact ⟨hn, hm, (hE n m hn hm).mp h⟩
  · rintro ⟨hn, hm, h⟩
    exact ⟨hn, hm, (hE n m hn hm).mpr h⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphFormulaGuard
