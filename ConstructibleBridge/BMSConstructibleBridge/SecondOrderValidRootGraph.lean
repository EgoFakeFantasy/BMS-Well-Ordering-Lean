import BMSConstructibleBridge.SecondOrderInterpretation
import BMSConstructibleBridge.SecondOrderRelations

/-!
# 保留有效根、孤立无效根的内部图

用原理解公理删除无效父根的边。所得图的每个根都内部无链，而原有效根的
集合含义由实际内部双模拟保持。供带任意母集参数的有限闭包构造复用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderValidRootGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing GraphTranslation

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (R S : set_l ℳ) : Prop :=
  ∀ b a, relation_l S b a ↔ SecondOrderDomain.wf_l R a ∧ relation_l R b a

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) :
    ∃ S, spec_l R S := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .conj (domain_m (.fvar (.there (.there .here))) (.fvar (.there .here)))
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here)))
  have hφ : language_m φ = true := by
    change (_ && _) = true
    rw [domain_pure_m _ _ rfl rfl]
    exact pure_language_m _ (GraphSyntax.edge_pure_m _ _ _ rfl rfl rfl)
  obtain ⟨S, hS⟩ := SecondOrderRelations.comprehension_l hℳ φ hφ ((Env.empty (M := ℳ)).pushFree R)
  refine ⟨S, fun b a => (hS b a).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderInterpretation.domain_l, SecondOrderPairing.edge_l]
  rfl

theorem wf_l {R S : set_l ℳ} (hS : spec_l R S) (a : num_l ℳ) :
    SecondOrderDomain.wf_l S a := by
  classical
  by_cases ha : SecondOrderDomain.wf_l R a
  · exact SecondOrderDomain.mono_l R S a (fun b c h => ((hS b c).mp h).2) ha
  · exact SecondOrderDomain.leaf_l S a (fun b h => ha ((hS b a).mp h).1)

theorem agrees_l (hℳ : Theory.Models ℳ theory_m) {R S : set_l ℳ} (hS : spec_l R S)
    (a : num_l ℳ) (ha : SecondOrderDomain.wf_l R a) :
    SecondOrderBisimulation.eq_l R S a a := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .conj (.equal (.fvar .here) (.fvar (.there .here)))
      (domain_m (.fvar (.there (.there .here))) (.fvar .here))
  have hφ : language_m φ = true := by
    change (true && _) = true
    exact domain_pure_m _ _ rfl rfl
  obtain ⟨F, hF⟩ := SecondOrderRelations.comprehension_l hℳ φ hφ ((Env.empty (M := ℳ)).pushFree R)
  have hf b c : relation_l F b c ↔ b = c ∧ SecondOrderDomain.wf_l R b := by
    refine (hF b c).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderInterpretation.domain_l]
    rfl
  refine ⟨F, ?_, (hf a a).mpr ⟨rfl, ha⟩⟩
  intro b c hbc
  obtain ⟨rfl, hb⟩ := (hf b c).mp hbc
  constructor
  · intro d hd
    exact ⟨d, (hS d b).mpr ⟨hb, hd⟩,
      (hf d d).mpr ⟨rfl, SecondOrderDomain.child_l hℳ R b d hb hd⟩⟩
  · intro d hd
    have hdR := ((hS d b).mp hd).2
    exact ⟨d, hdR, (hf d d).mpr ⟨rfl, SecondOrderDomain.child_l hℳ R b d hb hdR⟩⟩

#print axioms exists_l
#print axioms wf_l
#print axioms agrees_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderValidRootGraph
