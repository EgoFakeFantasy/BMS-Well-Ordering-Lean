import BMSConstructibleBridge.SecondOrderGraphFormulaRelation
import BMSConstructibleBridge.SecondOrderMemberDefAtoms
import BMSConstructibleBridge.SecondOrderMemberStructure
import BMSConstructibleBridge.PowerlessBMSQuotientCoding

/-! # 实际商函数沿自然数和母集枚举的实数拉回

函数本身可为任意原商对象，不要求已经属于相对类。原图公式理解产生
全部数坐标上的关系实数，再用已有母根正规化图处理非子节点编号。
输出仅为 Prop 中的实际关系证书，没有宿主函数图假设或代表选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberFunctionPullback

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderQuotient (mk_l)
open PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ theory_m}

theorem exists_l (K : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) (f : SecondOrderQuotient.type_l hℳ) :
    ∃ J : set_l ℳ, ∀ i j, relation_l J i j ↔
      SecondOrderFunctionObjects.value_l hℳ f (numberCode_l K i).val
        (SecondOrderMemberStructure.value_l hℳ A a ha j).val := by
  let φ : Formula ℒ [] [.set, .set, .set] :=
    SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set] := Env.empty.pushFree f
  obtain ⟨P, hP⟩ := SecondOrderGraphFormulaRelation.exists_l hℳ φ η K.less A.real
  obtain ⟨N, hN⟩ := SecondOrderMemberNormalizer.exists_l hℳ A.real A.root a
  let ψ : Formula signature_m [] [.num, .num, .set, .set] :=
    .existsE .num (.conj
      (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here)) (.bvar .here))
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here)))
  obtain ⟨J, hJ⟩ := SecondOrderRelations.comprehension_l hℳ ψ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree N).pushFree P)
  refine ⟨J, fun i j => (hJ i j).trans ?_⟩
  have hRead : ψ.satisfies
      (((((Env.empty (M := ℳ)).pushFree N).pushFree P).pushFree j).pushFree i) ↔
        relation_l P i (SecondOrderMemberNormalizer.value_l A.real A.root a j) := by
    simp only [ψ, Formula.satisfies, SecondOrderPairing.edge_l]
    change (∃ b, relation_l N j b ∧ relation_l P i b) ↔ _
    simp only [hN]
    exact ⟨fun ⟨_, hb, hp⟩ => hb ▸ hp, fun hp => ⟨_, rfl, hp⟩⟩
  refine hRead.trans ?_
  have h := hP i (SecondOrderMemberNormalizer.value_l A.real A.root a j)
    (SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec i)
    (SecondOrderDomain.child_l hℳ A.real A.root _ A.wf
      (SecondOrderMemberNormalizer.member_l A.real A.root a ha j))
  simpa only [φ, η, SecondOrderObjectSyntax.value_l, Term.eval,
    Env.pushFree_here, Env.pushFree_there, SecondOrderMemberStructure.value_l,
    SecondOrderMemberNormalizer.code_l, numberCode_l, SecondOrderNaturalGraph.code_l,
    SecondOrderGraph.child_l] using h

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberFunctionPullback
