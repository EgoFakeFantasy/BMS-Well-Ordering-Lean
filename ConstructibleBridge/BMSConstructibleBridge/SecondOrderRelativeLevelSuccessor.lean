import BMSConstructibleBridge.SecondOrderRelativeLevelProperties

/-! # 相对层值的后继 Def 方程

在任意母历史内找出前驱的规范代表，再以商唯一性连接任意输入／输出编码。
这里只证明既有 Def 关系的规格，不将模型相对规格冒充纯集合语言的定义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelSuccessor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem value_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {α β C C' : SecondOrderGraph.code_l ℳ}
    (hSucc : ∀ X, SecondOrderGraph.mem_l X β ↔
      SecondOrderGraph.mem_l X α ∨ SecondOrderGraph.eq_l X α)
    (hC : SecondOrderRelativeLevel.spec_l hℳ B hB α C)
    (hC' : SecondOrderRelativeLevel.spec_l hℳ B hB β C') :
    SecondOrderMemberDef.spec_l hℳ (SecondOrderQuotient.mk_l hℳ C) (SecondOrderQuotient.mk_l hℳ C') := by
  obtain ⟨A, hA, Q, D, R, S, m, W, hP, hS, hm, hβm, hWm, hC'W⟩ := hC'
  let M := SecondOrderRootCorrespondence.member_code_l hℳ A hP m hm
  have hβM : SecondOrderGraph.eq_l β M := hβm
  have hαβ : SecondOrderGraph.mem_l α β := (hSucc α).mpr (Or.inr (SecondOrderGraph.refl_l hℳ α))
  have hαM := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ α) hβM).mp hαβ
  obtain ⟨n, hn, hnm, hαn⟩ := SecondOrderRootCorrespondence.predecessor_exists_l hℳ A hP
    (SecondOrderOrdinalHistoryCoherence.ordinal_transitive_l hℳ A hA) α hm hαM
  let N := SecondOrderRootCorrespondence.member_code_l hℳ A hP n hn
  have hαN : SecondOrderGraph.eq_l α N := hαn
  have hImmediate : SecondOrderRelativeHierarchyStep.immediate_l R n m := by
    refine ⟨hnm, ?_⟩
    intro i him
    have hi := ((hP.predecessors i m).mp him).1
    let I := SecondOrderRootCorrespondence.member_code_l hℳ A hP i hi
    have hIM := (SecondOrderRootCorrespondence.edge_iff_l hℳ A hP hi hm).mp him
    have hIβ := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ I) hβM).mpr hIM
    rcases (hSucc I).mp hIβ with hIα | hIα
    · exact Or.inr ((SecondOrderRootCorrespondence.edge_iff_l hℳ A hP hi hn).mpr
        ((SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ I) hαN).mp hIα))
    · exact Or.inl (SecondOrderRootRepresentatives.injective_l hℳ hP.equality hP.representatives hi hn
        (SecondOrderGraph.trans_l hℳ hIα hαN))
  have hTrans := SecondOrderRootOrdinalRelation.transitive_l hℳ A hA
    hP.equality hP.representatives hP.predecessors
  have hIrrefl := SecondOrderRootOrdinalRelation.irreflexive_l hℳ A
    hP.equality hP.representatives hP.predecessors
  have hAsymm : ∀ i j, relation_l R i j → ¬relation_l R j i :=
    fun i j hij hji => hIrrefl i (hTrans i j i hij hji)
  obtain ⟨k, V, hk, hVn, hDef⟩ : SecondOrderRelativeHierarchyStep.successor_l R S m W := by
    rcases hS.history m W hWm with ⟨hMin, _⟩ | hSucc | ⟨hLimit, _⟩
    · exact False.elim (hMin n hnm)
    · exact hSucc
    · exact False.elim (hLimit.2 ⟨n, hImmediate⟩)
  have hkn := SecondOrderRelativeHierarchyStep.immediate_unique_l hAsymm hk hImmediate
  subst k
  let L : SecondOrderGraph.code_l ℳ := ⟨V, zero_l ℳ, hS.wellFounded n V hVn⟩
  let U : SecondOrderGraph.code_l ℳ := ⟨W, zero_l ℳ, hS.wellFounded m W hWm⟩
  have hL : SecondOrderRelativeLevel.spec_l hℳ B hB α L :=
    ⟨A, hA, Q, D, R, S, n, V, hP, hS, hn, hαn, hVn,
      SecondOrderBisimulation.refl_l hℳ V (zero_l ℳ)⟩
  have hCL := SecondOrderRelativeLevel.unique_l hℳ
    (SecondOrderGraph.refl_l hℳ ⟨B, zero_l ℳ, hB⟩) (SecondOrderGraph.refl_l hℳ α) hC hL
  obtain ⟨a, hDefault, V₀, E, D₀, Q₀, R₀, T, F, G, P, hDef⟩ := hDef
  have hValue := SecondOrderCanonicalMemberDefSemantics.represents_l hℳ L hDefault hDef
  change SecondOrderMemberDef.spec_l hℳ (SecondOrderQuotient.mk_l hℳ L) (SecondOrderQuotient.mk_l hℳ U) at hValue
  have hInput := (SecondOrderQuotient.eq_iff_l hℳ C L).mpr hCL
  have hOutput := (SecondOrderQuotient.eq_iff_l hℳ C' U).mpr hC'W
  rw [← hInput, ← hOutput] at hValue
  exact hValue

#print axioms value_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelSuccessor
