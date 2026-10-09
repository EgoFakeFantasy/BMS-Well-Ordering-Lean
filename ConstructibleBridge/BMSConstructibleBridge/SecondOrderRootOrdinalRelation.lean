import BMSConstructibleBridge.SecondOrderRootRepresentatives
import BMSConstructibleBridge.SecondOrderRootRelationWellFounded
import BMSConstructibleBridge.SecondOrderFoundation
import YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
import YesMetaZFC.SetTheory.Ord.Basic

/-! # 实际商序数的规范成员前驱图

最小数代表去掉同一成员的重复根。前驱关系由原模型理解产生，内部良基性
由饱和值域证明，而传递性及可比性直接读取原商序数的上游 IsOrdinal 接口。
不要求整个商模型满足 Collection 或原 PowerlessTheory。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootOrdinalRelation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def edge_l (A Q D : set_l ℳ) (i j : num_l ℳ) : Prop :=
  mem_l i D ∧ mem_l j D ∧ ∃ c, relation_l A c j ∧ relation_l Q i c

def spec_l (A Q D R : set_l ℳ) : Prop := ∀ i j, relation_l R i j ↔ edge_l A Q D i j

def formula_m : Formula signature_m [] [.num, .num, .set, .set, .set] :=
  .conj (.rel .mem (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) .nil))) <|
    .conj (.rel .mem (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there .here))) .nil))) <|
      .existsE .num <| .conj
        (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.bvar .here) (.fvar (.there .here)))
        (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.bvar .here))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem formula_l (A Q D : set_l ℳ) (i j : num_l ℳ) :
    formula_m.satisfies ((((((Env.empty (M := ℳ)).pushFree Q).pushFree A).pushFree D).pushFree j).pushFree i) ↔
      edge_l A Q D i j := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A Q D : set_l ℳ) : ∃! R, spec_l A Q D R := by
  obtain ⟨R, hR⟩ := SecondOrderRelations.comprehension_l hℳ formula_m pure_m
    ((((Env.empty (M := ℳ)).pushFree Q).pushFree A).pushFree D)
  have hSpec : spec_l A Q D R := fun i j => (hR i j).trans (formula_l A Q D i j)
  exact ⟨R, hSpec, fun S hS => SecondOrderRelations.ext_l hℳ S R
    (fun i j => (hS i j).trans (hSpec i j).symm)⟩

theorem wf_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {Q D R : set_l ℳ}
    (hQ : ∀ i j, relation_l Q i j ↔ SecondOrderBisimulation.eq_l A.real A.real i j)
    (hD : SecondOrderRootRepresentatives.spec_l A.real Q D A.root) (hR : spec_l A.real Q D R) :
    ∀ n, SecondOrderDomain.wf_l R n := by
  apply SecondOrderRootRelationWellFounded.wf_l hℳ A.real R
  · intro i j hij
    exact SecondOrderDomain.child_l hℳ A.real A.root j A.wf ((hD j).mp ((hR i j).mp hij).2.1).1
  · intro i j hij
    obtain ⟨_, _, c, hc, hEq⟩ := (hR i j).mp hij
    exact ⟨c, hc, (hQ i c).mp hEq⟩

private def child_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {Q D : set_l ℳ} (hD : SecondOrderRootRepresentatives.spec_l A.real Q D A.root)
    (n : num_l ℳ) (hn : mem_l n D) : SecondOrderGraph.code_l ℳ :=
  SecondOrderGraph.child_l hℳ A n ((hD n).mp hn).1

theorem transitive_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ A)) {Q D R : set_l ℳ}
    (hQ : ∀ i j, relation_l Q i j ↔ SecondOrderBisimulation.eq_l A.real A.real i j)
    (hD : SecondOrderRootRepresentatives.spec_l A.real Q D A.root) (hR : spec_l A.real Q D R) :
    ∀ i j k, relation_l R i j → relation_l R j k → relation_l R i k := by
  intro i j k hij hjk
  obtain ⟨hi, hj, c, hc, hIC⟩ := (hR i j).mp hij
  obtain ⟨_, hk, d, hd, hJD⟩ := (hR j k).mp hjk
  let I := child_l hℳ A hD i hi
  let J := child_l hℳ A hD j hj
  let K := child_l hℳ A hD k hk
  have hMemI : SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ I)
      (SecondOrderQuotient.mk_l hℳ A) := SecondOrderGraph.child_mem_l hℳ A i ((hD i).mp hi).1
  have hMemJ : SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ J)
      (SecondOrderQuotient.mk_l hℳ A) := SecondOrderGraph.child_mem_l hℳ A j ((hD j).mp hj).1
  have hMemK : SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ K)
      (SecondOrderQuotient.mk_l hℳ A) := SecondOrderGraph.child_mem_l hℳ A k ((hD k).mp hk).1
  have hIJ : SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ I)
      (SecondOrderQuotient.mk_l hℳ J) := ⟨c, hc, (hQ i c).mp hIC⟩
  have hJK : SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ J)
      (SecondOrderQuotient.mk_l hℳ K) := ⟨d, hd, (hQ j d).mp hJD⟩
  have hIK := hα.wellOrder.linear.trans (SecondOrderQuotient.mk_l hℳ I) hMemI
    (SecondOrderQuotient.mk_l hℳ J) hMemJ (SecondOrderQuotient.mk_l hℳ K) hMemK hIJ hJK
  change SecondOrderGraph.mem_l I K at hIK
  obtain ⟨e, he, hIE⟩ := hIK
  exact (hR i k).mpr ⟨hi, hk, e, he, (hQ i e).mpr hIE⟩

theorem irreflexive_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {Q D R : set_l ℳ}
    (hQ : ∀ i j, relation_l Q i j ↔ SecondOrderBisimulation.eq_l A.real A.real i j)
    (hD : SecondOrderRootRepresentatives.spec_l A.real Q D A.root) (hR : spec_l A.real Q D R) :
    ∀ n, ¬relation_l R n n := by
  intro n hn
  obtain ⟨hDₙ, _, c, hc, hEq⟩ := (hR n n).mp hn
  exact SecondOrderFoundation.irrefl_l hℳ (child_l hℳ A hD n hDₙ) ⟨c, hc, (hQ n c).mp hEq⟩

theorem compare_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ A)) {Q D R : set_l ℳ}
    (hQ : ∀ i j, relation_l Q i j ↔ SecondOrderBisimulation.eq_l A.real A.real i j)
    (hD : SecondOrderRootRepresentatives.spec_l A.real Q D A.root) (hR : spec_l A.real Q D R) :
    ∀ i j, mem_l i D → mem_l j D → relation_l R i j ∨ i = j ∨ relation_l R j i := by
  intro i j hi hj
  let I := child_l hℳ A hD i hi
  let J := child_l hℳ A hD j hj
  have hMemI : SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ I)
      (SecondOrderQuotient.mk_l hℳ A) := SecondOrderGraph.child_mem_l hℳ A i ((hD i).mp hi).1
  have hMemJ : SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ J)
      (SecondOrderQuotient.mk_l hℳ A) := SecondOrderGraph.child_mem_l hℳ A j ((hD j).mp hj).1
  rcases hα.wellOrder.linear.compare (SecondOrderQuotient.mk_l hℳ I) hMemI
      (SecondOrderQuotient.mk_l hℳ J) hMemJ with hEq | hIJ | hJI
  · have hExt : SetTheory.Extensional
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) :=
      ⟨SecondOrderQuotient.ext_l hℳ⟩
    have hEqual := hExt.eq_of_same_members _ _ hEq
    have hBisim := (SecondOrderQuotient.eq_iff_l hℳ I J).mp hEqual
    exact Or.inr (Or.inl (SecondOrderRootRepresentatives.injective_l hℳ hQ hD hi hj hBisim))
  · change SecondOrderGraph.mem_l I J at hIJ
    obtain ⟨c, hc, hIC⟩ := hIJ
    exact Or.inl ((hR i j).mpr ⟨hi, hj, c, hc, (hQ i c).mpr hIC⟩)
  · change SecondOrderGraph.mem_l J I at hJI
    obtain ⟨c, hc, hJC⟩ := hJI
    exact Or.inr (Or.inr ((hR j i).mpr ⟨hj, hi, c, hc, (hQ j c).mpr hJC⟩))

#print axioms wf_l
#print axioms transitive_l
#print axioms compare_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootOrdinalRelation
