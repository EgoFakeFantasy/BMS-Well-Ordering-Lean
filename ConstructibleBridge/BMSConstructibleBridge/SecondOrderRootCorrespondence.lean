import BMSConstructibleBridge.SecondOrderOrdinalHierarchy
import BMSConstructibleBridge.SecondOrderPredecessorCorrespondence
import BMSConstructibleBridge.SecondOrderTransitiveSuperset

/-! # 两个传递根的规范成员代表对应

实际对应实数由最大双模拟关系与两个最小代表域交截获得。母根无需相等：
只要配对成员相等，传递性就保证其严格前驱在双方代表域中双向覆盖。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootCorrespondence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (A B : SecondOrderGraph.code_l ℳ) (D D' I : set_l ℳ) : Prop :=
  ∀ i j, relation_l I i j ↔ mem_l i D ∧ mem_l j D' ∧
    SecondOrderBisimulation.eq_l A.real B.real i j

private def intersection_m : Formula signature_m [] [.num, .num, .set, .set, .set] :=
  .conj (.rel .mem (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) .nil))) <|
    .conj (.rel .mem (.cons (.fvar (.there .here)) (.cons (.fvar (.there (.there (.there .here)))) .nil)))
      (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here)))

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ)
    (D D' : set_l ℳ) : ∃! I, spec_l A B D D' I := by
  obtain ⟨E, hE⟩ := SecondOrderBisimulation.maximum_l hℳ A.real B.real
  obtain ⟨I, hI⟩ := SecondOrderRelations.comprehension_l hℳ intersection_m (by rfl)
    ((((Env.empty (M := ℳ)).pushFree E).pushFree D').pushFree D)
  have hRead i j : intersection_m.satisfies
      ((((((Env.empty (M := ℳ)).pushFree E).pushFree D').pushFree D).pushFree j).pushFree i) ↔
      mem_l i D ∧ mem_l j D' ∧ relation_l E i j := by
    simp only [intersection_m, Formula.satisfies, SecondOrderPairing.edge_l]
    rfl
  have hSpec : spec_l A B D D' I := fun i j =>
    (hI i j).trans ((hRead i j).trans (and_congr Iff.rfl (and_congr Iff.rfl (hE i j))))
  exact ⟨I, hSpec, fun J hJ => SecondOrderRelations.ext_l hℳ J I
    (fun i j => (hJ i j).trans (hSpec i j).symm)⟩

def member_code_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {Q D R : set_l ℳ} (h : SecondOrderOrdinalHierarchy.presentation_l A Q D R)
    (i : num_l ℳ) (hi : mem_l i D) : SecondOrderGraph.code_l ℳ :=
  SecondOrderGraph.child_l hℳ A i ((h.representatives i).mp hi).1

theorem edge_iff_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {Q D R : set_l ℳ} (h : SecondOrderOrdinalHierarchy.presentation_l A Q D R)
    {i j : num_l ℳ} (hi : mem_l i D) (hj : mem_l j D) :
    relation_l R i j ↔ SecondOrderGraph.mem_l (member_code_l hℳ A h i hi) (member_code_l hℳ A h j hj) := by
  constructor
  · intro hij
    obtain ⟨_, _, c, hc, hEq⟩ := (h.predecessors i j).mp hij
    exact ⟨c, hc, (h.equality i c).mp hEq⟩
  · rintro ⟨c, hc, hEq⟩
    exact (h.predecessors i j).mpr ⟨hi, hj, c, hc, (h.equality i c).mpr hEq⟩

theorem predecessor_exists_l (hℳ : Theory.Models ℳ theory_m) (B : SecondOrderGraph.code_l ℳ)
    {Q' D' R' : set_l ℳ} (hB : SecondOrderOrdinalHierarchy.presentation_l B Q' D' R')
    (hTransB : SecondOrderTransitiveSuperset.transitive_l B) (K : SecondOrderGraph.code_l ℳ)
    {m : num_l ℳ} (hm : mem_l m D')
    (hKM : SecondOrderGraph.mem_l K (member_code_l hℳ B hB m hm)) :
    ∃ j, ∃ hj : mem_l j D', relation_l R' j m ∧
      SecondOrderGraph.eq_l K (member_code_l hℳ B hB j hj) := by
  let M := member_code_l hℳ B hB m hm
  have hMB : SecondOrderGraph.mem_l M B :=
    SecondOrderGraph.child_mem_l hℳ B m ((hB.representatives m).mp hm).1
  obtain ⟨b, hb, hKb⟩ := hTransB M K hMB hKM
  obtain ⟨j, hj, hjb⟩ := SecondOrderRootRepresentatives.covers_l hℳ hB.equality hB.representatives hb
  let J := member_code_l hℳ B hB j hj
  have hKJ : SecondOrderGraph.eq_l K J := SecondOrderBisimulation.trans_l hℳ
    K.real B.real B.real K.root b j hKb (SecondOrderBisimulation.symm_l hℳ B.real B.real j b hjb)
  have hJM := (SecondOrderGraph.mem_congr_l hℳ hKJ (SecondOrderGraph.refl_l hℳ M)).mp hKM
  exact ⟨j, hj, (edge_iff_l hℳ B hB hj hm).mpr hJM, hKJ⟩

private theorem forth_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ)
    {Q Q' D D' R R' I : set_l ℳ}
    (hA : SecondOrderOrdinalHierarchy.presentation_l A Q D R)
    (hB : SecondOrderOrdinalHierarchy.presentation_l B Q' D' R')
    (hTransB : SecondOrderTransitiveSuperset.transitive_l B) (hI : spec_l A B D D' I)
    {n m : num_l ℳ} (hnm : relation_l I n m) {k : num_l ℳ} (hk : relation_l R k n) :
    ∃ j, relation_l R' j m ∧ relation_l I k j := by
  obtain ⟨hn, hm, hEqnm⟩ := (hI n m).mp hnm
  have hkd := ((hA.predecessors k n).mp hk).1
  let K := member_code_l hℳ A hA k hkd
  have hNM : SecondOrderGraph.eq_l (member_code_l hℳ A hA n hn) (member_code_l hℳ B hB m hm) := hEqnm
  have hKM := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ K) hNM).mp
    ((edge_iff_l hℳ A hA hkd hn).mp hk)
  obtain ⟨j, hj, hjm, hKJ⟩ := predecessor_exists_l hℳ B hB hTransB K hm hKM
  exact ⟨j, hjm, (hI k j).mpr ⟨hkd, hj, hKJ⟩⟩

theorem correspondence_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ)
    {Q Q' D D' R R' I : set_l ℳ}
    (hA : SecondOrderOrdinalHierarchy.presentation_l A Q D R)
    (hB : SecondOrderOrdinalHierarchy.presentation_l B Q' D' R')
    (hTransA : SecondOrderTransitiveSuperset.transitive_l A)
    (hTransB : SecondOrderTransitiveSuperset.transitive_l B) (hI : spec_l A B D D' I) :
    SecondOrderPredecessorCorrespondence.spec_l R R' I := by
  constructor
  · intro i j a b hia hjb
    obtain ⟨hi, ha, hEqia⟩ := (hI i a).mp hia
    obtain ⟨hj, hb, hEqjb⟩ := (hI j b).mp hjb
    exact (edge_iff_l hℳ A hA hi hj).trans
      ((SecondOrderGraph.mem_congr_l hℳ
        (show SecondOrderGraph.eq_l (member_code_l hℳ A hA i hi) (member_code_l hℳ B hB a ha) from hEqia)
        (show SecondOrderGraph.eq_l (member_code_l hℳ A hA j hj) (member_code_l hℳ B hB b hb) from hEqjb)).trans
          (edge_iff_l hℳ B hB ha hb).symm)
  · intro i a b hia hib
    obtain ⟨_, ha, hEqia⟩ := (hI i a).mp hia
    obtain ⟨_, hb, hEqib⟩ := (hI i b).mp hib
    exact SecondOrderRootRepresentatives.injective_l hℳ hB.equality hB.representatives ha hb
      (SecondOrderBisimulation.trans_l hℳ B.real A.real B.real a i b
        (SecondOrderBisimulation.symm_l hℳ A.real B.real i a hEqia) hEqib)
  · intro i j a hia hja
    obtain ⟨hi, _, hEqia⟩ := (hI i a).mp hia
    obtain ⟨hj, _, hEqja⟩ := (hI j a).mp hja
    exact SecondOrderRootRepresentatives.injective_l hℳ hA.equality hA.representatives hi hj
      (SecondOrderBisimulation.trans_l hℳ A.real B.real A.real i a j hEqia
        (SecondOrderBisimulation.symm_l hℳ A.real B.real j a hEqja))
  · intro n m hnm k hk
    exact forth_l hℳ A B hA hB hTransB hI hnm hk
  · intro n m hnm j hj
    obtain ⟨J, hJ⟩ := SecondOrderRelationOps.converse_l hℳ I
    have hRev : spec_l B A D' D J := by
      intro a i
      rw [hJ a i, hI i a]
      constructor
      · rintro ⟨hi, ha, hEq⟩
        exact ⟨ha, hi, SecondOrderBisimulation.symm_l hℳ A.real B.real i a hEq⟩
      · rintro ⟨ha, hi, hEq⟩
        exact ⟨hi, ha, SecondOrderBisimulation.symm_l hℳ B.real A.real a i hEq⟩
    obtain ⟨k, hk, hkj⟩ := forth_l hℳ B A hB hA hTransA hRev ((hJ m n).mpr hnm) hj
    exact ⟨k, hk, (hJ j k).mp hkj⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootCorrespondence
