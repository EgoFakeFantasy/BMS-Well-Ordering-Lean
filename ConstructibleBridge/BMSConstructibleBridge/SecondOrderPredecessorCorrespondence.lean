import BMSConstructibleBridge.SecondOrderRelativeHierarchyStep

/-! # 实际前驱关系对应保持阶段分类

对应仅要求在配对节点的严格初始段上双向覆盖；不要求整个原始图索引域相同。
两个唯一性条件用于最大前驱的传输，不把关系对应变成宿主选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorCorrespondence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderRelativeHierarchyStep (minimal_l immediate_l limit_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

structure spec_l (R R' I : set_l ℳ) : Prop where
  edges : ∀ i j a b, relation_l I i a → relation_l I j b →
    (relation_l R i j ↔ relation_l R' a b)
  rightUnique : ∀ i a b, relation_l I i a → relation_l I i b → a = b
  leftUnique : ∀ i j a, relation_l I i a → relation_l I j a → i = j
  forth : ∀ i a, relation_l I i a → ∀ j, relation_l R j i →
    ∃ b, relation_l R' b a ∧ relation_l I j b
  back : ∀ i a, relation_l I i a → ∀ b, relation_l R' b a →
    ∃ j, relation_l R j i ∧ relation_l I j b

theorem minimal_iff_l {R R' I : set_l ℳ} (h : spec_l R R' I)
    {n m : num_l ℳ} (hnm : relation_l I n m) : minimal_l R n ↔ minimal_l R' m := by
  constructor
  · intro hn j hj
    obtain ⟨i, hi, _⟩ := h.back n m hnm j hj
    exact hn i hi
  · intro hm i hi
    obtain ⟨j, hj, _⟩ := h.forth n m hnm i hi
    exact hm j hj

theorem immediate_iff_l {R R' I : set_l ℳ} (h : spec_l R R' I)
    {k n l m : num_l ℳ} (hkl : relation_l I k l) (hnm : relation_l I n m) :
    immediate_l R k n ↔ immediate_l R' l m := by
  constructor
  · intro hk
    refine ⟨(h.edges k n l m hkl hnm).mp hk.1, ?_⟩
    intro b hb
    obtain ⟨j, hj, hjb⟩ := h.back n m hnm b hb
    rcases hk.2 j hj with hjk | hjk
    · subst j
      exact Or.inl (h.rightUnique k b l hjb hkl)
    · exact Or.inr ((h.edges j k b l hjb hkl).mp hjk)
  · intro hl
    refine ⟨(h.edges k n l m hkl hnm).mpr hl.1, ?_⟩
    intro j hj
    obtain ⟨b, hb, hjb⟩ := h.forth n m hnm j hj
    rcases hl.2 b hb with hbl | hbl
    · subst b
      exact Or.inl (h.leftUnique j k l hjb hkl)
    · exact Or.inr ((h.edges j k b l hjb hkl).mpr hbl)

theorem successor_iff_l {R R' I : set_l ℳ} (h : spec_l R R' I)
    {n m : num_l ℳ} (hnm : relation_l I n m) :
    (∃ k, immediate_l R k n) ↔ ∃ l, immediate_l R' l m := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨l, _, hkl⟩ := h.forth n m hnm k hk.1
    exact ⟨l, (immediate_iff_l h hkl hnm).mp hk⟩
  · rintro ⟨l, hl⟩
    obtain ⟨k, _, hkl⟩ := h.back n m hnm l hl.1
    exact ⟨k, (immediate_iff_l h hkl hnm).mpr hl⟩

theorem limit_iff_l {R R' I : set_l ℳ} (h : spec_l R R' I)
    {n m : num_l ℳ} (hnm : relation_l I n m) : limit_l R n ↔ limit_l R' m := by
  exact and_congr (not_congr (minimal_iff_l h hnm)) (not_congr (successor_iff_l h hnm))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorCorrespondence
