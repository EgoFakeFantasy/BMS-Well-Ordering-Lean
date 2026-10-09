import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 显式添加一个有序对的函数图延拓

输入新图的精确成员方程，而非重新用分离构造未知界的图。
这使后续层内证明可以由配对、并集闭包保持同一个固定层界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionAppend

open Logic FirstOrder SecondOrderQuotient SecondOrderFunctionObjects

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem value_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {f g c d p : type_l hℳ}
    (hp : SecondOrderPairObjects.ordered_l hℳ c d p)
    (hg : ∀ q, mem_l hℳ q g ↔ mem_l hℳ q f ∨ q = p) (x y : type_l hℳ) :
    SecondOrderFunctionObjects.value_l hℳ g x y ↔
      SecondOrderFunctionObjects.value_l hℳ f x y ∨ x = c ∧ y = d := by
  constructor
  · rintro ⟨q, hq, hxy⟩
    rcases (hg q).mp hq with hq | rfl
    · exact Or.inl ⟨q, hq, hxy⟩
    · exact Or.inr ((SecondOrderPairObjects.ordered_eq_l hℳ hxy hp).mp rfl)
  · rintro (⟨q, hq, hxy⟩ | ⟨rfl, rfl⟩)
    · exact ⟨q, (hg q).mpr (Or.inl hq), hxy⟩
    · exact ⟨p, (hg p).mpr (Or.inr rfl), hp⟩

theorem map_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {f g A D S c d p : type_l hℳ}
    (hf : SecondOrderFunctionObjects.map_l hℳ f A D) (hc : ¬mem_l hℳ c A) (hd : mem_l hℳ d D)
    (hS : ∀ x, mem_l hℳ x S ↔ mem_l hℳ x A ∨ x = c)
    (hp : SecondOrderPairObjects.ordered_l hℳ c d p)
    (hg : ∀ q, mem_l hℳ q g ↔ mem_l hℳ q f ∨ q = p) :
    SecondOrderFunctionObjects.map_l hℳ g S D := by
  have hValue := value_l hℳ hp hg
  have hUnique (x y z : type_l hℳ) (hy : SecondOrderFunctionObjects.value_l hℳ g x y)
      (hz : SecondOrderFunctionObjects.value_l hℳ g x z) : y = z := by
    rcases (hValue x y).mp hy with hy | ⟨hxc, hyd⟩
    · rcases (hValue x z).mp hz with hz | ⟨hxc, _⟩
      · exact SecondOrderFunctionProperties.value_unique_l hℳ hf hy hz
      · exact (hc (hxc ▸ (SecondOrderFunctionProperties.value_mem_l hℳ hf hy).1)).elim
    · rcases (hValue x z).mp hz with hz | ⟨_, hzd⟩
      · exact (hc (hxc ▸ (SecondOrderFunctionProperties.value_mem_l hℳ hf hz).1)).elim
      · exact hyd.trans hzd.symm
  constructor
  · intro q hq
    rcases (hg q).mp hq with hq | rfl
    · obtain ⟨x, y, hx, hy, hxy⟩ := hf.1 q hq
      exact ⟨x, y, (hS x).mpr (Or.inl hx), hy, hxy⟩
    · exact ⟨c, d, (hS c).mpr (Or.inr rfl), hd, hp⟩
  · intro x hx
    have hExists : ∃ y, mem_l hℳ y D ∧ SecondOrderFunctionObjects.value_l hℳ g x y := by
      rcases (hS x).mp hx with hx | rfl
      · obtain ⟨y, hy, _⟩ := hf.2 x hx
        exact ⟨y, hy.1, (hValue x y).mpr (Or.inl hy.2)⟩
      · exact ⟨d, hd, (hValue x d).mpr (Or.inr ⟨rfl, rfl⟩)⟩
    obtain ⟨y, hy⟩ := hExists
    exact ⟨y, hy, fun z hz => hUnique x z y hz.2 hy.2⟩

theorem singleton_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {f A D c d p : type_l hℳ}
    (hA : ∀ x, mem_l hℳ x A ↔ x = c) (hd : mem_l hℳ d D)
    (hp : SecondOrderPairObjects.ordered_l hℳ c d p) (hf : ∀ q, mem_l hℳ q f ↔ q = p) :
    SecondOrderFunctionObjects.map_l hℳ f A D ∧
      ∀ x y, SecondOrderFunctionObjects.value_l hℳ f x y ↔ x = c ∧ y = d := by
  have hValue (x y : type_l hℳ) : SecondOrderFunctionObjects.value_l hℳ f x y ↔ x = c ∧ y = d := by
    constructor
    · rintro ⟨q, hq, hxy⟩
      have hqp := (hf q).mp hq
      exact (SecondOrderPairObjects.ordered_eq_l hℳ hxy hp).mp hqp
    · rintro ⟨rfl, rfl⟩
      exact ⟨p, (hf p).mpr rfl, hp⟩
  refine ⟨⟨?_, ?_⟩, hValue⟩
  · intro q hq
    have hqp := (hf q).mp hq
    subst q
    exact ⟨c, d, (hA c).mpr rfl, hd, hp⟩
  · intro x hx
    have hxc := (hA x).mp hx
    exact ⟨d, ⟨hd, (hValue x d).mpr ⟨hxc, rfl⟩⟩,
      fun y hy => ((hValue x y).mp hy.2).2⟩

#print axioms map_l
#print axioms singleton_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionAppend
