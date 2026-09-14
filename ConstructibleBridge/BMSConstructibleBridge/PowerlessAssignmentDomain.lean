import BMSConstructibleBridge.PowerlessAssignmentUpdate

/-!
# 单变量更新的定义域保持

两侧均保留真实函数图条件；单凭取值关系不能排除非有序对杂项。
合法变量槽位保证更新不会扩大定义域，长度无需假定为外部自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentDomain

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

theorem domain_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f g i a n m A B : carrier_l ℳ} (hf : map_l f n A) (hg : map_l g m B)
    (hi : member_l ℳ i n) (h : PowerlessAssignmentUpdate.update_l f i a g) : n = m := by
  classical
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro x
  constructor
  · intro hx
    by_cases hxi : x = i
    · subst x
      exact (PowerlessFunction.value_mem_l hℳ hg (PowerlessAssignmentUpdate.at_l h)).1
    · obtain ⟨y, hy, _⟩ := hf.2 x hx
      exact (PowerlessFunction.value_mem_l hℳ hg ((h x y).mpr (Or.inr ⟨hxi, hy.2⟩))).1
  · intro hx
    obtain ⟨y, hy, _⟩ := hg.2 x hx
    rcases (h x y).mp hy.2 with ⟨hxi, _⟩ | ⟨_, hxy⟩
    · exact hxi.symm ▸ hi
    · exact (PowerlessFunction.value_mem_l hℳ hf hxy).1

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentDomain
