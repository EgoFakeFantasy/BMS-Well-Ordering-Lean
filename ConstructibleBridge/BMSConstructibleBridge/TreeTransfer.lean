import Mathlib.Order.WellFounded

/-!
# 良基树码的成员关系传输

`R` 表示码树的直接子节点，`E` 表示双模拟等价。解释成员关系允许先取子节点，
再换成等价的另一份代码。以下证明这种换码不会破坏可达性；只要求指定根良基，
不要求环境的所有代码树都良基，也不把模型内部的无下降链当作环境良基性。

这给出二阶解释所需的一个具体传输引理，尚未构造集合论到树码的完整解释。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.TreeTransfer

set_option autoImplicit false

/-- 节点等价保持子节点；对称性提供反向匹配。所有字段均只量化自然数。 -/
structure congruence_l (R E : Nat → Nat → Prop) : Prop where
  refl : ∀ a, E a a
  symm : ∀ {a b}, E a b → E b a
  trans : ∀ {a b c}, E a b → E b c → E a c
  forth : ∀ {a b c}, E a b → R c a → ∃ d, R d b ∧ E c d

/-- 解释中的成员关系：等价于某个直接子节点，而非必须使用同一份代码。 -/
def mem_l (R E : Nat → Nat → Prop) (a b : Nat) : Prop :=
  ∃ c, R c b ∧ E a c

variable {R E : Nat → Nat → Prop} (h : congruence_l R E)

include h

private theorem mem_right {a b c : Nat} (h₀ : E b c) (h₁ : mem_l R E a b) :
    mem_l R E a c := by
  obtain ⟨d, h₁, h₂⟩ := h₁
  obtain ⟨e, h₃, h₄⟩ := h.forth h₀ h₁
  exact ⟨e, h₃, h.trans h₂ h₄⟩

/-- 成员关系在两端换成双模拟等价码时不变。 -/
theorem mem_congr_l {a b c d : Nat} (h₀ : E a b) (h₁ : E c d) :
    mem_l R E a c ↔ mem_l R E b d := by
  constructor
  · rintro ⟨e, h₂, h₃⟩
    exact mem_right h h₁ ⟨e, h₂, h.trans (h.symm h₀) h₃⟩
  · rintro ⟨e, h₂, h₃⟩
    exact mem_right h (h.symm h₁) ⟨e, h₂, h.trans h₀ h₃⟩

private theorem acc_congr {a b : Nat} (h₀ : E a b) (h₁ : Acc (mem_l R E) b) :
    Acc (mem_l R E) a :=
  .intro a (fun _ h₂ => h₁.inv (mem_right h h₀ h₂))

/-- 指定码树的实际可达性传到允许双模拟换码的成员关系。 -/
theorem acc_l {a : Nat} (h₀ : Acc R a) : Acc (mem_l R E) a := by
  induction h₀ with
  | intro a _ hᵢ =>
      refine .intro a ?_
      rintro b ⟨c, h₁, h₂⟩
      exact acc_congr h h₂ (hᵢ c h₁)

/-- 一个外部良基根中的全部标签，经成员下降映射给出原标签序的良基性。 -/
theorem pullback_l {S : Nat → Nat → Prop} {a : Nat} (f : Nat → Nat)
    (h₀ : Acc R a) (h₁ : ∀ n, mem_l R E (f n) a)
    (h₂ : ∀ {n m}, S n m → mem_l R E (f n) (f m)) : WellFounded S := by
  have h₃ := acc_l h h₀
  refine ⟨fun n => ?_⟩
  exact Subrelation.accessible (fun h₄ => h₂ h₄)
    (InvImage.accessible f (h₃.inv (h₁ n)))

end YesMetaZFC.BMS.ConstructibleBridge.TreeTransfer
