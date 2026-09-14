import BMSConstructibleBridge.CountableGraph
import YesMetaZFC.SetTheory.Language
import YesMetaZFC.Logic.Semantics

/-!
# 图码商上的纯集合论结构

源语言的一阶等词必须是真正的载体相等，而不是未经处理的图码字面相等。
因此将跨图双模拟取商，再由成员换码不变性构造纯集合论结构。后续任意公式
的翻译可以直接复用原有类型化一阶语义，不另造一套逻辑核。

此结构仍位于标准宿主语义层，不是二阶算术中模型存在性的证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.GraphQuotient

open Logic FirstOrder

set_option autoImplicit false

def setoid_l : Setoid CountableGraph.code_l :=
  ⟨CountableGraph.eq_l, ⟨CountableGraph.refl_l, CountableGraph.symm_l, CountableGraph.trans_l⟩⟩

def type_l := Quotient setoid_l

def mk_l (A : CountableGraph.code_l) : type_l := Quotient.mk setoid_l A

theorem eq_iff_l (A B : CountableGraph.code_l) : mk_l A = mk_l B ↔ CountableGraph.eq_l A B :=
  ⟨fun h => Quotient.exact h, fun h => @Quotient.sound _ setoid_l A B h⟩

theorem surj_l (a : type_l) : ∃ A, mk_l A = a :=
  Quotient.inductionOn a (fun A => ⟨A, rfl⟩)

/-- 成员关系由已证的两端换码不变性下降到商，不使用代表选择函数。 -/
def mem_l (a b : type_l) : Prop :=
  Quotient.liftOn₂ a b CountableGraph.mem_l (by
    intro A B C D h h₁
    exact propext (CountableGraph.mem_congr_l h h₁))

theorem mem_iff_l (A B : CountableGraph.code_l) :
    mem_l (mk_l A) (mk_l B) ↔ CountableGraph.mem_l A B := Iff.rfl

/-- 解释等词现在确为结构载体上的等号。 -/
def structure_l : FirstOrder.Structure ℒ where
  Carrier _ := type_l
  nonempty _ := ⟨mk_l CountableGraph.empty_l⟩
  funcInterp f := nomatch f
  relInterp
    | .membership, .cons a (.cons b .nil) => mem_l a b

theorem ext_l (a b : type_l) : (∀ c, mem_l c a ↔ mem_l c b) → a = b := by
  refine Quotient.inductionOn₂ a b (fun A B h => ?_)
  apply Quotient.sound
  exact (CountableGraph.ext_l A B).mpr (fun C => h (mk_l C))

private theorem acc (A : CountableGraph.code_l) : Acc mem_l (mk_l A) := by
  induction A using CountableGraph.wellFounded_l.induction with
  | h A hᵢ =>
      refine .intro (mk_l A) ?_
      intro b h
      obtain ⟨B, rfl⟩ := surj_l b
      exact hᵢ B h

/-- 商成员关系仍良基，没有因合并代码产生新下降链。 -/
theorem wellFounded_l : WellFounded mem_l := by
  refine ⟨fun a => ?_⟩
  obtain ⟨A, rfl⟩ := surj_l a
  exact acc A

end YesMetaZFC.BMS.ConstructibleBridge.GraphQuotient
