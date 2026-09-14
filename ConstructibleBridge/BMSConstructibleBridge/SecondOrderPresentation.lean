import BMSConstructibleBridge.ArithmeticPresentation
import YesMetaZFC.BMS.HeightDescent

/-!
# BM4 良序目标的单集合量词呈现

以自然数配对编码函数图，将算术呈现中的函数量词改为一个 `Set Nat` 量词。
图的全域性、唯一性及一步检查之后只出现自然数量词；任意集合参数均被覆盖，
并未把候选下降链限制为可计算或可构造的链。

这是宿主层的精确目标翻译。检查器仍须在对象算术中表示并证明总性，才能得到
正式的二阶算术公式；本模块不声称已经构造 `Z₂` 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPresentation

open StabilityFrame

set_option autoImplicit false

/-- 用配对码表示任意自然数函数的图。 -/
def graph_l (f : Nat → Nat) : Set Nat :=
  {t | (Nat.unpair t).2 = f (Nat.unpair t).1}

/-- 函数图的数值查询精确保留函数值。 -/
theorem mem_graph_l (f : Nat → Nat) (n m : Nat) :
    Nat.pair n m ∈ graph_l f ↔ m = f n := by
  simp only [graph_l, Set.mem_ofPred_eq, Nat.unpair_pair]

/-- 集合代码表示一个全域、单值的自然数函数。 -/
def function_l (X : Set Nat) : Prop :=
  ∀ n, ∃! m, Nat.pair n m ∈ X

/-- 每个函数的配对图都满足全域性和唯一性。 -/
theorem function_graph_l (f : Nat → Nat) : function_l (graph_l f) := by
  intro n
  exact ⟨f n, (mem_graph_l f n (f n)).mpr rfl,
    fun m h => (mem_graph_l f n m).mp h⟩

/-- 合法图代码与自然数函数之间的对应，不要求该函数可计算。 -/
theorem function_iff_l (X : Set Nat) : function_l X ↔
    ∃ f : Nat → Nat, ∀ n m, Nat.pair n m ∈ X ↔ m = f n := by
  constructor
  · intro h
    let f := fun n => Classical.choose (h n)
    refine ⟨f, ?_⟩
    intro n m
    have h₁ := Classical.choose_spec (h n)
    constructor
    · exact h₁.2 m
    · intro h₂
      rw [h₂]
      exact h₁.1
  · rintro ⟨f, h⟩ n
    exact ⟨f n, (h n (f n)).mpr rfl, fun m h₁ => (h n m).mp h₁⟩

/-- 单集合量词的 BM4 目标；全部内部量词均遍历自然数。 -/
def sentence_l : Prop :=
  ∀ X : Set Nat, function_l X →
    ∃ n a b, Nat.pair n a ∈ X ∧ Nat.pair (n + 1) b ∈ X ∧
      ∀ k, ArithmeticPresentation.check_l b a k ≠ true

/-- 集合图版本与函数版本的目标完全等价。 -/
theorem function_sentence_iff_l : sentence_l ↔ ArithmeticPresentation.sentence_l := by
  constructor
  · intro h f
    rcases h (graph_l f) (function_graph_l f) with ⟨n, a, b, h₁, h₂, h₃⟩
    have ha := (mem_graph_l f n a).mp h₁
    have hb := (mem_graph_l f (n + 1) b).mp h₂
    exact ⟨n, by simpa only [ha, hb] using h₃⟩
  · intro h X hX
    rcases (function_iff_l X).mp hX with ⟨f, h₁⟩
    rcases h f with ⟨n, h₂⟩
    exact ⟨n, f n, f (n + 1), (h₁ n (f n)).mpr rfl,
      (h₁ (n + 1) (f (n + 1))).mpr rfl, h₂⟩

/-- 单集合量词目标精确保留原生成数组上的无无限下降链命题。 -/
theorem sentence_iff_l : sentence_l ↔
    ¬ ∃ f : Nat → GeneratedArray,
      ∀ n, GeneratedStep (f (n + 1)) (f n) :=
  function_sentence_iff_l.trans ArithmeticPresentation.sentence_iff_l

/-- 单集合目标也等价于排除每个固定当前高度内的全部无限链。 -/
theorem height_sentence_iff_l : sentence_l ↔
    ∀ k, ¬ ∃ f : Nat → HeightDescent.fiber_l k,
      ∀ n, HeightDescent.step_l k (f (n + 1)) (f n) := by
  rw [sentence_iff_l, HeightDescent.descent_iff_l]
  simp only [not_exists]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPresentation
