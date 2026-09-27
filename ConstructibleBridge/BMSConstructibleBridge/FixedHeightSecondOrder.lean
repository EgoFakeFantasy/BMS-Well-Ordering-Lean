import BMSConstructibleBridge.ArithmeticPresentation
import BMSConstructibleBridge.FiniteHeight
import BMSConstructibleBridge.SecondOrderPresentation

/-!
# 当前行数有界的纯二阶目标（宿主层精确规格）

与旧 `PureSecondOrder` / `SeedReflection` 的区别：旧链的终点是
`SeedReflection.sentence_l n`，只表达"从第 n 个种子出发"；本模块的目标
是 `FiniteHeight.carrier_l N` 上**全部当前高度 ≤ N 的生成数组**，
起始种子高度不受限制。

宿主规格：对任意 `X : Set Nat`，若 `X` 是一个全域单值函数图，且
`X` 的**全部**值经原 `ArithmeticPresentation.decode_l` 解码后当前高度 ≤ N，
则存在一步位置使得检查器不给出严格下降见证。高度上界写在前提里，
因此本模块的目标对应**不需要**先在对象算术中证明高度单调性。

本模块只给出**宿主层规格**及其与有界载体下降链的等价；真实纯算术矩阵
（`∃φ` 的构造、纯性证据与标准语义对应）在独立模块 `FixedHeightPureFormula` 中给出。
两者都**不是**任意非标准 Z₂ 模型中的算法总性，也**不是** Z₂ 的良序推导。
未使用 BMS 的全局良基性或稳定性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.FixedHeightSecondOrder

set_option autoImplicit false

/-- 当前高度有界的单集合量词目标。

    前提直接限制 `X` 的全部值（不只是种子或起点）：
    对每个 `i` 与每个 `a`，若 `Nat.pair i a ∈ X`，则 `a` 解码后的
    当前高度 ≤ `N`。结论要求存在相邻两步使检查器不给出下降见证。 -/
def sentence_l (N : Nat) : Prop :=
  ∀ X : Set Nat, SecondOrderPresentation.function_l X →
    (∀ i a, Nat.pair i a ∈ X →
      HeightDescent.height_l (ArithmeticPresentation.decode_l a).1 ≤ N) →
      ∃ i a b, Nat.pair i a ∈ X ∧ Nat.pair (i + 1) b ∈ X ∧
        ∀ k, ArithmeticPresentation.check_l b a k ≠ true

/-- 集合图版本与自然数函数版本精确等价。

    两端都不引入可计算性或可构造性限制；图中每个值都由原 `decode_l`
    解码，任意种子高度与任意下降实数均被保留。 -/
theorem function_sentence_iff_l (N : Nat) : sentence_l N ↔
    ∀ f : Nat → Nat,
      (∀ i, HeightDescent.height_l (ArithmeticPresentation.decode_l (f i)).1 ≤ N) →
        ∃ i, ∀ k, ArithmeticPresentation.check_l (f (i + 1)) (f i) k ≠ true := by
  constructor
  · intro h f hf
    have hbound : ∀ i a, Nat.pair i a ∈ SecondOrderPresentation.graph_l f →
        HeightDescent.height_l (ArithmeticPresentation.decode_l a).1 ≤ N := by
      intro i a ha
      have hae : a = f i := (SecondOrderPresentation.mem_graph_l f i a).mp ha
      simpa [hae] using hf i
    rcases h (SecondOrderPresentation.graph_l f)
        (SecondOrderPresentation.function_graph_l f) hbound with ⟨i, a, b, ha, hb, hk⟩
    have hae : a = f i := (SecondOrderPresentation.mem_graph_l f i a).mp ha
    have hbe : b = f (i + 1) := (SecondOrderPresentation.mem_graph_l f (i + 1) b).mp hb
    exact ⟨i, fun k => by simpa [hae, hbe] using hk k⟩
  · intro h X hX hXN
    rcases (SecondOrderPresentation.function_iff_l X).mp hX with ⟨f, hf⟩
    have hfN : ∀ i, HeightDescent.height_l (ArithmeticPresentation.decode_l (f i)).1 ≤ N := by
      intro i
      exact hXN i (f i) ((hf i (f i)).mpr rfl)
    rcases h f hfN with ⟨i, hi⟩
    exact ⟨i, f i, f (i + 1), (hf i (f i)).mpr rfl,
      (hf (i + 1) (f (i + 1))).mpr rfl, hi⟩

/-- 高度有界的编码下降链与有界载体上的原下降链精确等价。

    只用原 `decode_l` / `code_l` 与 `decode_code_l`，不调用 BMS 的
    全局良基性、稳定性或可比性。 -/
theorem descent_iff_l (N : Nat) :
    (∃ f : Nat → Nat,
        (∀ i, HeightDescent.height_l (ArithmeticPresentation.decode_l (f i)).1 ≤ N) ∧
          ∀ i, ArithmeticPresentation.step_l (f (i + 1)) (f i)) ↔
      ∃ f : Nat → FiniteHeight.carrier_l N,
        ∀ i, FiniteHeight.step_l N (f (i + 1)) (f i) := by
  constructor
  · rintro ⟨f, hf, hs⟩
    refine ⟨(fun i => ⟨ArithmeticPresentation.decode_l (f i), hf i⟩), ?_⟩
    intro i
    exact (ArithmeticPresentation.step_iff_l (f (i + 1)) (f i)).mp (hs i)
  · rintro ⟨f, hs⟩
    refine ⟨(fun i => ArithmeticPresentation.code_l (f i).1), ?_, ?_⟩
    · intro i
      simpa [ArithmeticPresentation.decode_code_l] using (f i).2
    · intro i
      apply (ArithmeticPresentation.step_iff_l _ _).mpr
      simpa [ArithmeticPresentation.decode_code_l, FiniteHeight.step_l] using hs i

/-- 当前高度有界目标精确保留有界载体上的无无限下降链命题。

    这是宿主层的目标等价，不是 Z₂ 内部推导，也不声称该句已经成立。 -/
theorem sentence_iff_l (N : Nat) : sentence_l N ↔
    ¬ ∃ f : Nat → FiniteHeight.carrier_l N,
      ∀ i, FiniteHeight.step_l N (f (i + 1)) (f i) := by
  rw [function_sentence_iff_l N]
  rw [← not_congr (descent_iff_l N)]
  simp only [not_exists, not_and, not_forall, ArithmeticPresentation.step_l]

end YesMetaZFC.BMS.ConstructibleBridge.FixedHeightSecondOrder
