import BMSConstructibleBridge.CodedReflection
import BMSConstructibleBridge.PrimitiveCoding

/-!
# 逐高度反射所需的精确目标句

`sentence_l n` 只说从第 `n` 个原种子开始的任意集合编码链必有断点；
其矩阵只使用已证原始递归的 seed、解码和检查器。它与该原种子的可达性
等价。统一这些句子便得到原 BM4 良序，不需要统一选择各高度的标签系统。

本模块不假定或声称 `Z₂` 已证明这些句子。对象理论中的逐实例证明生成器
及统一反射的实例化须与这里的宿主层等价严格区分。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SeedReflection

open StabilityFrame

set_option autoImplicit false

private def base (n : Nat) : GeneratedArray := ⟨validSeed n, .seed n⟩

/-- 第 `n` 个种子的单集合无下降链句；包括原始 seed 的起点检查。 -/
def sentence_l (n : Nat) : Prop :=
  ∀ X : Set Nat, SecondOrderPresentation.function_l X →
    (∃ a, Nat.pair 0 a ∈ X ∧ (ArithmeticPresentation.decode_l a).1.raw = seed n) →
    ∃ i a b, Nat.pair i a ∈ X ∧ Nat.pair (i + 1) b ∈ X ∧
      ∀ k, ArithmeticPresentation.check_l b a k ≠ true

private theorem descent_iff (n : Nat) : sentence_l n ↔
    ¬ ∃ f : Nat → GeneratedArray, f 0 = base n ∧
      ∀ i, GeneratedStep (f (i + 1)) (f i) := by
  classical
  open ArithmeticPresentation SecondOrderPresentation in
    constructor
    · intro h
      rintro ⟨f, h₀, h₁⟩
      let g := fun i => code_l (f i)
      have h₂ : ∃ a, Nat.pair 0 a ∈ graph_l g ∧ (decode_l a).1.raw = seed n := by
        refine ⟨g 0, (mem_graph_l g 0 (g 0)).mpr rfl, ?_⟩
        simp only [g, decode_code_l, h₀, base, raw_validSeed]
      obtain ⟨i, a, b, ha, hb, h₃⟩ := h (graph_l g) (function_graph_l g) h₂
      have ha := (mem_graph_l g i a).mp ha
      have hb := (mem_graph_l g (i + 1) b).mp hb
      obtain ⟨k, hk⟩ : step_l (g (i + 1)) (g i) := by
        apply (step_iff_l _ _).mpr
        simpa only [g, decode_code_l] using h₁ i
      exact h₃ k (by simpa only [ha, hb] using hk)
    · intro h X hX h₀
      obtain ⟨f, hf⟩ := (function_iff_l X).mp hX
      obtain ⟨a, ha, h₀⟩ := h₀
      rw [(hf 0 a).mp ha] at h₀
      by_contra h₁
      apply h
      refine ⟨fun i => decode_l (f i), Subtype.ext (ValidArray.ext h₀), ?_⟩
      intro i
      apply (step_iff_l _ _).mp
      by_contra h₂
      apply h₁
      exact ⟨i, f i, f (i + 1), (hf i _).mpr rfl, (hf (i + 1) _).mpr rfl,
        fun k hk => h₂ ⟨k, hk⟩⟩

private theorem acc_of_generated {a : GeneratedArray} (h : Acc GeneratedStep a) :
    Acc Step a.1 := by
  induction h with
  | intro a _ hᵢ =>
      apply Acc.intro a.1
      intro b h
      exact hᵢ ⟨b, generated_of_step a.2 h⟩ h

/-- 逐高度的集合句精确表达该原始种子的可达性。 -/
theorem acc_iff_l (n : Nat) : sentence_l n ↔ Acc Step (validSeed n) := by
  classical
  rw [descent_iff]
  constructor
  · intro h
    have h₀ : Acc GeneratedStep (base n) := by
      by_contra h₀
      exact h (not_acc_iff_exists_descending_chain.mp h₀)
    exact acc_of_generated h₀
  · intro h h₀
    have h₁ : Acc GeneratedStep (base n) := InvImage.accessible Subtype.val h
    exact (not_acc_iff_exists_descending_chain.mpr h₀) h₁

/-- 指定高度的局部可数反射系统给出对应无下降链句。 -/
theorem of_local_l {n : Nat} (h : CodedReflection.local_l n) : sentence_l n :=
  (acc_iff_l n).mpr (CodedReflection.seed_acc_l h)

/-- 所有逐高度句足以装配原严格良序，无需统一模型或统一标签。 -/
theorem wellOrder_l (h : ∀ n, sentence_l n) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent :=
  LocalDescent.wellOrder_l (fun n => (acc_iff_l n).mp (h n))

/-- 逐高度族与完整 BM4 的集合目标等价，既不加强也不减弱终局。 -/
theorem sentence_iff_l : (∀ n, sentence_l n) ↔ SecondOrderPresentation.sentence_l := by
  constructor
  · intro h
    exact SecondOrderPresentation.sentence_iff_l.mpr
      (LocalDescent.no_descent_l (fun n => (acc_iff_l n).mp (h n)))
  · intro h n
    apply (acc_iff_l n).mpr
    apply acc_of_generated (a := base n)
    by_contra h₀
    obtain ⟨f, _, hf⟩ := not_acc_iff_exists_descending_chain.mp h₀
    exact SecondOrderPresentation.sentence_iff_l.mp h ⟨f, hf⟩

end YesMetaZFC.BMS.ConstructibleBridge.SeedReflection
