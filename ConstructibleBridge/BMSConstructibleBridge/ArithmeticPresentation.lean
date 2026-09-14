import Mathlib.Logic.Equiv.List
import YesMetaZFC.BMS.WellFoundedness

/-!
# BM4 生成数组的算术呈现

自然数编码一个初始高度及有限展开指标列，解码后执行该列。所有自然数都有
输出，且每个生成数组都被覆盖；无需判定任意合法数组是否属于生成闭包。
一步关系使用可执行检查器与一个自然数见证，而不使用序数或稳定性模型。

本文件只给出 Lean 宿主层的算术呈现及精确等价。它尚未把检查器的递归过程
表示为二阶算术的公式，也未在对象理论中证明其总性，或证明最终良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ArithmeticPresentation

open StabilityFrame

/-- 从给定数组开始，依次执行有限展开指标列。 -/
def run_l (a : ValidArray) (s : List Nat) : ValidArray :=
  s.foldl ValidArray.expand a

/-- 展开指标列保持生成性。 -/
theorem generated_run_l {a : ValidArray} (h : Generated a) (s : List Nat) :
    Generated (run_l a s) := by
  induction s generalizing a with
  | nil => exact h
  | cons n s hᵢ => exact hᵢ (.expand h n)

/-- 在指标列末尾追加一个指标，等于对已有结果再展开一次。 -/
theorem run_append_l (a : ValidArray) (s : List Nat) (n : Nat) :
    run_l a (s ++ [n]) = (run_l a s).expand n := by
  simp only [run_l, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- 每个生成数组都具有实际的初始高度与有限展开轨迹。 -/
theorem exists_run_l {a : ValidArray} (h : Generated a) :
    ∃ n s, run_l (validSeed n) s = a := by
  induction h with
  | seed n => exact ⟨n, [], rfl⟩
  | @expand a h n hᵢ =>
      rcases hᵢ with ⟨m, s, hs⟩
      exact ⟨m, s ++ [n], by rw [run_append_l, hs]⟩

/-- 执行一个高度与轨迹对，输出带生成证明的数组。 -/
def eval_l (p : Nat × List Nat) : GeneratedArray :=
  ⟨run_l (validSeed p.1) p.2, generated_run_l (.seed p.1) p.2⟩

/-- 高度与轨迹的自然数编码；此编码与数组语义无关。 -/
def encode_l (n : Nat) (s : List Nat) : Nat :=
  Encodable.encode (n, s)

/-- 总解码：不在轨迹编码像中的自然数解释为零高度空轨迹。 -/
def decode_l (n : Nat) : GeneratedArray :=
  eval_l ((Encodable.decode (α := Nat × List Nat) n).getD (0, []))

/-- 实际编码的解码执行结果。 -/
theorem decode_encode_l (n : Nat) (s : List Nat) :
    decode_l (encode_l n s) = eval_l (n, s) := by
  simp only [decode_l, encode_l, Encodable.encodek, Option.getD_some]

/-- 自然数总解码覆盖所有生成数组。 -/
theorem surj_l : Function.Surjective decode_l := by
  intro a
  rcases exists_run_l a.2 with ⟨n, s, h⟩
  refine ⟨encode_l n s, ?_⟩
  rw [decode_encode_l]
  exact Subtype.ext h

/-- 有限原始数组等式的编码见证；选择条件本身可判定。 -/
theorem exists_code_l (a : GeneratedArray) : ∃ n, (decode_l n).1.raw = a.1.raw := by
  rcases surj_l a with ⟨n, h⟩
  exact ⟨n, congrArg (fun b : GeneratedArray => b.1.raw) h⟩

/-- 取解码为给定生成数组的最小自然数，不作任意见证选择。 -/
def code_l (a : GeneratedArray) : Nat := Nat.find (exists_code_l a)

/-- 规范编码的解码精确还原原数组。 -/
theorem decode_code_l (a : GeneratedArray) : decode_l (code_l a) = a :=
  Subtype.ext (ValidArray.ext (Nat.find_spec (exists_code_l a)))

/-- 规范编码不超过该数组的任意已有代码。 -/
theorem code_le_l {a : GeneratedArray} {n : Nat} (h : decode_l n = a) :
    code_l a ≤ n :=
  Nat.find_min' (exists_code_l a) (congrArg (fun b : GeneratedArray => b.1.raw) h)

/-- 不同生成数组有不同规范编码。 -/
theorem code_inj_l : Function.Injective code_l := by
  intro a b h
  rw [← decode_code_l a, ← decode_code_l b, h]

/-- 任意自然数代码的规范化，搜索结果不超过输入代码。 -/
def norm_l (n : Nat) : Nat := code_l (decode_l n)

theorem norm_le_l (n : Nat) : norm_l n ≤ n := code_le_l rfl

/-- 规范化不改变数组语义。 -/
theorem decode_norm_l (n : Nat) : decode_l (norm_l n) = decode_l n :=
  decode_code_l (decode_l n)

/-- 两个代码规范化相等，当且仅当它们表示同一个数组。 -/
theorem norm_eq_l (m n : Nat) : norm_l m = norm_l n ↔ decode_l m = decode_l n :=
  code_inj_l.eq_iff

/-- 规范化是幂等的，因而规范代码可以用有限数值判定识别。 -/
theorem norm_idem_l (n : Nat) : norm_l (norm_l n) = norm_l n :=
  congrArg code_l (decode_norm_l n)

/-- 原数组的规范码已经是不动点。 -/
theorem norm_code_l (a : GeneratedArray) : norm_l (code_l a) = code_l a :=
  congrArg code_l (decode_code_l a)

/-- 规范代码子类型由数值不动点条件识别，不再有重复数组。 -/
abbrev carrier_l := {n : Nat // norm_l n = n}

/-- 规范代码与原生成数组的实际双射，不只是一个满射呈现。 -/
def equiv_l : carrier_l ≃ GeneratedArray where
  toFun n := decode_l n.1
  invFun a := ⟨code_l a, norm_code_l a⟩
  left_inv n := Subtype.ext n.2
  right_inv a := decode_code_l a

/-- 检查给定指标是否见证一次非平凡展开；只比较有限自然数数组。 -/
def check_l (m n k : Nat) : Bool :=
  decide ((decode_l m).1.raw = ((decode_l n).1.expand k).raw ∧
    (decode_l m).1.raw ≠ (decode_l n).1.raw)

/-- 同时规范化两端，不改变任意指标的检查结果。 -/
theorem check_norm_l (m n k : Nat) : check_l (norm_l m) (norm_l n) k = check_l m n k := by
  simp only [check_l, decode_norm_l]

/-- 有限数组检查器与原合法数组等式精确对应。 -/
theorem check_iff_l (m n k : Nat) :
    check_l m n k = true ↔
      (decode_l m).1 = (decode_l n).1.expand k ∧
        (decode_l m).1 ≠ (decode_l n).1 := by
  simp only [check_l, decide_eq_true_eq]
  constructor
  · rintro ⟨h, h₀⟩
    refine ⟨ValidArray.ext h, ?_⟩
    intro h₁
    exact h₀ (congrArg (fun a : ValidArray => a.raw) h₁)
  · rintro ⟨h, h₀⟩
    refine ⟨congrArg (fun a : ValidArray => a.raw) h, ?_⟩
    intro h₁
    exact h₀ (ValidArray.ext h₁)

/-- 自然数上的实际严格一步关系；存在量词仅遍历展开指标。 -/
def step_l (m n : Nat) : Prop :=
  ∃ k, check_l m n k = true

/-- 编码的一步关系既不增加下降边，也不丢失原下降边。 -/
theorem step_iff_l (m n : Nat) :
    step_l m n ↔ GeneratedStep (decode_l m) (decode_l n) := by
  simp only [step_l, check_iff_l, GeneratedStep, Step, ExpansionEdge]
  constructor
  · rintro ⟨k, h, h₀⟩
    exact ⟨⟨k, h⟩, h₀⟩
  · rintro ⟨⟨k, h⟩, h₀⟩
    exact ⟨k, h, h₀⟩

/-- 重复编码不改变良基性：两个不同编码若代表相同数组，不会产生自降边。 -/
theorem wf_iff_l : WellFounded step_l ↔ WellFounded GeneratedStep :=
  surj_l.wellFounded_iff (fun {m n} => step_iff_l m n)

/-- 自然数下降链与原生成数组下降链的存在性精确等价。 -/
theorem descent_iff_l :
    (∃ f : Nat → Nat, ∀ n, step_l (f (n + 1)) (f n)) ↔
      ∃ f : Nat → GeneratedArray,
        ∀ n, GeneratedStep (f (n + 1)) (f n) := by
  constructor
  · rintro ⟨f, h⟩
    exact ⟨fun n => decode_l (f n), fun n => (step_iff_l _ _).mp (h n)⟩
  · rintro ⟨f, h⟩
    refine ⟨fun n => code_l (f n), fun n => (step_iff_l _ _).mpr ?_⟩
    simpa only [decode_code_l] using h n

/-- 无无限下降链也保持原目标，而不是只限制可计算下降链。 -/
theorem no_descent_iff_l :
    (¬ ∃ f : Nat → Nat, ∀ n, step_l (f (n + 1)) (f n)) ↔
      ¬ ∃ f : Nat → GeneratedArray,
        ∀ n, GeneratedStep (f (n + 1)) (f n) :=
  not_congr descent_iff_l

/-- 良序目标的宿主层二阶算术形状：仅有一个函数量词，余下均为自然数量词。
这不是已构造的对象语言公式，也不包含该句已经成立的假设或证明。 -/
def sentence_l : Prop :=
  ∀ f : Nat → Nat, ∃ n, ∀ k, check_l (f (n + 1)) (f n) k ≠ true

/-- 算术形状的目标精确保留原 BM4 无无限下降链命题。 -/
theorem sentence_iff_l : sentence_l ↔
    ¬ ∃ f : Nat → GeneratedArray,
      ∀ n, GeneratedStep (f (n + 1)) (f n) := by
  rw [← no_descent_iff_l]
  classical
  simp only [sentence_l, not_exists, not_forall, step_l]

end YesMetaZFC.BMS.ConstructibleBridge.ArithmeticPresentation
