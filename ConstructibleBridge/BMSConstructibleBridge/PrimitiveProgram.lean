import BMSConstructibleBridge.PrimitiveFormulas

/-!
# 可执行的原始递归程序及纯公式编译

以实际数据类型承载七种原始递归构造，公式编译直接递归程序，不从 `Prop` 中
选择公式。原 `Nat.Primrec` 证书仍只给出程序的存在性；本文件不把这种存在性
冒充具体 BM4 检查器的可执行程序，也没有声称对象算术中的算法总性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PrimitiveProgram

open Logic FirstOrder SecondOrderSyntax

set_option autoImplicit false

/-- 七种构造的实际程序语法；没有无界最小化指令。 -/
inductive code_m where
  | zero | succ | left | right
  | pair (c d : code_m) | comp (c d : code_m) | prec (c d : code_m)
  deriving DecidableEq, Repr

/-- 程序的总求值；原始递归使用与已有有限 β 历史相同的约定。 -/
def eval_l : code_m → Nat → Nat
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun n => n.unpair.1
  | .right => fun n => n.unpair.2
  | .pair c d => fun n => Nat.pair (eval_l c n) (eval_l d n)
  | .comp c d => fun n => eval_l c (eval_l d n)
  | .prec c d => Nat.unpaired (PrimitiveHistory.run_l (eval_l c) (eval_l d))

/-- 先对抽象程序展开外层配对，避免内核在具体程序中归约配对逆函数。 -/
theorem prec_l (c d : code_m) (m n : Nat) :
    eval_l (.prec c d) (Nat.pair m n) =
      PrimitiveHistory.run_l (eval_l c) (eval_l d) m n := by
  simp only [eval_l, Nat.unpaired, Nat.unpair_pair]

/-- 给定程序后实际构造公式图，连同全部环境中的纯性和语义证书。 -/
def graph_m (c : code_m) : PrimitiveFormulas.graph_l (eval_l c) :=
  match c with
  | .zero => PrimitiveFormulas.zero_l
  | .succ => PrimitiveFormulas.succ_l
  | .left => PrimitiveFormulas.left_l
  | .right => PrimitiveFormulas.right_l
  | .pair c d => (graph_m c).pair_l (graph_m d)
  | .comp c d => (graph_m c).comp_l (graph_m d)
  | .prec c d => (graph_m c).prec_l (graph_m d)

/-- 每个实际程序的求值确实原始递归。 -/
theorem primrec_l (c : code_m) : Nat.Primrec (eval_l c) := by
  induction c with
  | zero => exact Nat.Primrec.zero
  | succ => exact Nat.Primrec.succ
  | left => exact Nat.Primrec.left
  | right => exact Nat.Primrec.right
  | pair c d hᵢ hⱼ => exact hᵢ.pair hⱼ
  | comp c d hᵢ hⱼ => exact hᵢ.comp hⱼ
  | prec c d hᵢ hⱼ => exact hᵢ.prec hⱼ

/-- 旧原始递归证书保证程序存在；并未将 `Prop` 证书强行消去为程序数据。 -/
theorem complete_m {f : Nat → Nat} (h : Nat.Primrec f) : ∃ c, eval_l c = f := by
  induction h with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | pair _ _ hᵢ hⱼ =>
      obtain ⟨c, rfl⟩ := hᵢ
      obtain ⟨d, rfl⟩ := hⱼ
      exact ⟨.pair c d, rfl⟩
  | comp _ _ hᵢ hⱼ =>
      obtain ⟨c, rfl⟩ := hᵢ
      obtain ⟨d, rfl⟩ := hⱼ
      exact ⟨.comp c d, rfl⟩
  | prec _ _ hᵢ hⱼ =>
      obtain ⟨c, rfl⟩ := hᵢ
      obtain ⟨d, rfl⟩ := hⱼ
      exact ⟨.prec c d, rfl⟩

/-- 编译器返回的真实公式，可在任意类型化变量上下文中实例化。 -/
def form_m {Γ Δ : SortContext signature_m} (c : code_m)
    (s t : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  (graph_m c).form s t

theorem pure_m {Γ Δ : SortContext signature_m} (c : code_m)
    (s t : Term signature_m Γ Δ .num) (hs : pure_term_m s = true) (ht : pure_term_m t = true) :
    SecondOrderSyntax.pure_m (form_m c s t) = true := (graph_m c).pure s t hs ht

theorem sound_m {Γ Δ : SortContext signature_m} (c : code_m)
    (η : Env structure_l Γ Δ) (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η (form_m c s t) ↔ eval_l c (Term.eval η s) = Term.eval η t :=
  (graph_m c).sound η s t

/-- 恒等函数的显式程序。 -/
def id_m : code_m := .pair .left .right

theorem id_l (n : Nat) : eval_l id_m n = n := Nat.pair_unpair n

/-- 常函数程序族按数码递归产生。 -/
def const_m : Nat → code_m
  | 0 => .zero
  | n + 1 => .comp .succ (const_m n)

theorem const_l (k n : Nat) : eval_l (const_m k) n = k := by
  induction k with
  | zero => rfl
  | succ k hᵢ => exact congrArg Nat.succ hᵢ

/-- 加法程序：初值为第一分量，每步把上次结果加一。 -/
def add_m : code_m := .prec id_m (.comp .succ (.comp .right .right))

theorem add_l (m n : Nat) : eval_l add_m (Nat.pair m n) = m + n := by
  rw [add_m, prec_l]
  induction n with
  | zero => exact id_l m
  | succ n hᵢ =>
      simpa only [PrimitiveHistory.run_l, eval_l, Nat.unpair_pair, Nat.add_succ] using
        congrArg Nat.succ hᵢ

/-- 乘法程序：从零开始，每步用已经给出的加法程序累加第一分量。 -/
def mul_m : code_m := .prec .zero (.comp add_m (.pair (.comp .right .right) .left))

theorem mul_l (m n : Nat) : eval_l mul_m (Nat.pair m n) = m * n := by
  rw [mul_m, prec_l]
  induction n with
  | zero => rfl
  | succ n hᵢ =>
      simp only [PrimitiveHistory.run_l, eval_l, Nat.unpair_pair] at hᵢ ⊢
      rw [add_l, hᵢ, Nat.mul_succ]

end YesMetaZFC.BMS.ConstructibleBridge.PrimitiveProgram
