import BMSConstructibleBridge.TextbookBoundedLevyCode

/-!
# `Delta0` 公式码的逐行有限证书

真正有界的有限 Lévy 分类必须把有界量词保留在基底中。本文件先把
`TextbookIsDelta0Code_l` 展开为只引用严格先前行的有限痕迹；后续对象语言
分类器可以检查这份痕迹，而不必在集合论公式中调用 Lean 的归纳命题。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- `Delta0` 痕迹的一行只记录公式元数和规范 E 码。 -/
structure TextbookDelta0Judgment where
  arity : Nat
  code : Nat
  deriving DecidableEq

namespace TextbookDelta0Judgment

/-- 一行记录表示的原始 `Delta0` 码命题。 -/
def Certified (entry : TextbookDelta0Judgment) : Prop :=
  TextbookIsDelta0Code_l entry.arity entry.code

/-- 否定保持元数。 -/
def negate (entry : TextbookDelta0Judgment) : TextbookDelta0Judgment :=
  { entry with code := textbookECode entry.code 0 2 }

/-- 同元数合取。 -/
def conjoin (left right : TextbookDelta0Judgment) :
    TextbookDelta0Judgment :=
  { left with code := textbookECode left.code right.code 3 }

/-- 用旧变量 `bound` 关闭子公式的末尾变量。 -/
def boundedExists (bound : Nat) (entry : TextbookDelta0Judgment) :
    TextbookDelta0Judgment :=
  { entry with
    arity := entry.arity - 1
    code := textbookECode
      (textbookECode
        (textbookECode (entry.arity - 1) bound 0) entry.code 3) 0 4 }

end TextbookDelta0Judgment

/-- 一行 `Delta0` 证书可引用的四种局部规则。 -/
def textbookDelta0RuleOver_l
    (available : TextbookDelta0Judgment → Prop)
    (entry : TextbookDelta0Judgment) : Prop :=
  (∃ left right : Fin entry.arity,
    entry.code = textbookECode left.1 right.1 0 ∨
      entry.code = textbookECode left.1 right.1 1) ∨
  (∃ child, available child ∧ entry = child.negate) ∨
  (∃ left, available left ∧ ∃ right, available right ∧
    left.arity = right.arity ∧ entry = left.conjoin right) ∨
  (∃ child, available child ∧ 0 < child.arity ∧
    ∃ bound : Fin (child.arity - 1), entry = child.boundedExists bound.1)

/-- 列表实现把可引用节点限制为严格先前行。 -/
def textbookDelta0LocalRule_l
    (previous : List TextbookDelta0Judgment)
    (entry : TextbookDelta0Judgment) : Prop :=
  textbookDelta0RuleOver_l (· ∈ previous) entry

/-- 有限前缀上的局部规则可判定。 -/
instance textbookDelta0LocalRule_decidable_l
    (previous : List TextbookDelta0Judgment)
    (entry : TextbookDelta0Judgment) :
    Decidable (textbookDelta0LocalRule_l previous entry) := by
  unfold textbookDelta0LocalRule_l textbookDelta0RuleOver_l
  infer_instance

/-- 扩充可引用节点保持局部规则。 -/
theorem textbookDelta0RuleOver_mono_l
    {available extended : TextbookDelta0Judgment → Prop}
    {entry : TextbookDelta0Judgment}
    (hSubset : ∀ child, available child → extended child)
    (hRule : textbookDelta0RuleOver_l available entry) :
    textbookDelta0RuleOver_l extended entry := by
  rcases hRule with hAtom | hNeg | hConj | hBounded
  · exact Or.inl hAtom
  · rcases hNeg with ⟨child, hChild, hEntry⟩
    exact Or.inr (Or.inl ⟨child, hSubset child hChild, hEntry⟩)
  · rcases hConj with ⟨left, hLeft, right, hRight, hRest⟩
    exact Or.inr (Or.inr (Or.inl
      ⟨left, hSubset left hLeft, right, hSubset right hRight, hRest⟩))
  · rcases hBounded with ⟨child, hChild, hRest⟩
    exact Or.inr (Or.inr (Or.inr
      ⟨child, hSubset child hChild, hRest⟩))

/-- 前序行正确时，一步局部规则推出当前行的原始 `Delta0` 证书。 -/
theorem textbookDelta0RuleOver_sound_l
    {available : TextbookDelta0Judgment → Prop}
    {entry : TextbookDelta0Judgment}
    (hPrevious : ∀ child, available child → child.Certified)
    (hRule : textbookDelta0RuleOver_l available entry) :
    entry.Certified := by
  rcases hRule with hAtom | hNeg | hConj | hBounded
  · rcases entry with ⟨arity, code⟩
    change TextbookIsDelta0Code_l arity code
    rcases hAtom with ⟨left, right, hCode | hCode⟩
    · change code = textbookECode left.1 right.1 0 at hCode
      rw [hCode]
      exact .mem left right
    · change code = textbookECode left.1 right.1 1 at hCode
      rw [hCode]
      exact .eq left right
  · rcases hNeg with ⟨child, hChild, hEntry⟩
    rw [hEntry]
    exact TextbookIsDelta0Code_l.neg (hPrevious child hChild)
  · rcases hConj with
      ⟨left, hLeft, right, hRight, hArity, hEntry⟩
    rw [hEntry]
    rcases left with ⟨leftArity, leftCode⟩
    rcases right with ⟨rightArity, rightCode⟩
    change leftArity = rightArity at hArity
    subst rightArity
    exact TextbookIsDelta0Code_l.conj
      (hPrevious _ hLeft) (hPrevious _ hRight)
  · rcases hBounded with ⟨child, hChild, hArity, bound, hEntry⟩
    rw [hEntry]
    rcases child with ⟨arity, code⟩
    change 0 < arity at hArity
    cases arity with
    | zero => exact (Nat.lt_irrefl 0 hArity).elim
    | succ arity =>
        change TextbookIsDelta0Code_l arity
          (textbookECode
            (textbookECode (textbookECode arity bound.1 0) code 3) 0 4)
        exact TextbookIsDelta0Code_l.boundedEx bound (hPrevious _ hChild)

/-- 逐行有限 `Delta0` 痕迹。 -/
inductive TextbookDelta0TraceValid : List TextbookDelta0Judgment → Prop where
  | nil : TextbookDelta0TraceValid []
  | snoc {previous : List TextbookDelta0Judgment}
      {entry : TextbookDelta0Judgment} :
      TextbookDelta0TraceValid previous →
      textbookDelta0LocalRule_l previous entry →
        TextbookDelta0TraceValid (previous ++ [entry])

/-- 合法痕迹中的每一行都具有正确原始证书。 -/
theorem TextbookDelta0TraceValid.certified_l
    {trace : List TextbookDelta0Judgment}
    (hTrace : TextbookDelta0TraceValid trace) :
    ∀ entry ∈ trace, entry.Certified := by
  induction hTrace with
  | nil => simp
  | @snoc previous entry hPrevious hRule ih =>
      intro current hCurrent
      rcases List.mem_append.mp hCurrent with hOld | hLast
      · exact ih current hOld
      · have hEqual : current = entry := List.mem_singleton.mp hLast
        subst current
        exact textbookDelta0RuleOver_sound_l
          (fun child hChild => ih child hChild) hRule

/-- 两份合法痕迹可以顺序拼接。 -/
theorem TextbookDelta0TraceValid.append_l
    {left right : List TextbookDelta0Judgment}
    (hLeft : TextbookDelta0TraceValid left)
    (hRight : TextbookDelta0TraceValid right) :
    TextbookDelta0TraceValid (left ++ right) := by
  induction hRight with
  | nil => simpa using hLeft
  | @snoc previous entry hPrevious hRule ih =>
      have hExtended : textbookDelta0LocalRule_l (left ++ previous) entry :=
        textbookDelta0RuleOver_mono_l
          (fun child hChild => List.mem_append_right left hChild) hRule
      simpa only [List.append_assoc] using
        TextbookDelta0TraceValid.snoc ih hExtended

namespace TextbookDelta0Judgment

/-- 一行记录由某份有限合法痕迹支持。 -/
def HasTrace (entry : TextbookDelta0Judgment) : Prop :=
  ∃ trace, TextbookDelta0TraceValid trace ∧ entry ∈ trace

/-- 向合法痕迹末尾加入一行局部合法记录。 -/
theorem hasTrace_of_localRule_l
    {trace : List TextbookDelta0Judgment}
    {entry : TextbookDelta0Judgment}
    (hTrace : TextbookDelta0TraceValid trace)
    (hRule : textbookDelta0LocalRule_l trace entry) : entry.HasTrace :=
  ⟨trace ++ [entry], .snoc hTrace hRule, by simp⟩

/-- 两种原子均具有单行证书。 -/
theorem atom_hasTrace_l (arity : Nat) (left right : Fin arity)
    (code : Nat) (hCode : code = textbookECode left.1 right.1 0 ∨
      code = textbookECode left.1 right.1 1) :
    HasTrace ⟨arity, code⟩ :=
  hasTrace_of_localRule_l .nil (Or.inl ⟨left, right, hCode⟩)

/-- 否定的痕迹由原痕迹追加一行得到。 -/
theorem HasTrace.negate_l {entry : TextbookDelta0Judgment}
    (hEntry : entry.HasTrace) : entry.negate.HasTrace := by
  rcases hEntry with ⟨trace, hTrace, hMember⟩
  exact hasTrace_of_localRule_l hTrace
    (Or.inr (Or.inl ⟨entry, hMember, rfl⟩))

/-- 合取先拼接两份痕迹，再追加合取节点。 -/
theorem HasTrace.conjoin_l {left right : TextbookDelta0Judgment}
    (hLeft : left.HasTrace) (hRight : right.HasTrace)
    (hArity : left.arity = right.arity) :
    (left.conjoin right).HasTrace := by
  rcases hLeft with ⟨leftTrace, hLeftTrace, hLeftMember⟩
  rcases hRight with ⟨rightTrace, hRightTrace, hRightMember⟩
  apply hasTrace_of_localRule_l (hLeftTrace.append_l hRightTrace)
  exact Or.inr (Or.inr (Or.inl
    ⟨left, List.mem_append_left rightTrace hLeftMember,
      right, List.mem_append_right leftTrace hRightMember, hArity, rfl⟩))

/-- 有界存在量词由子公式痕迹追加一行得到。 -/
theorem HasTrace.boundedExists_l {entry : TextbookDelta0Judgment}
    (hEntry : entry.HasTrace) (hArity : 0 < entry.arity)
    (bound : Fin (entry.arity - 1)) :
    (entry.boundedExists bound.1).HasTrace := by
  rcases hEntry with ⟨trace, hTrace, hMember⟩
  apply hasTrace_of_localRule_l hTrace
  exact Or.inr (Or.inr (Or.inr
    ⟨entry, hMember, hArity, bound, rfl⟩))

end TextbookDelta0Judgment

set_option maxHeartbeats 800000 in
/-- 每个原始 `Delta0` 码证书都能展开成有限逐行痕迹。 -/
theorem TextbookIsDelta0Code_l.hasTrace
    {arity code : Nat} (hCode : TextbookIsDelta0Code_l arity code) :
    TextbookDelta0Judgment.HasTrace ⟨arity, code⟩ := by
  exact TextbookIsDelta0Code_l.rec
    (motive := fun arity code _ =>
      TextbookDelta0Judgment.HasTrace ⟨arity, code⟩)
    (fun left right =>
      TextbookDelta0Judgment.atom_hasTrace_l _ left right _ (Or.inl rfl))
    (fun left right =>
      TextbookDelta0Judgment.atom_hasTrace_l _ left right _ (Or.inr rfl))
    (fun _ ih => by
      simpa [TextbookDelta0Judgment.negate] using
        TextbookDelta0Judgment.HasTrace.negate_l ih)
    (fun _ _ ihLeft ihRight => by
      simpa [TextbookDelta0Judgment.conjoin] using
        TextbookDelta0Judgment.HasTrace.conjoin_l ihLeft ihRight rfl)
    (fun bound _ ih => by
      simpa [TextbookDelta0Judgment.boundedExists] using
        TextbookDelta0Judgment.HasTrace.boundedExists_l ih
          (Nat.zero_lt_succ _) bound)
    hCode

/-- 有限逐行痕迹精确刻画原始 `Delta0` 码分类。 -/
theorem textbookDelta0Judgment_hasTrace_iff_certified_l
    (entry : TextbookDelta0Judgment) :
    entry.HasTrace ↔ entry.Certified := by
  constructor
  · rintro ⟨trace, hTrace, hMember⟩
    exact hTrace.certified_l entry hMember
  · intro hEntry
    exact TextbookIsDelta0Code_l.hasTrace hEntry

/-- 从给定前序开始依次检查剩余 `Delta0` 行。 -/
def checkTextbookDelta0TraceFrom_l
    (previous : List TextbookDelta0Judgment) :
    List TextbookDelta0Judgment → Bool
  | [] => true
  | entry :: remaining =>
      decide (textbookDelta0LocalRule_l previous entry) &&
        checkTextbookDelta0TraceFrom_l (previous ++ [entry]) remaining

/-- 从空前序开始检查完整痕迹。 -/
def checkTextbookDelta0Trace_l
    (trace : List TextbookDelta0Judgment) : Bool :=
  checkTextbookDelta0TraceFrom_l [] trace

/-- 分段检查与拼接后一次检查相同。 -/
theorem checkTextbookDelta0TraceFrom_append_l
    (previous first second : List TextbookDelta0Judgment) :
    checkTextbookDelta0TraceFrom_l previous (first ++ second) =
      (checkTextbookDelta0TraceFrom_l previous first &&
        checkTextbookDelta0TraceFrom_l (previous ++ first) second) := by
  induction first generalizing previous with
  | nil => simp [checkTextbookDelta0TraceFrom_l]
  | cons entry remaining ih =>
      simp only [List.cons_append, checkTextbookDelta0TraceFrom_l, ih,
        Bool.and_assoc, List.append_assoc, List.nil_append]

/-- 检查成功把合法前序扩充为合法完整痕迹。 -/
theorem checkTextbookDelta0TraceFrom_sound_l
    {previous remaining : List TextbookDelta0Judgment}
    (hPrevious : TextbookDelta0TraceValid previous)
    (hCheck : checkTextbookDelta0TraceFrom_l previous remaining = true) :
    TextbookDelta0TraceValid (previous ++ remaining) := by
  induction remaining generalizing previous with
  | nil => simpa using hPrevious
  | cons entry remaining ih =>
      have hBoth : textbookDelta0LocalRule_l previous entry ∧
          checkTextbookDelta0TraceFrom_l (previous ++ [entry]) remaining =
            true := by
        simpa only [checkTextbookDelta0TraceFrom_l, Bool.and_eq_true,
          decide_eq_true_eq] using hCheck
      obtain ⟨hRule, hRest⟩ := hBoth
      have hExtended := TextbookDelta0TraceValid.snoc hPrevious hRule
      simpa only [List.append_assoc, List.singleton_append] using
        ih hExtended hRest

/-- 合法痕迹在任意额外前序之后均检查成功。 -/
theorem TextbookDelta0TraceValid.checkFrom_l
    {trace : List TextbookDelta0Judgment}
    (hTrace : TextbookDelta0TraceValid trace)
    (previous : List TextbookDelta0Judgment) :
    checkTextbookDelta0TraceFrom_l previous trace = true := by
  induction hTrace with
  | nil => rfl
  | @snoc prior entry hPrior hRule ih =>
      rw [checkTextbookDelta0TraceFrom_append_l, ih]
      have hExtended : textbookDelta0LocalRule_l (previous ++ prior) entry :=
        textbookDelta0RuleOver_mono_l
          (fun child hMember => List.mem_append_right previous hMember) hRule
      simp only [checkTextbookDelta0TraceFrom_l, hExtended, decide_true,
        Bool.and_self]

/-- 可计算检查器与逐行合法性完全等价。 -/
theorem checkTextbookDelta0Trace_iff_valid_l
    (trace : List TextbookDelta0Judgment) :
    checkTextbookDelta0Trace_l trace = true ↔
      TextbookDelta0TraceValid trace := by
  constructor
  · intro hCheck
    exact checkTextbookDelta0TraceFrom_sound_l .nil hCheck
  · intro hTrace
    exact hTrace.checkFrom_l []

/-- 原始 `Delta0` 分类恰好意味着存在一份检查成功并包含目标行的痕迹。 -/
theorem textbookDelta0Judgment_certified_iff_checkedTrace_l
    (entry : TextbookDelta0Judgment) :
    entry.Certified ↔ ∃ trace,
      checkTextbookDelta0Trace_l trace = true ∧ entry ∈ trace := by
  rw [← textbookDelta0Judgment_hasTrace_iff_certified_l]
  simp only [TextbookDelta0Judgment.HasTrace,
    checkTextbookDelta0Trace_iff_valid_l]

end YesMetaZFC.BMS.ConstructibleBridge
