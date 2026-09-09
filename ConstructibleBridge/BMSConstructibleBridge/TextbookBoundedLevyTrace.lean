import BMSConstructibleBridge.TextbookBoundedLevyCode

/-!
# 真正有界有限 Lévy 公式码的逐行证书

把归纳定义的公式码分类转换为有限记录。每行只存极性、层级、元数和自然数码；
局部检查只引用前面已经出现的行。该有限检查边界将用于对象语言中的证书编码，
其自身不调用公式的 Tarski 语义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- 公式码分类记录；`isSigma = true` 表示 Sigma，`false` 表示 Pi。 -/
structure TextbookBoundedLevyJudgment where
  isSigma : Bool
  level : Nat
  arity : Nat
  code : Nat
  deriving DecidableEq

namespace TextbookBoundedLevyJudgment

/-- 记录表示的原始归纳分类命题。 -/
def Certified (entry : TextbookBoundedLevyJudgment) : Prop :=
  if entry.isSigma then TextbookBoundedIsSigmaCode_l entry.level entry.arity entry.code
  else TextbookBoundedIsPiCode_l entry.level entry.arity entry.code

/-- 否定同时改变极性和自然数公式码。 -/
def negate (entry : TextbookBoundedLevyJudgment) : TextbookBoundedLevyJudgment :=
  { entry with isSigma := !entry.isSigma, code := textbookECode entry.code 0 2 }

/-- 同极性合取保留左记录的层级与元数。 -/
def conjoin (left right : TextbookBoundedLevyJudgment) : TextbookBoundedLevyJudgment :=
  { left with code := textbookECode left.code right.code 3 }

/-- 一个 Sigma 存在量词关闭末尾变量。 -/
def quantify (entry : TextbookBoundedLevyJudgment) : TextbookBoundedLevyJudgment :=
  { entry with arity := entry.arity - 1, code := textbookECode entry.code 0 4 }

/-- 提高一层后，两个极性都接受原层的证书。 -/
def raise (isSigma : Bool) (entry : TextbookBoundedLevyJudgment) :
    TextbookBoundedLevyJudgment :=
  { entry with isSigma := isSigma, level := entry.level + 1 }

/-- 否定操作的分类正确性。 -/
theorem negate_certified_l {entry : TextbookBoundedLevyJudgment}
    (hEntry : entry.Certified) : entry.negate.Certified := by
  rcases entry with ⟨polarity, level, arity, code⟩
  cases polarity
  · exact TextbookBoundedIsSigmaCode_l.neg hEntry
  · exact TextbookBoundedIsPiCode_l.neg hEntry

/-- 合取操作在同层、同元数、同极性的记录上保持正确性。 -/
theorem conjoin_certified_l {left right : TextbookBoundedLevyJudgment}
    (hPolarity : left.isSigma = right.isSigma)
    (hLevel : left.level = right.level) (hArity : left.arity = right.arity)
    (hLeft : left.Certified) (hRight : right.Certified) :
    (left.conjoin right).Certified := by
  rcases left with ⟨leftPolarity, level, arity, leftCode⟩
  rcases right with ⟨rightPolarity, rightLevel, rightArity, rightCode⟩
  cases hPolarity
  cases hLevel
  cases hArity
  cases leftPolarity
  · exact TextbookBoundedIsPiCode_l.conj hLeft hRight
  · exact TextbookBoundedIsSigmaCode_l.conj hLeft hRight

/-- 存在量词只消费正元数的 Sigma 记录。 -/
theorem quantify_certified_l {entry : TextbookBoundedLevyJudgment}
    (hPolarity : entry.isSigma = true) (hArity : 0 < entry.arity)
    (hEntry : entry.Certified) : entry.quantify.Certified := by
  rcases entry with ⟨polarity, level, arity, code⟩
  cases hPolarity
  cases arity with
  | zero => exact (Nat.lt_irrefl 0 hArity).elim
  | succ arity => exact TextbookBoundedIsSigmaCode_l.ex hEntry

/-- 累积层级的两种提升规则统一保持分类正确性。 -/
theorem raise_certified_l (isSigma : Bool) {entry : TextbookBoundedLevyJudgment}
    (hEntry : entry.Certified) : (entry.raise isSigma).Certified := by
  rcases entry with ⟨polarity, level, arity, code⟩
  cases polarity <;> cases isSigma
  · exact TextbookBoundedIsPiCode_l.lift hEntry
  · exact TextbookBoundedIsSigmaCode_l.ofPi hEntry
  · exact TextbookBoundedIsPiCode_l.ofSigma hEntry
  · exact TextbookBoundedIsSigmaCode_l.lift hEntry

end TextbookBoundedLevyJudgment

/--
一行证书的有限局部规则。基底行由已经对象化的 `Delta0` 分类器认证；其余
存在量化都限定在先前记录中，不递归调用有界 `Sigma` 或 `Pi` 分类命题。
-/
def textbookBoundedLevyRuleOver_l (available : TextbookBoundedLevyJudgment → Prop)
    (entry : TextbookBoundedLevyJudgment) : Prop :=
  TextbookIsDelta0Code_l entry.arity entry.code ∨
  (∃ child, available child ∧ entry = child.negate) ∨
  (∃ left, available left ∧ ∃ right, available right ∧
    left.isSigma = right.isSigma ∧ left.level = right.level ∧
      left.arity = right.arity ∧ entry = left.conjoin right) ∨
  (∃ child, available child ∧ child.isSigma = true ∧ 0 < child.arity ∧
    entry = child.quantify) ∨
  (∃ child, available child ∧ entry = child.raise entry.isSigma)

/-- 列表实现将可引用的记录限定为已经出现的行。 -/
def textbookBoundedLevyLocalRule_l (previous : List TextbookBoundedLevyJudgment)
    (entry : TextbookBoundedLevyJudgment) : Prop :=
  textbookBoundedLevyRuleOver_l (· ∈ previous) entry

/-- 有限局部规则可以直接判定。 -/
noncomputable instance textbookBoundedLevyLocalRule_decidable_l
    (previous : List TextbookBoundedLevyJudgment) (entry : TextbookBoundedLevyJudgment) :
    Decidable (textbookBoundedLevyLocalRule_l previous entry) := by
  exact Classical.propDecidable _

/-- 扩充先前记录不会破坏合法的单行推导。 -/
theorem textbookBoundedLevyLocalRule_mono_l
    {previous extended : List TextbookBoundedLevyJudgment}
    {entry : TextbookBoundedLevyJudgment}
    (hSubset : previous ⊆ extended)
    (hRule : textbookBoundedLevyLocalRule_l previous entry) :
    textbookBoundedLevyLocalRule_l extended entry := by
  rcases hRule with hDelta0 | hNeg | hConj | hEx | hRaise
  · exact Or.inl hDelta0
  · rcases hNeg with ⟨child, hChild, hEntry⟩
    exact Or.inr (Or.inl ⟨child, hSubset hChild, hEntry⟩)
  · rcases hConj with ⟨left, hLeft, right, hRight, hRest⟩
    exact Or.inr (Or.inr (Or.inl
      ⟨left, hSubset hLeft, right, hSubset hRight, hRest⟩))
  · rcases hEx with ⟨child, hChild, hRest⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨child, hSubset hChild, hRest⟩)))
  · rcases hRaise with ⟨child, hChild, hRest⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨child, hSubset hChild, hRest⟩)))

/-- 前序记录正确时，一步局部检查推出当前记录的原始分类证书。 -/
theorem textbookBoundedLevyRuleOver_sound_l
    {available : TextbookBoundedLevyJudgment → Prop} {entry : TextbookBoundedLevyJudgment}
    (hPrevious : ∀ child, available child → child.Certified)
    (hRule : textbookBoundedLevyRuleOver_l available entry) : entry.Certified := by
  rcases hRule with hDelta0 | hNeg | hConj | hEx | hRaise
  · rcases entry with ⟨polarity, level, arity, code⟩
    cases polarity
    · exact TextbookBoundedIsPiCode_l.delta0 hDelta0
    · exact TextbookBoundedIsSigmaCode_l.delta0 hDelta0
  · rcases hNeg with ⟨child, hChild, rfl⟩
    exact TextbookBoundedLevyJudgment.negate_certified_l (hPrevious child hChild)
  · rcases hConj with ⟨left, hLeft, right, hRight, hPolarity, hLevel, hArity, rfl⟩
    exact TextbookBoundedLevyJudgment.conjoin_certified_l hPolarity hLevel hArity
      (hPrevious left hLeft) (hPrevious right hRight)
  · rcases hEx with ⟨child, hChild, hPolarity, hArity, rfl⟩
    exact TextbookBoundedLevyJudgment.quantify_certified_l hPolarity hArity
      (hPrevious child hChild)
  · rcases hRaise with ⟨child, hChild, hEntry⟩
    rw [hEntry]
    exact TextbookBoundedLevyJudgment.raise_certified_l _ (hPrevious child hChild)

/-- 列表前序是通用单步正确性定理的一个实例。 -/
theorem textbookBoundedLevyLocalRule_sound_l
    {previous : List TextbookBoundedLevyJudgment} {entry : TextbookBoundedLevyJudgment}
    (hPrevious : ∀ child ∈ previous, child.Certified)
    (hRule : textbookBoundedLevyLocalRule_l previous entry) : entry.Certified :=
  textbookBoundedLevyRuleOver_sound_l hPrevious hRule

/-- 逐行检查的有限证书：每个后继只引用严格先前的记录。 -/
inductive TextbookBoundedLevyTraceValid : List TextbookBoundedLevyJudgment → Prop where
  | nil : TextbookBoundedLevyTraceValid []
  | snoc {previous : List TextbookBoundedLevyJudgment} {entry : TextbookBoundedLevyJudgment} :
      TextbookBoundedLevyTraceValid previous → textbookBoundedLevyLocalRule_l previous entry →
        TextbookBoundedLevyTraceValid (previous ++ [entry])

/-- 合法有限证书中的每行都满足原始归纳分类定义。 -/
theorem TextbookBoundedLevyTraceValid.certified_l
    {trace : List TextbookBoundedLevyJudgment} (hTrace : TextbookBoundedLevyTraceValid trace) :
    ∀ entry ∈ trace, entry.Certified := by
  induction hTrace with
  | nil => simp
  | @snoc previous entry hPrevious hRule ih =>
      intro current hCurrent
      rcases List.mem_append.mp hCurrent with hOld | hLast
      · exact ih current hOld
      · have hEqual : current = entry := List.mem_singleton.mp hLast
        subst current
        exact textbookBoundedLevyLocalRule_sound_l ih hRule

/-- 两份合法记录可顺序拼接；右侧每行仍只引用它原来的先前记录。 -/
theorem TextbookBoundedLevyTraceValid.append_l
    {left right : List TextbookBoundedLevyJudgment}
    (hLeft : TextbookBoundedLevyTraceValid left) (hRight : TextbookBoundedLevyTraceValid right) :
    TextbookBoundedLevyTraceValid (left ++ right) := by
  induction hRight with
  | nil => simpa using hLeft
  | @snoc previous entry hPrevious hRule ih =>
      have hExtended := textbookBoundedLevyLocalRule_mono_l
        (extended := left ++ previous)
        (fun _ hMember => List.mem_append_right left hMember) hRule
      simpa only [List.append_assoc] using TextbookBoundedLevyTraceValid.snoc ih hExtended

namespace TextbookBoundedLevyJudgment

/-- 一条分类记录由某份有限合法记录支持。 -/
def HasTrace (entry : TextbookBoundedLevyJudgment) : Prop :=
  ∃ trace, TextbookBoundedLevyTraceValid trace ∧ entry ∈ trace

/-- 将一行局部合法的记录加入已验证的有限记录。 -/
theorem hasTrace_of_localRule_l {trace : List TextbookBoundedLevyJudgment}
    {entry : TextbookBoundedLevyJudgment} (hTrace : TextbookBoundedLevyTraceValid trace)
    (hRule : textbookBoundedLevyLocalRule_l trace entry) : entry.HasTrace :=
  ⟨trace ++ [entry], TextbookBoundedLevyTraceValid.snoc hTrace hRule, by simp⟩

/-- 任意 `Delta0` 基底码在两个极性和任意有限层都有单行证书。 -/
theorem delta0_hasTrace_l (isSigma : Bool) (level arity code : Nat)
    (hCode : TextbookIsDelta0Code_l arity code) :
    HasTrace ⟨isSigma, level, arity, code⟩ :=
  hasTrace_of_localRule_l .nil (Or.inl hCode)

/-- 否定的有限记录由原记录追加一行得到。 -/
theorem HasTrace.negate_l {entry : TextbookBoundedLevyJudgment}
    (hEntry : entry.HasTrace) : entry.negate.HasTrace := by
  rcases hEntry with ⟨trace, hTrace, hMember⟩
  exact hasTrace_of_localRule_l hTrace (Or.inr (Or.inl ⟨entry, hMember, rfl⟩))

/-- 两个同类合取分支先拼接各自证书，再加入合取行。 -/
theorem HasTrace.conjoin_l {left right : TextbookBoundedLevyJudgment}
    (hLeft : left.HasTrace) (hRight : right.HasTrace)
    (hPolarity : left.isSigma = right.isSigma)
    (hLevel : left.level = right.level) (hArity : left.arity = right.arity) :
    (left.conjoin right).HasTrace := by
  rcases hLeft with ⟨leftTrace, hLeftTrace, hLeftMember⟩
  rcases hRight with ⟨rightTrace, hRightTrace, hRightMember⟩
  apply hasTrace_of_localRule_l (hLeftTrace.append_l hRightTrace)
  exact Or.inr (Or.inr (Or.inl
    ⟨left, List.mem_append_left rightTrace hLeftMember,
      right, List.mem_append_right leftTrace hRightMember,
      hPolarity, hLevel, hArity, rfl⟩))

/-- 存在量词的有限记录保留正元数和极性检查。 -/
theorem HasTrace.quantify_l {entry : TextbookBoundedLevyJudgment}
    (hEntry : entry.HasTrace) (hPolarity : entry.isSigma = true)
    (hArity : 0 < entry.arity) : entry.quantify.HasTrace := by
  rcases hEntry with ⟨trace, hTrace, hMember⟩
  exact hasTrace_of_localRule_l hTrace (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨entry, hMember, hPolarity, hArity, rfl⟩))))

/-- 累积提升的有限记录可选择目标极性。 -/
theorem HasTrace.raise_l {entry : TextbookBoundedLevyJudgment}
    (hEntry : entry.HasTrace) (isSigma : Bool) : (entry.raise isSigma).HasTrace := by
  rcases hEntry with ⟨trace, hTrace, hMember⟩
  exact hasTrace_of_localRule_l hTrace (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨entry, hMember, rfl⟩))))

end TextbookBoundedLevyJudgment

/-- 每个原始 Sigma 码证书都能展开成有限逐行证书。 -/
theorem TextbookBoundedIsSigmaCode_l.hasTrace_l
    {level arity code : Nat} (hCode : TextbookBoundedIsSigmaCode_l level arity code) :
    TextbookBoundedLevyJudgment.HasTrace ⟨true, level, arity, code⟩ := by
  exact TextbookBoundedIsSigmaCode_l.rec
    (motive_1 := fun level arity code _ =>
      TextbookBoundedLevyJudgment.HasTrace ⟨true, level, arity, code⟩)
    (motive_2 := fun level arity code _ =>
      TextbookBoundedLevyJudgment.HasTrace ⟨false, level, arity, code⟩)
    (fun hDelta0 => TextbookBoundedLevyJudgment.delta0_hasTrace_l
      true _ _ _ hDelta0)
    (fun _ hBody => hBody.negate_l)
    (fun _ _ hLeft hRight => by
      have hConjunction := hLeft.conjoin_l hRight rfl rfl rfl
      exact hConjunction)
    (fun _ hBody => hBody.quantify_l rfl (Nat.zero_lt_succ _))
    (fun _ hBody => hBody.raise_l true)
    (fun _ hBody => hBody.raise_l true)
    (fun hDelta0 => TextbookBoundedLevyJudgment.delta0_hasTrace_l
      false _ _ _ hDelta0)
    (fun _ hBody => hBody.negate_l)
    (fun _ _ hLeft hRight => by
      have hConjunction := hLeft.conjoin_l hRight rfl rfl rfl
      exact hConjunction)
    (fun _ hBody => hBody.raise_l false)
    (fun _ hBody => hBody.raise_l false)
    hCode

/-- 每个原始 Pi 码证书都能展开成有限逐行证书。 -/
theorem TextbookBoundedIsPiCode_l.hasTrace_l
    {level arity code : Nat} (hCode : TextbookBoundedIsPiCode_l level arity code) :
    TextbookBoundedLevyJudgment.HasTrace ⟨false, level, arity, code⟩ := by
  exact TextbookBoundedIsPiCode_l.rec
    (motive_1 := fun level arity code _ =>
      TextbookBoundedLevyJudgment.HasTrace ⟨true, level, arity, code⟩)
    (motive_2 := fun level arity code _ =>
      TextbookBoundedLevyJudgment.HasTrace ⟨false, level, arity, code⟩)
    (fun hDelta0 => TextbookBoundedLevyJudgment.delta0_hasTrace_l
      true _ _ _ hDelta0)
    (fun _ hBody => hBody.negate_l)
    (fun _ _ hLeft hRight => by
      have hConjunction := hLeft.conjoin_l hRight rfl rfl rfl
      exact hConjunction)
    (fun _ hBody => hBody.quantify_l rfl (Nat.zero_lt_succ _))
    (fun _ hBody => hBody.raise_l true)
    (fun _ hBody => hBody.raise_l true)
    (fun hDelta0 => TextbookBoundedLevyJudgment.delta0_hasTrace_l
      false _ _ _ hDelta0)
    (fun _ hBody => hBody.negate_l)
    (fun _ _ hLeft hRight => by
      have hConjunction := hLeft.conjoin_l hRight rfl rfl rfl
      exact hConjunction)
    (fun _ hBody => hBody.raise_l false)
    (fun _ hBody => hBody.raise_l false)
    hCode

/-- 有限记录刻画原始分类定义，两个方向均没有附加语义假设。 -/
theorem textbookBoundedLevyJudgment_hasTrace_iff_certified_l
    (entry : TextbookBoundedLevyJudgment) : entry.HasTrace ↔ entry.Certified := by
  constructor
  · rintro ⟨trace, hTrace, hMember⟩
    exact hTrace.certified_l entry hMember
  · intro hEntry
    rcases entry with ⟨polarity, level, arity, code⟩
    cases polarity
    · exact TextbookBoundedIsPiCode_l.hasTrace_l hEntry
    · exact TextbookBoundedIsSigmaCode_l.hasTrace_l hEntry

/-- 从给定前序记录开始，按顺序检查剩余行。 -/
noncomputable def checkTextbookBoundedLevyTraceFrom_l (previous : List TextbookBoundedLevyJudgment) :
    List TextbookBoundedLevyJudgment → Bool
  | [] => true
  | entry :: remaining =>
      decide (textbookBoundedLevyLocalRule_l previous entry) &&
        checkTextbookBoundedLevyTraceFrom_l (previous ++ [entry]) remaining

/-- 检查空前序下的完整有限证书。 -/
noncomputable def checkTextbookBoundedLevyTrace_l (trace : List TextbookBoundedLevyJudgment) : Bool :=
  checkTextbookBoundedLevyTraceFrom_l [] trace

/-- 两段顺序检查与拼接后的单次检查一致。 -/
theorem checkTextbookBoundedLevyTraceFrom_append_l
    (previous first second : List TextbookBoundedLevyJudgment) :
    checkTextbookBoundedLevyTraceFrom_l previous (first ++ second) =
      (checkTextbookBoundedLevyTraceFrom_l previous first &&
        checkTextbookBoundedLevyTraceFrom_l (previous ++ first) second) := by
  induction first generalizing previous with
  | nil => simp [checkTextbookBoundedLevyTraceFrom_l]
  | cons entry remaining ih =>
      simp only [List.cons_append, checkTextbookBoundedLevyTraceFrom_l, ih,
        Bool.and_assoc, List.append_assoc, List.nil_append]

/-- 检查成功把合法前序记录扩充为合法的完整记录。 -/
theorem checkTextbookBoundedLevyTraceFrom_sound_l
    {previous remaining : List TextbookBoundedLevyJudgment}
    (hPrevious : TextbookBoundedLevyTraceValid previous)
    (hCheck : checkTextbookBoundedLevyTraceFrom_l previous remaining = true) :
    TextbookBoundedLevyTraceValid (previous ++ remaining) := by
  induction remaining generalizing previous with
  | nil => simpa using hPrevious
  | cons entry remaining ih =>
      have hBoth : textbookBoundedLevyLocalRule_l previous entry ∧
          checkTextbookBoundedLevyTraceFrom_l (previous ++ [entry]) remaining = true := by
        simpa only [checkTextbookBoundedLevyTraceFrom_l, Bool.and_eq_true,
          decide_eq_true_eq] using hCheck
      obtain ⟨hRule, hRest⟩ := hBoth
      have hExtended := TextbookBoundedLevyTraceValid.snoc hPrevious hRule
      simpa only [List.append_assoc, List.singleton_append] using ih hExtended hRest

/-- 任意合法有限记录在任意额外前序之后都能检查成功。 -/
theorem TextbookBoundedLevyTraceValid.checkFrom_l
    {trace : List TextbookBoundedLevyJudgment} (hTrace : TextbookBoundedLevyTraceValid trace)
    (previous : List TextbookBoundedLevyJudgment) :
    checkTextbookBoundedLevyTraceFrom_l previous trace = true := by
  induction hTrace with
  | nil => rfl
  | @snoc prior entry hPrior hRule ih =>
      rw [checkTextbookBoundedLevyTraceFrom_append_l, ih]
      have hExtended : textbookBoundedLevyLocalRule_l (previous ++ prior) entry :=
        textbookBoundedLevyLocalRule_mono_l
          (fun _ hMember => List.mem_append_right previous hMember) hRule
      simp only [checkTextbookBoundedLevyTraceFrom_l, hExtended, decide_true,
        Bool.and_self]

/-- 可计算检查器与逐行合法性完全等价。 -/
theorem checkTextbookBoundedLevyTrace_iff_valid_l (trace : List TextbookBoundedLevyJudgment) :
    checkTextbookBoundedLevyTrace_l trace = true ↔ TextbookBoundedLevyTraceValid trace := by
  constructor
  · intro hCheck
    exact checkTextbookBoundedLevyTraceFrom_sound_l .nil hCheck
  · intro hTrace
    exact hTrace.checkFrom_l []

/-- 原始码分类恰好意味着存在一份检查成功并包含该记录的有限证书。 -/
theorem textbookBoundedLevyJudgment_certified_iff_checkedTrace_l
    (entry : TextbookBoundedLevyJudgment) :
    entry.Certified ↔ ∃ trace, checkTextbookBoundedLevyTrace_l trace = true ∧ entry ∈ trace := by
  rw [← textbookBoundedLevyJudgment_hasTrace_iff_certified_l]
  simp only [TextbookBoundedLevyJudgment.HasTrace, checkTextbookBoundedLevyTrace_iff_valid_l]

/-- Sigma 公式码的可计算有限证书刻画。 -/
theorem textbookBoundedIsSigmaCode_iff_checkedTrace_l (level arity code : Nat) :
    TextbookBoundedIsSigmaCode_l level arity code ↔
      ∃ trace, checkTextbookBoundedLevyTrace_l trace = true ∧
        (⟨true, level, arity, code⟩ : TextbookBoundedLevyJudgment) ∈ trace :=
  textbookBoundedLevyJudgment_certified_iff_checkedTrace_l ⟨true, level, arity, code⟩

/-- Pi 公式码的可计算有限证书刻画。 -/
theorem textbookBoundedIsPiCode_iff_checkedTrace_l (level arity code : Nat) :
    TextbookBoundedIsPiCode_l level arity code ↔
      ∃ trace, checkTextbookBoundedLevyTrace_l trace = true ∧
        (⟨false, level, arity, code⟩ : TextbookBoundedLevyJudgment) ∈ trace :=
  textbookBoundedLevyJudgment_certified_iff_checkedTrace_l ⟨false, level, arity, code⟩

end YesMetaZFC.BMS.ConstructibleBridge
