import BMSConstructibleBridge.TextbookLevyCode

/-!
# 有限 Lévy 公式码的逐行证书

把归纳定义的公式码分类转换为有限记录。每行只存极性、层级、元数和自然数码；
局部检查只引用前面已经出现的行。该有限检查边界将用于对象语言中的证书编码，
其自身不调用公式的 Tarski 语义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- 公式码分类记录；`isSigma = true` 表示 Sigma，`false` 表示 Pi。 -/
structure TextbookLevyJudgment where
  isSigma : Bool
  level : Nat
  arity : Nat
  code : Nat
  deriving DecidableEq

namespace TextbookLevyJudgment

/-- 记录表示的原始归纳分类命题。 -/
def Certified (entry : TextbookLevyJudgment) : Prop :=
  if entry.isSigma then TextbookIsSigmaCode entry.level entry.arity entry.code
  else TextbookIsPiCode entry.level entry.arity entry.code

/-- 否定同时改变极性和自然数公式码。 -/
def negate (entry : TextbookLevyJudgment) : TextbookLevyJudgment :=
  { entry with isSigma := !entry.isSigma, code := textbookECode entry.code 0 2 }

/-- 同极性合取保留左记录的层级与元数。 -/
def conjoin (left right : TextbookLevyJudgment) : TextbookLevyJudgment :=
  { left with code := textbookECode left.code right.code 3 }

/-- 一个 Sigma 存在量词关闭末尾变量。 -/
def quantify (entry : TextbookLevyJudgment) : TextbookLevyJudgment :=
  { entry with arity := entry.arity - 1, code := textbookECode entry.code 0 4 }

/-- 提高一层后，两个极性都接受原层的证书。 -/
def raise (isSigma : Bool) (entry : TextbookLevyJudgment) :
    TextbookLevyJudgment :=
  { entry with isSigma := isSigma, level := entry.level + 1 }

/-- 否定操作的分类正确性。 -/
theorem negate_certified_l {entry : TextbookLevyJudgment}
    (hEntry : entry.Certified) : entry.negate.Certified := by
  rcases entry with ⟨polarity, level, arity, code⟩
  cases polarity
  · exact TextbookIsSigmaCode.neg hEntry
  · exact TextbookIsPiCode.neg hEntry

/-- 合取操作在同层、同元数、同极性的记录上保持正确性。 -/
theorem conjoin_certified_l {left right : TextbookLevyJudgment}
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
  · exact TextbookIsPiCode.conj hLeft hRight
  · exact TextbookIsSigmaCode.conj hLeft hRight

/-- 存在量词只消费正元数的 Sigma 记录。 -/
theorem quantify_certified_l {entry : TextbookLevyJudgment}
    (hPolarity : entry.isSigma = true) (hArity : 0 < entry.arity)
    (hEntry : entry.Certified) : entry.quantify.Certified := by
  rcases entry with ⟨polarity, level, arity, code⟩
  cases hPolarity
  cases arity with
  | zero => exact (Nat.lt_irrefl 0 hArity).elim
  | succ arity => exact TextbookIsSigmaCode.ex hEntry

/-- 累积层级的两种提升规则统一保持分类正确性。 -/
theorem raise_certified_l (isSigma : Bool) {entry : TextbookLevyJudgment}
    (hEntry : entry.Certified) : (entry.raise isSigma).Certified := by
  rcases entry with ⟨polarity, level, arity, code⟩
  cases polarity <;> cases isSigma
  · exact TextbookIsPiCode.lift hEntry
  · exact TextbookIsSigmaCode.ofPi hEntry
  · exact TextbookIsPiCode.ofSigma hEntry
  · exact TextbookIsSigmaCode.lift hEntry

end TextbookLevyJudgment

/--
一行证书的有限局部规则。除原子变量索引外，所有存在量化都限定在先前记录中，
没有递归调用原始的 `TextbookIsSigmaCode` 或 `TextbookIsPiCode`。
-/
def textbookLevyRuleOver_l (available : TextbookLevyJudgment → Prop)
    (entry : TextbookLevyJudgment) : Prop :=
  (∃ left right : Fin entry.arity,
    entry.code = textbookECode left.1 right.1 0 ∨
      entry.code = textbookECode left.1 right.1 1) ∨
  (∃ child, available child ∧ entry = child.negate) ∨
  (∃ left, available left ∧ ∃ right, available right ∧
    left.isSigma = right.isSigma ∧ left.level = right.level ∧
      left.arity = right.arity ∧ entry = left.conjoin right) ∨
  (∃ child, available child ∧ child.isSigma = true ∧ 0 < child.arity ∧
    entry = child.quantify) ∨
  (∃ child, available child ∧ entry = child.raise entry.isSigma)

/-- 列表实现将可引用的记录限定为已经出现的行。 -/
def textbookLevyLocalRule_l (previous : List TextbookLevyJudgment)
    (entry : TextbookLevyJudgment) : Prop :=
  textbookLevyRuleOver_l (· ∈ previous) entry

/-- 有限局部规则可以直接判定。 -/
instance textbookLevyLocalRule_decidable_l
    (previous : List TextbookLevyJudgment) (entry : TextbookLevyJudgment) :
    Decidable (textbookLevyLocalRule_l previous entry) := by
  unfold textbookLevyLocalRule_l textbookLevyRuleOver_l
  infer_instance

/-- 扩充先前记录不会破坏合法的单行推导。 -/
theorem textbookLevyLocalRule_mono_l
    {previous extended : List TextbookLevyJudgment}
    {entry : TextbookLevyJudgment}
    (hSubset : previous ⊆ extended)
    (hRule : textbookLevyLocalRule_l previous entry) :
    textbookLevyLocalRule_l extended entry := by
  rcases hRule with hAtom | hNeg | hConj | hEx | hRaise
  · exact Or.inl hAtom
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
theorem textbookLevyRuleOver_sound_l
    {available : TextbookLevyJudgment → Prop} {entry : TextbookLevyJudgment}
    (hPrevious : ∀ child, available child → child.Certified)
    (hRule : textbookLevyRuleOver_l available entry) : entry.Certified := by
  rcases hRule with hAtom | hNeg | hConj | hEx | hRaise
  · rcases entry with ⟨polarity, level, arity, code⟩
    rcases hAtom with ⟨left, right, hCode | hCode⟩
    · change Fin arity at left right
      change code = textbookECode left.1 right.1 0 at hCode
      subst code
      cases polarity
      · exact TextbookIsPiCode.mem left right
      · exact TextbookIsSigmaCode.mem left right
    · change Fin arity at left right
      change code = textbookECode left.1 right.1 1 at hCode
      subst code
      cases polarity
      · exact TextbookIsPiCode.eq left right
      · exact TextbookIsSigmaCode.eq left right
  · rcases hNeg with ⟨child, hChild, rfl⟩
    exact TextbookLevyJudgment.negate_certified_l (hPrevious child hChild)
  · rcases hConj with ⟨left, hLeft, right, hRight, hPolarity, hLevel, hArity, rfl⟩
    exact TextbookLevyJudgment.conjoin_certified_l hPolarity hLevel hArity
      (hPrevious left hLeft) (hPrevious right hRight)
  · rcases hEx with ⟨child, hChild, hPolarity, hArity, rfl⟩
    exact TextbookLevyJudgment.quantify_certified_l hPolarity hArity
      (hPrevious child hChild)
  · rcases hRaise with ⟨child, hChild, hEntry⟩
    rw [hEntry]
    exact TextbookLevyJudgment.raise_certified_l _ (hPrevious child hChild)

/-- 列表前序是通用单步正确性定理的一个实例。 -/
theorem textbookLevyLocalRule_sound_l
    {previous : List TextbookLevyJudgment} {entry : TextbookLevyJudgment}
    (hPrevious : ∀ child ∈ previous, child.Certified)
    (hRule : textbookLevyLocalRule_l previous entry) : entry.Certified :=
  textbookLevyRuleOver_sound_l hPrevious hRule

/-- 逐行检查的有限证书：每个后继只引用严格先前的记录。 -/
inductive TextbookLevyTraceValid : List TextbookLevyJudgment → Prop where
  | nil : TextbookLevyTraceValid []
  | snoc {previous : List TextbookLevyJudgment} {entry : TextbookLevyJudgment} :
      TextbookLevyTraceValid previous → textbookLevyLocalRule_l previous entry →
        TextbookLevyTraceValid (previous ++ [entry])

/-- 合法有限证书中的每行都满足原始归纳分类定义。 -/
theorem TextbookLevyTraceValid.certified_l
    {trace : List TextbookLevyJudgment} (hTrace : TextbookLevyTraceValid trace) :
    ∀ entry ∈ trace, entry.Certified := by
  induction hTrace with
  | nil => simp
  | @snoc previous entry hPrevious hRule ih =>
      intro current hCurrent
      rcases List.mem_append.mp hCurrent with hOld | hLast
      · exact ih current hOld
      · have hEqual : current = entry := List.mem_singleton.mp hLast
        subst current
        exact textbookLevyLocalRule_sound_l ih hRule

/-- 两份合法记录可顺序拼接；右侧每行仍只引用它原来的先前记录。 -/
theorem TextbookLevyTraceValid.append_l
    {left right : List TextbookLevyJudgment}
    (hLeft : TextbookLevyTraceValid left) (hRight : TextbookLevyTraceValid right) :
    TextbookLevyTraceValid (left ++ right) := by
  induction hRight with
  | nil => simpa using hLeft
  | @snoc previous entry hPrevious hRule ih =>
      have hExtended := textbookLevyLocalRule_mono_l
        (extended := left ++ previous)
        (fun _ hMember => List.mem_append_right left hMember) hRule
      simpa only [List.append_assoc] using TextbookLevyTraceValid.snoc ih hExtended

namespace TextbookLevyJudgment

/-- 一条分类记录由某份有限合法记录支持。 -/
def HasTrace (entry : TextbookLevyJudgment) : Prop :=
  ∃ trace, TextbookLevyTraceValid trace ∧ entry ∈ trace

/-- 将一行局部合法的记录加入已验证的有限记录。 -/
theorem hasTrace_of_localRule_l {trace : List TextbookLevyJudgment}
    {entry : TextbookLevyJudgment} (hTrace : TextbookLevyTraceValid trace)
    (hRule : textbookLevyLocalRule_l trace entry) : entry.HasTrace :=
  ⟨trace ++ [entry], TextbookLevyTraceValid.snoc hTrace hRule, by simp⟩

/-- 两类原子均具有单行证书。 -/
theorem atom_hasTrace_l (isSigma : Bool) (level arity : Nat)
    (left right : Fin arity) (code : Nat)
    (hCode : code = textbookECode left.1 right.1 0 ∨
      code = textbookECode left.1 right.1 1) :
    HasTrace ⟨isSigma, level, arity, code⟩ :=
  hasTrace_of_localRule_l .nil (Or.inl ⟨left, right, hCode⟩)

/-- 否定的有限记录由原记录追加一行得到。 -/
theorem HasTrace.negate_l {entry : TextbookLevyJudgment}
    (hEntry : entry.HasTrace) : entry.negate.HasTrace := by
  rcases hEntry with ⟨trace, hTrace, hMember⟩
  exact hasTrace_of_localRule_l hTrace (Or.inr (Or.inl ⟨entry, hMember, rfl⟩))

/-- 两个同类合取分支先拼接各自证书，再加入合取行。 -/
theorem HasTrace.conjoin_l {left right : TextbookLevyJudgment}
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
theorem HasTrace.quantify_l {entry : TextbookLevyJudgment}
    (hEntry : entry.HasTrace) (hPolarity : entry.isSigma = true)
    (hArity : 0 < entry.arity) : entry.quantify.HasTrace := by
  rcases hEntry with ⟨trace, hTrace, hMember⟩
  exact hasTrace_of_localRule_l hTrace (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨entry, hMember, hPolarity, hArity, rfl⟩))))

/-- 累积提升的有限记录可选择目标极性。 -/
theorem HasTrace.raise_l {entry : TextbookLevyJudgment}
    (hEntry : entry.HasTrace) (isSigma : Bool) : (entry.raise isSigma).HasTrace := by
  rcases hEntry with ⟨trace, hTrace, hMember⟩
  exact hasTrace_of_localRule_l hTrace (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨entry, hMember, rfl⟩))))

end TextbookLevyJudgment

/-- 每个原始 Sigma 码证书都能展开成有限逐行证书。 -/
theorem TextbookIsSigmaCode.hasTrace_l
    {level arity code : Nat} (hCode : TextbookIsSigmaCode level arity code) :
    TextbookLevyJudgment.HasTrace ⟨true, level, arity, code⟩ := by
  exact TextbookIsSigmaCode.rec
    (motive_1 := fun level arity code _ =>
      TextbookLevyJudgment.HasTrace ⟨true, level, arity, code⟩)
    (motive_2 := fun level arity code _ =>
      TextbookLevyJudgment.HasTrace ⟨false, level, arity, code⟩)
    (fun left right => TextbookLevyJudgment.atom_hasTrace_l
      true _ _ left right _ (Or.inl rfl))
    (fun left right => TextbookLevyJudgment.atom_hasTrace_l
      true _ _ left right _ (Or.inr rfl))
    (fun _ hBody => hBody.negate_l)
    (fun _ _ hLeft hRight => by
      have hConjunction := hLeft.conjoin_l hRight rfl rfl rfl
      exact hConjunction)
    (fun _ hBody => hBody.quantify_l rfl (Nat.zero_lt_succ _))
    (fun _ hBody => hBody.raise_l true)
    (fun _ hBody => hBody.raise_l true)
    (fun left right => TextbookLevyJudgment.atom_hasTrace_l
      false _ _ left right _ (Or.inl rfl))
    (fun left right => TextbookLevyJudgment.atom_hasTrace_l
      false _ _ left right _ (Or.inr rfl))
    (fun _ hBody => hBody.negate_l)
    (fun _ _ hLeft hRight => by
      have hConjunction := hLeft.conjoin_l hRight rfl rfl rfl
      exact hConjunction)
    (fun _ hBody => hBody.raise_l false)
    (fun _ hBody => hBody.raise_l false)
    hCode

/-- 每个原始 Pi 码证书都能展开成有限逐行证书。 -/
theorem TextbookIsPiCode.hasTrace_l
    {level arity code : Nat} (hCode : TextbookIsPiCode level arity code) :
    TextbookLevyJudgment.HasTrace ⟨false, level, arity, code⟩ := by
  exact TextbookIsPiCode.rec
    (motive_1 := fun level arity code _ =>
      TextbookLevyJudgment.HasTrace ⟨true, level, arity, code⟩)
    (motive_2 := fun level arity code _ =>
      TextbookLevyJudgment.HasTrace ⟨false, level, arity, code⟩)
    (fun left right => TextbookLevyJudgment.atom_hasTrace_l
      true _ _ left right _ (Or.inl rfl))
    (fun left right => TextbookLevyJudgment.atom_hasTrace_l
      true _ _ left right _ (Or.inr rfl))
    (fun _ hBody => hBody.negate_l)
    (fun _ _ hLeft hRight => by
      have hConjunction := hLeft.conjoin_l hRight rfl rfl rfl
      exact hConjunction)
    (fun _ hBody => hBody.quantify_l rfl (Nat.zero_lt_succ _))
    (fun _ hBody => hBody.raise_l true)
    (fun _ hBody => hBody.raise_l true)
    (fun left right => TextbookLevyJudgment.atom_hasTrace_l
      false _ _ left right _ (Or.inl rfl))
    (fun left right => TextbookLevyJudgment.atom_hasTrace_l
      false _ _ left right _ (Or.inr rfl))
    (fun _ hBody => hBody.negate_l)
    (fun _ _ hLeft hRight => by
      have hConjunction := hLeft.conjoin_l hRight rfl rfl rfl
      exact hConjunction)
    (fun _ hBody => hBody.raise_l false)
    (fun _ hBody => hBody.raise_l false)
    hCode

/-- 有限记录刻画原始分类定义，两个方向均没有附加语义假设。 -/
theorem textbookLevyJudgment_hasTrace_iff_certified_l
    (entry : TextbookLevyJudgment) : entry.HasTrace ↔ entry.Certified := by
  constructor
  · rintro ⟨trace, hTrace, hMember⟩
    exact hTrace.certified_l entry hMember
  · intro hEntry
    rcases entry with ⟨polarity, level, arity, code⟩
    cases polarity
    · exact TextbookIsPiCode.hasTrace_l hEntry
    · exact TextbookIsSigmaCode.hasTrace_l hEntry

/-- 从给定前序记录开始，按顺序检查剩余行。 -/
def checkTextbookLevyTraceFrom_l (previous : List TextbookLevyJudgment) :
    List TextbookLevyJudgment → Bool
  | [] => true
  | entry :: remaining =>
      decide (textbookLevyLocalRule_l previous entry) &&
        checkTextbookLevyTraceFrom_l (previous ++ [entry]) remaining

/-- 检查空前序下的完整有限证书。 -/
def checkTextbookLevyTrace_l (trace : List TextbookLevyJudgment) : Bool :=
  checkTextbookLevyTraceFrom_l [] trace

/-- 两段顺序检查与拼接后的单次检查一致。 -/
theorem checkTextbookLevyTraceFrom_append_l
    (previous first second : List TextbookLevyJudgment) :
    checkTextbookLevyTraceFrom_l previous (first ++ second) =
      (checkTextbookLevyTraceFrom_l previous first &&
        checkTextbookLevyTraceFrom_l (previous ++ first) second) := by
  induction first generalizing previous with
  | nil => simp [checkTextbookLevyTraceFrom_l]
  | cons entry remaining ih =>
      simp only [List.cons_append, checkTextbookLevyTraceFrom_l, ih,
        Bool.and_assoc, List.append_assoc, List.nil_append]

/-- 检查成功把合法前序记录扩充为合法的完整记录。 -/
theorem checkTextbookLevyTraceFrom_sound_l
    {previous remaining : List TextbookLevyJudgment}
    (hPrevious : TextbookLevyTraceValid previous)
    (hCheck : checkTextbookLevyTraceFrom_l previous remaining = true) :
    TextbookLevyTraceValid (previous ++ remaining) := by
  induction remaining generalizing previous with
  | nil => simpa using hPrevious
  | cons entry remaining ih =>
      have hBoth : textbookLevyLocalRule_l previous entry ∧
          checkTextbookLevyTraceFrom_l (previous ++ [entry]) remaining = true := by
        simpa only [checkTextbookLevyTraceFrom_l, Bool.and_eq_true,
          decide_eq_true_eq] using hCheck
      obtain ⟨hRule, hRest⟩ := hBoth
      have hExtended := TextbookLevyTraceValid.snoc hPrevious hRule
      simpa only [List.append_assoc, List.singleton_append] using ih hExtended hRest

/-- 任意合法有限记录在任意额外前序之后都能检查成功。 -/
theorem TextbookLevyTraceValid.checkFrom_l
    {trace : List TextbookLevyJudgment} (hTrace : TextbookLevyTraceValid trace)
    (previous : List TextbookLevyJudgment) :
    checkTextbookLevyTraceFrom_l previous trace = true := by
  induction hTrace with
  | nil => rfl
  | @snoc prior entry hPrior hRule ih =>
      rw [checkTextbookLevyTraceFrom_append_l, ih]
      have hExtended : textbookLevyLocalRule_l (previous ++ prior) entry :=
        textbookLevyLocalRule_mono_l
          (fun _ hMember => List.mem_append_right previous hMember) hRule
      simp only [checkTextbookLevyTraceFrom_l, hExtended, decide_true,
        Bool.and_self]

/-- 可计算检查器与逐行合法性完全等价。 -/
theorem checkTextbookLevyTrace_iff_valid_l (trace : List TextbookLevyJudgment) :
    checkTextbookLevyTrace_l trace = true ↔ TextbookLevyTraceValid trace := by
  constructor
  · intro hCheck
    exact checkTextbookLevyTraceFrom_sound_l .nil hCheck
  · intro hTrace
    exact hTrace.checkFrom_l []

/-- 原始码分类恰好意味着存在一份检查成功并包含该记录的有限证书。 -/
theorem textbookLevyJudgment_certified_iff_checkedTrace_l
    (entry : TextbookLevyJudgment) :
    entry.Certified ↔ ∃ trace, checkTextbookLevyTrace_l trace = true ∧ entry ∈ trace := by
  rw [← textbookLevyJudgment_hasTrace_iff_certified_l]
  simp only [TextbookLevyJudgment.HasTrace, checkTextbookLevyTrace_iff_valid_l]

/-- Sigma 公式码的可计算有限证书刻画。 -/
theorem textbookIsSigmaCode_iff_checkedTrace_l (level arity code : Nat) :
    TextbookIsSigmaCode level arity code ↔
      ∃ trace, checkTextbookLevyTrace_l trace = true ∧
        (⟨true, level, arity, code⟩ : TextbookLevyJudgment) ∈ trace :=
  textbookLevyJudgment_certified_iff_checkedTrace_l ⟨true, level, arity, code⟩

/-- Pi 公式码的可计算有限证书刻画。 -/
theorem textbookIsPiCode_iff_checkedTrace_l (level arity code : Nat) :
    TextbookIsPiCode level arity code ↔
      ∃ trace, checkTextbookLevyTrace_l trace = true ∧
        (⟨false, level, arity, code⟩ : TextbookLevyJudgment) ∈ trace :=
  textbookLevyJudgment_certified_iff_checkedTrace_l ⟨false, level, arity, code⟩

end YesMetaZFC.BMS.ConstructibleBridge
