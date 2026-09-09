import BMSConstructibleBridge.ExternalLevyHierarchy
import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookPositiveFormulaEnumeration
import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookECodeDecode
import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookECodeFormula

/-!
# 以 textbook E 码编译成员公式

Wang 的五个 `E` 子句恰好对应成员原子、等式原子、否定、合取和存在量词。
因此可直接把公式树编译为 `2^i * 3^j * 5^tag`，无需在独立公式码与
`E` 关系码之间加入一个无法在对象语言中核验的选择函数。
-/

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Constructible

/-- 按 textbook `E` 的五个构造标签递归编译外部成员公式。 -/
def textbookFormulaCode_l :
    {arity : Nat} -> FOFormula arity -> Nat
  | _, .mem left right => textbookECode left.1 right.1 0
  | _, .eq left right => textbookECode left.1 right.1 1
  | _, .neg body => textbookECode (textbookFormulaCode_l body) 0 2
  | _, .conj left right =>
      textbookECode (textbookFormulaCode_l left)
        (textbookFormulaCode_l right) 3
  | _, .ex body => textbookECode (textbookFormulaCode_l body) 0 4

/-- 三字段 textbook 码相等当且仅当三个指数分别相等。 -/
@[simp]
theorem textbookECode_eq_iff_l (i j tag i' j' tag' : Nat) :
    textbookECode i j tag = textbookECode i' j' tag' ↔
      i = i' ∧ j = j' ∧ tag = tag' := by
  constructor
  · exact textbookECode_injective_fields
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- 规范 textbook 公式码在固定元数上是单射。 -/
theorem textbookFormulaCode_injective_l {arity : Nat} :
    Function.Injective (@textbookFormulaCode_l arity) := by
  intro formula
  induction formula with
  | mem left right =>
      intro other hCode
      cases other with
      | mem otherLeft otherRight =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          congr
          · exact Fin.ext hCode.1
          · exact Fin.ext hCode.2.1
      | eq otherLeft otherRight =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | neg body =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | conj first second =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | ex body =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
  | eq left right =>
      intro other hCode
      cases other with
      | mem otherLeft otherRight =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | eq otherLeft otherRight =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          congr
          · exact Fin.ext hCode.1
          · exact Fin.ext hCode.2.1
      | neg body =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | conj first second =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | ex body =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
  | neg body ih =>
      intro other hCode
      cases other with
      | mem otherLeft otherRight =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | eq otherLeft otherRight =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | neg otherBody =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          exact congrArg FOFormula.neg (ih hCode.1)
      | conj first second =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | ex otherBody =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
  | conj left right ihLeft ihRight =>
      intro other hCode
      cases other with
      | mem otherLeft otherRight =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | eq otherLeft otherRight =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | neg body =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | conj otherLeft otherRight =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          exact congrArg₂ FOFormula.conj (ihLeft hCode.1)
            (ihRight hCode.2.1)
      | ex body =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
  | ex body ih =>
      intro other hCode
      cases other with
      | mem otherLeft otherRight =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | eq otherLeft otherRight =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | neg otherBody =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | conj first second =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          omega
      | ex otherBody =>
          simp only [textbookFormulaCode_l, textbookECode_eq_iff_l] at hCode
          exact congrArg FOFormula.ex (ih hCode.1)

/-- 规范编译码在 `E` 中给出的关系正是公式递归关系。 -/
theorem textbookEZF_textbookFormulaCode_l
    (a : ZFSet) {arity : Nat} (formula : FOFormula arity) :
    textbookEZF a (FiniteSequenceZF.natCode arity)
        (FiniteSequenceZF.natCode (textbookFormulaCode_l formula)) =
      textbookFormulaRelationZF a formula := by
  induction formula with
  | mem left right =>
      simpa [textbookFormulaCode_l, textbookFormulaRelationZF] using
        textbookEZF_code_zero a arity left.1 right.1 left.2 right.2
  | eq left right =>
      simpa [textbookFormulaCode_l, textbookFormulaRelationZF] using
        textbookEZF_code_one a arity left.1 right.1 left.2 right.2
  | neg body ih =>
      simpa [textbookFormulaCode_l, textbookFormulaRelationZF,
        textbookTupleSpace, ih] using
        textbookEZF_code_two a arity (textbookFormulaCode_l body) 0
  | conj left right ihLeft ihRight =>
      simpa [textbookFormulaCode_l, textbookFormulaRelationZF,
        ihLeft, ihRight] using
        textbookEZF_code_three a arity
          (textbookFormulaCode_l left) (textbookFormulaCode_l right)
  | @ex arity body ih =>
      simpa [textbookFormulaCode_l, textbookFormulaRelationZF, ih] using
        textbookEZF_code_four a arity (textbookFormulaCode_l body) 0

/-- 正元数下，规范 E 码精确认可满足给定公式的表示元组。 -/
theorem textbookTupleGraph_mem_compiledRelation_iff_l
    (a : ZFSet) {arity : Nat} (formula : FOFormula (arity + 1))
    (assignment : Tuple (ZFCarrier a) (arity + 1)) :
    textbookTupleGraph assignment ∈
        textbookEZF a (FiniteSequenceZF.natCode (arity + 1))
          (FiniteSequenceZF.natCode (textbookFormulaCode_l formula)) <->
      FOFormula.Satisfies (zfCarrierMem a) formula assignment := by
  rw [textbookEZF_textbookFormulaCode_l]
  exact textbookTupleGraph_mem_textbookPositiveFormulaRelation_iff
    a formula assignment

/-- 否定、合取与存在量词的递归子码严格小于父码。 -/
theorem textbookFormulaCode_child_lt_l
    {arity : Nat} {body : FOFormula arity} :
    textbookFormulaCode_l body <
      textbookFormulaCode_l (.neg body) := by
  simpa [textbookFormulaCode_l] using
    textbookECode_index_lt (textbookFormulaCode_l body) 0 2

end ConstructibleBridge
end BMS
end YesMetaZFC
