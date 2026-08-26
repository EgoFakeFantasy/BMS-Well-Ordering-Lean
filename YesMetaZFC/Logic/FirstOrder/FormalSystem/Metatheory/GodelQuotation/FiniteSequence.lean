import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation
/-!
# Gödel quotation 的标准公式序列
标准有限函数图的通用语法实现已前移到 `StandardSequence`；本模块只保留公式列表
的逐项 quotation 及其对象序列接口。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
/-- 从公式列表逐项计算规范 Gödel quotation。 -/
def quote_list? : List (Formula ℒ) → Option (List SetTerm)
  | [] => some []
  | formula :: rest => do
      let code ← quote? formula
      let codes ← quote_list? rest
      pure (code :: codes)
/-- 公式列表的标准对象有限序列 quotation。 -/
def quote_sequence? (formulas : List (Formula ℒ)) : Option SetTerm := (quote_list? formulas).map standard_sequence
/-- admissible 公式列表的逐项 quotation 总能计算成功。 -/
theorem quote_list?_exists {formulas : List (Formula ℒ)} (hFormulas : ∀ formula, formula ∈ formulas →
      Formula.Admissible formula) :
    ∃ codes, quote_list? formulas = some codes := by
  induction formulas with
  | nil =>
      exact ⟨([] : List SetTerm), rfl⟩
  | cons head tail ih =>
      rcases quote?_exists (hFormulas head (by simp)) with
        ⟨headCode, hHeadCode⟩
      rcases ih (fun formula hFormula =>
          hFormulas formula (by simp [hFormula])) with
        ⟨tailCodes, hTailCodes⟩
      exact ⟨headCode :: tailCodes,
        by simp [quote_list?, hHeadCode, hTailCodes]⟩
/-- 成功逐项引用后，每个结果编码项都 admissible。 -/
theorem quote_list?_codes_admissible
    {formulas : List (Formula ℒ)} {codes : List SetTerm} (hQuote : quote_list? formulas = some codes) :
    ∀ code, code ∈ codes → Term.Admissible code SetSort.set := by
  induction formulas generalizing codes with
  | nil =>
      simp [quote_list?] at hQuote
      subst codes
      simp
  | cons head tail ih =>
      cases hHead : quote? head with
      | none =>
          simp [quote_list?, hHead] at hQuote
      | some headCode =>
          cases hTail : quote_list? tail with
          | none =>
              simp [quote_list?, hHead, hTail] at hQuote
          | some tailCodes =>
              simp [quote_list?, hHead, hTail] at hQuote
              subst codes
              intro code hCode
              rcases List.mem_cons.mp hCode with rfl | hTailCode
              · exact quote?_admissible hHead
              · exact ih hTail code hTailCode
/-- 成功逐项 quotation 保持列表长度。 -/
theorem quote_list?_length
    {formulas : List (Formula ℒ)} {codes : List SetTerm} (hQuote : quote_list? formulas = some codes) :
    codes.length = formulas.length := by
  induction formulas generalizing codes with
  | nil =>
      simp [quote_list?] at hQuote
      subst codes
      rfl
  | cons head tail ih =>
      cases hHead : quote? head with
      | none =>
          simp [quote_list?, hHead] at hQuote
      | some headCode =>
          cases hTail : quote_list? tail with
          | none =>
              simp [quote_list?, hHead, hTail] at hQuote
          | some tailCodes =>
              simp [quote_list?, hHead, hTail] at hQuote
              subst codes
              simp [ih hTail]
/-- 成功逐项 quotation 在每个标准指标上保持公式与编码的对应。 -/
theorem quote_list?_getElem?
    {formulas : List (Formula ℒ)} {codes : List SetTerm} (hQuote : quote_list? formulas = some codes)
    {index : Nat} {formula : Formula ℒ} (hFormula : formulas[index]? = some formula) :
    ∃ code, codes[index]? = some code ∧ quote? formula = some code := by
  induction formulas generalizing codes index formula with
  | nil =>
      simp at hFormula
  | cons head tail ih =>
      cases hHead : quote? head with
      | none =>
          simp [quote_list?, hHead] at hQuote
      | some headCode =>
          cases hTail : quote_list? tail with
          | none =>
              simp [quote_list?, hHead, hTail] at hQuote
          | some tailCodes =>
              simp [quote_list?, hHead, hTail] at hQuote
              subst codes
              cases index with
              | zero =>
                  simp at hFormula
                  subst formula
                  exact ⟨headCode, by simp [hHead]⟩
              | succ index =>
                  simp only [List.getElem?_cons_succ] at hFormula ⊢
                  exact ih hTail hFormula
/-- 成功的公式序列 quotation 是 closed、sort 正确的对象项。 -/
theorem quote_sequence?_admissible
    {formulas : List (Formula ℒ)} {sequence : SetTerm} (hQuote : quote_sequence? formulas = some sequence) :
    Term.Admissible sequence SetSort.set := by
  cases hCodes : quote_list? formulas with
  | none =>
      simp [quote_sequence?, hCodes] at hQuote
  | some codes =>
      simp [quote_sequence?, hCodes] at hQuote
      subst sequence
      exact seq_admissible_m 0 (quote_list?_codes_admissible hCodes)
/-- admissible 公式列表的标准对象序列 quotation 总能成功。 -/
theorem quote_sequence?_exists {formulas : List (Formula ℒ)} (hFormulas : ∀ formula, formula ∈ formulas →
      Formula.Admissible formula) :
    ∃ sequence, quote_sequence? formulas = some sequence := by
  rcases quote_list?_exists hFormulas with ⟨codes, hCodes⟩
  exact ⟨standard_sequence codes, by simp [quote_sequence?, hCodes]⟩
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
