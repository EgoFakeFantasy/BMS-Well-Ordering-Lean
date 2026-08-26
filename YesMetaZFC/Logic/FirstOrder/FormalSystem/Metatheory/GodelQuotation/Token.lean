import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation
/-!
# Gödel quotation 的标准自然数符号串
对象编码把公式看作自然数有限序列。本模块给出与对象编码标签完全一致的标准
`List Nat` quotation；它与 `SetTerm` quotation 使用同一具名环境，因此二者的成功性
严格同步。后续替换先在这个标准有限串上计算，再证明其对象实现满足
`code_substitution_spec`，从而避免把对象函数符号误当作 Lean 可约函数。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
open Nonlogical.BasicSetTheory
/-- 一个逻辑符号的标准自然数标签 `2^e`。 -/
abbrev logical_token (symbol : LogicalSymbolKind) : Nat :=
  Numbered.logical_token symbol
/-- 隶属符号的标准自然数标签 `2^7`。 -/
abbrev membership_token : Nat :=
  Numbered.membership_token
/-- 第 `name` 个变量符号的标准自然数标签 `3^(name+1)`。 -/
abbrev variable_token (name : Nat) : Nat :=
  Numbered.variable_token name
/-- 等式原子的标准符号串。 -/
abbrev equality_tokens (left right : List Nat) : List Nat :=
  Numbered.equality_tokens left right
/-- 隶属原子的标准符号串。 -/
abbrev membership_tokens (left right : List Nat) : List Nat :=
  Numbered.membership_tokens left right
/-- 否定公式的标准符号串。 -/
abbrev negation_tokens (body : List Nat) : List Nat :=
  Numbered.negation_tokens body
/-- 蕴含公式的标准符号串。 -/
abbrev implication_tokens (left right : List Nat) : List Nat :=
  Numbered.implication_tokens left right
/-- 全称公式的标准符号串。 -/
abbrev universal_tokens (name : Nat) (body : List Nat) : List Nat :=
  Numbered.universal_tokens name body
/-- 存在量词按 `¬∀¬` 展开的标准符号串。 -/
abbrev existential_tokens (name : Nat) (body : List Nat) : List Nat :=
  Numbered.existential_tokens name body
/-- 合取按 `¬(φ → ¬ψ)` 展开的标准符号串。 -/
abbrev conjunction_tokens (left right : List Nat) : List Nat :=
  Numbered.conjunction_tokens left right
/-- 显式具名环境下的纯集合论项符号串 quotation。 -/
abbrev quote_term_tokens_with? (freeNaming : FreeVarId → Nat) (boundNames : List Nat) :
    Term ℒ → Option (List Nat) :=
  Numbered.quote_term_tokens_with? freeNaming boundNames
/-- 显式具名环境下的 Hilbert 核公式符号串 quotation。 -/
abbrev quote_hilbert_tokens_with? (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (depth : Nat) :
    Formula ℒ → Option (List Nat) :=
  Numbered.quote_hilbert_tokens_with?
    freeNaming binderNaming boundNames depth
/-- 公共公式的规范标准自然数符号串。 -/
def quote_tokens? (formula : Formula ℒ) : Option (List Nat) :=
  Numbered.quote_tokens? formula
private theorem option_bind_some_isSome_eq
    {α β γ δ : Type} (left : Option α) (right : Option β) (leftMap : α → γ) (rightMap : β → δ) (hDefined : left.isSome = right.isSome) :
    (left.bind (fun value => some (leftMap value))).isSome = (right.bind (fun value => some (rightMap value))).isSome := by
  cases left <;> cases right <;> simp_all
private theorem option_bind₂_some_isSome_eq
    {α₁ α₂ β₁ β₂ γ δ : Type} (leftFirst : Option α₁) (leftSecond : Option α₂) (rightFirst : Option β₁) (rightSecond : Option β₂)
    (leftMap : α₁ → α₂ → γ) (rightMap : β₁ → β₂ → δ) (hFirst : leftFirst.isSome = rightFirst.isSome) (hSecond : leftSecond.isSome = rightSecond.isSome) :
    (leftFirst.bind (fun first =>
      leftSecond.bind (fun second => some (leftMap first second)))).isSome = (rightFirst.bind (fun first =>
      rightSecond.bind (fun second => some (rightMap first second)))).isSome := by
  cases leftFirst <;> cases rightFirst <;>
    cases leftSecond <;> cases rightSecond <;> simp_all
/-- 项的标准符号串 quotation 与对象项 quotation 在同一条件下成功。 -/
theorem quote_term_tokens_with?_isSome (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (term : Term ℒ) :
    (quote_term_tokens_with? freeNaming boundNames term).isSome = (quote_term_with? freeNaming boundNames term).isSome := by
  cases term with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          cases hName : boundNames[index]? <;>
            simp [quote_term_tokens_with?, quote_term_with?, hName]
      | fvar sort id =>
          cases sort
          simp [quote_term_tokens_with?, quote_term_with?]
  | app function arguments =>
      exact nomatch function
/-- 公式的标准符号串 quotation 与对象项 quotation 的成功性严格同步。 -/
theorem quote_hilbert_tokens_with?_isSome (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (depth : Nat) (formula : Formula ℒ) :
    (quote_hilbert_tokens_with? freeNaming binderNaming
        boundNames depth formula).isSome = (quote_hilbert_with? freeNaming binderNaming
        boundNames depth formula).isSome := by
  induction formula generalizing boundNames depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      cases relation
      cases arguments with
      | nil => rfl
      | cons left rest =>
          cases rest with
          | nil => rfl
          | cons right tail =>
              cases tail with
              | nil =>
                  exact option_bind₂_some_isSome_eq (quote_term_tokens_with? freeNaming boundNames left) (quote_term_tokens_with? freeNaming boundNames right)
                    (quote_term_with? freeNaming boundNames left) (quote_term_with? freeNaming boundNames right)
                    membership_tokens
                    membership_atomic_formula_code_term (quote_term_tokens_with?_isSome _ _ _) (quote_term_tokens_with?_isSome _ _ _)
              | cons extra tail => rfl
  | equal left right =>
      exact option_bind₂_some_isSome_eq (quote_term_tokens_with? freeNaming boundNames left) (quote_term_tokens_with? freeNaming boundNames right)
        (quote_term_with? freeNaming boundNames left) (quote_term_with? freeNaming boundNames right)
        equality_tokens equality_formula_code_term (quote_term_tokens_with?_isSome _ _ _) (quote_term_tokens_with?_isSome _ _ _)
  | neg body ih =>
      exact option_bind_some_isSome_eq (quote_hilbert_tokens_with? freeNaming binderNaming
          boundNames depth body) (quote_hilbert_with? freeNaming binderNaming
          boundNames depth body)
        negation_tokens negation_formula_code_term (ih boundNames depth)
  | conj left right =>
      rfl
  | disj left right =>
      rfl
  | imp left right ihLeft ihRight =>
      exact option_bind₂_some_isSome_eq (quote_hilbert_tokens_with? freeNaming binderNaming
          boundNames depth left) (quote_hilbert_tokens_with? freeNaming binderNaming
          boundNames depth right) (quote_hilbert_with? freeNaming binderNaming
          boundNames depth left) (quote_hilbert_with? freeNaming binderNaming
          boundNames depth right)
        implication_tokens implication_formula_code_term (ihLeft boundNames depth) (ihRight boundNames depth)
  | iff left right =>
      rfl
  | forallE sort body ih =>
      cases sort
      exact option_bind_some_isSome_eq (quote_hilbert_tokens_with? freeNaming binderNaming (binderNaming depth :: boundNames) (depth + 1) body)
        (quote_hilbert_with? freeNaming binderNaming (binderNaming depth :: boundNames) (depth + 1) body) (universal_tokens (binderNaming depth))
        (universal_formula_code_term (named_variable_code (binderNaming depth))) (ih (binderNaming depth :: boundNames) (depth + 1))
  | existsE sort body =>
      rfl
/-- 规范符号串与规范对象项 quotation 的成功性一致。 -/
theorem quote_tokens?_isSome (formula : Formula ℒ) : (quote_tokens? formula).isSome = (quote? formula).isSome :=
  quote_hilbert_tokens_with?_isSome _ _ _ _ _
/-- 每个 admissible 纯集合论公式都有标准有限自然数符号串。 -/
theorem quote_tokens?_exists {formula : Formula ℒ} (hFormula : Formula.Admissible formula) :
    ∃ tokens, quote_tokens? formula = some tokens := by
  rcases quote?_exists hFormula with ⟨code, hCode⟩
  have hSome : (quote_tokens? formula).isSome = true := by
    rw [quote_tokens?_isSome, hCode]
    rfl
  cases hTokens : quote_tokens? formula with
  | none =>
      simp [hTokens] at hSome
  | some tokens =>
      exact ⟨tokens, rfl⟩
/-- `closeFreeAt` 在标准符号串 quotation 上由具名环境插入精确实现。 -/
theorem quote_term_tokens_with?_closeFreeAt (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (id depth : Nat) (term : Term ℒ)
    (hDepth : depth ≤ boundNames.length) :
    quote_term_tokens_with? freeNaming (boundNames.insertIdx depth (freeNaming id)) (Term.closeFreeAt SetTheory.SetSort.set id depth term) =
      quote_term_tokens_with? freeNaming boundNames term := by
  cases term with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          by_cases hIndex : depth ≤ index
          · have hStrict : depth < index + 1 := by omega
            simp [Term.closeFreeAt, quote_term_tokens_with?, hIndex,
              List.getElem?_insertIdx_of_gt hStrict]
          · have hStrict : index < depth := by omega
            simp [Term.closeFreeAt, quote_term_tokens_with?, hIndex,
              List.getElem?_insertIdx_of_lt hStrict]
      | fvar sort freeId =>
          cases sort
          by_cases hId : freeId = id
          · subst freeId
            simp [Term.closeFreeAt, quote_term_tokens_with?, hDepth,
              List.getElem?_insertIdx_self]
          · simp [Term.closeFreeAt, quote_term_tokens_with?, hId]
  | app function arguments =>
      exact nomatch function
/-- 公式符号串 quotation 同样把 `closeFreeAt` 精确解释为具名环境插入。 -/
theorem quote_hilbert_tokens_with?_closeFreeAt (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (quoteDepth id closeDepth : Nat)
    (formula : Formula ℒ) (hDepth : closeDepth ≤ boundNames.length) :
    quote_hilbert_tokens_with? freeNaming binderNaming (boundNames.insertIdx closeDepth (freeNaming id)) quoteDepth
        (Formula.closeFreeAt SetTheory.SetSort.set id closeDepth formula) =
      quote_hilbert_tokens_with? freeNaming binderNaming
        boundNames quoteDepth formula := by
  induction formula generalizing boundNames quoteDepth closeDepth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      cases relation
      cases arguments with
      | nil => rfl
      | cons left rest =>
          cases rest with
          | nil => rfl
          | cons right tail =>
              cases tail with
              | nil =>
                  simp [Formula.closeFreeAt,
                    quote_hilbert_tokens_with?,
                    quote_term_tokens_with?_closeFreeAt _ _ id closeDepth _ hDepth]
              | cons extra tail => rfl
  | equal left right =>
      simp [Formula.closeFreeAt, quote_hilbert_tokens_with?,
        quote_term_tokens_with?_closeFreeAt _ _ id closeDepth _ hDepth]
  | neg body ih =>
      have hBody := ih boundNames quoteDepth closeDepth hDepth
      simpa [Formula.closeFreeAt, quote_hilbert_tokens_with?] using
        congrArg (fun result => result.bind (fun bodyCode =>
            some (negation_tokens bodyCode)))
          hBody
  | conj left right =>
      rfl
  | disj left right =>
      rfl
  | imp left right ihLeft ihRight =>
      have hLeft := ihLeft boundNames quoteDepth closeDepth hDepth
      have hRight := ihRight boundNames quoteDepth closeDepth hDepth
      have hCombined : (quote_hilbert_tokens_with? freeNaming binderNaming (boundNames.insertIdx closeDepth (freeNaming id)) quoteDepth
              (Formula.closeFreeAt SetTheory.SetSort.set id closeDepth left)).bind (fun leftCode =>
                (quote_hilbert_tokens_with? freeNaming binderNaming (boundNames.insertIdx closeDepth (freeNaming id)) quoteDepth
                    (Formula.closeFreeAt SetTheory.SetSort.set id closeDepth right)).bind (fun rightCode =>
                    some (implication_tokens leftCode rightCode))) = (quote_hilbert_tokens_with? freeNaming binderNaming
                boundNames quoteDepth left).bind (fun leftCode =>
                (quote_hilbert_tokens_with? freeNaming binderNaming
                    boundNames quoteDepth right).bind (fun rightCode =>
                    some (implication_tokens leftCode rightCode))) := by
        rw [hLeft, hRight]
      simpa [Formula.closeFreeAt, quote_hilbert_tokens_with?] using hCombined
  | iff left right =>
      rfl
  | forallE sort body ih =>
      cases sort
      let name := binderNaming quoteDepth
      have hDepth' : closeDepth + 1 ≤ (name :: boundNames).length := by
        simp
        omega
      have hBody := ih (name :: boundNames) (quoteDepth + 1) (closeDepth + 1) hDepth'
      simp only [List.insertIdx_succ_cons] at hBody
      simpa [Formula.closeFreeAt, Formula.next_depth,
        quote_hilbert_tokens_with?, name] using
        congrArg (fun result => result.bind (fun bodyCode =>
            some (universal_tokens name bodyCode)))
          hBody
  | existsE sort body =>
      rfl
/-- 规范符号串在最外层关闭自由变量时保持原公式体编码。 -/
theorem quote_hilbert_tokens_close_free_zero (id : FreeVarId) (formula : Formula ℒ) :
    quote_hilbert_tokens_with? free_name bound_name [free_name id] 0 (Formula.closeFreeAt SetTheory.SetSort.set id 0 formula) =
      quote_hilbert_tokens_with? free_name bound_name [] 0 formula := by
  simpa [List.insertIdx] using
    quote_hilbert_tokens_with?_closeFreeAt
      free_name bound_name [] 0 id 0 formula (by simp)
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
