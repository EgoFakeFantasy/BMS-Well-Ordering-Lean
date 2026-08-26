import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemCodeReplayInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemAtomicFormulaDecodeRejection

/-!
# FormalSystem 公式码的 checked 解码拒绝

本模块把对象公式码的一步生成反演与宿主 checked decoder 的严格子串下降组合起来。
递归调用始终先把对象子码成员沿等式运输到闭的标准 token 序列，因此父层
存在量词的 eigen 变量会在本层消去。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/--
相对于当前 token 串的严格短串公式码拒绝族。

该接口正是长度强归纳假设；binder 环境可以在全称分支中扩展，自由变量基数保持
不变。
-/
def FSFormulaDecodeRejectionBelow
    (freeBase : Nat) (tokens : List Nat) : Prop :=
  ∀ (boundNames : List Nat) (childTokens : List Nat),
    childTokens.length < tokens.length →
      FSFormulaTokens childTokens →
        FSFormulaBinderTokens childTokens →
          fs_named_hilbert_tokens_decode_with_env
              freeBase boundNames childTokens =
            none →
            ⊢ₘ[godel_quotation_theory]
              ¬ₘ (standard_token_sequence childTokens ∈ₘ
                FormulaCodeₘ)

/--
对象子码等于标准短串时，把子码成员运输到标准闭码，再用闭否定结束当前上下文。
-/
private theorem gq_formula_child_falsum_of_standard_rejection
    {Γ : Context signature}
    (child : SetTerm) (childTokens : List Nat)
    (hChild : Term.Admissible child SetSort.set)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        child ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        child ≐ₘ standard_token_sequence childTokens)
    (hReject :
      ⊢ₘ[godel_quotation_theory]
        ¬ₘ (standard_token_sequence childTokens ∈ₘ
          FormulaCodeₘ)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  have hStandardMember :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence childTokens ∈ₘ
          FormulaCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        child
        (standard_token_sequence childTokens)
        FormulaCodeₘ
        hChild
        (standard_token_sequence_admissible childTokens)
        formula_code_set_term_admissible
        hEquality)
      hMember
  exact FirstOrder.Derives.negElim
    hStandardMember
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      hReject)

/--
否定生成分支中，checked 解码失败严格下降到正文；短正文的闭拒绝随后结束当前
对象上下文。
-/
private theorem gq_formula_negation_decode_branch_falsum
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat)
    (hRejectBelow :
      FSFormulaDecodeRejectionBelow freeBase tokens)
    (hTokens : FSFormulaTokens tokens)
    (hBinders : FSFormulaBinderTokens tokens)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      (∃ₘ[SetSort.set, 306],
        ((x#306 ∈ₘ FormulaCodeₘ) ∧ₘ
          (standard_token_sequence tokens ≐ₘ
            neg_codeₘ(x#306)))) ⟶ₘ
        Formula.falsum := by
  let body : SetTerm := x#306
  let conditionBody : SetFormula :=
    (body ∈ₘ FormulaCodeₘ) ∧ₘ
      (standard_token_sequence tokens ≐ₘ
        neg_codeₘ(body))
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, 306], conditionBody
  have hBody :
      Term.Admissible body SetSort.set := by
    simpa [body] using set_variable_admissible 306
  have hConditionBody :
      Formula.Admissible conditionBody := by
    dsimp only [conditionBody]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        hBody formula_code_set_term_admissible)
      (Formula.Admissible.equal
        (standard_token_sequence_admissible tokens)
        (negation_formula_code_term_admissible
          body hBody))
  have hCondition :
      Formula.Admissible condition := by
    dsimp only [condition]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 306 hConditionBody
  change
    ⊢ₘ[godel_quotation_theory]
      condition ⟶ₘ Formula.falsum
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hCondition)
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 306)
    (body := conditionBody)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hConditionBody)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [condition, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set 306 0 conditionBody
  · exact List.not_mem_nil
  · exact hExists
  · let Δ : Context signature := conditionBody :: Γ
    have hAt :
        Δ ⊢ₘ[godel_quotation_theory]
          conditionBody :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete
          hConditionBody)
    have hMember :
        Δ ⊢ₘ[godel_quotation_theory]
          body ∈ₘ FormulaCodeₘ := by
      simpa [conditionBody] using
        FirstOrder.Derives.conjElimLeft hAt
    have hEquality :
        Δ ⊢ₘ[godel_quotation_theory]
          standard_token_sequence tokens ≐ₘ
            neg_codeₘ(body) := by
      simpa [conditionBody] using
        FirstOrder.Derives.conjElimRight hAt
    rcases
        gq_negation_code_decode_failure_descends_with_signature
          freeBase boundNames body tokens
          hTokens hBinders
          (hBody := by
            simpa [body] using
              Term.check_admissible_complete hBody)
          hMember hEquality hDecode with
      hFalsum | ⟨bodyTokens, hLength,
        hBodyDecode, hBodyTokens, hBodyBinders,
        hBodyEquality⟩
    · exact hFalsum
    · exact
        gq_formula_child_falsum_of_standard_rejection
          body bodyTokens hBody hMember hBodyEquality
          (hRejectBelow boundNames bodyTokens hLength
            hBodyTokens hBodyBinders hBodyDecode)

/--
蕴含生成分支先在父码的有限定义域内消去左右正文长度，再把 parser 失败严格下降
到其中一侧。
-/
private theorem gq_formula_implication_decode_branch_falsum
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat)
    (hRejectBelow :
      FSFormulaDecodeRejectionBelow freeBase tokens)
    (hTokens : FSFormulaTokens tokens)
    (hBinders : FSFormulaBinderTokens tokens)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      (∃ₘ[SetSort.set, 307],
        ∃ₘ[SetSort.set, 308],
          (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
            (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
            (standard_token_sequence tokens ≐ₘ
              imp_codeₘ(x#307, x#308)))) ⟶ₘ
        Formula.falsum := by
  let left : SetTerm := x#307
  let right : SetTerm := x#308
  let conditionBody : SetFormula :=
    ((left ∈ₘ FormulaCodeₘ) ∧ₘ
      (right ∈ₘ FormulaCodeₘ)) ∧ₘ
      (standard_token_sequence tokens ≐ₘ
        imp_codeₘ(left, right))
  let inner : SetFormula :=
    ∃ₘ[SetSort.set, 308], conditionBody
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, 307], inner
  have hLeft :
      Term.Admissible left SetSort.set := by
    simpa [left] using set_variable_admissible 307
  have hRight :
      Term.Admissible right SetSort.set := by
    simpa [right] using set_variable_admissible 308
  have hConditionBody :
      Formula.Admissible conditionBody := by
    dsimp only [conditionBody]
    exact Formula.Admissible.conj
      (Formula.Admissible.conj
        (membership_formula_admissible
          hLeft formula_code_set_term_admissible)
        (membership_formula_admissible
          hRight formula_code_set_term_admissible))
      (Formula.Admissible.equal
        (standard_token_sequence_admissible tokens)
        (implication_formula_code_term_admissible
          left right hLeft hRight))
  have hInner :
      Formula.Admissible inner := by
    dsimp only [inner]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 308 hConditionBody
  have hCondition :
      Formula.Admissible condition := by
    dsimp only [condition]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 307 hInner
  change
    ⊢ₘ[godel_quotation_theory]
      condition ⟶ₘ Formula.falsum
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hCondition)
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 307)
    (body := inner)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hInner)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [condition, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set 307 0 inner
  · exact List.not_mem_nil
  · exact hExists
  · let Δ : Context signature := inner :: Γ
    have hInnerAt :
        Δ ⊢ₘ[godel_quotation_theory] inner :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete hInner)
    apply FirstOrder.Derives.exists_elim
      (T := godel_quotation_theory)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := 308)
      (body := conditionBody)
      (conclusion := Formula.falsum)
      (hBodyCheck :=
        Formula.check_admissible_complete hConditionBody)
    · intro formula hFormula
      rw [(godel_quotation_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · simpa [inner, Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 308 0 conditionBody
      · rcases List.mem_singleton.mp hFormula with rfl
        have hInnerFresh :
            (SetSort.set, 308) ∉
              Formula.freeSupport inner := by
          simpa [inner, Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set 308 0 conditionBody
        simpa [condition] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, 308)
            SetSort.set 307 0 inner hInnerFresh
    · exact List.not_mem_nil
    · exact hInnerAt
    · let Ε : Context signature := conditionBody :: Δ
      have hAt :
          Ε ⊢ₘ[godel_quotation_theory]
            conditionBody :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
          (Formula.check_admissible_complete
            hConditionBody)
      have hMembers :
          Ε ⊢ₘ[godel_quotation_theory]
            (left ∈ₘ FormulaCodeₘ) ∧ₘ
              (right ∈ₘ FormulaCodeₘ) := by
        simpa [conditionBody] using
          FirstOrder.Derives.conjElimLeft hAt
      have hLeftMember :
          Ε ⊢ₘ[godel_quotation_theory]
            left ∈ₘ FormulaCodeₘ :=
        FirstOrder.Derives.conjElimLeft hMembers
      have hRightMember :
          Ε ⊢ₘ[godel_quotation_theory]
            right ∈ₘ FormulaCodeₘ :=
        FirstOrder.Derives.conjElimRight hMembers
      have hEquality :
          Ε ⊢ₘ[godel_quotation_theory]
            standard_token_sequence tokens ≐ₘ
              imp_codeₘ(left, right) := by
        simpa [conditionBody] using
          FirstOrder.Derives.conjElimRight hAt
      have hLeftFinite :
          Ε ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition left :=
        gq_formula_code_member_implies_finite_sequence
          left hLeft hLeftMember
      have hRightFinite :
          Ε ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition right :=
        gq_formula_code_member_implies_finite_sequence
          right hRight hRightMember
      have hLeftDomainMember :
          Ε ⊢ₘ[godel_quotation_theory]
            domₘ(left) ∈ₘ
              domₘ(imp_codeₘ(left, right)) :=
        gq_implication_left_domain_mem_code_domain
          left right hLeftFinite hRightFinite
      apply
        gq_domain_length_elim_of_member_of_standard_equality
          (child := left)
          (parent := imp_codeₘ(left, right))
          tokens Formula.falsum
          hLeftDomainMember hEquality
      intro leftLength hLeftLength
      let leftDomainCondition : SetFormula :=
        domₘ(left) ≐ₘ numₘ(leftLength)
      let Ζ : Context signature :=
        leftDomainCondition :: Ε
      have hWeakenΕΖ :
          ∀ formula, formula ∈ Ε → formula ∈ Ζ := by
        intro formula hFormula
        exact List.mem_cons_of_mem
          leftDomainCondition hFormula
      have hLeftDomain :
          Ζ ⊢ₘ[godel_quotation_theory]
            domₘ(left) ≐ₘ numₘ(leftLength) :=
        FirstOrder.Derives.assumption
          (by simp [Ζ, leftDomainCondition])
      have hLeftMember' :
          Ζ ⊢ₘ[godel_quotation_theory]
            left ∈ₘ FormulaCodeₘ :=
        FirstOrder.Derives.context_weaken
          (Γ := Ε) (Δ := Ζ) hWeakenΕΖ
          hLeftMember
      have hRightMember' :
          Ζ ⊢ₘ[godel_quotation_theory]
            right ∈ₘ FormulaCodeₘ :=
        FirstOrder.Derives.context_weaken
          (Γ := Ε) (Δ := Ζ) hWeakenΕΖ
          hRightMember
      have hLeftFinite' :
          Ζ ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition left :=
        FirstOrder.Derives.context_weaken
          (Γ := Ε) (Δ := Ζ) hWeakenΕΖ
          hLeftFinite
      have hRightFinite' :
          Ζ ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition right :=
        FirstOrder.Derives.context_weaken
          (Γ := Ε) (Δ := Ζ) hWeakenΕΖ
          hRightFinite
      have hEquality' :
          Ζ ⊢ₘ[godel_quotation_theory]
            standard_token_sequence tokens ≐ₘ
              imp_codeₘ(left, right) :=
        FirstOrder.Derives.context_weaken
          (Γ := Ε) (Δ := Ζ) hWeakenΕΖ
          hEquality
      have hRightDomainMember :
          Ζ ⊢ₘ[godel_quotation_theory]
            domₘ(right) ∈ₘ
              domₘ(imp_codeₘ(left, right)) :=
        gq_implication_right_domain_mem_code_domain
          left right leftLength
          hLeftFinite' hRightFinite' hLeftDomain
      apply
        gq_domain_length_elim_of_member_of_standard_equality
          (child := right)
          (parent := imp_codeₘ(left, right))
          tokens Formula.falsum
          hRightDomainMember hEquality'
      intro rightLength hRightLength
      let rightDomainCondition : SetFormula :=
        domₘ(right) ≐ₘ numₘ(rightLength)
      let Η : Context signature :=
        rightDomainCondition :: Ζ
      have hWeakenΖΗ :
          ∀ formula, formula ∈ Ζ → formula ∈ Η := by
        intro formula hFormula
        exact List.mem_cons_of_mem
          rightDomainCondition hFormula
      have hLeftMember'' :
          Η ⊢ₘ[godel_quotation_theory]
            left ∈ₘ FormulaCodeₘ :=
        FirstOrder.Derives.context_weaken
          (Γ := Ζ) (Δ := Η) hWeakenΖΗ
          hLeftMember'
      have hRightMember'' :
          Η ⊢ₘ[godel_quotation_theory]
            right ∈ₘ FormulaCodeₘ :=
        FirstOrder.Derives.context_weaken
          (Γ := Ζ) (Δ := Η) hWeakenΖΗ
          hRightMember'
      have hLeftDomain' :
          Η ⊢ₘ[godel_quotation_theory]
            domₘ(left) ≐ₘ numₘ(leftLength) :=
        FirstOrder.Derives.context_weaken
          (Γ := Ζ) (Δ := Η) hWeakenΖΗ
          hLeftDomain
      have hRightDomain :
          Η ⊢ₘ[godel_quotation_theory]
            domₘ(right) ≐ₘ numₘ(rightLength) :=
        FirstOrder.Derives.assumption
          (by simp [Η, rightDomainCondition])
      have hEquality'' :
          Η ⊢ₘ[godel_quotation_theory]
            standard_token_sequence tokens ≐ₘ
              imp_codeₘ(left, right) :=
        FirstOrder.Derives.context_weaken
          (Γ := Ζ) (Δ := Η) hWeakenΖΗ
          hEquality'
      rcases
          gq_implication_code_decode_failure_descends_of_domains_arbitrary_with_signature
            freeBase boundNames left right tokens
            leftLength rightLength
            hTokens hBinders
            (hLeft := by
              simpa [left] using
                Term.check_admissible_complete hLeft)
            (hRight := by
              simpa [right] using
                Term.check_admissible_complete hRight)
            hLeftMember'' hRightMember''
            hLeftDomain' hRightDomain
            hEquality'' hDecode with
        hFalsum |
          (⟨leftTokens, hLength, hLeftDecode,
              hLeftTokens, hLeftBinders,
              hLeftEquality⟩ |
            ⟨rightTokens, hLength, hRightDecode,
              hRightTokens, hRightBinders,
              hRightEquality⟩)
      · exact hFalsum
      · exact
          gq_formula_child_falsum_of_standard_rejection
            left leftTokens hLeft hLeftMember''
            hLeftEquality
            (hRejectBelow boundNames leftTokens hLength
              hLeftTokens hLeftBinders hLeftDecode)
      · exact
          gq_formula_child_falsum_of_standard_rejection
            right rightTokens hRight hRightMember''
            hRightEquality
            (hRejectBelow boundNames rightTokens hLength
              hRightTokens hRightBinders hRightDecode)

/--
全称生成分支先由有限 binder 检查恢复输入中的具体变量名，再把任意对象 binder
对齐到规范具名变量码。正文长度随后在规范父码的有限定义域中消去。
-/
private theorem gq_formula_universal_decode_branch_falsum
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat)
    (hRejectBelow :
      FSFormulaDecodeRejectionBelow freeBase tokens)
    (hTokens : FSFormulaTokens tokens)
    (hBinders : FSFormulaBinderTokens tokens)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      (∃ₘ[SetSort.set, 309],
        ∃ₘ[SetSort.set, 310],
          (((x#309 ∈ₘ VarSymₘ) ∧ₘ
            (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
            (standard_token_sequence tokens ≐ₘ
              forall_codeₘ(x#309, x#310)))) ⟶ₘ
        Formula.falsum := by
  let boundVariable : SetTerm := x#309
  let body : SetTerm := x#310
  let conditionBody : SetFormula :=
    ((boundVariable ∈ₘ VarSymₘ) ∧ₘ
      (body ∈ₘ FormulaCodeₘ)) ∧ₘ
      (standard_token_sequence tokens ≐ₘ
        forall_codeₘ(boundVariable, body))
  let inner : SetFormula :=
    ∃ₘ[SetSort.set, 310], conditionBody
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, 309], inner
  have hBoundVariable :
      Term.Admissible boundVariable SetSort.set := by
    simpa [boundVariable] using
      set_variable_admissible 309
  have hBody :
      Term.Admissible body SetSort.set := by
    simpa [body] using set_variable_admissible 310
  have hConditionBody :
      Formula.Admissible conditionBody := by
    dsimp only [conditionBody]
    exact Formula.Admissible.conj
      (Formula.Admissible.conj
        (membership_formula_admissible
          hBoundVariable
          variable_symbol_set_term_admissible)
        (membership_formula_admissible
          hBody formula_code_set_term_admissible))
      (Formula.Admissible.equal
        (standard_token_sequence_admissible tokens)
        (universal_formula_code_term_admissible
          boundVariable body
          hBoundVariable hBody))
  have hInner :
      Formula.Admissible inner := by
    dsimp only [inner]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 310 hConditionBody
  have hCondition :
      Formula.Admissible condition := by
    dsimp only [condition]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 309 hInner
  change
    ⊢ₘ[godel_quotation_theory]
      condition ⟶ₘ Formula.falsum
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hCondition)
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 309)
    (body := inner)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hInner)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [condition, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set 309 0 inner
  · exact List.not_mem_nil
  · exact hExists
  · let Δ : Context signature := inner :: Γ
    have hInnerAt :
        Δ ⊢ₘ[godel_quotation_theory] inner :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete hInner)
    apply FirstOrder.Derives.exists_elim
      (T := godel_quotation_theory)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := 310)
      (body := conditionBody)
      (conclusion := Formula.falsum)
      (hBodyCheck :=
        Formula.check_admissible_complete hConditionBody)
    · intro formula hFormula
      rw [(godel_quotation_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · simpa [inner, Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 310 0 conditionBody
      · rcases List.mem_singleton.mp hFormula with rfl
        have hInnerFresh :
            (SetSort.set, 310) ∉
              Formula.freeSupport inner := by
          simpa [inner, Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set 310 0 conditionBody
        simpa [condition] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, 310)
            SetSort.set 309 0 inner hInnerFresh
    · exact List.not_mem_nil
    · exact hInnerAt
    · let Ε : Context signature := conditionBody :: Δ
      have hAt :
          Ε ⊢ₘ[godel_quotation_theory]
            conditionBody :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
          (Formula.check_admissible_complete
            hConditionBody)
      have hMembers :
          Ε ⊢ₘ[godel_quotation_theory]
            (boundVariable ∈ₘ VarSymₘ) ∧ₘ
              (body ∈ₘ FormulaCodeₘ) := by
        simpa [conditionBody] using
          FirstOrder.Derives.conjElimLeft hAt
      have hBoundVariableMember :
          Ε ⊢ₘ[godel_quotation_theory]
            boundVariable ∈ₘ VarSymₘ :=
        FirstOrder.Derives.conjElimLeft hMembers
      have hBodyMember :
          Ε ⊢ₘ[godel_quotation_theory]
            body ∈ₘ FormulaCodeₘ :=
        FirstOrder.Derives.conjElimRight hMembers
      have hEquality :
          Ε ⊢ₘ[godel_quotation_theory]
            standard_token_sequence tokens ≐ₘ
              forall_codeₘ(boundVariable, body) := by
        simpa [conditionBody] using
          FirstOrder.Derives.conjElimRight hAt
      have hBodyCodeString :
          Ε ⊢ₘ[godel_quotation_theory]
            body ∈ₘ CodeStrₘ :=
        FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ε) (by simp) <|
              gq_formula_code_member_implies_code_string
                body hBody)
          hBodyMember
      have hOpening :=
        FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ε) (by simp) <|
              gq_universal_formula_opening_inversion
                boundVariable body)
          (FirstOrder.Derives.conjIntro
            hBoundVariableMember hBodyCodeString)
      have hUniversalPoint :
          Ε ⊢ₘ[godel_quotation_theory]
            ((numₘ(1) ∈ₘ
                domₘ(forall_codeₘ(
                  boundVariable, body))) ∧ₘ
              ((forall_codeₘ(boundVariable, body) ·ₘ
                  numₘ(1)) ≐ₘ
                numₘ(Numbered.logical_token
                  .universal))) :=
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hOpening
      by_cases hUniversal :
          tokens[1]? =
            some (Numbered.logical_token .universal)
      · rcases
            fs_formula_binder_tokens_getElem?
              tokens hBinders 1 hUniversal with
          ⟨token, name, hGet, hVariableDecode⟩
        have hGet' :
            tokens[2]? = some token := by
          simpa using hGet
        let namedVariable : SetTerm :=
          Numbered.named_variable_code name
        have hNamedVariable :
            Term.Admissible namedVariable SetSort.set := by
          simpa [namedVariable] using
            variable_code_term_admissible
              (numₘ(name))
              (finite_numeral_term_admissible name)
        have hBoundVariableEquality :
            Ε ⊢ₘ[godel_quotation_theory]
              boundVariable ≐ₘ namedVariable := by
          simpa [namedVariable] using
            gq_universal_bound_variable_eq_named_of_decode
              boundVariable body tokens token name
              (hBoundVariable := by
                simpa [boundVariable] using
                  Term.check_admissible_complete
                    hBoundVariable)
              (hBody := by
                simpa [body] using
                  Term.check_admissible_complete hBody)
              hGet'
              hVariableDecode
              hBoundVariableMember hBodyMember hEquality
        have hConstructorEquality :
            Ε ⊢ₘ[godel_quotation_theory]
              forall_codeₘ(boundVariable, body) ≐ₘ
                forall_codeₘ(namedVariable, body) :=
          Metatheory.Derives.binary_term_constructor_congr_of_equalities
            (fun binder formula =>
              forall_codeₘ(binder, formula))
            (fun binder formula hBinder hFormula =>
              universal_formula_code_term_admissible
                binder formula hBinder hFormula)
            (by
              intros
              simp [Term.substituteFree])
            boundVariable namedVariable body body
            hBoundVariable hNamedVariable
            hBody hBody
            hBoundVariableEquality
            (FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set) body)
        have hNamedEquality :
            Ε ⊢ₘ[godel_quotation_theory]
              standard_token_sequence tokens ≐ₘ
                forall_codeₘ(namedVariable, body) :=
          Metatheory.Derives.equality_trans
            hEquality hConstructorEquality
        have hBodyFinite :
            Ε ⊢ₘ[godel_quotation_theory]
              finite_sequence_condition body :=
          gq_formula_code_member_implies_finite_sequence
            body hBody hBodyMember
        have hBodyDomainMember :
            Ε ⊢ₘ[godel_quotation_theory]
              domₘ(body) ∈ₘ
                domₘ(forall_codeₘ(
                  namedVariable, body)) := by
          simpa [namedVariable] using
            gq_universal_body_domain_mem_code_domain
              name body hBodyFinite
        apply
          gq_domain_length_elim_of_member_of_standard_equality
            (child := body)
            (parent :=
              forall_codeₘ(namedVariable, body))
            tokens Formula.falsum
            hBodyDomainMember hNamedEquality
        intro bodyLength hBodyLength
        let bodyDomainCondition : SetFormula :=
          domₘ(body) ≐ₘ numₘ(bodyLength)
        let Ζ : Context signature :=
          bodyDomainCondition :: Ε
        have hWeakenΕΖ :
            ∀ formula, formula ∈ Ε → formula ∈ Ζ := by
          intro formula hFormula
          exact List.mem_cons_of_mem
            bodyDomainCondition hFormula
        have hBoundVariableMember' :
            Ζ ⊢ₘ[godel_quotation_theory]
              boundVariable ∈ₘ VarSymₘ :=
          FirstOrder.Derives.context_weaken
            (Γ := Ε) (Δ := Ζ) hWeakenΕΖ
            hBoundVariableMember
        have hBodyMember' :
            Ζ ⊢ₘ[godel_quotation_theory]
              body ∈ₘ FormulaCodeₘ :=
          FirstOrder.Derives.context_weaken
            (Γ := Ε) (Δ := Ζ) hWeakenΕΖ
            hBodyMember
        have hBodyDomain :
            Ζ ⊢ₘ[godel_quotation_theory]
              domₘ(body) ≐ₘ numₘ(bodyLength) :=
          FirstOrder.Derives.assumption
            (by simp [Ζ, bodyDomainCondition])
        have hEquality' :
            Ζ ⊢ₘ[godel_quotation_theory]
              standard_token_sequence tokens ≐ₘ
                forall_codeₘ(boundVariable, body) :=
          FirstOrder.Derives.context_weaken
            (Γ := Ε) (Δ := Ζ) hWeakenΕΖ
            hEquality
        rcases
            gq_universal_code_decode_failure_descends_of_domain_arbitrary_binder_with_signature
              freeBase boundNames
              boundVariable body tokens bodyLength
              token name hTokens hBinders
              (hBoundVariable := by
                simpa [boundVariable] using
                  Term.check_admissible_complete
                    hBoundVariable)
              (hBody := by
                simpa [body] using
                  Term.check_admissible_complete hBody)
              hGet'
              hVariableDecode
              hBoundVariableMember' hBodyMember'
              hBodyDomain hEquality' hDecode with
          hFalsum |
            ⟨bodyTokens, hLength, hBodyDecode,
              hBodyTokens, hBodyBinders,
              hBodyEquality⟩
        · exact hFalsum
        · exact
            gq_formula_child_falsum_of_standard_rejection
              body bodyTokens hBody hBodyMember'
              hBodyEquality
              (hRejectBelow (name :: boundNames)
                bodyTokens hLength hBodyTokens
                hBodyBinders hBodyDecode)
      · exact
          gq_standard_token_sequence_falsum_of_point_not_expected
            tokens
            (forall_codeₘ(boundVariable, body))
            1
            (Numbered.logical_token .universal)
            hUniversal hEquality hUniversalPoint

/--
一步公式生成的四个分支统一排除 checked decoder 失败。

三个复合分支只消费严格短串拒绝族；原子分支保持为独立的精确接口，避免把项码
反演的负担混入公式构造归纳。
-/
private theorem gq_formula_generation_decode_falsum
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat)
    (hRejectBelow :
      FSFormulaDecodeRejectionBelow freeBase tokens)
    (hTokens : FSFormulaTokens tokens)
    (hBinders : FSFormulaBinderTokens tokens)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      formula_code_generation_condition
          FormulaCodeₘ
          (standard_token_sequence tokens) ⟶ₘ
        Formula.falsum := by
  let code : SetTerm :=
    standard_token_sequence tokens
  let atomic : SetFormula :=
    code ∈ₘ AtomicCodeₘ
  let negation : SetFormula :=
    ∃ₘ[SetSort.set, 306],
      ((x#306 ∈ₘ FormulaCodeₘ) ∧ₘ
        (code ≐ₘ neg_codeₘ(x#306)))
  let implication : SetFormula :=
    ∃ₘ[SetSort.set, 307],
      ∃ₘ[SetSort.set, 308],
        (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
          (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
          (code ≐ₘ imp_codeₘ(x#307, x#308)))
  let universal : SetFormula :=
    ∃ₘ[SetSort.set, 309],
      ∃ₘ[SetSort.set, 310],
        (((x#309 ∈ₘ VarSymₘ) ∧ₘ
          (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
          (code ≐ₘ forall_codeₘ(x#309, x#310)))
  let rest : SetFormula :=
    implication ∨ₘ universal
  let tail : SetFormula :=
    negation ∨ₘ rest
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hGenerationAdmissible :
      Formula.Admissible
        (formula_code_generation_condition
          FormulaCodeₘ code) :=
    Formula.Admissible.imp_right <|
      (gq_formula_code_member_implies_generation
        code hCode
        (by simp [code])).admissible
  change
    ⊢ₘ[godel_quotation_theory]
      formula_code_generation_condition
          FormulaCodeₘ code ⟶ₘ
        Formula.falsum
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [formula_code_generation_condition
      FormulaCodeₘ code]
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_generation_condition
          FormulaCodeₘ code :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hGenerationAdmissible)
  have hShape :
      Γ ⊢ₘ[godel_quotation_theory]
        atomic ∨ₘ tail := by
    simpa [formula_code_generation_condition,
      atomic, tail, rest, negation,
      implication, universal] using
      hGeneration
  apply FirstOrder.Derives.disjElim hShape
  · let Δ : Context signature :=
      atomic :: Γ
    have hAtomicMember :
        Δ ⊢ₘ[godel_quotation_theory]
          atomic :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hAtomicNot :
        ⊢ₘ[godel_quotation_theory]
          ¬ₘ atomic := by
      simpa [atomic, code] using
        gq_standard_atomic_formula_code_not_of_decode_none
          freeBase boundNames tokens
          hTokens hDecode
    exact FirstOrder.Derives.negElim
      hAtomicMember
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ])
        hAtomicNot)
  · let Δ : Context signature :=
      tail :: Γ
    have hTail :
        Δ ⊢ₘ[godel_quotation_theory]
          tail :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    apply FirstOrder.Derives.disjElim hTail
    · let Ε : Context signature :=
        negation :: Δ
      exact FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε)
          (by simp [Ε, negation, code]) <|
            gq_formula_negation_decode_branch_falsum
              freeBase boundNames tokens
              hRejectBelow hTokens hBinders hDecode)
        (FirstOrder.Derives.assumption
          (by simp [negation, code]))
    · let Ε : Context signature :=
        rest :: Δ
      have hRest :
          Ε ⊢ₘ[godel_quotation_theory]
            rest :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
      apply FirstOrder.Derives.disjElim hRest
      · let Ζ : Context signature :=
          implication :: Ε
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ζ)
            (by simp [Ζ, implication, code]) <|
              gq_formula_implication_decode_branch_falsum
                freeBase boundNames tokens
                hRejectBelow hTokens hBinders hDecode)
          (FirstOrder.Derives.assumption
            (by simp [implication, code]))
      · let Ζ : Context signature :=
          universal :: Ε
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ζ)
            (by simp [Ζ, universal, code]) <|
              gq_formula_universal_decode_branch_falsum
                freeBase boundNames tokens
                hRejectBelow hTokens hBinders hDecode)
          (FirstOrder.Derives.assumption
            (by simp [universal, code]))

/--
有限签名与 binder 检查通过时，完整公式 decoder 的具体失败可在对象层排除标准
公式码成员。

证明按 token 长度强归纳。公式生成反演的三个复合分支都严格下降，故唯一未被
原子基础分支由真实的 checked 原子公式码拒绝定理承担。
-/
theorem gq_standard_formula_code_not_of_decode_none
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens)
    (hBinders : FSFormulaBinderTokens tokens)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ (standard_token_sequence tokens ∈ₘ
        FormulaCodeₘ) := by
  have hRejectBelow :
      FSFormulaDecodeRejectionBelow freeBase tokens := by
    intro childBoundNames childTokens hLength
      hChildTokens hChildBinders hChildDecode
    exact
      gq_standard_formula_code_not_of_decode_none
        freeBase childBoundNames childTokens
        hChildTokens hChildBinders hChildDecode
  let code : SetTerm :=
    standard_token_sequence tokens
  let membership : SetFormula :=
    code ∈ₘ FormulaCodeₘ
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    dsimp only [membership]
    exact membership_formula_admissible
      hCode formula_code_set_term_admissible
  change
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ membership
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        hMembershipAdmissible)
  let Γ : Context signature :=
    [membership]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        membership :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hMembershipAdmissible)
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_generation_condition
          FormulaCodeₘ code :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_formula_code_member_implies_generation
            code hCode
            (by simp [code]))
      (by simpa [membership] using hMember)
  have hGenerationReject :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_generation_condition
            FormulaCodeₘ code ⟶ₘ
          Formula.falsum :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
        simpa [code] using
          gq_formula_generation_decode_falsum
            freeBase boundNames tokens
            hRejectBelow hTokens hBinders hDecode
  exact FirstOrder.Derives.impElim
    hGenerationReject hGeneration
termination_by tokens.length
decreasing_by
  exact hLength

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
