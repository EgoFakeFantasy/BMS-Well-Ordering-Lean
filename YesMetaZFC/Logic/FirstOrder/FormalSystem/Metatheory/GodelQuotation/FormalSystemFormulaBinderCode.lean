import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCode

/-!
# FormalSystem 公式 binder 的有限后继证书

`FormulaCodeₘ` 只描述一般公式编码，不能把全称量词后的变量 token 反解为宿主名字。
本模块增加严格局部的可计算条件：每个全称 token 必须有直接后继，且该后继通过
有界变量名字检查。它不要求规范奇偶命名，也不携带解析树。
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

/-! ## 宿主可计算检查 -/

/-- 逐相邻位置检查全称 token 的后继，并拒绝末位裸全称 token。 -/
def fs_formula_binder_tokens_check : List Nat → Bool
  | [] =>
      true
  | [token] =>
      decide
        (token ≠ Numbered.logical_token .universal)
  | first :: second :: rest =>
      (decide
          (first ≠ Numbered.logical_token .universal) ||
        (fs_variable_name_decode second).isSome) &&
      fs_formula_binder_tokens_check (second :: rest)

/-- 一条 token 串通过全称 binder 的有限后继检查。 -/
def FSFormulaBinderTokens (tokens : List Nat) : Prop :=
  fs_formula_binder_tokens_check tokens = true

/-- 全称 binder 检查失败的两个有限局部原因。 -/
inductive FSFormulaBinderTokenFailure
    (tokens : List Nat) : Prop
  | successor_absent
      (index : Nat)
      (hUniversal :
        tokens[index]? =
          some (Numbered.logical_token .universal))
      (hNext :
        tokens[index + 1]? = none)
  | variable_decode
      (index token : Nat)
      (hUniversal :
        tokens[index]? =
          some (Numbered.logical_token .universal))
      (hNext :
        tokens[index + 1]? = some token)
      (hDecode :
        fs_variable_name_decode token = none)

/-- 布尔检查为假时，构造性定位一个具体 binder 失败。 -/
theorem fs_formula_binder_tokens_failure_of_false
    (tokens : List Nat)
    (hCheck :
      fs_formula_binder_tokens_check tokens = false) :
    FSFormulaBinderTokenFailure tokens := by
  induction tokens with
  | nil =>
      simp [fs_formula_binder_tokens_check] at hCheck
  | cons first rest ih =>
      cases rest with
      | nil =>
          have hFirst :
              first =
                Numbered.logical_token .universal := by
            by_cases hEqual :
                first =
                  Numbered.logical_token .universal
            · exact hEqual
            · simp [fs_formula_binder_tokens_check,
                hEqual] at hCheck
          exact
            .successor_absent 0
              (by simp [hFirst])
              (by simp)
      | cons second tail =>
          have hLift :
              FSFormulaBinderTokenFailure
                  (second :: tail) →
                FSFormulaBinderTokenFailure
                  (first :: second :: tail) := by
            intro hFailure
            cases hFailure with
            | successor_absent index hUniversal hNext =>
                exact
                  .successor_absent (index + 1)
                    (by simpa using hUniversal)
                    (by
                      simpa [Nat.add_assoc] using hNext)
            | variable_decode index token
                hUniversal hNext hDecode =>
                exact
                  .variable_decode (index + 1) token
                    (by simpa using hUniversal)
                    (by
                      simpa [Nat.add_assoc] using hNext)
                    hDecode
          by_cases hFirst :
              first =
                Numbered.logical_token .universal
          · cases hDecode :
                fs_variable_name_decode second with
            | none =>
                exact
                  .variable_decode 0 second
                    (by simp [hFirst])
                    (by simp)
                    hDecode
            | some name =>
                have hTail :
                    fs_formula_binder_tokens_check
                        (second :: tail) =
                      false := by
                  simpa [fs_formula_binder_tokens_check,
                    hFirst, hDecode] using hCheck
                exact hLift (ih hTail)
          · have hTail :
                fs_formula_binder_tokens_check
                    (second :: tail) =
                  false := by
              simpa [fs_formula_binder_tokens_check,
                hFirst] using hCheck
            exact hLift (ih hTail)

/--
通过有限检查后，可在任意具体全称位置提取直接后继及其变量名字。
-/
theorem fs_formula_binder_tokens_getElem?
    (tokens : List Nat)
    (hTokens : FSFormulaBinderTokens tokens)
    (index : Nat)
    (hUniversal :
      tokens[index]? =
        some (Numbered.logical_token .universal)) :
    ∃ token name,
      tokens[index + 1]? = some token ∧
        fs_variable_name_decode token = some name := by
  unfold FSFormulaBinderTokens at hTokens
  induction tokens generalizing index with
  | nil =>
      simp at hUniversal
  | cons first rest ih =>
      cases rest with
      | nil =>
          cases index with
          | zero =>
              simp at hUniversal
              subst first
              simp [fs_formula_binder_tokens_check] at hTokens
          | succ index =>
              simp at hUniversal
      | cons second tail =>
          rw [fs_formula_binder_tokens_check] at hTokens
          have hParts := Bool.and_eq_true_iff.mp hTokens
          cases index with
          | zero =>
              simp at hUniversal
              subst first
              have hSome :
                  (fs_variable_name_decode second).isSome =
                    true := by
                simpa using hParts.1
              cases hDecode :
                  fs_variable_name_decode second with
              | none =>
                  simp [hDecode] at hSome
              | some name =>
                  exact
                    ⟨second, name, by simp, hDecode⟩
          | succ index =>
              exact ih hParts.2 index (by
                simpa using hUniversal)

/--
索引式全称后继证书可计算地压回布尔检查。
-/
theorem fs_formula_binder_tokens_of_successors
    (tokens : List Nat)
    (hSuccessors :
      gq_universal_successor_condition
        (fun token =>
          ∃ name,
            fs_variable_name_decode token = some name)
        tokens) :
    FSFormulaBinderTokens tokens := by
  unfold FSFormulaBinderTokens
  induction tokens with
  | nil =>
      rfl
  | cons first rest ih =>
      cases rest with
      | nil =>
          have hFirst :
              first ≠
                Numbered.logical_token .universal := by
            intro hEqual
            rcases hSuccessors 0 (by
                simp [hEqual]) with
              ⟨next, hNext, _⟩
            simp at hNext
          simp [fs_formula_binder_tokens_check,
            hFirst]
      | cons second tail =>
          have hHead :
              (decide
                    (first ≠
                      Numbered.logical_token .universal) ||
                  (fs_variable_name_decode second).isSome) =
                true := by
            by_cases hFirst :
                first =
                  Numbered.logical_token .universal
            · rcases hSuccessors 0 (by
                  simp [hFirst]) with
                ⟨next, hNext, name, hDecode⟩
              simp at hNext
              subst next
              simp [hFirst, hDecode]
            · simp [hFirst]
          have hTailSuccessors :
              gq_universal_successor_condition
                (fun token =>
                  ∃ name,
                    fs_variable_name_decode token =
                      some name)
                (second :: tail) := by
            intro index hUniversal
            rcases hSuccessors (index + 1) (by
                simpa using hUniversal) with
              ⟨next, hNext, hAllowed⟩
            exact
              ⟨next, by
                simpa [Nat.add_assoc] using hNext,
                hAllowed⟩
          rw [fs_formula_binder_tokens_check,
            Bool.and_eq_true_iff]
          exact ⟨hHead, ih hTailSuccessors⟩

/-- 删除首 token 后，binder 检查仍然成立。 -/
theorem fs_formula_binder_tokens_tail
    {first : Nat} {rest : List Nat}
    (hTokens :
      FSFormulaBinderTokens (first :: rest)) :
    FSFormulaBinderTokens rest := by
  unfold FSFormulaBinderTokens at hTokens ⊢
  cases rest with
  | nil =>
      rfl
  | cons second tail =>
      rw [fs_formula_binder_tokens_check] at hTokens
      exact (Bool.and_eq_true_iff.mp hTokens).2

/-- 删除任意有限前缀后，binder 检查仍然成立。 -/
theorem fs_formula_binder_tokens_drop
    (prefixTokens tokens : List Nat)
    (hTokens :
      FSFormulaBinderTokens (prefixTokens ++ tokens)) :
    FSFormulaBinderTokens tokens := by
  induction prefixTokens with
  | nil =>
      simpa using hTokens
  | cons first rest ih =>
      apply ih
      apply fs_formula_binder_tokens_tail
      simpa using hTokens

/--
若紧随某段 token 的分隔符不能解码为变量，则整串通过 binder 检查时，该前段
自身也通过检查。该条件排除了末位裸全称 token 被后续分隔符意外补全。
-/
theorem fs_formula_binder_tokens_prefix_of_undecodable
    (tokens : List Nat) (boundary : Nat)
    (suffix : List Nat)
    (hBoundary :
      fs_variable_name_decode boundary = none)
    (hTokens :
      FSFormulaBinderTokens
        (tokens ++ boundary :: suffix)) :
    FSFormulaBinderTokens tokens := by
  induction tokens with
  | nil =>
      unfold FSFormulaBinderTokens
      rfl
  | cons first rest ih =>
      cases rest with
      | nil =>
          have hFull :
              FSFormulaBinderTokens
                (first :: boundary :: suffix) := by
            simpa using hTokens
          unfold FSFormulaBinderTokens at hFull ⊢
          rw [fs_formula_binder_tokens_check] at hFull
          have hHead :=
            (Bool.and_eq_true_iff.mp hFull).1
          have hFirst :
              first ≠
                Numbered.logical_token .universal := by
            intro hEqual
            simp [hEqual, hBoundary] at hHead
          simp [fs_formula_binder_tokens_check,
            hFirst]
      | cons second tail =>
          have hFull :
              FSFormulaBinderTokens
                (first :: second ::
                  (tail ++ boundary :: suffix)) := by
            simpa using hTokens
          unfold FSFormulaBinderTokens at hFull ⊢
          rw [fs_formula_binder_tokens_check] at hFull ⊢
          have hParts :=
            Bool.and_eq_true_iff.mp hFull
          apply Bool.and_eq_true_iff.mpr
          refine ⟨hParts.1, ?_⟩
          apply ih
          unfold FSFormulaBinderTokens
          simpa using hParts.2

/-- 规范否定外壳中的正文继承 binder 检查。 -/
theorem fs_formula_binder_tokens_negation_body
    (body : List Nat)
    (hTokens :
      FSFormulaBinderTokens
        (Numbered.negation_tokens body)) :
    FSFormulaBinderTokens body := by
  let rightParenthesis :=
    Numbered.logical_token .rightParenthesis
  have hBodyBoundary :
      FSFormulaBinderTokens
        (body ++ [rightParenthesis]) := by
    apply fs_formula_binder_tokens_drop
      [Numbered.logical_token .leftParenthesis,
        Numbered.logical_token .negation]
    simpa [Numbered.negation_tokens,
      rightParenthesis, List.append_assoc] using
      hTokens
  apply fs_formula_binder_tokens_prefix_of_undecodable
    body rightParenthesis []
  · native_decide
  · simpa using hBodyBoundary

/-- 规范蕴含外壳中的左正文继承 binder 检查。 -/
theorem fs_formula_binder_tokens_implication_left
    (left right : List Nat)
    (hTokens :
      FSFormulaBinderTokens
        (Numbered.implication_tokens left right)) :
    FSFormulaBinderTokens left := by
  let implication :=
    Numbered.logical_token .implication
  let rightParenthesis :=
    Numbered.logical_token .rightParenthesis
  have hTail :
      FSFormulaBinderTokens
        (left ++ implication ::
          (right ++ [rightParenthesis])) := by
    apply fs_formula_binder_tokens_drop
      [Numbered.logical_token .leftParenthesis]
    simpa [Numbered.implication_tokens,
      implication, rightParenthesis,
      List.append_assoc] using hTokens
  apply fs_formula_binder_tokens_prefix_of_undecodable
    left implication
      (right ++ [rightParenthesis])
  · native_decide
  · exact hTail

/-- 规范蕴含外壳中的右正文继承 binder 检查。 -/
theorem fs_formula_binder_tokens_implication_right
    (left right : List Nat)
    (hTokens :
      FSFormulaBinderTokens
        (Numbered.implication_tokens left right)) :
    FSFormulaBinderTokens right := by
  let implication :=
    Numbered.logical_token .implication
  let rightParenthesis :=
    Numbered.logical_token .rightParenthesis
  have hRightBoundary :
      FSFormulaBinderTokens
        (right ++ [rightParenthesis]) := by
    apply fs_formula_binder_tokens_drop
      ([Numbered.logical_token .leftParenthesis] ++
        left ++ [implication])
    simpa [Numbered.implication_tokens,
      implication, rightParenthesis,
      List.append_assoc] using hTokens
  apply fs_formula_binder_tokens_prefix_of_undecodable
    right rightParenthesis []
  · native_decide
  · simpa using hRightBoundary

/-- 规范全称外壳中的正文继承 binder 检查。 -/
theorem fs_formula_binder_tokens_universal_body
    (name : Nat) (body : List Nat)
    (hTokens :
      FSFormulaBinderTokens
        (Numbered.universal_tokens name body)) :
    FSFormulaBinderTokens body := by
  let rightParenthesis :=
    Numbered.logical_token .rightParenthesis
  have hBodyBoundary :
      FSFormulaBinderTokens
        (body ++ [rightParenthesis]) := by
    apply fs_formula_binder_tokens_drop
      [Numbered.logical_token .leftParenthesis,
        Numbered.logical_token .universal,
        Numbered.variable_token name]
    simpa [Numbered.universal_tokens,
      rightParenthesis, List.append_assoc] using
      hTokens
  apply fs_formula_binder_tokens_prefix_of_undecodable
    body rightParenthesis []
  · native_decide
  · simpa using hBodyBoundary

/-- 规范 quotation 自动通过 binder 后继检查。 -/
theorem fs_quote_tokens_formula_binder_tokens
    {formula : SetFormula} {tokens : List Nat}
    (hQuote :
      Numbered.quote_tokens? formula = some tokens) :
    FSFormulaBinderTokens tokens := by
  apply fs_formula_binder_tokens_of_successors
  intro index hUniversal
  rcases
      quote_tokens?_universal_successors
        (σ := signature) hQuote index hUniversal with
    ⟨token, hToken, depth, hDepth⟩
  subst token
  exact
    ⟨Numbered.variable_token (bound_name depth),
      by simpa using hToken,
      bound_name depth,
      fs_variable_name_decode_encode
        (bound_name depth)⟩

/-! ## 对象层局部条件 -/

/--
定义域内单个位置的全称后继核心。
`nextToken` 已按变量名字 binder 的深度提升；定义域限制由外层全称条件统一承担。
-/
def fs_formula_binder_condition_lifted
    (code index nextToken : SetTerm) : SetFormula :=
  (((code ·ₘ index) ≐ₘ
      numₘ(Numbered.logical_token .universal)) ⟶ₘ
    (((Sₘ(index)) ∈ₘ domₘ(code)) ∧ₘ
      fs_variable_token_condition nextToken))

/-- 具名位置 binder 下的全称后继条件。 -/
def fs_formula_binder_condition_with_id
    (code : SetTerm) (tokenIndexId : FreeVarId) :
    SetFormula :=
  ∀ₘ[SetSort.set, tokenIndexId],
    ((x#tokenIndexId ∈ₘ domₘ(code)) ⟶ₘ
      fs_formula_binder_condition_lifted
        code (x#tokenIndexId)
        (code ·ₘ Sₘ(x#tokenIndexId)))

/-- 规范 de Bruijn 位置 binder 下的全称后继条件。 -/
def fs_formula_binder_condition
    (code : SetTerm) : SetFormula :=
  ∀ₘ[SetSort.set],
    ((bₛ#0 ∈ₘ domₘ(code)) ⟶ₘ
      fs_formula_binder_condition_lifted
        code (bₛ#0)
        (code ·ₘ Sₘ(bₛ#1)))

/-- 具名位置 binder 下的完整 replay 词法条件。 -/
def fs_formula_replay_condition_with_id
    (code : SetTerm) (tokenIndexId : FreeVarId) :
    SetFormula :=
  fs_formula_signature_condition_with_id
      code tokenIndexId ∧ₘ
    fs_formula_binder_condition_with_id
      code tokenIndexId

/-- verifier 使用的完整 replay 词法条件。 -/
def fs_formula_replay_condition
    (code : SetTerm) : SetFormula :=
  fs_formula_signature_condition code ∧ₘ
    fs_formula_binder_condition code

theorem fs_formula_binder_condition_with_id_admissible
    (code : SetTerm) (tokenIndexId : FreeVarId)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (fs_formula_binder_condition_with_id
        code tokenIndexId) := by
  have hIndex :
      Term.Admissible (x#tokenIndexId) SetSort.set :=
    set_variable_admissible tokenIndexId
  have hDomain :
      Term.Admissible (domₘ(code)) SetSort.set :=
    domain_term_admissible code hCode
  have hValue :
      Term.Admissible
        (code ·ₘ x#tokenIndexId) SetSort.set :=
    function_application_term_admissible
      code (x#tokenIndexId) hCode hIndex
  have hNext :
      Term.Admissible
        (Sₘ(x#tokenIndexId)) SetSort.set :=
    successor_term_admissible
      (x#tokenIndexId) hIndex
  have hNextValue :
      Term.Admissible
        (code ·ₘ Sₘ(x#tokenIndexId))
        SetSort.set :=
    function_application_term_admissible
      code (Sₘ(x#tokenIndexId))
      hCode hNext
  have hPoint :
      Formula.Admissible
        ((x#tokenIndexId ∈ₘ domₘ(code)) ⟶ₘ
          fs_formula_binder_condition_lifted
            code (x#tokenIndexId)
            (code ·ₘ Sₘ(x#tokenIndexId))) := by
    exact Formula.Admissible.imp
      (membership_formula_admissible
        hIndex hDomain)
      (Formula.Admissible.imp
        (Formula.Admissible.equal
          hValue
          (finite_numeral_term_admissible
            (Numbered.logical_token .universal)))
        (Formula.Admissible.conj
          (membership_formula_admissible
            hNext hDomain)
          (fs_variable_token_condition_admissible
            (code ·ₘ Sₘ(x#tokenIndexId))
            hNextValue)))
  exact Formula.Admissible.forall_closeFreeAt
    SetSort.set tokenIndexId hPoint

theorem fs_formula_binder_condition_with_id_freeSupport_subset
    (code : SetTerm) (tokenIndexId : FreeVarId)
    (freeVariable : FreeVariable signature)
    (hMember :
      freeVariable ∈
        Formula.freeSupport
          (fs_formula_binder_condition_with_id
            code tokenIndexId)) :
    freeVariable ∈ Term.freeSupport code := by
  simp [fs_formula_binder_condition_with_id,
    fs_formula_binder_condition_lifted,
    fs_variable_token_condition,
    Formula.freeSupport, Term.freeSupport,
    Term.freeSupportList,
    finite_numeral_term_freeSupport,
    Formula.mem_freeSupport_closeFreeAt_iff] at hMember
  grind

theorem fs_formula_binder_condition_freeSupport_subset
    (code : SetTerm)
    (freeVariable : FreeVariable signature)
    (hMember :
      freeVariable ∈
        Formula.freeSupport
          (fs_formula_binder_condition code)) :
    freeVariable ∈ Term.freeSupport code := by
  simp [fs_formula_binder_condition,
    fs_formula_binder_condition_lifted,
    fs_variable_token_condition,
    Formula.freeSupport, Term.freeSupport,
    Term.freeSupportList,
    finite_numeral_term_freeSupport] at hMember
  grind

/-- 具名位置变量对代码新鲜时，显式条件等于规范 de Bruijn 条件。 -/
theorem fs_formula_binder_condition_with_id_eq
    (code : SetTerm) (tokenIndexId : FreeVarId)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      (SetSort.set, tokenIndexId) ∉
        Term.freeSupport code) :
    fs_formula_binder_condition_with_id
        code tokenIndexId =
      fs_formula_binder_condition code := by
  have hCodeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set tokenIndexId depth code =
        code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set tokenIndexId depth code hCode.2 hFresh
  have hNumeralClose (number depth : Nat) :
      Term.closeFreeAt SetSort.set tokenIndexId depth
          (numₘ(number)) =
        numₘ(number) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set tokenIndexId depth
      (numₘ(number))
      (finite_numeral_term_admissible number).2 (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  simp [fs_formula_binder_condition_with_id,
    fs_formula_binder_condition,
    fs_formula_binder_condition_lifted,
    fs_variable_token_condition,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt,
    set_variable, set_bound_variable,
    hCodeClose, hNumeralClose]

theorem fs_formula_binder_condition_admissible
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (fs_formula_binder_condition code) := by
  let tokenIndexId :=
    FreshVariable.fresh_id SetSort.set [code ≐ₘ code]
  have hFresh :
      (SetSort.set, tokenIndexId) ∉
        Term.freeSupport code := by
    simpa [tokenIndexId] using
      FreshVariable.fresh_term_not_mem_m
        SetSort.set code
  rw [← fs_formula_binder_condition_with_id_eq
    code tokenIndexId hCode hFresh]
  exact fs_formula_binder_condition_with_id_admissible
    code tokenIndexId hCode

/-- 规范 binder 条件沿自由变量项代换严格保持形状。 -/
theorem fs_formula_binder_condition_substitute
    (code replacement codeResult : SetTerm)
    (sourceId : FreeVarId)
    (hCode :
      Term.substituteFree SetSort.set sourceId replacement code =
        codeResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (fs_formula_binder_condition code) =
      fs_formula_binder_condition codeResult := by
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId replacement
          (numₘ(number)) =
        numₘ(number) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set sourceId replacement
      (numₘ(number)) (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  simp [fs_formula_binder_condition,
    fs_formula_binder_condition_lifted,
    fs_variable_token_condition,
    Formula.substituteFree, Term.substituteFree,
    hCode, hNumeralFixed]

theorem fs_formula_replay_condition_with_id_eq
    (code : SetTerm) (tokenIndexId : FreeVarId)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      (SetSort.set, tokenIndexId) ∉
        Term.freeSupport code) :
    fs_formula_replay_condition_with_id
        code tokenIndexId =
      fs_formula_replay_condition code := by
  simp [fs_formula_replay_condition_with_id,
    fs_formula_replay_condition,
    fs_formula_signature_condition_with_id_eq
      code tokenIndexId hCode hFresh,
    fs_formula_binder_condition_with_id_eq
      code tokenIndexId hCode hFresh]

theorem fs_formula_replay_condition_admissible
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (fs_formula_replay_condition code) :=
  Formula.Admissible.conj
    (fs_formula_signature_condition_admissible
      code hCode)
    (fs_formula_binder_condition_admissible
      code hCode)

theorem fs_formula_replay_condition_freeSupport_subset
    (code : SetTerm)
    (freeVariable : FreeVariable signature)
    (hMember :
      freeVariable ∈
        Formula.freeSupport
          (fs_formula_replay_condition code)) :
    freeVariable ∈ Term.freeSupport code := by
  simp [fs_formula_replay_condition,
    Formula.freeSupport] at hMember
  rcases hMember with hMember | hMember
  · exact
      fs_formula_signature_condition_freeSupport_subset
        code freeVariable hMember
  · exact
      fs_formula_binder_condition_freeSupport_subset
        code freeVariable hMember

theorem fs_formula_replay_condition_substitute
    (code replacement codeResult : SetTerm)
    (sourceId : FreeVarId)
    (hCode :
      Term.substituteFree SetSort.set sourceId replacement code =
        codeResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (fs_formula_replay_condition code) =
      fs_formula_replay_condition codeResult := by
  simp [fs_formula_replay_condition,
    Formula.substituteFree,
    fs_formula_signature_condition_substitute
      code replacement codeResult sourceId hCode,
    fs_formula_binder_condition_substitute
      code replacement codeResult sourceId hCode]

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
