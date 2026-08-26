import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.RosserFinite
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.SyntaxCoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoder
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderComposition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.CanonicalFormulaPayload
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.NamedFormulaPayload

/-!
# 有界证书化证明码的构造性解包

本模块只实现 natural-number proof code 的有限解码边界：

* 外层 Gödel pair 解出公式行码与证书行码；
* 证书行码逐项解出 `HilbertLineCertificateCode`；
* 公式行 token 经过 checked parser 后解出 Hilbert 归约公式。

逻辑公理行的 `HilbertLogicalAxiom` 目前仍由显式语法证书提供；本模块不使用
经典判定器把它伪装成可计算谓词。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace Rosser

open Nonlogical.BasicSetTheory
open ProofCode
open GodelQuotation

set_option autoImplicit false

/-! ## 证书序列与外层 proof code -/

/-- 从自然数序列码解出证书标签序列。 -/
def fs_certificate_sequence_decode
    (code : Nat) :
    Option (List HilbertLineCertificateCode) :=
  (nat_sequence_decode code).mapM
    HilbertLineCertificateCode.decode

/-- 规范证书序列编码可被 checked 解包精确恢复。 -/
theorem fs_certificate_sequence_decode_value
    (certificates : List HilbertLineCertificateCode) :
    fs_certificate_sequence_decode
        (nat_sequence_code_value
          (certificates.map HilbertLineCertificateCode.value)) =
      some certificates := by
  unfold fs_certificate_sequence_decode
  rw [nat_sequence_decode_code_value]
  induction certificates with
  | nil =>
      rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.mapM_cons,
        HilbertLineCertificateCode.decode_value, Option.bind_eq_bind]
      rw [ih]
      rfl

/-- proof code 解出的有限公式 token 序列与证书序列。 -/
def fs_certified_proof_code_decode
    (proofCode : Nat) :
    List (List Nat) ×
      Option (List HilbertLineCertificateCode) :=
  let pair := godel_unpair_value proofCode
  (proof_sequence_decode pair.1,
    fs_certificate_sequence_decode pair.2)

/-- 规范证书化 proof code 的有限解包定理。 -/
theorem fs_certified_proof_code_decode_value
    (rowTokens : SetFormula → List Nat)
    (proof : List SetFormula)
    (certificates : List HilbertLineCertificateCode) :
    fs_certified_proof_code_decode
        (certified_hilbert_proof_code_value
          rowTokens proof certificates) =
      (proof.map rowTokens, some certificates) := by
  unfold fs_certified_proof_code_decode
  simp only [certified_hilbert_proof_code_value,
    godel_unpair_value_pair,
    proof_sequence_decode_code_value,
    fs_certificate_sequence_decode_value]

/-! ## 固定环境下的公式行解码 -/

/-- 单个 token 行的 proof-carrying checked 解码结果。 -/
structure FSDecodedFormula where
  formula : SetFormula
  h_admissible : Formula.Admissible formula

/-! ## 公式行 token 的有限解码 -/

/--
把单行 checked 解码结果提升为带 admissibility payload 的结果。

证明行使用对象公式码允许的具名变量编码；逻辑证书 payload 的规范性由对应
certificate checker 单独负责。
-/
def fs_formula_row_decode
    (freeBase : Nat) (row : List Nat) :
    Option FSDecodedFormula :=
  match hParsed :
      GodelQuotation.fs_named_hilbert_tokens_decode_with_env
        freeBase [] row with
  | none =>
      none
  | some formula =>
      some {
        formula := formula
        h_admissible :=
          by
            simpa [GodelQuotation.Numbered.scope_of_names,
              Scope.empty] using
              fs_named_hilbert_tokens_decode_with_env_admissible
                freeBase [] hParsed
      }

/-- 单行 checked 解码成功时，恢复其 Hilbert 核构造分类。 -/
theorem fs_formula_row_decode_core
    {freeBase : Nat}
    {row : List Nat}
    {decoded : FSDecodedFormula}
    (hDecode :
      fs_formula_row_decode freeBase row =
        some decoded) :
    GodelQuotation.Numbered.HilbertCore
      decoded.formula := by
  unfold fs_formula_row_decode at hDecode
  split at hDecode
  · simp at hDecode
  · next formula hParsed =>
    have hDecoded :
        ({
          formula := formula
          h_admissible := by
            simpa [GodelQuotation.Numbered.scope_of_names,
              Scope.empty] using
              fs_named_hilbert_tokens_decode_with_env_admissible
                freeBase [] hParsed
        } : FSDecodedFormula) = decoded :=
      Option.some.inj hDecode
    subst decoded
    rcases
        (GodelQuotation.fs_named_hilbert_tokens_decode_with_env_iff
          freeBase [] row formula).mp hParsed with
      ⟨tree, _, hTree⟩
    exact
      GodelQuotation.fs_named_hilbert_token_tree_decode_core
        freeBase hTree

/-- 规范 quotation 行的 checked payload 精确回放。 -/
theorem fs_formula_row_decode_quote
    (freeBase : Nat)
    {formula : SetFormula}
    (hFormula : Formula.Admissible formula)
    {tokens : List Nat}
    (hQuote : GodelQuotation.Numbered.quote_tokens? formula = some tokens) :
    fs_formula_row_decode freeBase tokens =
      some {
        formula := Formula.hilbertize SetSort.set formula
        h_admissible := Formula.Admissible.hilbertize hFormula
      } := by
  have hDecoded :
      GodelQuotation.fs_named_hilbert_tokens_decode_with_env
          freeBase [] tokens =
        some (Formula.hilbertize SetSort.set formula) :=
    fs_named_hilbert_tokens_decode_with_env_quote
      freeBase
      hFormula hQuote
  have hCanonical :
      GodelQuotation.Numbered.quote_tokens?
          (Formula.hilbertize SetSort.set formula) =
        some tokens := by
    unfold GodelQuotation.Numbered.quote_tokens?
      GodelQuotation.Numbered.quote_tokens_with? at hQuote ⊢
    change
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize SetSort.set
            (Formula.hilbertize SetSort.set formula)) =
        some tokens
    rw [Formula.hilbertize_idempotent]
    exact hQuote
  unfold fs_formula_row_decode
  split
  · next hParsed =>
      simp_all
  · next decoded hParsed =>
      have hDecodedEq :
          decoded = Formula.hilbertize SetSort.set formula :=
        Option.some.inj (hParsed.symm.trans hDecoded)
      subst decoded
      rfl

/-! ## 公式行序列与严格 MP 检查 -/

def fs_formula_rows_decode_payload
    (freeBase : Nat) :
    List (List Nat) → Option (List FSDecodedFormula) :=
  List.mapM (fs_formula_row_decode freeBase)

/-! ## 规范 quotation 行的 payload 精确回放 -/

/-- 规范 quotation 行的 payload 解码，并保留逐行公式对齐关系。 -/
theorem fs_formula_rows_decode_payload_quote
    (freeBase : Nat)
    {proof : List SetFormula}
    (hRows :
      ∀ formula, formula ∈ proof →
        Formula.Admissible formula) :
    ∃ decoded,
      fs_formula_rows_decode_payload freeBase
          (proof.map certified_row_tokens) =
        some decoded ∧
      decoded.map FSDecodedFormula.formula =
        proof.map (Formula.hilbertize SetSort.set) := by
  induction proof with
  | nil =>
      exact ⟨([] : List FSDecodedFormula), rfl, rfl⟩
  | cons head tail ih =>
      have hHead : Formula.Admissible head := hRows head (by simp)
      have hTail :
          ∀ formula, formula ∈ tail →
            Formula.Admissible formula := by
        intro formula hFormula
        exact hRows formula (by simp [hFormula])
      rcases ih hTail with
        ⟨decodedTail, hDecodedTail, hDecodedTailMap⟩
      rcases formula_code_witness_exists hHead with
        ⟨headWitness⟩
      have hHeadDecode :
          fs_formula_row_decode freeBase
              headWitness.tokens =
            some {
              formula := Formula.hilbertize SetSort.set head
              h_admissible := Formula.Admissible.hilbertize hHead
            } :=
        fs_formula_row_decode_quote freeBase hHead
          headWitness.h_tokens
      let decodedHead : FSDecodedFormula := {
        formula := Formula.hilbertize SetSort.set head
        h_admissible := Formula.Admissible.hilbertize hHead
      }
      have hDecodedTail' :
          List.mapM (fs_formula_row_decode freeBase)
              (tail.map certified_row_tokens) =
            some decodedTail := by
        simpa [fs_formula_rows_decode_payload] using hDecodedTail
      refine ⟨decodedHead :: decodedTail, ?_, ?_⟩
      · simp [fs_formula_rows_decode_payload,
          List.map_cons, certified_row_tokens_eq headWitness,
          hHeadDecode, hDecodedTail', decodedHead]
      · simp [decodedHead, hDecodedTailMap]

/-- 复用公开公式 Gödel 编码的可计算相等检查。 -/
def fs_formula_code_eq
    (left right : SetFormula) : Bool :=
  decide
    (GodelQuotation.SyntaxCoding.formula_encode left =
      GodelQuotation.SyntaxCoding.formula_encode right)

/-- 公式相等检查通过时给出真实的语法等式。 -/
theorem fs_formula_code_eq_sound
    {left right : SetFormula}
    (hCheck : fs_formula_code_eq left right = true) :
    left = right := by
  apply GodelQuotation.SyntaxCoding.formula_encode_injective
  exact of_decide_eq_true hCheck

/-- 复用公开项 Gödel 编码的可计算相等检查。 -/
def fs_term_code_eq
    (left right : SetTerm) : Bool :=
  decide
    (GodelQuotation.SyntaxCoding.term_encode left =
      GodelQuotation.SyntaxCoding.term_encode right)

/-- 项相等检查通过时给出真实的语法等式。 -/
theorem fs_term_code_eq_sound
    {left right : SetTerm}
    (hCheck : fs_term_code_eq left right = true) :
    left = right := by
  apply GodelQuotation.SyntaxCoding.term_encode_injective
  exact of_decide_eq_true hCheck

/-- 从 `t = t` 公式载体中取出项。 -/
def fs_term_carrier_decode (carrier : SetFormula) :
    Option SetTerm :=
  match carrier with
  | .equal left right =>
      if fs_term_code_eq left right = true then
        some left
      else
        none
  | _ =>
      none

/-- `t=t` 载体通过 checked 解码时只会还原为相同两项。 -/
theorem fs_term_carrier_decode_sound
    {carrier : SetFormula} {term : SetTerm}
    (hDecode : fs_term_carrier_decode carrier = some term) :
    carrier = Formula.equal term term := by
  cases carrier with
  | equal left right =>
      unfold fs_term_carrier_decode at hDecode
      by_cases hCheck :
          fs_term_code_eq left right = true
      · simp [hCheck] at hDecode
        subst term
        have hEqual : left = right :=
          fs_term_code_eq_sound hCheck
        subst right
        rfl
      · simp [hCheck] at hDecode
  | falsum =>
      simp [fs_term_carrier_decode] at hDecode
  | truth =>
      simp [fs_term_carrier_decode] at hDecode
  | rel relation arguments =>
      simp [fs_term_carrier_decode] at hDecode
  | neg body =>
      simp [fs_term_carrier_decode] at hDecode
  | conj left right =>
      simp [fs_term_carrier_decode] at hDecode
  | disj left right =>
      simp [fs_term_carrier_decode] at hDecode
  | imp left right =>
      simp [fs_term_carrier_decode] at hDecode
  | iff left right =>
      simp [fs_term_carrier_decode] at hDecode
  | forallE sort body =>
      simp [fs_term_carrier_decode] at hDecode
  | existsE sort body =>
      simp [fs_term_carrier_decode] at hDecode

/-- 逻辑 base 证书的自然数编码。 -/
def fs_logical_base_certificate_code
    (tag : Nat) (payload : Nat) : Nat :=
  godel_pair_value tag payload

/-- 逻辑全称闭包证书的序列项编码。 -/
def fs_logical_closure_certificate_code
    (eigen : Nat) (rest : List Nat) : Nat :=
  nat_sequence_code_value (eigen :: rest)

/-- 逻辑公理基础证书的公共 checked 内核。 -/
def fs_logical_base_axiom_check_with
    (payloadDecode : Nat → Option (List SetFormula))
    (formulaDecode : Nat → Option SetFormula)
    (formula : SetFormula) (code : Nat) : Bool :=
  let pair := godel_unpair_value code
  match pair.1 with
  | 0 =>
      match payloadDecode pair.2 with
      | some (antecedent :: middle :: consequent :: []) =>
          fs_formula_code_eq formula
            (Formula.imp
              (Formula.imp antecedent
                (Formula.imp middle consequent))
              (Formula.imp
                (Formula.imp antecedent middle)
                (Formula.imp antecedent consequent)))
      | _ =>
          false
  | 1 =>
      match payloadDecode pair.2 with
      | some (body :: []) =>
          fs_formula_code_eq formula
            (Formula.imp body (Formula.imp body body))
      | _ =>
          false
  | 2 =>
      match payloadDecode pair.2 with
      | some (body :: extra :: []) =>
          fs_formula_code_eq formula
            (Formula.imp body (Formula.imp extra body))
      | _ =>
          false
  | 3 =>
      match payloadDecode pair.2 with
      | some (body :: conclusion :: []) =>
          fs_formula_code_eq formula
            (Formula.imp body
              (Formula.imp (Formula.neg body) conclusion))
      | _ =>
          false
  | 4 =>
      match payloadDecode pair.2 with
      | some (body :: []) =>
          fs_formula_code_eq formula
            (Formula.imp
              (Formula.imp (Formula.neg body) body)
              body)
      | _ =>
          false
  | 5 =>
      match payloadDecode pair.2 with
      | some (body :: conclusion :: []) =>
          fs_formula_code_eq formula
            (Formula.imp (Formula.neg body)
              (Formula.imp body conclusion))
      | _ =>
          false
  | 6 =>
      match payloadDecode pair.2 with
      | some (body :: conclusion :: []) =>
          fs_formula_code_eq formula
            (Formula.imp
              (Formula.imp body conclusion)
              (Formula.imp
                (Formula.imp (Formula.neg body) conclusion)
                conclusion))
      | _ =>
          false
  | 7 =>
      let payload := godel_unpair_value pair.2
      let formulaCodes := godel_unpair_value payload.2
      match formulaDecode formulaCodes.1,
        formulaDecode formulaCodes.2 with
      | some body, some carrier =>
          match fs_term_carrier_decode carrier with
          | some term =>
              (Term.check_wellSorted SetSort.set term &&
                Term.check_scoped Scope.empty term) &&
                fs_formula_code_eq formula
                  (Formula.imp
                    (Formula.forallE SetSort.set
                      (Formula.closeFreeAt
                        SetSort.set payload.1 0 body))
                    (Formula.openAt
                      SetSort.set 0 term
                      (Formula.closeFreeAt
                        SetSort.set payload.1 0 body)))
          | none =>
              false
      | _, _ =>
          false
  | 8 =>
      let payload := godel_unpair_value pair.2
      let formulaCodes := godel_unpair_value payload.2
      match formulaDecode formulaCodes.1,
        formulaDecode formulaCodes.2 with
      | some antecedent, some consequent =>
          fs_formula_code_eq formula
            (Formula.imp
              (Formula.forallE SetSort.set
                (Formula.imp
                  (Formula.closeFreeAt
                    SetSort.set payload.1 0 antecedent)
                  (Formula.closeFreeAt
                    SetSort.set payload.1 0 consequent)))
              (Formula.imp
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt
                    SetSort.set payload.1 0 antecedent))
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt
                    SetSort.set payload.1 0 consequent))))
      | _, _ =>
          false
  | 9 =>
      let payload := godel_unpair_value pair.2
      match formulaDecode payload.2 with
      | some body =>
          (decide
              ((SetSort.set, payload.1) ∉
                Formula.freeSupport body)) &&
            fs_formula_code_eq formula
              (Formula.imp body
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt
                    SetSort.set payload.1 0 body)))
      | none =>
          false
  | 10 =>
      match nat_sequence_decode pair.2 with
      | leftId :: rightId :: bodyCode :: [] =>
          match formulaDecode bodyCode with
          | some body =>
              fs_formula_code_eq formula
                (Formula.imp
                  (Formula.equal
                    (Term.var (.fvar SetSort.set leftId))
                    (Term.var (.fvar SetSort.set rightId)))
                  (Formula.imp body
                    (Formula.substituteFree
                      SetSort.set leftId
                      (Term.var (.fvar SetSort.set rightId))
                      body)))
          | none =>
              false
      | _ =>
          false
  | 11 =>
      fs_formula_code_eq formula
        (Formula.equal
          (Term.var (.fvar SetSort.set pair.2))
          (Term.var (.fvar SetSort.set pair.2)))
  | _ =>
      false

/-- proof code 运行时使用共享自由变量基点的具名解码。 -/
def fs_logical_base_axiom_check
    (freeBase : Nat)
    (formula : SetFormula) (code : Nat) : Bool :=
  fs_logical_base_axiom_check_with
    (fs_named_formula_payload_decode freeBase)
    (fs_named_formula_token_code_decode freeBase)
    formula code

/-- 正向证书内部化使用带 re-quote 检查的规范解码。 -/
def fs_logical_base_axiom_canonical_check
    (formula : SetFormula) (code : Nat) : Bool :=
  fs_logical_base_axiom_check_with
    fs_formula_payload_decode
    fs_formula_token_code_decode
    formula code

/-- 任意解码后端的 checked base 分支通过时还原为真实 Hilbert 基础公理。 -/
theorem fs_logical_base_axiom_check_with_sound
    {payloadDecode : Nat → Option (List SetFormula)}
    {formulaDecode : Nat → Option SetFormula}
    {formula : SetFormula} {code : Nat}
    (hCheck :
      fs_logical_base_axiom_check_with
        payloadDecode formulaDecode formula code = true) :
    HilbertBaseAxiom formula := by
  unfold fs_logical_base_axiom_check_with at hCheck
  generalize hPair : godel_unpair_value code = pair at hCheck
  dsimp at hCheck
  have hNoLarge : ¬ 12 ≤ pair.1 := by
    intro hLarge
    obtain ⟨tail, hTail⟩ := Nat.le.dest hLarge
    rw [← hTail] at hCheck
    simp [Nat.add_comm] at hCheck
  have hBound : pair.1 ≤ 11 := by
    omega
  have hCases :
      pair.1 = 0 ∨ pair.1 = 1 ∨ pair.1 = 2 ∨ pair.1 = 3 ∨
        pair.1 = 4 ∨ pair.1 = 5 ∨ pair.1 = 6 ∨ pair.1 = 7 ∨
        pair.1 = 8 ∨ pair.1 = 9 ∨ pair.1 = 10 ∨ pair.1 = 11 := by
    omega
  rcases hCases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · rw [h0] at hCheck
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons antecedent tail =>
            cases hTailPayload : tail with
            | nil =>
                simp [hPayload, hTailPayload] at hCheck
            | cons middle tail =>
                cases hMiddlePayload : tail with
                | nil =>
                    simp [hPayload, hTailPayload, hMiddlePayload] at hCheck
                | cons consequent tail =>
                    cases hRestPayload : tail with
                    | nil =>
                        simp [hPayload, hTailPayload,
                          hMiddlePayload, hRestPayload] at hCheck
                        have hFormula :
                            formula =
                              Formula.imp
                                (Formula.imp antecedent
                                  (Formula.imp middle consequent))
                                (Formula.imp
                                  (Formula.imp antecedent middle)
                                  (Formula.imp antecedent consequent)) :=
                          fs_formula_code_eq_sound hCheck
                        rw [hFormula]
                        exact HilbertBaseAxiom.implication_distribution
                          antecedent middle consequent
                    | cons extra tail =>
                        simp [hPayload, hTailPayload,
                          hMiddlePayload, hRestPayload] at hCheck
  · rw [h1] at hCheck
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons body tail =>
            cases hTailPayload : tail with
            | nil =>
                simp [hPayload, hTailPayload] at hCheck
                have hFormula :
                    formula = Formula.imp body (Formula.imp body body) :=
                  fs_formula_code_eq_sound hCheck
                rw [hFormula]
                exact HilbertBaseAxiom.self_implication body
            | cons extra tail =>
                simp [hPayload, hTailPayload] at hCheck
  · rw [h2] at hCheck
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons body tail =>
            cases hTailPayload : tail with
            | nil =>
                simp [hPayload, hTailPayload] at hCheck
            | cons extra tail =>
                cases hRestPayload : tail with
                | nil =>
                    simp [hPayload, hTailPayload,
                      hRestPayload] at hCheck
                    have hFormula :
                        formula =
                          Formula.imp body
                            (Formula.imp extra body) :=
                      fs_formula_code_eq_sound hCheck
                    rw [hFormula]
                    exact HilbertBaseAxiom.weakening body extra
                | cons rest tail =>
                    simp [hPayload, hTailPayload,
                      hRestPayload] at hCheck
  · rw [h3] at hCheck
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons body tail =>
            cases hTailPayload : tail with
            | nil =>
                simp [hPayload, hTailPayload] at hCheck
            | cons conclusion tail =>
                cases hRestPayload : tail with
                | nil =>
                    simp [hPayload, hTailPayload,
                      hRestPayload] at hCheck
                    have hFormula :
                        formula =
                          Formula.imp body
                            (Formula.imp (Formula.neg body) conclusion) :=
                      fs_formula_code_eq_sound hCheck
                    rw [hFormula]
                    exact HilbertBaseAxiom.contradiction body conclusion
                | cons rest tail =>
                    simp [hPayload, hTailPayload,
                      hRestPayload] at hCheck
  · rw [h4] at hCheck
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons body tail =>
            cases hTailPayload : tail with
            | nil =>
                simp [hPayload, hTailPayload] at hCheck
                have hFormula :
                    formula =
                      Formula.imp
                        (Formula.imp (Formula.neg body) body)
                        body :=
                  fs_formula_code_eq_sound hCheck
                rw [hFormula]
                exact HilbertBaseAxiom.classical body
            | cons extra tail =>
                simp [hPayload, hTailPayload] at hCheck
  · rw [h5] at hCheck
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons body tail =>
            cases hTailPayload : tail with
            | nil =>
                simp [hPayload, hTailPayload] at hCheck
            | cons conclusion tail =>
                cases hRestPayload : tail with
                | nil =>
                    simp [hPayload, hTailPayload,
                      hRestPayload] at hCheck
                    have hFormula :
                        formula =
                          Formula.imp (Formula.neg body)
                            (Formula.imp body conclusion) :=
                      fs_formula_code_eq_sound hCheck
                    rw [hFormula]
                    exact HilbertBaseAxiom.explosion body conclusion
                | cons rest tail =>
                    simp [hPayload, hTailPayload,
                      hRestPayload] at hCheck
  · rw [h6] at hCheck
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons body tail =>
            cases hTailPayload : tail with
            | nil =>
                simp [hPayload, hTailPayload] at hCheck
            | cons conclusion tail =>
                cases hRestPayload : tail with
                | nil =>
                    simp [hPayload, hTailPayload,
                      hRestPayload] at hCheck
                    have hFormula :
                        formula =
                          Formula.imp
                            (Formula.imp body conclusion)
                            (Formula.imp
                              (Formula.imp (Formula.neg body) conclusion)
                              conclusion) :=
                      fs_formula_code_eq_sound hCheck
                    rw [hFormula]
                    exact HilbertBaseAxiom.case_analysis body conclusion
                | cons rest tail =>
                    simp [hPayload, hTailPayload,
                      hRestPayload] at hCheck
  · simp only [h7] at hCheck
    generalize hPayload : godel_unpair_value pair.2 = payload at hCheck
    generalize hFormulaCodes :
        godel_unpair_value payload.2 = formulaCodes at hCheck
    cases hBody :
        formulaDecode formulaCodes.1 with
    | none =>
        simp [hBody] at hCheck
    | some body =>
        cases hCarrierCode :
            formulaDecode formulaCodes.2 with
        | none =>
            simp [hBody, hCarrierCode] at hCheck
        | some carrier =>
            cases hCarrier :
                fs_term_carrier_decode carrier with
            | none =>
                simp [hBody, hCarrierCode, hCarrier] at hCheck
            | some term =>
                simp [hBody, hCarrierCode, hCarrier] at hCheck
                rcases hCheck with
                  ⟨⟨hSorted, hScoped⟩, hFormulaCheck⟩
                have hFormula :
                    formula =
                      Formula.imp
                        (Formula.forallE SetSort.set
                          (Formula.closeFreeAt
                            SetSort.set payload.1 0 body))
                        (Formula.openAt
                          SetSort.set 0 term
                          (Formula.closeFreeAt
                            SetSort.set payload.1 0 body)) :=
                  fs_formula_code_eq_sound hFormulaCheck
                have hTermWellSorted :
                    TermWellSorted term SetSort.set :=
                  Term.check_wellSorted_sound hSorted
                have hTermClosed :
                    Term.BoundClosed term :=
                  Term.check_scoped_sound hScoped
                rw [hFormula]
                exact HilbertBaseAxiom.forall_specialization
                  SetSort.set
                  (Formula.closeFreeAt
                    SetSort.set payload.1 0 body) term
                  hTermWellSorted hTermClosed
  · simp only [h8] at hCheck
    generalize hPayload : godel_unpair_value pair.2 = payload at hCheck
    generalize hFormulaCodes :
        godel_unpair_value payload.2 = formulaCodes at hCheck
    cases hAntecedent :
        formulaDecode formulaCodes.1 with
    | none =>
        simp [hAntecedent] at hCheck
    | some antecedent =>
        cases hConsequent :
            formulaDecode formulaCodes.2 with
        | none =>
            simp [hAntecedent, hConsequent] at hCheck
        | some consequent =>
            simp [hAntecedent, hConsequent] at hCheck
            have hFormula :
                formula =
                  Formula.imp
                    (Formula.forallE SetSort.set
                      (Formula.imp
                        (Formula.closeFreeAt
                          SetSort.set payload.1 0 antecedent)
                        (Formula.closeFreeAt
                          SetSort.set payload.1 0 consequent)))
                    (Formula.imp
                      (Formula.forallE SetSort.set
                        (Formula.closeFreeAt
                          SetSort.set payload.1 0 antecedent))
                      (Formula.forallE SetSort.set
                        (Formula.closeFreeAt
                          SetSort.set payload.1 0 consequent))) :=
              fs_formula_code_eq_sound hCheck
            rw [hFormula]
            exact HilbertBaseAxiom.forall_distribution
              SetSort.set
              (Formula.closeFreeAt
                SetSort.set payload.1 0 antecedent)
              (Formula.closeFreeAt
                SetSort.set payload.1 0 consequent)
  · simp only [h9] at hCheck
    generalize hPayload : godel_unpair_value pair.2 = payload at hCheck
    cases hBody :
        formulaDecode payload.2 with
    | none =>
        simp [hBody] at hCheck
    | some body =>
        simp [hBody] at hCheck
        rcases hCheck with
          ⟨hFreshCheck, hFormulaCheck⟩
        have hFresh :
            (SetSort.set, payload.1) ∉ Formula.freeSupport body :=
          hFreshCheck
        have hFormula :
            formula =
              Formula.imp body
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt
                    SetSort.set payload.1 0 body)) :=
          fs_formula_code_eq_sound hFormulaCheck
        rw [hFormula]
        exact HilbertBaseAxiom.vacuous_forall
          SetSort.set payload.1 body hFresh
  · rw [h10] at hCheck
    cases hPayload : nat_sequence_decode pair.2 with
    | nil =>
        simp [hPayload] at hCheck
    | cons leftId tail =>
        cases hTailPayload : tail with
        | nil =>
            simp [hPayload, hTailPayload] at hCheck
        | cons rightId tail =>
            cases hRestPayload : tail with
            | nil =>
                simp [hPayload, hTailPayload,
                  hRestPayload] at hCheck
            | cons bodyCode tail =>
                cases hFinalPayload : tail with
                | nil =>
                    cases hBody :
                        formulaDecode bodyCode with
                    | none =>
                        simp [hPayload, hTailPayload,
                          hRestPayload, hFinalPayload,
                          hBody] at hCheck
                    | some body =>
                        simp [hPayload, hTailPayload,
                          hRestPayload, hFinalPayload,
                          hBody] at hCheck
                        have hFormula :
                            formula =
                              Formula.imp
                                (Formula.equal
                                  (Term.var
                                    (.fvar SetSort.set leftId))
                                  (Term.var
                                    (.fvar SetSort.set rightId)))
                                (Formula.imp body
                                  (Formula.substituteFree
                                    SetSort.set leftId
                                    (Term.var
                                      (.fvar SetSort.set rightId))
                                    body)) :=
                          fs_formula_code_eq_sound hCheck
                        rw [hFormula]
                        exact HilbertBaseAxiom.equality_substitution
                          SetSort.set leftId rightId body
                | cons rest tail =>
                    simp [hPayload, hTailPayload,
                      hRestPayload, hFinalPayload] at hCheck
  · rw [h11] at hCheck
    have hFormula :
        formula =
          Formula.equal
            (Term.var (.fvar SetSort.set pair.2))
            (Term.var (.fvar SetSort.set pair.2)) :=
      fs_formula_code_eq_sound hCheck
    rw [hFormula]
    exact HilbertBaseAxiom.equality_reflexivity
      (σ := Nonlogical.BasicSetTheory.signature) SetSort.set pair.2

/-- 具名运行时基础 checker 的 soundness。 -/
theorem fs_logical_base_axiom_check_sound
    {freeBase : Nat}
    {formula : SetFormula} {code : Nat}
    (hCheck :
      fs_logical_base_axiom_check
        freeBase formula code = true) :
    HilbertBaseAxiom formula := by
  exact fs_logical_base_axiom_check_with_sound
    (by
      simpa [fs_logical_base_axiom_check] using hCheck)

/-- 规范基础 checker 的 soundness。 -/
theorem fs_logical_base_axiom_canonical_check_sound
    {formula : SetFormula} {code : Nat}
    (hCheck :
      fs_logical_base_axiom_canonical_check
        formula code = true) :
    HilbertBaseAxiom formula := by
  exact fs_logical_base_axiom_check_with_sound
    (by
      simpa [fs_logical_base_axiom_canonical_check] using hCheck)

/-- 逻辑公理证书的 checked 序列折叠公共内核。 -/
def fs_logical_axiom_check_rows_with
    (baseCheck : SetFormula → Nat → Bool)
    (codes : List Nat) (formula : SetFormula) : Bool :=
  match codes with
  | [] =>
      false
  | baseCode :: [] =>
      baseCheck formula baseCode
  | eigen :: rest =>
      match formula with
      | .forallE sort body =>
          (decide
              ((sort, eigen) ∉ Formula.freeSupport body)) &&
            fs_logical_axiom_check_rows_with baseCheck rest
              (Formula.openAt sort 0
                (Term.var (.fvar sort eigen)) body)
      | _ =>
          false

/-- proof code 运行时使用具名基础 checker 的逻辑闭包检查。 -/
def fs_logical_axiom_check_rows
    (freeBase : Nat)
    (codes : List Nat) (formula : SetFormula) : Bool :=
  fs_logical_axiom_check_rows_with
    (fs_logical_base_axiom_check freeBase) codes formula

/-- 正向内部化使用规范基础 checker 的逻辑闭包检查。 -/
def fs_logical_axiom_canonical_check_rows
    (codes : List Nat) (formula : SetFormula) : Bool :=
  fs_logical_axiom_check_rows_with
    fs_logical_base_axiom_canonical_check codes formula

/-- 自然数逻辑公理证书的 checked 判定。 -/
def fs_logical_axiom_check
    (freeBase certificateCode : Nat)
    (formula : SetFormula) : Bool :=
  fs_logical_axiom_check_rows freeBase
    (nat_sequence_decode certificateCode) formula

/-- 规范自然数逻辑公理证书的 checked 判定。 -/
def fs_logical_axiom_canonical_check
    (certificateCode : Nat)
    (formula : SetFormula) : Bool :=
  fs_logical_axiom_canonical_check_rows
    (nat_sequence_decode certificateCode) formula

/-- 任意 sound 基础 checker 的闭包序列通过时还原 Hilbert 逻辑公理。 -/
theorem fs_logical_axiom_check_rows_with_sound
    {baseCheck : SetFormula → Nat → Bool}
    (hBaseSound :
      ∀ {formula code},
        baseCheck formula code = true →
          HilbertBaseAxiom formula)
    {codes : List Nat} {formula : SetFormula}
    (hCheck :
      fs_logical_axiom_check_rows_with
        baseCheck codes formula = true) :
    HilbertLogicalAxiom formula := by
  cases codes with
  | nil =>
      simp [fs_logical_axiom_check_rows_with] at hCheck
  | cons eigen tail =>
      cases tail with
      | nil =>
          exact HilbertLogicalAxiom.base
            (hBaseSound hCheck)
      | cons baseCode rest =>
          cases formula with
          | falsum =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | truth =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | rel relation arguments =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | equal left right =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | neg body =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | conj left right =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | disj left right =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | imp left right =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | iff left right =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | forallE sort body =>
              simp only [fs_logical_axiom_check_rows_with] at hCheck
              rcases Bool.and_eq_true_iff.mp hCheck with
                ⟨hFreshCheck, hRestCheck⟩
              have hFresh :
                  (sort, eigen) ∉ Formula.freeSupport body :=
                of_decide_eq_true hFreshCheck
              have hInner :
                  HilbertLogicalAxiom
                    (Formula.openAt sort 0
                      (Term.var (.fvar sort eigen)) body) :=
                fs_logical_axiom_check_rows_with_sound
                  hBaseSound hRestCheck
              have hRestore :
                  Formula.closeFreeAt sort eigen 0
                      (Formula.openAt sort 0
                        (Term.var (.fvar sort eigen)) body) =
                    body :=
                Formula.closeFreeAt_openAt sort eigen 0 body hFresh
              simpa [hRestore] using
                (HilbertLogicalAxiom.forall_closure
                  sort eigen hInner)
          | existsE sort body =>
              simp [fs_logical_axiom_check_rows_with] at hCheck

/-- 具名逻辑公理闭包 checker 的 soundness。 -/
theorem fs_logical_axiom_check_rows_sound
    {freeBase : Nat}
    {codes : List Nat} {formula : SetFormula}
    (hCheck :
      fs_logical_axiom_check_rows
        freeBase codes formula = true) :
    HilbertLogicalAxiom formula := by
  exact fs_logical_axiom_check_rows_with_sound
    (fun h => fs_logical_base_axiom_check_sound h)
    (by
      simpa [fs_logical_axiom_check_rows] using hCheck)

/-- 规范逻辑公理闭包 checker 的 soundness。 -/
theorem fs_logical_axiom_canonical_check_rows_sound
    {codes : List Nat} {formula : SetFormula}
    (hCheck :
      fs_logical_axiom_canonical_check_rows
        codes formula = true) :
    HilbertLogicalAxiom formula := by
  exact fs_logical_axiom_check_rows_with_sound
    (fun h => fs_logical_base_axiom_canonical_check_sound h)
    (by
      simpa [fs_logical_axiom_canonical_check_rows] using hCheck)

/-- 自然数逻辑公理证书通过时还原为真实的 Hilbert 逻辑公理。 -/
theorem fs_logical_axiom_check_sound
    {freeBase certificateCode : Nat}
    {formula : SetFormula}
    (hCheck :
      fs_logical_axiom_check
        freeBase certificateCode formula = true) :
    HilbertLogicalAxiom formula := by
  exact fs_logical_axiom_check_rows_sound hCheck

/-- 规范自然数逻辑公理证书通过时还原为真实的 Hilbert 逻辑公理。 -/
theorem fs_logical_axiom_canonical_check_sound
    {certificateCode : Nat}
    {formula : SetFormula}
    (hCheck :
      fs_logical_axiom_canonical_check
        certificateCode formula = true) :
    HilbertLogicalAxiom formula := by
  exact fs_logical_axiom_canonical_check_rows_sound hCheck

/-- MP 行 checked replay 所需的显式有限见证。 -/
structure FSModusPonensWitness
    (proof : List SetFormula)
    (formula : SetFormula)
    (implicationIndex premiseIndex : Nat) where
  antecedent : SetFormula
  consequent : SetFormula
  h_implication :
    proof[implicationIndex]? =
      some (Formula.imp antecedent consequent)
  h_premise :
    proof[premiseIndex]? = some antecedent
  h_premise_earlier :
    premiseIndex < implicationIndex
  h_conclusion :
    formula = consequent

/-- 对已经解出的公式列表检查一行是否是严格 MP。 -/
def fs_modus_ponens_check
    (proof : List SetFormula)
    (formula : SetFormula)
    (implicationIndex premiseIndex : Nat) : Bool :=
  (decide (premiseIndex < implicationIndex)) &&
    match proof[implicationIndex]?,
      proof[premiseIndex]? with
    | some (.imp antecedent consequent), some premise =>
        fs_formula_code_eq premise antecedent &&
          fs_formula_code_eq formula consequent
    | _, _ =>
        false

/-- MP checked replay 通过时构造与对象行条件同形的严格索引见证。 -/
def fs_modus_ponens_witness_of_check
    {proof : List SetFormula}
    {formula : SetFormula}
    {implicationIndex premiseIndex : Nat}
    (hCheck :
      fs_modus_ponens_check
        proof formula implicationIndex premiseIndex =
        true) :
    FSModusPonensWitness
      proof formula implicationIndex premiseIndex := by
  unfold fs_modus_ponens_check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with
    ⟨hEarlier, hLine⟩
  have hPremiseEarlier :
      premiseIndex < implicationIndex :=
    of_decide_eq_true hEarlier
  cases hImplication :
      proof[implicationIndex]? with
  | none =>
      simp [hImplication] at hLine
  | some implication =>
      cases implication with
      | imp antecedent consequent =>
          cases hPremise :
              proof[premiseIndex]? with
          | none =>
              simp [hImplication, hPremise] at hLine
          | some premise =>
              simp only [hImplication, hPremise] at hLine
              rcases Bool.and_eq_true_iff.mp hLine with
                ⟨hPremiseCode, hConclusionCode⟩
              refine {
                antecedent := antecedent
                consequent := consequent
                h_implication := hImplication
                h_premise := ?_
                h_premise_earlier := hPremiseEarlier
                h_conclusion := ?_
              }
              · have hPremiseEq :
                    premise = antecedent :=
                  fs_formula_code_eq_sound hPremiseCode
                rw [hPremiseEq] at hPremise
                exact hPremise
              · exact fs_formula_code_eq_sound hConclusionCode
      | falsum =>
          simp [hImplication] at hLine
      | truth =>
          simp [hImplication] at hLine
      | rel relation arguments =>
          simp [hImplication] at hLine
      | equal left right =>
          simp [hImplication] at hLine
      | neg body =>
          simp [hImplication] at hLine
      | conj left right =>
          simp [hImplication] at hLine
      | disj left right =>
          simp [hImplication] at hLine
      | iff left right =>
          simp [hImplication] at hLine
      | forallE sort body =>
          simp [hImplication] at hLine
      | existsE sort body =>
          simp [hImplication] at hLine

/-- MP checked replay 的结构化 soundness 公开为存在命题。 -/
theorem fs_modus_ponens_check_sound
    {proof : List SetFormula}
    {formula : SetFormula}
    {implicationIndex premiseIndex : Nat}
    (hCheck :
      fs_modus_ponens_check
        proof formula implicationIndex premiseIndex =
        true) :
    Nonempty
      (FSModusPonensWitness
        proof formula implicationIndex premiseIndex) :=
  ⟨fs_modus_ponens_witness_of_check hCheck⟩

/-- 带 checked 判定证据的 Hilbert 轨迹。 -/
inductive FSCheckedHilbertTrace
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    (logicalCheck : Nat → SetFormula → Bool) :
    List SetFormula → List HilbertLineCertificateCode → Prop where
  | nil :
      FSCheckedHilbertTrace enumeration logicalCheck [] []
  | logical
      {proof : List SetFormula}
      {formula : SetFormula}
      {certificates : List HilbertLineCertificateCode}
      (previous :
        FSCheckedHilbertTrace
          enumeration logicalCheck proof certificates)
      (certificateCode : Nat)
      (hCheck :
        logicalCheck certificateCode formula = true)
      (hAdmissible : Formula.Admissible formula) :
      FSCheckedHilbertTrace enumeration logicalCheck
        (proof ++ [formula])
        (certificates ++
          [HilbertLineCertificateCode.logical certificateCode])
  | theory
      {proof : List SetFormula}
      {formula : SetFormula}
      {certificates : List HilbertLineCertificateCode}
      (previous :
        FSCheckedHilbertTrace
          enumeration logicalCheck proof certificates)
      (certificateCode : Nat)
      (hCertificate :
        enumeration.certificate_verifier certificateCode formula = true)
      (hAdmissible : Formula.Admissible formula) :
      FSCheckedHilbertTrace enumeration logicalCheck
        (proof ++ [formula])
        (certificates ++
          [HilbertLineCertificateCode.theory certificateCode])
  | modusPonens
      {proof : List SetFormula}
      {antecedent consequent : SetFormula}
      {certificates : List HilbertLineCertificateCode}
      (previous :
        FSCheckedHilbertTrace
          enumeration logicalCheck proof certificates)
      (implicationIndex premiseIndex : Nat)
      (hImplication :
        proof[implicationIndex]? =
          some (Formula.imp antecedent consequent))
      (hPremise :
        proof[premiseIndex]? =
          some antecedent)
      (hPremiseEarlier :
        premiseIndex < implicationIndex) :
      FSCheckedHilbertTrace enumeration logicalCheck
        (proof ++ [consequent])
        (certificates ++
          [HilbertLineCertificateCode.modusPonens
            implicationIndex premiseIndex])

namespace FSCheckedHilbertTrace

/-- checked 轨迹中的每一行都给出目标理论的归纳式 Hilbert 推导。 -/
theorem derives_of_mem
    {theory : SetTheory}
    {enumeration : ProofCode.HilbertTheoryEnumeration theory}
    {logicalCheck : Nat → SetFormula → Bool}
    (hLogicalSound :
      ∀ {certificateCode formula},
        logicalCheck certificateCode formula = true →
          HilbertLogicalAxiom formula)
    {proof : List SetFormula}
    {certificates : List HilbertLineCertificateCode}
    (hTrace :
      FSCheckedHilbertTrace
        enumeration logicalCheck proof certificates)
    {formula : SetFormula}
    (hFormula : formula ∈ proof) :
    HilbertDerives theory formula := by
  induction hTrace generalizing formula with
  | nil =>
      simp at hFormula
  | logical previous certificateCode hCheck hAdmissible ih =>
      simp only [List.mem_append, List.mem_singleton] at hFormula
      rcases hFormula with hFormula | rfl
      · exact ih hFormula
      · exact .logical_axiom
          (hLogicalSound hCheck)
          hAdmissible
  | theory previous certificateCode hCertificate hAdmissible ih =>
      simp only [List.mem_append, List.mem_singleton] at hFormula
      rcases hFormula with hFormula | rfl
      · exact ih hFormula
      · exact .theory_axiom
          (enumeration.certificate_sound hCertificate)
          hAdmissible
  | modusPonens previous implicationIndex premiseIndex
      hImplication hPremise hPremiseEarlier ih =>
      simp only [List.mem_append, List.mem_singleton] at hFormula
      rcases hFormula with hFormula | rfl
      · exact ih hFormula
      · rcases List.getElem?_eq_some_iff.mp hImplication with
          ⟨hImplicationIndex, hImplicationGet⟩
        have hImplicationMem :=
          List.getElem_mem hImplicationIndex
        rw [hImplicationGet] at hImplicationMem
        rcases List.getElem?_eq_some_iff.mp hPremise with
          ⟨hPremiseIndex, hPremiseGet⟩
        have hPremiseMem :=
          List.getElem_mem hPremiseIndex
        rw [hPremiseGet] at hPremiseMem
        exact .modus_ponens
          (ih hPremiseMem)
          (ih hImplicationMem)

end FSCheckedHilbertTrace

/-! ## 可组合 replay 状态 -/

/-- checked replay 状态显式保存当前公式列表、证书列表及其 checked 轨迹。 -/
structure FSReplayState
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat) where
  proof : List SetFormula
  certificates : List HilbertLineCertificateCode
  trace :
    FSCheckedHilbertTrace
      enumeration (fs_logical_axiom_check freeBase)
        proof certificates

/-- 理论公理行的可计算 checked replay。 -/
def fs_replay_theory_row
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    {freeBase : Nat}
    (state : FSReplayState enumeration freeBase)
    (formula : SetFormula)
    (certificateCode : Nat)
    (hAdmissible : Formula.Admissible formula) :
    Option (FSReplayState enumeration freeBase) :=
  if hCertificate :
      enumeration.certificate_verifier
          certificateCode formula =
        true then
    some {
      proof := state.proof ++ [formula]
      certificates :=
        state.certificates ++
          [HilbertLineCertificateCode.theory certificateCode]
      trace :=
        FSCheckedHilbertTrace.theory
          state.trace certificateCode
          hCertificate hAdmissible
    }
  else
    none

/-- 严格 MP 行的 checked replay；公式相等只经公开自然数编码判定。 -/
def fs_replay_modus_ponens_row
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    {freeBase : Nat}
    (state : FSReplayState enumeration freeBase)
    (formula : SetFormula)
    (implicationIndex premiseIndex : Nat) :
    Option (FSReplayState enumeration freeBase) :=
  if hCheck :
      fs_modus_ponens_check
          state.proof formula
          implicationIndex premiseIndex =
        true then
    by
      let witness :=
        fs_modus_ponens_witness_of_check hCheck
      exact some {
        proof := state.proof ++ [formula]
        certificates :=
          state.certificates ++
            [HilbertLineCertificateCode.modusPonens
              implicationIndex premiseIndex]
        trace :=
          by
            simpa [witness.h_conclusion] using
              (FSCheckedHilbertTrace.modusPonens
                state.trace implicationIndex premiseIndex
                witness.h_implication witness.h_premise
                witness.h_premise_earlier)
      }
  else
    none

/-- 逻辑公理行的 checked replay。 -/
def fs_replay_logical_row
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    {freeBase : Nat}
    (state : FSReplayState enumeration freeBase)
    (formula : SetFormula)
    (certificateCode : Nat)
    (hAdmissible : Formula.Admissible formula) :
    Option (FSReplayState enumeration freeBase) :=
  if hCheck :
      fs_logical_axiom_check
        freeBase certificateCode formula = true then
    some {
      proof := state.proof ++ [formula]
      certificates :=
        state.certificates ++
          [HilbertLineCertificateCode.logical certificateCode]
      trace :=
        FSCheckedHilbertTrace.logical
          state.trace certificateCode
          hCheck hAdmissible
    }
  else
    none

/-- 三类证书标签的完整 checked replay。 -/
def fs_replay_row
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    {freeBase : Nat}
    (state : FSReplayState enumeration freeBase)
    (formula : SetFormula)
    (certificate : HilbertLineCertificateCode)
    (hAdmissible : Formula.Admissible formula) :
    Option (FSReplayState enumeration freeBase) :=
  match certificate with
  | .logical certificateCode =>
      fs_replay_logical_row
        enumeration state formula
        certificateCode hAdmissible
  | .theory certificateCode =>
      fs_replay_theory_row
        enumeration state formula
        certificateCode hAdmissible
  | .modusPonens implicationIndex premiseIndex =>
      fs_replay_modus_ponens_row
        enumeration state formula
        implicationIndex premiseIndex

/-- 空 replay 状态。 -/
def fs_replay_nil
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat) :
    FSReplayState enumeration freeBase where
  proof := []
  certificates := []
  trace := FSCheckedHilbertTrace.nil

/-- 全部证书行的有限 checked replay 折叠。 -/
def fs_replay_rows
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat) :
    (state : FSReplayState enumeration freeBase) →
      (rows : List FSDecodedFormula) →
      (certificates : List HilbertLineCertificateCode) →
      Option (FSReplayState enumeration freeBase)
  | state, rows, certificates =>
      match rows with
      | [] =>
          match certificates with
          | [] =>
              some state
          | _ =>
              none
      | row :: rows =>
          match certificates with
          | [] =>
              none
          | certificate :: certificates =>
              match fs_replay_row
                  enumeration state row.formula
                  certificate row.h_admissible with
              | none =>
                  none
              | some next =>
                  fs_replay_rows
                    enumeration freeBase next rows certificates

/--
原始 token 行的逐行 checked replay。

每一步先解码当前行，再立即核验同位置证书；因此失败位置之前的 replay 状态不会
被后续坏行丢失。已解码行折叠 `fs_replay_rows` 仍作为携带 admissibility 载荷的
内部证明层。
-/
def fs_replay_raw_rows
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat) :
    (state : FSReplayState enumeration freeBase) →
      (rows : List (List Nat)) →
      (certificates : List HilbertLineCertificateCode) →
      Option (FSReplayState enumeration freeBase)
  | state, rows, certificates =>
      match rows with
      | [] =>
          match certificates with
          | [] =>
              some state
          | _ =>
              none
      | row :: rows =>
          match certificates with
          | [] =>
              none
          | certificate :: certificates =>
              match fs_formula_row_decode freeBase row with
              | none =>
                  none
              | some decoded =>
                  match fs_replay_row
                      enumeration state decoded.formula
                      certificate decoded.h_admissible with
                  | none =>
                      none
                  | some next =>
                      fs_replay_raw_rows
                        enumeration freeBase next rows certificates

/--
当整段行解码成功时，逐行原始 replay 与携带 payload 的 replay 精确一致。

该等式只用于把既有正向 checked 轨迹复用到新的逐行入口；负向反演直接读取
`fs_replay_raw_rows` 的成功前缀，不再依赖全局 `mapM`。
-/
theorem fs_replay_raw_rows_eq_of_decode
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat)
    (state : FSReplayState enumeration freeBase)
    {rows : List (List Nat)}
    {decodedRows : List FSDecodedFormula}
    (certificates : List HilbertLineCertificateCode)
    (hDecode :
      fs_formula_rows_decode_payload freeBase rows =
        some decodedRows) :
    fs_replay_raw_rows enumeration freeBase state rows certificates =
      fs_replay_rows
        enumeration freeBase state decodedRows certificates := by
  induction rows generalizing state decodedRows certificates with
  | nil =>
      simp [fs_formula_rows_decode_payload] at hDecode
      subst decodedRows
      cases certificates <;> rfl
  | cons row rows ih =>
      cases decodedRows with
      | nil =>
          cases hRow : fs_formula_row_decode freeBase row with
          | none =>
              simp [fs_formula_rows_decode_payload, hRow] at hDecode
          | some decoded =>
              cases hRows :
                  List.mapM (fs_formula_row_decode freeBase) rows with
              | none =>
                  simp [fs_formula_rows_decode_payload,
                    hRow, hRows] at hDecode
              | some tail =>
                  simp [fs_formula_rows_decode_payload,
                    hRow, hRows] at hDecode
      | cons decoded tail =>
          have hMap :
              (row :: rows).mapM (fs_formula_row_decode freeBase) =
                some (decoded :: tail) := by
            simpa [fs_formula_rows_decode_payload] using hDecode
          rcases fs_option_mapM_cons_eq_some
              (fs_formula_row_decode freeBase) hMap with
            ⟨hRow, hRows⟩
          cases certificates with
          | nil =>
              rfl
          | cons certificate certificates =>
              simp only [fs_replay_raw_rows,
                fs_replay_rows, hRow]
              cases hStep :
                  fs_replay_row enumeration state
                    decoded.formula certificate
                    decoded.h_admissible with
              | none =>
                  simp
              | some next =>
                  simp
                  exact ih next certificates <| by
                    simpa [fs_formula_rows_decode_payload] using hRows

/-- checked replay 折叠对两段连续行保持组合性。 -/
theorem fs_replay_rows_append
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat)
    {state middle final :
      FSReplayState enumeration freeBase}
    {rows tailRows : List FSDecodedFormula}
    {certificates tailCertificates :
      List HilbertLineCertificateCode}
    (hReplay :
      fs_replay_rows
        enumeration freeBase state rows certificates =
        some middle)
    (hTail :
      fs_replay_rows
        enumeration freeBase middle tailRows tailCertificates =
        some final) :
    fs_replay_rows enumeration freeBase state
        (rows ++ tailRows)
        (certificates ++ tailCertificates) =
      some final := by
  induction rows generalizing state certificates middle with
  | nil =>
      cases certificates with
      | nil =>
          simp [fs_replay_rows] at hReplay
          subst middle
          exact hTail
      | cons certificate certificates =>
          simp [fs_replay_rows] at hReplay
  | cons row rows ih =>
      cases certificates with
      | nil =>
          simp [fs_replay_rows] at hReplay
      | cons certificate certificates =>
          simp only [List.cons_append, fs_replay_rows] at hReplay ⊢
          cases hStep :
              fs_replay_row enumeration state row.formula
                certificate row.h_admissible with
          | none =>
              simp [hStep] at hReplay ⊢
          | some next =>
              simp [hStep] at hReplay ⊢
              exact ih hReplay hTail

/-- 由公式投影的末项对齐，拆出 checked 行列表的最后一行。 -/
theorem fs_decoded_rows_split_append
    {rows : List FSDecodedFormula}
    {initialFormulas : List SetFormula}
    {formula : SetFormula}
    (hRows :
      rows.map FSDecodedFormula.formula =
        initialFormulas ++ [formula]) :
    ∃ initialRows lastRow,
      rows = initialRows ++ [lastRow] ∧
      initialRows.map FSDecodedFormula.formula = initialFormulas ∧
      lastRow.formula = formula := by
  induction initialFormulas generalizing rows with
  | nil =>
      cases rows with
      | nil =>
          simp at hRows
      | cons lastRow tail =>
          cases tail with
          | nil =>
              have hLast :
                  lastRow.formula = formula := by
                simpa using hRows
              exact ⟨([] : List FSDecodedFormula), lastRow,
                by simp, by simp, hLast⟩
          | cons nextRow tail =>
              simp at hRows
  | cons head tail ih =>
      cases rows with
      | nil =>
          simp at hRows
      | cons row rows =>
          simp only [List.map_cons, List.cons_append] at hRows
          rcases List.cons.inj hRows with
            ⟨hHead, hTail⟩
          rcases ih hTail with
            ⟨initialRows, lastRow, hSplit,
              hPrefix, hLast⟩
          refine ⟨row :: initialRows, lastRow, ?_, ?_, hLast⟩
          · simp [hSplit]
          · simp [hPrefix, hHead]

/-- 带 checked 行条件的轨迹一定能被有限 replay 执行成功。 -/
theorem fs_replay_rows_of_checked_trace
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    (freeBase : Nat)
    {proof : List SetFormula}
    {certificates : List HilbertLineCertificateCode}
    (hTrace :
      FSCheckedHilbertTrace
        enumeration (fs_logical_axiom_check freeBase)
        proof certificates)
    {rows : List FSDecodedFormula}
    (hRows :
      rows.map FSDecodedFormula.formula = proof) :
    ∃ state,
      fs_replay_rows enumeration freeBase
          (fs_replay_nil enumeration freeBase)
          rows certificates =
        some state ∧
      state.proof = proof ∧
      state.certificates = certificates := by
  induction hTrace generalizing rows with
  | nil =>
      cases rows with
      | nil =>
          refine
            ⟨fs_replay_nil enumeration freeBase,
              rfl, rfl, rfl⟩
      | cons row rows =>
          simp at hRows
  | @logical proof formula certificates previous
      certificateCode hCheck hAdmissible ih =>
      rcases fs_decoded_rows_split_append hRows with
        ⟨initialRows, lastRow, hRowsSplit,
          hInitialRows, hLast⟩
      rcases ih hInitialRows with
        ⟨middle, hReplay, hMiddleProof,
          hMiddleCertificates⟩
      have hLastCheck :
          fs_logical_axiom_check freeBase certificateCode
              lastRow.formula = true := by
        simpa [hLast] using hCheck
      let next : FSReplayState enumeration freeBase := {
        proof := middle.proof ++ [lastRow.formula]
        certificates := middle.certificates ++
          [HilbertLineCertificateCode.logical certificateCode]
        trace := FSCheckedHilbertTrace.logical
          middle.trace certificateCode
          hLastCheck lastRow.h_admissible
      }
      have hOne :
          fs_replay_rows enumeration freeBase middle
              [lastRow]
              [HilbertLineCertificateCode.logical certificateCode] =
            some next := by
        simp [fs_replay_rows, fs_replay_row,
          fs_replay_logical_row, hLastCheck, next]
      refine ⟨next, ?_, ?_, ?_⟩
      · rw [hRowsSplit]
        exact
          fs_replay_rows_append
            enumeration freeBase hReplay hOne
      · simp [next, hMiddleProof, hLast]
      · simp [next, hMiddleCertificates]
  | @theory proof formula certificates previous
      certificateCode hCertificate hAdmissible ih =>
      rcases fs_decoded_rows_split_append hRows with
        ⟨initialRows, lastRow, hRowsSplit,
          hInitialRows, hLast⟩
      rcases ih hInitialRows with
        ⟨middle, hReplay, hMiddleProof,
          hMiddleCertificates⟩
      have hLastCertificate :
          enumeration.certificate_verifier certificateCode
              lastRow.formula = true := by
        simpa [hLast] using hCertificate
      let next : FSReplayState enumeration freeBase := {
        proof := middle.proof ++ [lastRow.formula]
        certificates := middle.certificates ++
          [HilbertLineCertificateCode.theory certificateCode]
        trace := FSCheckedHilbertTrace.theory
          middle.trace certificateCode
          hLastCertificate lastRow.h_admissible
      }
      have hOne :
          fs_replay_rows enumeration freeBase middle
              [lastRow]
              [HilbertLineCertificateCode.theory certificateCode] =
            some next := by
        simp [fs_replay_rows, fs_replay_row,
          fs_replay_theory_row, hLastCertificate, next]
      refine ⟨next, ?_, ?_, ?_⟩
      · rw [hRowsSplit]
        exact
          fs_replay_rows_append
            enumeration freeBase hReplay hOne
      · simp [next, hMiddleProof, hLast]
      · simp [next, hMiddleCertificates]
  | @modusPonens proof antecedent consequent certificates
      previous implicationIndex premiseIndex hImplication
      hPremise hPremiseEarlier ih =>
      rcases fs_decoded_rows_split_append hRows with
        ⟨initialRows, lastRow, hRowsSplit,
          hInitialRows, hLast⟩
      rcases ih hInitialRows with
        ⟨middle, hReplay, hMiddleProof,
          hMiddleCertificates⟩
      have hCheck :
          fs_modus_ponens_check
              middle.proof lastRow.formula
              implicationIndex premiseIndex = true := by
        rw [hMiddleProof, hLast]
        simp [fs_modus_ponens_check, hImplication,
          hPremise, hPremiseEarlier, fs_formula_code_eq]
      let witness :=
        fs_modus_ponens_witness_of_check hCheck
      let next : FSReplayState enumeration freeBase := {
        proof := middle.proof ++ [lastRow.formula]
        certificates := middle.certificates ++
          [HilbertLineCertificateCode.modusPonens
            implicationIndex premiseIndex]
        trace := by
          simpa [witness.h_conclusion] using
            (FSCheckedHilbertTrace.modusPonens
              middle.trace implicationIndex premiseIndex
              witness.h_implication witness.h_premise
              witness.h_premise_earlier)
      }
      have hOne :
          fs_replay_rows enumeration freeBase middle
              [lastRow]
              [HilbertLineCertificateCode.modusPonens
                implicationIndex premiseIndex] =
            some next := by
        simp [fs_replay_rows, fs_replay_row,
          fs_replay_modus_ponens_row, hCheck, next]
      refine ⟨next, ?_, ?_, ?_⟩
      · rw [hRowsSplit]
        exact
          fs_replay_rows_append
            enumeration freeBase hReplay hOne
      · simp [next, hMiddleProof, hLast]
      · simp [next, hMiddleCertificates]

/-- 从 natural-number proof code 执行完整的有限 checked replay。 -/
def fs_replay_code
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    (proofCode : Nat) :
    Option (FSReplayState enumeration proofCode) :=
  let decoded := fs_certified_proof_code_decode proofCode
  match decoded.2 with
  | some certificates =>
      fs_replay_raw_rows
        enumeration proofCode
        (fs_replay_nil enumeration proofCode)
        decoded.1 certificates
  | none =>
      none

/-- checked replay 成功后，每一条回放行都确实可由目标理论推出。 -/
theorem fs_replay_code_sound
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    {proofCode : Nat}
    {state : FSReplayState enumeration proofCode}
    {formula : SetFormula}
    (hFormula : formula ∈ state.proof) :
    HilbertDerives theory formula :=
  state.trace.derives_of_mem
    (fun hCheck => fs_logical_axiom_check_sound hCheck)
    hFormula

end Rosser
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
