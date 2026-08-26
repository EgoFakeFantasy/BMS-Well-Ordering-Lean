import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedProofCodeEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Diagonal
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Support
import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency

/-!
# 有限证明码反射与 Rosser 纯句法终局

本模块只保留 Rosser 论证真正需要的有限接口：

* 带显式证书 payload 的对象层比较公式；
* 纯 Hilbert 句法上的一致性终局。

本模块只处理对象层有限序列、固定点和有限代码比较。
checked replay 的证明码关系位于 `CheckedCompleteness`，这里仅保留对象层
Rosser 公式和纯句法终局所需的固定接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace Rosser

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 公式代码见证与末项证明码 -/

/-- 一个公式同时携带 token quotation、对象 quotation 以及可用性证明。 -/
structure FormulaCodeWitness (formula : SetFormula) where
  tokens : List Nat
  code : SetTerm
  h_admissible : Formula.Admissible formula
  h_tokens : GodelQuotation.Numbered.quote_tokens? formula = some tokens
  h_code : GodelQuotation.Numbered.quote? formula = some code

/-- quotation 失败时使用空序列的总化行 token 函数。 -/
def certified_row_tokens (formula : SetFormula) : List Nat :=
  (GodelQuotation.Numbered.quote_tokens? formula).getD []

@[simp]
theorem certified_row_tokens_eq
    {formula : SetFormula} (witness : FormulaCodeWitness formula) :
    certified_row_tokens formula = witness.tokens := by
  simp [certified_row_tokens, witness.h_tokens]

/-- 否定公式的 quotation 代码由公式代码的否定构造子直接给出。 -/
theorem quote_negation_code
    {formula : SetFormula} {code : SetTerm}
    (hCode : GodelQuotation.Numbered.quote? formula = some code) :
    GodelQuotation.Numbered.quote? (Formula.neg formula) =
      some (neg_codeₘ(code)) := by
  have hCode' :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          [] 0
          (Formula.hilbertize SetSort.set formula) =
        some code := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using hCode
  change Option.bind
      (GodelQuotation.Numbered.quote_hilbert_with?
        GodelQuotation.free_name GodelQuotation.bound_name [] 0
        (Formula.hilbertize SetSort.set formula))
      (fun bodyCode => some (neg_codeₘ(bodyCode))) =
    some (neg_codeₘ(code))
  rw [hCode']
  rfl

/-- 蕴含公式的 quotation 代码由两端代码的蕴含构造子直接给出。 -/
theorem quote_implication_code
    {left right : SetFormula}
    {leftCode rightCode : SetTerm}
    (hLeft :
      GodelQuotation.Numbered.quote? left = some leftCode)
    (hRight :
      GodelQuotation.Numbered.quote? right = some rightCode) :
    GodelQuotation.Numbered.quote? (Formula.imp left right) =
      some (imp_codeₘ(leftCode, rightCode)) := by
  have hLeft' :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          [] 0
          (Formula.hilbertize SetSort.set left) =
        some leftCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using hLeft
  have hRight' :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          [] 0
          (Formula.hilbertize SetSort.set right) =
        some rightCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using hRight
  change Option.bind
      (GodelQuotation.Numbered.quote_hilbert_with?
        GodelQuotation.free_name GodelQuotation.bound_name [] 0
        (Formula.hilbertize SetSort.set left))
      (fun leftCode =>
        Option.bind
          (GodelQuotation.Numbered.quote_hilbert_with?
            GodelQuotation.free_name GodelQuotation.bound_name [] 0
            (Formula.hilbertize SetSort.set right))
          (fun rightCode =>
            some (imp_codeₘ(leftCode, rightCode)))) =
    some (imp_codeₘ(leftCode, rightCode))
  rw [hLeft', hRight']
  rfl

/-- 每个可用 FormalSystem 公式都有一个具体的代码见证。 -/
theorem formula_code_witness_exists
    {formula : SetFormula} (hFormula : Formula.Admissible formula) :
    Nonempty (FormulaCodeWitness formula) := by
  rcases GodelQuotation.Numbered.quote_tokens?_exists hFormula with
    ⟨tokens, hTokens⟩
  rcases GodelQuotation.Numbered.quote?_exists hFormula with
    ⟨code, hCode⟩
  exact ⟨{
    tokens := tokens
    code := code
    h_admissible := hFormula
    h_tokens := hTokens
    h_code := hCode
  }⟩

/-! ## 带固定编号的对象层 Rosser 比较 -/

/--
证书化证明码条件的固定编号包装。

`base + 20` 至 `base + 23` 单独留给逐行检查，`base + 11` 至
`base + 16` 留给逻辑证书内部回放；其余证明码见证位于 `base` 至
`base + 10`。这样具体 verifier 可以从逐行编号之后继续分配内部编号，
而不会与证明序列编码轨迹发生碰撞。
-/
def proof_condition
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion : SetTerm)
    (base : FreeVarId) : SetFormula :=
  CertifiedProof.code_condition_with_ids
    verifier proofCode conclusion
    base (base + 1) (base + 2) (base + 3)
    (base + 20) (base + 23)
    (base + 11) (base + 12) (base + 13)
    (base + 14) (base + 15) (base + 16)
    (base + 21) (base + 22)
    (base + 4) (base + 5) (base + 6)
    (base + 7) (base + 8) (base + 9)
    (base + 10)

/--
固定编号证明码条件在四个存在见证全部打开后的公式体。

该命名接口供有限反演统一消费；它不改变公开证明码谓词，也不附加
verifier 之外的证明论前提。
-/
def proof_witness
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion sequence certificates
      formulaCode certificateCode : SetTerm)
    (base : FreeVarId) : SetFormula :=
  (((CertifiedProof.sequence_condition_with_ids
        verifier sequence certificates
        (base + 20) (base + 23)
        (base + 11) (base + 12) (base + 13)
        (base + 14) (base + 15) (base + 16)
        (base + 21) (base + 22) ∧ₘ
      proof_sequence_code_condition_with_ids
        sequence formulaCode
        (base + 4) (base + 5) (base + 6)
        (base + 7) (base + 8)) ∧ₘ
      nat_sequence_code_condition_with_ids
        certificates certificateCode
        (base + 9) (base + 10)) ∧ₘ
    ((CertifiedProof.proof_code_component_bound
        proofCode formulaCode ∧ₘ
      CertifiedProof.proof_code_component_bound
        proofCode certificateCode) ∧ₘ
      ((proofCode ≐ₘ
          godel_pairₘ(⟨formulaCode, certificateCode⟩ₘ)) ∧ₘ
        proof_sequence_terminal_condition
          sequence conclusion)))

theorem proof_witness_admissible
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion sequence certificates
      formulaCode certificateCode : SetTerm)
    (base : FreeVarId)
    (hProofCode : Term.Admissible proofCode SetSort.set)
    (hConclusion : Term.Admissible conclusion SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificateCode : Term.Admissible certificateCode SetSort.set) :
    Formula.Admissible
      (proof_witness
        verifier proofCode conclusion sequence certificates
        formulaCode certificateCode base) := by
  have hSequenceCondition :=
    CertifiedProof.sequence_condition_with_ids_admissible
      verifier sequence certificates
      (base + 20) (base + 23)
      (base + 11) (base + 12) (base + 13)
      (base + 14) (base + 15) (base + 16)
      (base + 21) (base + 22)
      hSequence hCertificates
  have hProofSequenceCode :=
    proof_sequence_code_condition_with_ids_admissible
      sequence formulaCode
      (base + 4) (base + 5) (base + 6)
      (base + 7) (base + 8)
      hSequence hFormulaCode
  have hCertificateSequenceCode :=
    nat_sequence_code_condition_with_ids_admissible
      certificates certificateCode
      (base + 9) (base + 10)
      hCertificates hCertificateCode
  have hProofCodeSuccessor :=
    successor_term_admissible proofCode hProofCode
  have hFormulaBound :
      Formula.Admissible
        (CertifiedProof.proof_code_component_bound
          proofCode formulaCode) := by
    simpa [CertifiedProof.proof_code_component_bound] using
      membership_formula_admissible
        hFormulaCode hProofCodeSuccessor
  have hCertificateBound :
      Formula.Admissible
        (CertifiedProof.proof_code_component_bound
          proofCode certificateCode) := by
    simpa [CertifiedProof.proof_code_component_bound] using
      membership_formula_admissible
        hCertificateCode hProofCodeSuccessor
  have hPair :
      Formula.Admissible
        (proofCode ≐ₘ
          godel_pairₘ(⟨formulaCode, certificateCode⟩ₘ)) :=
    Formula.Admissible.equal hProofCode
      (godel_pairing_term_admissible
        (⟨formulaCode, certificateCode⟩ₘ)
        (ordered_pair_term_admissible
          formulaCode certificateCode
          hFormulaCode hCertificateCode))
  have hTerminal :=
    proof_sequence_terminal_condition_admissible
      sequence conclusion hSequence hConclusion
  simpa [proof_witness] using
    Formula.Admissible.conj
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          hSequenceCondition hProofSequenceCode)
        hCertificateSequenceCode)
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          hFormulaBound hCertificateBound)
        (Formula.Admissible.conj hPair hTerminal))

/-- 固定编号证明码条件展开为四个见证及其命名公式体。 -/
theorem proof_condition_eq_witness
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion : SetTerm)
    (base : FreeVarId) :
    proof_condition
        verifier proofCode conclusion base =
      ((formula_codeₘ(conclusion) ∧ₘ proofCode ∈ₘ ωₘ) ∧ₘ
        (∃ₘ[SetSort.set, base],
          (x#base ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
            (∃ₘ[SetSort.set, base + 1],
              (x#(base + 1) ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
                (∃ₘ[SetSort.set, base + 2],
                  CertifiedProof.proof_code_component_bound
                      proofCode (x#(base + 2)) ∧ₘ
                    (∃ₘ[SetSort.set, base + 3],
                      CertifiedProof.proof_code_component_bound
                          proofCode (x#(base + 3)) ∧ₘ
                        proof_witness
                          verifier proofCode conclusion
                          (x#base) (x#(base + 1))
                          (x#(base + 2)) (x#(base + 3))
                          base))))) := by
  rfl

theorem proof_condition_admissible
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion : SetTerm)
    (base : FreeVarId)
    (hProofCode : Term.Admissible proofCode SetSort.set)
    (hConclusion : Term.Admissible conclusion SetSort.set) :
    Formula.Admissible
      (proof_condition
        verifier proofCode conclusion base) := by
  exact CertifiedProof.code_condition_with_ids_admissible
    verifier proofCode conclusion
    base (base + 1) (base + 2) (base + 3)
    (base + 20) (base + 23)
    (base + 11) (base + 12) (base + 13)
    (base + 14) (base + 15) (base + 16)
    (base + 21) (base + 22)
    (base + 4) (base + 5) (base + 6)
    (base + 7) (base + 8) (base + 9)
    (base + 10)
    hProofCode hConclusion

private theorem term_mem_freeSupport_closeFreeAt_of_mem_of_ne
    (freeVariable : FreeVariable (signature))
    (target : signature.SortSymbol)
    (id : FreeVarId)
    (depth : Nat)
    (term : SetTerm)
    (hMember : freeVariable ∈ Term.freeSupport term)
    (hNe : freeVariable ≠ (target, id)) :
    freeVariable ∈
      Term.freeSupport
        (Term.closeFreeAt target id depth term) := by
  refine Term.rec (motive_1 := fun term =>
      freeVariable ∈ Term.freeSupport term →
        freeVariable ≠ (target, id) →
          freeVariable ∈
            Term.freeSupport
              (Term.closeFreeAt target id depth term))
    (motive_2 := fun terms =>
      freeVariable ∈ Term.freeSupportList terms →
        freeVariable ≠ (target, id) →
          freeVariable ∈
            Term.freeSupportList
              (terms.map (Term.closeFreeAt target id depth)))
    ?_ ?_ ?_ ?_ term hMember hNe
  · intro sourceVar hMember hNe
    cases sourceVar with
    | bvar sort index =>
        simp [Term.freeSupport] at hMember
    | fvar sort freeId =>
        by_cases hClose : sort = target ∧ freeId = id
        · exact False.elim <| hNe (by
            have hVariable :
                freeVariable = (sort, freeId) :=
              List.mem_singleton.mp hMember
            exact hVariable.trans (by
              rcases hClose with ⟨rfl, rfl⟩
              rfl))
        · simpa [Term.closeFreeAt, Term.freeSupport, hClose] using hMember
  · intro function arguments ih hMember hNe
    simpa [Term.closeFreeAt, Term.freeSupport] using
      ih hMember hNe
  · intro hMember hNe
    simp [Term.freeSupportList] at hMember
  · intro head tail ihHead ihTail hMember hNe
    rcases List.mem_append.mp hMember with hHead | hTail
    · exact List.mem_append.mpr (Or.inl <|
        ihHead hHead hNe)
    · exact List.mem_append.mpr (Or.inr <|
        ihTail hTail hNe)

private theorem formula_mem_freeSupport_closeFreeAt_of_mem_of_ne
    (freeVariable : FreeVariable (signature))
    (target : signature.SortSymbol)
    (id : FreeVarId)
    (depth : Nat)
    (formula : SetFormula)
    (hMember : freeVariable ∈ Formula.freeSupport formula)
    (hNe : freeVariable ≠ (target, id)) :
    freeVariable ∈
      Formula.freeSupport
        (Formula.closeFreeAt target id depth formula) := by
  revert hMember hNe
  induction formula generalizing depth with
  | falsum =>
      intro hMember hNe
      simp [Formula.freeSupport] at hMember
  | truth =>
      intro hMember hNe
      simp [Formula.freeSupport] at hMember
  | rel relation arguments =>
      intro hMember hNe
      change freeVariable ∈ Term.freeSupportList arguments at hMember
      change freeVariable ∈
        Term.freeSupportList
          (arguments.map (Term.closeFreeAt target id depth))
      revert hMember hNe
      induction arguments with
      | nil =>
          intro hNe hMember
          exact False.elim (List.not_mem_nil hMember)
      | cons head tail ihTail =>
          intro hNe hMember
          rcases List.mem_append.mp hMember with hHead | hTail
          · exact List.mem_append.mpr (Or.inl <|
              term_mem_freeSupport_closeFreeAt_of_mem_of_ne
                freeVariable target id depth head hHead hNe)
          · exact List.mem_append.mpr (Or.inr <|
              ihTail hNe hTail)
  | equal left right =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          term_mem_freeSupport_closeFreeAt_of_mem_of_ne
            freeVariable target id depth left hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          term_mem_freeSupport_closeFreeAt_of_mem_of_ne
            freeVariable target id depth right hRight hNe)
  | neg body ih =>
      intro hMember hNe
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih depth hMember hNe
  | conj left right ihLeft ihRight =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          ihLeft depth hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          ihRight depth hRight hNe)
  | disj left right ihLeft ihRight =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          ihLeft depth hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          ihRight depth hRight hNe)
  | imp left right ihLeft ihRight =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          ihLeft depth hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          ihRight depth hRight hNe)
  | iff left right ihLeft ihRight =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          ihLeft depth hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          ihRight depth hRight hNe)
  | forallE sort body ih =>
      intro hMember hNe
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih (if sort = target then depth + 1 else depth) hMember hNe
  | existsE sort body ih =>
      intro hMember hNe
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih (if sort = target then depth + 1 else depth) hMember hNe

private theorem formula_mem_freeSupport_closeFreeAt_iff
    (freeVariable : FreeVariable (signature))
    (target : signature.SortSymbol)
    (id : FreeVarId)
    (depth : Nat)
    (formula : SetFormula) :
    freeVariable ∈
        Formula.freeSupport
          (Formula.closeFreeAt target id depth formula) ↔
      freeVariable ∈ Formula.freeSupport formula ∧
        freeVariable ≠ (target, id) := by
  constructor
  · intro hMember
    refine ⟨?_, ?_⟩
    · by_cases hFresh : freeVariable ∈ Formula.freeSupport formula
      · exact hFresh
      · exact False.elim <|
          (Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            freeVariable target id depth formula hFresh) hMember
    · intro hEqual
      subst hEqual
      exact Formula.not_mem_freeSupport_closeFreeAt
        target id depth formula hMember
  · intro hMember
    exact formula_mem_freeSupport_closeFreeAt_of_mem_of_ne
      freeVariable target id depth formula hMember.1 hMember.2

private theorem term_mem_freeSupport_closeFreeAt_iff
    (freeVariable : FreeVariable (signature))
    (target : signature.SortSymbol)
    (id : FreeVarId)
    (depth : Nat)
    (term : SetTerm) :
    freeVariable ∈
        Term.freeSupport
          (Term.closeFreeAt target id depth term) ↔
      freeVariable ∈ Term.freeSupport term ∧
        freeVariable ≠ (target, id) := by
  constructor
  · intro hMember
    refine ⟨?_, ?_⟩
    · by_cases hFresh : freeVariable ∈ Term.freeSupport term
      · exact hFresh
      · exact False.elim <|
          (Term.not_mem_freeSupport_closeFreeAt_of_not_mem
            freeVariable target id depth term hFresh) hMember
    · intro hEqual
      subst hEqual
      exact Term.not_mem_freeSupport_closeFreeAt
        target id depth term hMember
  · intro hMember
    exact term_mem_freeSupport_closeFreeAt_of_mem_of_ne
      freeVariable target id depth term hMember.1 hMember.2

@[simp] private theorem term_freeSupport_app_eq
    (function : signature.FuncSymbol)
    (arguments : List SetTerm) :
    Term.freeSupport (Term.app function arguments) =
      Term.freeSupportList arguments := by
  simp [Term.freeSupport]

private theorem term_freeSupport_function_application
    (left right : SetTerm)
    (freeVariable : FreeVariable (signature))
    (hMember :
      freeVariable ∈
        Term.freeSupport (left ·ₘ right)) :
    freeVariable ∈ Term.freeSupport left ∨
      freeVariable ∈ Term.freeSupport right := by
  simpa [function_application_term, Term.freeSupport,
    Term.freeSupportList] using hMember

private theorem term_freeSupport_fvar
    (id : FreeVarId)
    (freeVariable : FreeVariable (signature))
    (hMember :
      freeVariable ∈
        Term.freeSupport
          (Term.var (Var.fvar SetSort.set id))) :
    freeVariable = (SetSort.set, id) := by
  simpa [Term.freeSupport] using hMember

@[simp] private theorem term_freeSupport_fvar_eq
    (sort : signature.SortSymbol)
    (id : FreeVarId) :
    Term.freeSupport
        (Term.var (Var.fvar sort id)) =
      [(sort, id)] := by
  simp [Term.freeSupport]

@[simp] private theorem term_mem_freeSupport_fvar_iff
    (freeVariable : FreeVariable (signature))
    (sort : signature.SortSymbol)
    (id : FreeVarId) :
    freeVariable ∈
        Term.freeSupport
          (Term.var (Var.fvar sort id)) ↔
      freeVariable = (sort, id) := by
  simp [Term.freeSupport]

theorem proof_condition_support
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion : SetTerm)
    (base : FreeVarId)
    (hFormulaSupport :
      ∀ formula freeVariable,
        freeVariable ∈ Formula.freeSupport
            (verifier.formula_condition formula) →
        freeVariable ∈ Term.freeSupport formula)
    (hVerifierSupport :
      ∀ formula certificate freeVariable,
        freeVariable ∈ Formula.freeSupport
            (verifier.condition formula certificate) →
        freeVariable ∈ Term.freeSupport formula ∨
          freeVariable ∈ Term.freeSupport certificate) :
    ∀ freeVariable,
      freeVariable ∈ Formula.freeSupport
          (proof_condition
            verifier proofCode conclusion base) →
      freeVariable ∈ Term.freeSupport proofCode ∨
        freeVariable ∈ Term.freeSupport conclusion := by
  have hVerifierApplicationSupport
      (left right certificate : SetTerm)
      (freeVariable : FreeVariable (signature))
      (hMember :
        freeVariable ∈
          Formula.freeSupport
            (verifier.condition (left ·ₘ right) certificate)) :
      freeVariable ∈ Term.freeSupport left ∨
        freeVariable ∈ Term.freeSupport right ∨
          freeVariable ∈ Term.freeSupport certificate := by
    rcases hVerifierSupport
        (left ·ₘ right) certificate freeVariable hMember with
      hFormula | hCertificate
    · rcases term_freeSupport_function_application
          left right freeVariable hFormula with
        hLeft | hRight
      · exact Or.inl hLeft
      · exact Or.inr (Or.inl hRight)
    · exact Or.inr (Or.inr hCertificate)
  have hFormulaApplicationSupport
      (left right : SetTerm)
      (freeVariable : FreeVariable (signature))
      (hMember :
        freeVariable ∈
          Formula.freeSupport
            (verifier.formula_condition (left ·ₘ right))) :
      freeVariable ∈ Term.freeSupport left ∨
        freeVariable ∈ Term.freeSupport right := by
    exact term_freeSupport_function_application
      left right freeVariable
      (hFormulaSupport
        (left ·ₘ right) freeVariable hMember)
  have hFormulaLineVariableSupport
      (leftId rightId : FreeVarId)
      (freeVariable : FreeVariable (signature))
      (hMember :
        freeVariable ∈
            Formula.freeSupport
              (verifier.formula_condition
                ((x#leftId) ·ₘ (x#rightId))) ∧
          freeVariable ≠ (SetSort.set, rightId)) :
      freeVariable = (SetSort.set, leftId) := by
    rcases hFormulaApplicationSupport
        (x#leftId) (x#rightId)
        freeVariable hMember.1 with
      hLeft | hRight
    · exact term_freeSupport_fvar
        leftId freeVariable hLeft
    · exact False.elim <|
        hMember.2
          (term_freeSupport_fvar
            rightId freeVariable hRight)
  have hVerifierLineSupport
      (left right certificate : SetTerm)
      (certificateId indexId : FreeVarId)
      (freeVariable : FreeVariable (signature))
      (hMember :
        (freeVariable ∈
            Formula.freeSupport
              (verifier.condition (left ·ₘ right) certificate) ∧
          freeVariable ≠ (SetSort.set, certificateId)) ∧
        freeVariable ≠ (SetSort.set, indexId)) :
      freeVariable ∈ Term.freeSupport left ∨
        freeVariable ∈ Term.freeSupport right ∨
          freeVariable ∈ Term.freeSupport certificate := by
    exact hVerifierApplicationSupport
      left right certificate freeVariable hMember.1.1
  have hLogicalLineVariableSupport
      (leftId rightId certificateId
        logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
        logicalLineIndexId logicalCodeTraceId logicalCodeIndexId : FreeVarId)
      (freeVariable : FreeVariable (signature))
      (hMember :
        (freeVariable ∈
              Formula.freeSupport
                (CertifiedProof.logical_certificate_condition_with_ids
                  ((x#leftId) ·ₘ (x#rightId)) (x#certificateId)
                  logicalCertificateSequenceId logicalFormulaTraceId
                  logicalLastIndexId logicalLineIndexId
                  logicalCodeTraceId logicalCodeIndexId) ∧
            freeVariable ≠ (SetSort.set, certificateId)) ∧
          freeVariable ≠ (SetSort.set, rightId)) :
      freeVariable = (SetSort.set, leftId) := by
    rcases
        CertifiedProof.logical_certificate_condition_with_ids_freeSupport_subset
          ((x#leftId) ·ₘ (x#rightId)) (x#certificateId)
          logicalCertificateSequenceId logicalFormulaTraceId
          logicalLastIndexId logicalLineIndexId
          logicalCodeTraceId logicalCodeIndexId
          freeVariable hMember.1.1 with
      hFormula | hCertificate
    · rcases term_freeSupport_function_application
          (x#leftId) (x#rightId) freeVariable hFormula with
        hLeft | hRight
      · exact term_freeSupport_fvar leftId freeVariable hLeft
      · exact False.elim <|
          hMember.2
            (term_freeSupport_fvar rightId freeVariable hRight)
    · exact False.elim <|
        hMember.1.2
          (term_freeSupport_fvar certificateId freeVariable hCertificate)
  have hVerifierLineVariableSupport
      (leftId rightId certificateId indexId : FreeVarId)
      (freeVariable : FreeVariable (signature))
      (hMember :
        (freeVariable ∈
            Formula.freeSupport
              (verifier.condition
                ((x#leftId) ·ₘ (x#rightId)) (x#certificateId)) ∧
          freeVariable ≠ (SetSort.set, certificateId)) ∧
        freeVariable ≠ (SetSort.set, indexId)) :
      freeVariable = (SetSort.set, leftId) ∨
        freeVariable = (SetSort.set, rightId) ∨
          freeVariable = (SetSort.set, certificateId) := by
    rcases hVerifierLineSupport
        (x#leftId) (x#rightId) (x#certificateId)
        certificateId indexId freeVariable hMember with
      hLeft | hRight | hCertificate
    · exact Or.inl <|
        term_freeSupport_fvar leftId freeVariable hLeft
    · exact Or.inr (Or.inl <|
        term_freeSupport_fvar rightId freeVariable hRight)
    · exact Or.inr (Or.inr <|
        term_freeSupport_fvar certificateId freeVariable hCertificate)
  clear hFormulaSupport hVerifierSupport
  clear hFormulaApplicationSupport
  clear hVerifierLineSupport hVerifierApplicationSupport
  have hCloseSubset
      (freeVariable : FreeVariable (signature))
      (target : signature.SortSymbol)
      (id : FreeVarId)
      (depth : Nat)
      (formula : SetFormula)
      (hMember :
        freeVariable ∈
          Formula.freeSupport
            (Formula.closeFreeAt target id depth formula)) :
      freeVariable ∈ Formula.freeSupport formula := by
    by_cases hFresh : freeVariable ∈ Formula.freeSupport formula
    · exact hFresh
    · exact False.elim <|
        (Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
          freeVariable target id depth formula hFresh) hMember
  have hTermCloseSubset
      (freeVariable : FreeVariable (signature))
      (target : signature.SortSymbol)
      (id : FreeVarId)
      (depth : Nat)
      (term : SetTerm)
      (hMember :
        freeVariable ∈
          Term.freeSupport
            (Term.closeFreeAt target id depth term)) :
      freeVariable ∈ Term.freeSupport term := by
    by_cases hFresh : freeVariable ∈ Term.freeSupport term
    · exact hFresh
    · exact False.elim <|
        (Term.not_mem_freeSupport_closeFreeAt_of_not_mem
          freeVariable target id depth term hFresh) hMember
  have hCloseSupport
      (freeVariable : FreeVariable (signature))
      (target : signature.SortSymbol)
      (id : FreeVarId)
      (depth : Nat)
      (formula : SetFormula)
      (hMember :
        freeVariable ∈
          Formula.freeSupport
            (Formula.closeFreeAt target id depth formula)) :
      freeVariable ≠ (target, id) ∧
        freeVariable ∈ Formula.freeSupport formula := by
    constructor
    · intro hEqual
      subst hEqual
      exact Formula.not_mem_freeSupport_closeFreeAt
        target id depth formula hMember
    · exact hCloseSubset
        freeVariable target id depth formula hMember
  have hTermSupport
      (freeVariable : FreeVariable (signature))
      (target : signature.SortSymbol)
      (id : FreeVarId)
      (depth : Nat)
      (term : SetTerm)
      (hMember :
        freeVariable ∈
          Term.freeSupport
            (Term.closeFreeAt target id depth term)) :
      freeVariable ≠ (target, id) ∧
        freeVariable ∈ Term.freeSupport term := by
    constructor
    · intro hEqual
      subst hEqual
      exact Term.not_mem_freeSupport_closeFreeAt
        target id depth term hMember
    · exact hTermCloseSubset
        freeVariable target id depth term hMember
  intro freeVariable hMember
  simp only [proof_condition,
    CertifiedProof.code_condition_with_ids,
    CertifiedProof.proof_code_component_bound,
    CertifiedProof.sequence_condition_with_ids,
    CertifiedProof.line_condition_with_ids,
    CertifiedProof.theory_certificate_line_condition_with_id,
    CertifiedProof.modus_ponens_line_condition_with_ids,
    proof_sequence_code_condition_with_ids,
    proof_sequence_code_step_condition_with_ids,
    nat_sequence_code_condition_with_ids,
    sequence_domain_code_bound,
    nat_sequence_value_code_bound_with_id,
    sequence_trace_code_bound_with_id,
    nat_sequence_code_step_condition,
    Formula.freeSupport,
    Term.freeSupport,
    Term.freeSupportList,
    List.mem_append,
    List.not_mem_nil] at hMember
  rcases hMember with hMember | hMember
  · grind
  · have hSupport :=
      hCloseSupport freeVariable SetSort.set base 0 _ hMember
    clear hMember
    rcases hSupport with ⟨hNe0, hMember⟩
    simp only [Formula.freeSupport] at hMember
    rcases List.mem_append.mp hMember with
      hSequenceGuard | hMember
    · have hEqual :
          freeVariable = (SetSort.set, base) := by
        simpa [Term.freeSupportList, Term.freeSupport] using
          hSequenceGuard
      exact False.elim (hNe0 hEqual)
    have hSupport :=
      hCloseSupport freeVariable SetSort.set (base + 1) 0 _ hMember
    clear hMember
    rcases hSupport with ⟨hNe1, hMember⟩
    simp only [Formula.freeSupport] at hMember
    rcases List.mem_append.mp hMember with
      hCertificateGuard | hMember
    · have hEqual :
          freeVariable = (SetSort.set, base + 1) := by
        simpa [Term.freeSupportList, Term.freeSupport] using
          hCertificateGuard
      exact False.elim (hNe1 hEqual)
    have hSupport :=
      hCloseSupport freeVariable SetSort.set (base + 2) 0 _ hMember
    clear hMember
    rcases hSupport with ⟨hNe2, hMember⟩
    simp only [Formula.freeSupport] at hMember
    rcases List.mem_append.mp hMember with
      hFormulaCodeGuard | hMember
    · have hGuardSupport :
          freeVariable = (SetSort.set, base + 2) ∨
            freeVariable ∈ Term.freeSupport proofCode := by
        simpa [CertifiedProof.proof_code_component_bound,
          Term.freeSupportList, Term.freeSupport] using
          hFormulaCodeGuard
      rcases hGuardSupport with hEqual | hProofCode
      · exact False.elim (hNe2 hEqual)
      · exact Or.inl hProofCode
    have hSupport :=
      hCloseSupport freeVariable SetSort.set (base + 3) 0 _ hMember
    clear hMember
    rcases hSupport with ⟨hNe3, hMember⟩
    simp only [Formula.freeSupport, List.mem_append] at hMember
    rcases hMember with hCertificateCodeGuard | hMember
    · have hGuardSupport :
          freeVariable = (SetSort.set, base + 3) ∨
            freeVariable ∈ Term.freeSupport proofCode := by
        simpa [CertifiedProof.proof_code_component_bound,
          Term.freeSupportList, Term.freeSupport] using
          hCertificateCodeGuard
      rcases hGuardSupport with hEqual | hProofCode
      · exact False.elim (hNe3 hEqual)
      · exact Or.inl hProofCode
    simp [Formula.freeSupport, Term.freeSupport, Term.freeSupportList,
      Formula.closeFreeAt, Term.closeFreeAt,
      Formula.next_depth,
      finite_numeral_term,
      CertifiedProof.certificate_payload_bound,
      CertifiedProof.logical_certificate_code,
      CertifiedProof.theory_certificate_code,
      CertifiedProof.modus_ponens_certificate_code,
      godel_pairing_term, ordered_pair_term,
      proof_sequence_terminal_condition,
      formula_mem_freeSupport_closeFreeAt_iff,] at hMember
    have hVerifierLineSpecial :=
      hVerifierLineVariableSupport
        base (base + 20) (base + 23) (base + 20) freeVariable
    have hFormulaLineSpecial :=
      hFormulaLineVariableSupport
        base (base + 20) freeVariable
    have hLogicalLineSpecial :=
      hLogicalLineVariableSupport
        base (base + 20) (base + 23)
        (base + 11) (base + 12) (base + 13)
        (base + 14) (base + 15) (base + 16)
        freeVariable
    rcases freeVariable with ⟨freeSort, freeId⟩
    simp only [Prod.mk.injEq] at hMember hNe0 hNe1 hNe2 hNe3 hFormulaLineSpecial hVerifierLineSpecial hLogicalLineSpecial
    by_cases hSort : freeSort = SetSort.set
    · subst freeSort
      simp_all
      have hNoLogical :
          ¬(((SetSort.set, freeId) ∈
                  Formula.freeSupport
                    (CertifiedProof.logical_certificate_condition_with_ids
                      (x#base ·ₘ x#(base + 20)) (x#(base + 23))
                      (base + 11) (base + 12) (base + 13)
                      (base + 14) (base + 15) (base + 16)) ∧
                ¬freeId = base + 23) ∧
              ¬freeId = base + 20) := by
        intro hLogical
        rcases hLogical with ⟨⟨hSupport, h23⟩, h20⟩
        have h23' :
            (SetSort.set, freeId) ≠
              (SetSort.set, base + 23) := by
          intro hEqual
          exact h23 (congrArg Prod.snd hEqual)
        have h20' :
            (SetSort.set, freeId) ≠
              (SetSort.set, base + 20) := by
          intro hEqual
          exact h20 (congrArg Prod.snd hEqual)
        have hBase :=
          hLogicalLineSpecial hSupport h23' h20'
        exact hNe0 (congrArg Prod.snd hBase)
      have hNoFormula :
          ¬((SetSort.set, freeId) ∈
                Formula.freeSupport
                  (verifier.formula_condition
                    (x#base ·ₘ x#(base + 20))) ∧
              ¬freeId = base + 20) := by
        intro hFormula
        have h20' :
            (SetSort.set, freeId) ≠
              (SetSort.set, base + 20) := by
          intro hEqual
          exact hFormula.2
            (congrArg Prod.snd hEqual)
        have hBase :=
          hFormulaLineSpecial hFormula.1 h20'
        exact hNe0 (congrArg Prod.snd hBase)
      have hNoVerifier :
          ¬(((SetSort.set, freeId) ∈
                  Formula.freeSupport
                    (verifier.condition
                      (x#base ·ₘ x#(base + 20)) (x#(base + 23))) ∧
                ¬freeId = base + 23) ∧
              ¬freeId = base + 20) := by
        intro hVerifier
        rcases hVerifier with ⟨⟨hSupport, h23⟩, h20⟩
        have h23' :
            (SetSort.set, freeId) ≠
              (SetSort.set, base + 23) := by
          intro hEqual
          exact h23 (congrArg Prod.snd hEqual)
        have h20' :
            (SetSort.set, freeId) ≠
              (SetSort.set, base + 20) := by
          intro hEqual
          exact h20 (congrArg Prod.snd hEqual)
        have hBase :=
          hVerifierLineSpecial hSupport h23' h20'
        exact hNe0 (congrArg Prod.snd hBase)
      exact Or.elim hMember
        (fun hLines =>
          Or.elim hLines
            (fun hFormula => False.elim (hNoFormula hFormula))
            (fun hCertificateLines =>
              Or.elim hCertificateLines
                (fun hLogical =>
                  False.elim (hNoLogical hLogical))
                (fun hVerifier =>
                  False.elim (hNoVerifier hVerifier))))
        (fun hResult => hResult)
    · have h23' :
          (freeSort, freeId) ≠
            (SetSort.set, base + 23) := by
        intro hEqual
        exact hSort (congrArg Prod.fst hEqual)
      have h20' :
          (freeSort, freeId) ≠
            (SetSort.set, base + 20) := by
        intro hEqual
        exact hSort (congrArg Prod.fst hEqual)
      simp only [hSort, false_and, false_or,
        not_false_eq_true, and_true, or_false] at hMember
      have hNoLogical :
          (freeSort, freeId) ∉
            Formula.freeSupport
              (CertifiedProof.logical_certificate_condition_with_ids
                (x#base ·ₘ x#(base + 20)) (x#(base + 23))
                (base + 11) (base + 12) (base + 13)
                (base + 14) (base + 15) (base + 16)) := by
        intro hSupport
        have hBase :=
          hLogicalLineSpecial
            ⟨⟨hSupport, h23'⟩, h20'⟩
        exact hSort (congrArg Prod.fst hBase)
      have hNoFormula :
          (freeSort, freeId) ∉
            Formula.freeSupport
              (verifier.formula_condition
                (x#base ·ₘ x#(base + 20))) := by
        intro hSupport
        have hBase :=
          hFormulaLineSpecial
            ⟨hSupport, h20'⟩
        exact hSort (congrArg Prod.fst hBase)
      have hNoVerifier :
          (freeSort, freeId) ∉
            Formula.freeSupport
              (verifier.condition
                (x#base ·ₘ x#(base + 20)) (x#(base + 23))) := by
        intro hSupport
        have hBase :=
          hVerifierLineSpecial
            ⟨⟨hSupport, h23'⟩, h20'⟩
        rcases hBase with hBase | hBase | hBase
        · exact hSort (congrArg Prod.fst hBase)
        · exact hSort (congrArg Prod.fst hBase)
        · exact hSort (congrArg Prod.fst hBase)
      exact Or.elim hMember
        (fun hLines =>
          Or.elim hLines
            (fun hFormula =>
              False.elim (hNoFormula hFormula))
            (fun hCertificateLines =>
              Or.elim hCertificateLines
                (fun hLogical =>
                  False.elim
                    (hNoLogical hLogical))
                (fun hVerifier =>
                  False.elim
                    (hNoVerifier hVerifier))))
        (fun hResult => by grind)

/--
重新闭合四个证明码见证后，见证体的自由支持退回完整证明码条件的自由支持。

因此，只要目标变量不同于四个见证号，且不出现在 proof code 与结论项中，
它也不会出现在打开后的见证体中。该接口避免下游重复展开 verifier。
-/
theorem proof_witness_fresh
    (verifier : ObjectCertificateVerifier)
    (proofCode conclusion : SetTerm)
    (base : FreeVarId)
    (target : FreeVariable signature)
    (hFormulaSupport :
      ∀ formula freeVariable,
        freeVariable ∈ Formula.freeSupport
            (verifier.formula_condition formula) →
        freeVariable ∈ Term.freeSupport formula)
    (hVerifierSupport :
      ∀ formula certificate freeVariable,
        freeVariable ∈ Formula.freeSupport
            (verifier.condition formula certificate) →
        freeVariable ∈ Term.freeSupport formula ∨
          freeVariable ∈ Term.freeSupport certificate)
    (hProofCodeFresh :
      target ∉ Term.freeSupport proofCode)
    (hConclusionFresh :
      target ∉ Term.freeSupport conclusion)
    (hSequenceNe :
      target ≠ (SetSort.set, base))
    (hCertificatesNe :
      target ≠ (SetSort.set, base + 1))
    (hFormulaCodeNe :
      target ≠ (SetSort.set, base + 2))
    (hCertificateCodeNe :
      target ≠ (SetSort.set, base + 3)) :
    target ∉
      Formula.freeSupport
        (proof_witness
          verifier proofCode conclusion
          (x#base) (x#(base + 1))
          (x#(base + 2)) (x#(base + 3))
          base) := by
  intro hMember
  have hBoundedCertificateCode :
      target ∈
        Formula.freeSupport
          (CertifiedProof.proof_code_component_bound
              proofCode (x#(base + 3)) ∧ₘ
            proof_witness
              verifier proofCode conclusion
              (x#base) (x#(base + 1))
              (x#(base + 2)) (x#(base + 3))
              base) := by
    simp only [Formula.freeSupport, List.mem_append]
    exact Or.inr hMember
  have hClosedCertificateCode :=
    formula_mem_freeSupport_closeFreeAt_of_mem_of_ne
      target SetSort.set (base + 3) 0 _
        hBoundedCertificateCode
        hCertificateCodeNe
  have hExistsCertificateCode :
      target ∈
        Formula.freeSupport
          (∃ₘ[SetSort.set, base + 3],
            CertifiedProof.proof_code_component_bound
                proofCode (x#(base + 3)) ∧ₘ
              proof_witness
                verifier proofCode conclusion
                (x#base) (x#(base + 1))
                (x#(base + 2)) (x#(base + 3))
                base) := by
    simpa [Formula.freeSupport] using hClosedCertificateCode
  have hBoundedFormulaCode :
      target ∈
        Formula.freeSupport
          (CertifiedProof.proof_code_component_bound
              proofCode (x#(base + 2)) ∧ₘ
            (∃ₘ[SetSort.set, base + 3],
              CertifiedProof.proof_code_component_bound
                  proofCode (x#(base + 3)) ∧ₘ
                proof_witness
                  verifier proofCode conclusion
                  (x#base) (x#(base + 1))
                  (x#(base + 2)) (x#(base + 3))
                  base)) := by
    simp only [Formula.freeSupport, List.mem_append]
    exact Or.inr hExistsCertificateCode
  have hClosedFormulaCode :=
    formula_mem_freeSupport_closeFreeAt_of_mem_of_ne
      target SetSort.set (base + 2) 0 _
        hBoundedFormulaCode hFormulaCodeNe
  have hExistsFormulaCode :
      target ∈
        Formula.freeSupport
          (∃ₘ[SetSort.set, base + 2],
            CertifiedProof.proof_code_component_bound
                proofCode (x#(base + 2)) ∧ₘ
              (∃ₘ[SetSort.set, base + 3],
                CertifiedProof.proof_code_component_bound
                    proofCode (x#(base + 3)) ∧ₘ
                  proof_witness
                    verifier proofCode conclusion
                    (x#base) (x#(base + 1))
                    (x#(base + 2)) (x#(base + 3))
                    base)) := by
    simpa [Formula.freeSupport] using hClosedFormulaCode
  have hBoundedCertificates :
      target ∈
        Formula.freeSupport
          ((x#(base + 1) ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
            (∃ₘ[SetSort.set, base + 2],
              CertifiedProof.proof_code_component_bound
                  proofCode (x#(base + 2)) ∧ₘ
                (∃ₘ[SetSort.set, base + 3],
                  CertifiedProof.proof_code_component_bound
                      proofCode (x#(base + 3)) ∧ₘ
                    proof_witness
                      verifier proofCode conclusion
                      (x#base) (x#(base + 1))
                      (x#(base + 2)) (x#(base + 3))
                      base))) := by
    simp only [Formula.freeSupport, List.mem_append]
    exact Or.inr hExistsFormulaCode
  have hClosedCertificates :=
    formula_mem_freeSupport_closeFreeAt_of_mem_of_ne
      target SetSort.set (base + 1) 0 _
        hBoundedCertificates hCertificatesNe
  have hExistsCertificates :
      target ∈
        Formula.freeSupport
          (∃ₘ[SetSort.set, base + 1],
            (x#(base + 1) ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
              (∃ₘ[SetSort.set, base + 2],
                CertifiedProof.proof_code_component_bound
                    proofCode (x#(base + 2)) ∧ₘ
                  (∃ₘ[SetSort.set, base + 3],
                    CertifiedProof.proof_code_component_bound
                        proofCode (x#(base + 3)) ∧ₘ
                      proof_witness
                        verifier proofCode conclusion
                        (x#base) (x#(base + 1))
                        (x#(base + 2)) (x#(base + 3))
                        base))) := by
    simpa [Formula.freeSupport] using hClosedCertificates
  have hBoundedSequence :
      target ∈
        Formula.freeSupport
          ((x#base ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
            (∃ₘ[SetSort.set, base + 1],
              (x#(base + 1) ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
                (∃ₘ[SetSort.set, base + 2],
                  CertifiedProof.proof_code_component_bound
                      proofCode (x#(base + 2)) ∧ₘ
                    (∃ₘ[SetSort.set, base + 3],
                      CertifiedProof.proof_code_component_bound
                          proofCode (x#(base + 3)) ∧ₘ
                        proof_witness
                          verifier proofCode conclusion
                          (x#base) (x#(base + 1))
                          (x#(base + 2)) (x#(base + 3))
                          base)))) := by
    simp only [Formula.freeSupport, List.mem_append]
    exact Or.inr hExistsCertificates
  have hClosedSequence :=
    formula_mem_freeSupport_closeFreeAt_of_mem_of_ne
      target SetSort.set base 0 _
        hBoundedSequence hSequenceNe
  have hQuantified :
      target ∈
        Formula.freeSupport
          (∃ₘ[SetSort.set, base],
            (x#base ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
              (∃ₘ[SetSort.set, base + 1],
                (x#(base + 1) ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
                  (∃ₘ[SetSort.set, base + 2],
                    CertifiedProof.proof_code_component_bound
                        proofCode (x#(base + 2)) ∧ₘ
                      (∃ₘ[SetSort.set, base + 3],
                        CertifiedProof.proof_code_component_bound
                            proofCode (x#(base + 3)) ∧ₘ
                          proof_witness
                            verifier proofCode conclusion
                            (x#base) (x#(base + 1))
                            (x#(base + 2)) (x#(base + 3))
                            base)))) := by
    simpa [Formula.freeSupport] using hClosedSequence
  have hConditionMember :
      target ∈
        Formula.freeSupport
          (proof_condition
            verifier proofCode conclusion base) := by
    rw [proof_condition_eq_witness]
    simp only [Formula.freeSupport, List.mem_append]
    exact Or.inr hQuantified
  rcases
      proof_condition_support
        verifier proofCode conclusion base
        hFormulaSupport hVerifierSupport
        target hConditionMember with
    hProofCode | hConclusion
  · exact hProofCodeFresh hProofCode
  · exact hConclusionFresh hConclusion

/-- 在上界以下不存在指定公式的证书化证明码。 -/
def no_smaller_condition
    (verifier : ObjectCertificateVerifier)
    (bound conclusion : SetTerm)
    (smallerCodeId conditionBase : FreeVarId) : SetFormula :=
  ∀ₘ[SetSort.set, smallerCodeId],
    (x#smallerCodeId ∈ₘ bound) ⟶ₘ
      ¬ₘ proof_condition
        verifier (x#smallerCodeId) conclusion conditionBase

theorem no_smaller_condition_admissible
    (verifier : ObjectCertificateVerifier)
    (bound conclusion : SetTerm)
    (smallerCodeId conditionBase : FreeVarId)
    (hBound : Term.Admissible bound SetSort.set)
    (hConclusion : Term.Admissible conclusion SetSort.set) :
    Formula.Admissible
      (no_smaller_condition
        verifier bound conclusion smallerCodeId conditionBase) := by
  have hSmallerCode :
      Term.Admissible (x#smallerCodeId) SetSort.set :=
    set_variable_admissible smallerCodeId
  have hBoundMembership :=
    membership_formula_admissible hSmallerCode hBound
  have hProofCode :=
    proof_condition_admissible
      verifier (x#smallerCodeId) conclusion conditionBase
      hSmallerCode hConclusion
  have hBody :=
    Formula.Admissible.imp hBoundMembership
      (Formula.Admissible.neg hProofCode)
  simpa [no_smaller_condition] using
    Formula.Admissible.forall_closeFreeAt
      SetSort.set smallerCodeId hBody

/-- 左侧有证明码、且不存在更小的右侧证明码。 -/
def comparison_condition
    (verifier : ObjectCertificateVerifier)
    (left right : SetTerm)
    (proofCodeId smallerCodeId conditionBase : FreeVarId) : SetFormula :=
  ∃ₘ[SetSort.set, proofCodeId],
    proof_condition
        verifier (x#proofCodeId) left conditionBase ∧ₘ
      no_smaller_condition
        verifier (x#proofCodeId) right
        smallerCodeId conditionBase

theorem comparison_condition_admissible
    (verifier : ObjectCertificateVerifier)
    (left right : SetTerm)
    (proofCodeId smallerCodeId conditionBase : FreeVarId)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible
      (comparison_condition
        verifier left right
        proofCodeId smallerCodeId conditionBase) := by
  have hProofCode :
      Term.Admissible (x#proofCodeId) SetSort.set :=
    set_variable_admissible proofCodeId
  have hPositive :=
    proof_condition_admissible
      verifier (x#proofCodeId) left conditionBase
      hProofCode hLeft
  have hNoSmaller :=
    no_smaller_condition_admissible
      verifier (x#proofCodeId) right
      smallerCodeId conditionBase
      hProofCode hRight
  exact Formula.Admissible.exists_closeFreeAt
    SetSort.set proofCodeId
    (Formula.Admissible.conj hPositive hNoSmaller)

/-- 用代码变量作为左式、其否定代码作为右式的 Rosser 可证明性体。 -/
def provability_body
    (verifier : ObjectCertificateVerifier)
    (codeId proofCodeId smallerCodeId conditionBase : FreeVarId) : SetFormula :=
  comparison_condition
    verifier (x#codeId) (neg_codeₘ(x#codeId))
    proofCodeId smallerCodeId conditionBase

theorem provability_body_admissible
    (verifier : ObjectCertificateVerifier)
    (codeId proofCodeId smallerCodeId conditionBase : FreeVarId) :
    Formula.Admissible
      (provability_body
        verifier codeId proofCodeId smallerCodeId conditionBase) := by
  simpa [provability_body] using
    comparison_condition_admissible
    verifier
    (x#codeId) (neg_codeₘ(x#codeId))
    proofCodeId smallerCodeId conditionBase
    (set_variable_admissible codeId)
    (negation_formula_code_term_admissible
      (x#codeId) (set_variable_admissible codeId))

/-! ## 纯句法 Rosser 终局 -/

/--
Rosser 论证最后一步的纯 Hilbert 句法形式。

所有算术比较、quotation 和内部化工作都已经被压缩到固定点等价式与两个内部化
蕴含中；本定理本身不引用模型、标准性或语义可靠性。
-/
theorem independent_of_fixed_point_internalization
    {proofTheory : SetTheory}
    {fixedPoint predicate : SetFormula}
    (hFixedPoint :
      HilbertDerives proofTheory
        (Formula.hilbert_iff fixedPoint (Formula.neg predicate)))
    (hPositiveInternalization :
      HilbertDerives proofTheory fixedPoint →
        HilbertDerives proofTheory predicate)
    (hNegativeInternalization :
      HilbertDerives proofTheory (Formula.neg fixedPoint) →
        HilbertDerives proofTheory (Formula.neg predicate))
    (hConsistent : Derives.Consistent proofTheory []) :
    (¬ HilbertDerives proofTheory fixedPoint) ∧
      (¬ HilbertDerives proofTheory (Formula.neg fixedPoint)) := by
  constructor
  · intro hFixedPointDerives
    have hPredicate :=
      hPositiveInternalization hFixedPointDerives
    have hNegPredicate :=
      HilbertDerives.iff_elim_right
        SetSort.set hFixedPoint hFixedPointDerives
    exact hConsistent <|
      (HilbertDerives.neg_elim
        Formula.Admissible.falsum
        hPredicate hNegPredicate).to_derives
  · intro hNegFixedPointDerives
    have hNegPredicate :=
      hNegativeInternalization hNegFixedPointDerives
    have hFixedPointDerives :=
      HilbertDerives.iff_elim_left
        SetSort.set hFixedPoint hNegPredicate
    exact hConsistent <|
      (HilbertDerives.neg_elim
        Formula.Admissible.falsum
        hFixedPointDerives hNegFixedPointDerives).to_derives

end Rosser
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
