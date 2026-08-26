import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedProofCodeEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.RosserFinite
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaBinderReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CheckedSyntax
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CheckedSubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CheckedLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceInversion

/-!
# ProofT 证书化证明码的对象层反演

本模块把完整 `CertifiedProof.code_condition_with_ids` 的有限坐标约束逐步
反演为规范外部数据。这里只进行纯语法有限消去；不引入模型、标准性或额外
内部理论层。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation
open Rosser

set_option autoImplicit false

private theorem free_id_offset_ne_offset
    (base left right : FreeVarId)
    (hNe : left ≠ right) :
    base + left ≠ base + right := by
  intro hEquality
  exact hNe (Nat.add_left_cancel hEquality)

private theorem free_id_offset_ne_base
    (base offset : FreeVarId)
    (hPositive : 0 < offset) :
    base + offset ≠ base :=
  Ne.symm (Nat.ne_of_lt
    (Nat.lt_add_of_pos_right hPositive))

private theorem set_variable_fresh_of_ne
    (left right : FreeVarId)
    (hNe : left ≠ right) :
    (SetSort.set, left) ∉
      Term.freeSupport (x#right) := by
  intro hMember
  change (SetSort.set, left) ∈
    [(SetSort.set, right)] at hMember
  have hEquality :
      (SetSort.set, left) =
        (SetSort.set, right) :=
    List.mem_singleton.mp hMember
  exact hNe (congrArg Prod.snd hEquality)

private theorem set_free_variable_ne_of_id_ne
    {left right : FreeVarId}
    (hNe : left ≠ right) :
    (SetSort.set, left) ≠
      (SetSort.set, right) := by
  intro hEquality
  exact hNe (congrArg Prod.snd hEquality)

/-! ## 总证明码的两个规范坐标 -/

/--
总证明码的两个有界坐标由规范反配对唯一决定。

对象层不需要全局调用 Gödel 配对唯一性；两个显式坐标界先把见证压入
`S(number)`，随后只对有限 numeral 对进行地面配对计算。
-/
theorem ProofT.components_unique
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    {Γ : Context signature}
    (number : Nat)
    (formulaCode certificateCode : SetTerm)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificateCode : Term.Admissible certificateCode SetSort.set)
    (hFormulaBound :
      Γ ⊢ₘ[T]
        CertifiedProof.proof_code_component_bound
          (numₘ(number)) formulaCode)
    (hCertificateBound :
      Γ ⊢ₘ[T]
        CertifiedProof.proof_code_component_bound
          (numₘ(number)) certificateCode)
    (hPair :
      Γ ⊢ₘ[T]
        numₘ(number) ≐ₘ
          godel_pairₘ(⟨formulaCode, certificateCode⟩ₘ)) :
    Γ ⊢ₘ[T]
      (formulaCode ≐ₘ
          numₘ((godel_unpair_value number).1)) ∧ₘ
        (certificateCode ≐ₘ
          numₘ((godel_unpair_value number).2)) := by
  let conclusion : SetFormula :=
    (formulaCode ≐ₘ
        numₘ((godel_unpair_value number).1)) ∧ₘ
      (certificateCode ≐ₘ
        numₘ((godel_unpair_value number).2))
  have hConclusion :
      Formula.Admissible conclusion := by
    simpa [conclusion] using
      Formula.Admissible.conj
        (Formula.Admissible.equal
          hFormulaCode
          (finite_numeral_term_admissible
            (godel_unpair_value number).1))
        (Formula.Admissible.equal
          hCertificateCode
          (finite_numeral_term_admissible
            (godel_unpair_value number).2))
  have hFormulaMember :
      Γ ⊢ₘ[T]
        formulaCode ∈ₘ numₘ(number + 1) := by
    simpa [CertifiedProof.proof_code_component_bound,
      finite_numeral_term, successor_term] using hFormulaBound
  have hCertificateMember :
      Γ ⊢ₘ[T]
        certificateCode ∈ₘ numₘ(number + 1) := by
    simpa [CertifiedProof.proof_code_component_bound,
      finite_numeral_term, successor_term] using hCertificateBound
  apply
    C.member_elim
      (number + 1) formulaCode conclusion
      hFormulaCode hConclusion hFormulaMember
  intro left hLeft
  let leftEquality : SetFormula :=
    formulaCode ≐ₘ numₘ(left)
  let Δ : Context signature := leftEquality :: Γ
  change Δ ⊢ₘ[T] conclusion
  have hCertificateMemberAt :
      Δ ⊢ₘ[T]
        certificateCode ∈ₘ numₘ(number + 1) :=
    FirstOrder.Derives.context_weaken_cons hCertificateMember
  apply
    C.member_elim
      (number + 1) certificateCode conclusion
      hCertificateCode hConclusion hCertificateMemberAt
  intro right hRight
  let rightEquality : SetFormula :=
    certificateCode ≐ₘ numₘ(right)
  let Ε : Context signature := rightEquality :: Δ
  change Ε ⊢ₘ[T] conclusion
  have hLeftEquality :
      Ε ⊢ₘ[T]
        formulaCode ≐ₘ numₘ(left) := by
    simpa [Ε, Δ, leftEquality, rightEquality] using
      (FirstOrder.Derives.assumption
        (T := T)
        (Γ := Ε)
        (φ := leftEquality)
        (by simp [Ε, Δ]))
  have hRightEquality :
      Ε ⊢ₘ[T]
        certificateCode ≐ₘ numₘ(right) := by
    simpa [Ε, rightEquality] using
      (FirstOrder.Derives.assumption
        (T := T)
        (Γ := Ε)
        (φ := rightEquality)
        (by simp [Ε]))
  have hPairAt :
      Ε ⊢ₘ[T]
        numₘ(number) ≐ₘ
          godel_pairₘ(⟨formulaCode, certificateCode⟩ₘ) :=
    FirstOrder.Derives.context_weaken_cons
      (FirstOrder.Derives.context_weaken_cons hPair)
  have hPairCongruence :
      Ε ⊢ₘ[T]
        godel_pairₘ(⟨formulaCode, certificateCode⟩ₘ) ≐ₘ
          godel_pairₘ(⟨numₘ(left), numₘ(right)⟩ₘ) :=
    godel_pairing_term_congr_of_equalities
      formulaCode (numₘ(left))
      certificateCode (numₘ(right))
      hFormulaCode (finite_numeral_term_admissible left)
      hCertificateCode (finite_numeral_term_admissible right)
      hLeftEquality hRightEquality
  have hGround :
      Ε ⊢ₘ[T]
        godel_pairₘ(⟨numₘ(left), numₘ(right)⟩ₘ) ≐ₘ
          numₘ(godel_pair_value left right) :=
    FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Ε)
      (by simp)
      (C.pair_value left right)
  have hNumeralEquality :
      Ε ⊢ₘ[T]
        numₘ(number) ≐ₘ
          numₘ(godel_pair_value left right) :=
    Metatheory.Derives.equality_trans
      hPairAt
      (Metatheory.Derives.equality_trans
        hPairCongruence hGround)
  by_cases hCode :
      number = godel_pair_value left right
  · have hCoordinates :
        left = (godel_unpair_value number).1 ∧
          right = (godel_unpair_value number).2 := by
      have hPairValues :
          godel_pair_value left right =
            godel_pair_value
              (godel_unpair_value number).1
              (godel_unpair_value number).2 := by
        rw [← hCode, godel_unpair_value_spec]
      exact godel_pair_value_eq_iff.mp hPairValues
    rcases hCoordinates with ⟨rfl, rfl⟩
    simpa [conclusion] using
      FirstOrder.Derives.conjIntro
        hLeftEquality hRightEquality
  · have hFalse :
        Ε ⊢ₘ[T] Formula.falsum :=
      FirstOrder.Derives.negElim hNumeralEquality <|
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε) (by simp) (C.numeral_ne hCode)
    exact FirstOrder.Derives.falsumElim hFalse

/-! ## 四个见证打开后的规范序列 -/

/--
证明码见证体中的两条序列由 proof code 的规范反配对坐标唯一决定。

上下文新鲜性只针对两个序列编码内部用于存在消去的轨迹变量；所有对象项
本身固定为四个外层见证变量，因此其余新鲜性由编号偏移直接计算。
-/
theorem ProofT.witness_sequences
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (S : ProofT.SequenceInversion T)
    {Γ : Context signature}
    (verifier : ObjectCertificateVerifier)
    (number : Nat)
    (conclusion : SetTerm)
    (base : FreeVarId)
    (hProofTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, base + 4) ∉
          Formula.freeSupport formula)
    (hProofRowCodeFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, base + 6) ∉
          Formula.freeSupport formula)
    (hProofRowTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, base + 7) ∉
          Formula.freeSupport formula)
    (hCertificateTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, base + 9) ∉
          Formula.freeSupport formula)
    (hBody :
      Γ ⊢ₘ[T]
        proof_witness
          verifier (numₘ(number)) conclusion
          (x#base) (x#(base + 1))
          (x#(base + 2)) (x#(base + 3))
          base) :
    Γ ⊢ₘ[T]
      ((x#base) ≐ₘ
          standard_sequence
            ((proof_sequence_decode
                (godel_unpair_value number).1).map
              standard_token_sequence)) ∧ₘ
        ((x#(base + 1)) ≐ₘ
          standard_token_sequence
            (nat_sequence_decode
              (godel_unpair_value number).2)) := by
  let rows : List (List Nat) :=
    proof_sequence_decode
      (godel_unpair_value number).1
  let certificates : List Nat :=
    nat_sequence_decode
      (godel_unpair_value number).2
  have hLeft :=
    FirstOrder.Derives.conjElimLeft hBody
  have hRight :=
    FirstOrder.Derives.conjElimRight hBody
  have hSequenceAndProof :=
    FirstOrder.Derives.conjElimLeft hLeft
  have hProofSequence :
      Γ ⊢ₘ[T]
        proof_sequence_code_condition_with_ids
          (x#base) (x#(base + 2))
          (base + 4) (base + 5) (base + 6)
          (base + 7) (base + 8) := by
    simpa [proof_witness] using
      FirstOrder.Derives.conjElimRight hSequenceAndProof
  have hCertificateSequence :
      Γ ⊢ₘ[T]
        nat_sequence_code_condition_with_ids
          (x#(base + 1)) (x#(base + 3))
          (base + 9) (base + 10) := by
    simpa [proof_witness] using
      FirstOrder.Derives.conjElimRight hLeft
  have hBounds :=
    FirstOrder.Derives.conjElimLeft hRight
  have hPairAndTerminal :=
    FirstOrder.Derives.conjElimRight hRight
  have hFormulaBound :
      Γ ⊢ₘ[T]
        CertifiedProof.proof_code_component_bound
          (numₘ(number)) (x#(base + 2)) := by
    simpa [proof_witness] using
      FirstOrder.Derives.conjElimLeft hBounds
  have hCertificateBound :
      Γ ⊢ₘ[T]
        CertifiedProof.proof_code_component_bound
          (numₘ(number)) (x#(base + 3)) := by
    simpa [proof_witness] using
      FirstOrder.Derives.conjElimRight hBounds
  have hPair :
      Γ ⊢ₘ[T]
        numₘ(number) ≐ₘ
          godel_pairₘ(
            ⟨x#(base + 2), x#(base + 3)⟩ₘ) := by
    simpa [proof_witness] using
      FirstOrder.Derives.conjElimLeft hPairAndTerminal
  have hCoordinates :=
    ProofT.components_unique
      C
      number (x#(base + 2)) (x#(base + 3))
      (set_variable_admissible (base + 2))
      (set_variable_admissible (base + 3))
      hFormulaBound hCertificateBound hPair
  have hFormulaCode :
      Γ ⊢ₘ[T]
        (x#(base + 2)) ≐ₘ
          numₘ(proof_sequence_code_value rows) := by
    have hLeftCoordinate :=
      FirstOrder.Derives.conjElimLeft hCoordinates
    simpa [rows, proof_sequence_code_value_decode] using
      hLeftCoordinate
  have hCertificateCode :
      Γ ⊢ₘ[T]
        (x#(base + 3)) ≐ₘ
          numₘ(nat_sequence_code_value certificates) := by
    have hRightCoordinate :=
      FirstOrder.Derives.conjElimRight hCoordinates
    simpa [certificates, nat_sequence_code_value_decode] using
      hRightCoordinate
  have hProofSequenceUnique :
      Γ ⊢ₘ[T]
        (x#base) ≐ₘ
          standard_sequence
            (rows.map standard_token_sequence) := by
    apply
      S.proof_unique
        (x#base) (x#(base + 2)) rows
        (base + 4) (base + 5) (base + 6)
        (base + 7) (base + 8)
        (set_variable_admissible base)
        (set_variable_admissible (base + 2))
    · exact free_id_offset_ne_offset base 4 5 (by decide)
    · exact free_id_offset_ne_offset base 4 6 (by decide)
    · exact free_id_offset_ne_offset base 4 7 (by decide)
    · exact free_id_offset_ne_offset base 5 6 (by decide)
    · exact free_id_offset_ne_offset base 5 7 (by decide)
    · exact free_id_offset_ne_offset base 5 8 (by decide)
    · exact free_id_offset_ne_offset base 6 7 (by decide)
    · exact free_id_offset_ne_offset base 6 8 (by decide)
    · exact free_id_offset_ne_offset base 7 8 (by decide)
    · exact set_variable_fresh_of_ne
        (base + 4) base
        (free_id_offset_ne_base base 4 (by decide))
    · exact set_variable_fresh_of_ne
        (base + 5) base
        (free_id_offset_ne_base base 5 (by decide))
    · exact set_variable_fresh_of_ne
        (base + 5) (base + 2)
        (free_id_offset_ne_offset base 5 2 (by decide))
    · exact set_variable_fresh_of_ne
        (base + 6) base
        (free_id_offset_ne_base base 6 (by decide))
    · exact set_variable_fresh_of_ne
        (base + 6) (base + 2)
        (free_id_offset_ne_offset base 6 2 (by decide))
    · exact set_variable_fresh_of_ne
        (base + 7) base
        (free_id_offset_ne_base base 7 (by decide))
    · exact set_variable_fresh_of_ne
        (base + 7) (base + 2)
        (free_id_offset_ne_offset base 7 2 (by decide))
    · exact set_variable_fresh_of_ne
        (base + 8) base
        (free_id_offset_ne_base base 8 (by decide))
    · exact hProofTraceFreshContext
    · exact hProofRowCodeFreshContext
    · exact hProofRowTraceFreshContext
    · exact hProofSequence
    · exact hFormulaCode
  have hCertificateSequenceUnique :
      Γ ⊢ₘ[T]
        (x#(base + 1)) ≐ₘ
          standard_token_sequence certificates := by
    apply
      S.nat_unique
        (x#(base + 1)) (x#(base + 3))
        certificates (base + 9) (base + 10)
        (set_variable_admissible (base + 1))
        (set_variable_admissible (base + 3))
    · exact free_id_offset_ne_offset base 9 10 (by decide)
    · exact set_variable_fresh_of_ne
        (base + 9) (base + 1)
        (free_id_offset_ne_offset base 9 1 (by decide))
    · exact set_variable_fresh_of_ne
        (base + 10) (base + 1)
        (free_id_offset_ne_offset base 10 1 (by decide))
    · exact set_variable_fresh_of_ne
        (base + 10) (base + 3)
        (free_id_offset_ne_offset base 10 3 (by decide))
    · exact hCertificateTraceFreshContext
    · exact hCertificateSequence
    · exact hCertificateCode
  simpa [rows, certificates] using
    FirstOrder.Derives.conjIntro
      hProofSequenceUnique hCertificateSequenceUnique

/-! ## 见证体到规范序列的闭合蕴含 -/

/--
满足 replay 与支撑合同的 verifier 下，打开的证明码见证体直接推出两条规范序列。

轨迹变量的新鲜性由完整证明码条件的支撑收缩统一给出；后续四重存在消去
只需消费该蕴含，不再展开 verifier 或序列编码内部结构。
-/
theorem ProofT.witness_sequences_imp
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (S : ProofT.SequenceInversion T)
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (hSupport : ProofT.VerifierSupport verifier)
    (number : Nat)
    (conclusion : SetTerm)
    (base : FreeVarId)
    (hConclusion : Term.Admissible conclusion SetSort.set)
    (hConclusionProofTraceFresh :
      (SetSort.set, base + 4) ∉
        Term.freeSupport conclusion)
    (hConclusionProofRowCodeFresh :
      (SetSort.set, base + 6) ∉
        Term.freeSupport conclusion)
    (hConclusionProofRowTraceFresh :
      (SetSort.set, base + 7) ∉
        Term.freeSupport conclusion)
    (hConclusionCertificateTraceFresh :
      (SetSort.set, base + 9) ∉
        Term.freeSupport conclusion) :
    ([] : Context signature)
      ⊢ₘ[T]
        proof_witness
            verifier
            (numₘ(number)) conclusion
            (x#base) (x#(base + 1))
            (x#(base + 2)) (x#(base + 3))
            base ⟶ₘ
          (((x#base) ≐ₘ
              standard_sequence
                ((proof_sequence_decode
                    (godel_unpair_value number).1).map
                  standard_token_sequence)) ∧ₘ
            ((x#(base + 1)) ≐ₘ
              standard_token_sequence
                (nat_sequence_decode
                  (godel_unpair_value number).2))) := by
  let body : SetFormula :=
    proof_witness
      verifier
      (numₘ(number)) conclusion
      (x#base) (x#(base + 1))
      (x#(base + 2)) (x#(base + 3))
      base
  have hBodyCheck :
      Formula.CheckCertificate body :=
    Formula.check_admissible_complete <| by
      simpa [body] using
        proof_witness_admissible
          verifier
          (numₘ(number)) conclusion
          (x#base) (x#(base + 1))
          (x#(base + 2)) (x#(base + 3))
          base
          (finite_numeral_term_admissible number)
          hConclusion
          (set_variable_admissible base)
          (set_variable_admissible (base + 1))
          (set_variable_admissible (base + 2))
          (set_variable_admissible (base + 3))
  have hFormulaSupport :
      ∀ formula freeVariable,
        freeVariable ∈ Formula.freeSupport
            (verifier.formula_condition formula) →
        freeVariable ∈ Term.freeSupport formula := by
    intro formula freeVariable hMember
    rw [hTransport.formula_condition] at hMember
    exact
      fs_formula_replay_condition_freeSupport_subset
        formula freeVariable hMember
  have hBodyFresh
      (target : FreeVarId)
      (hConclusionFresh :
        (SetSort.set, target) ∉
          Term.freeSupport conclusion)
      (hNe0 : target ≠ base)
      (hNe1 : target ≠ base + 1)
      (hNe2 : target ≠ base + 2)
      (hNe3 : target ≠ base + 3) :
      (SetSort.set, target) ∉
        Formula.freeSupport body := by
    simpa [body] using
      proof_witness_fresh
        verifier
        (numₘ(number)) conclusion base
        (SetSort.set, target)
        hFormulaSupport
        hSupport.freeSupport_subset
        (by simp [finite_numeral_term_freeSupport])
        hConclusionFresh
        (set_free_variable_ne_of_id_ne hNe0)
        (set_free_variable_ne_of_id_ne hNe1)
        (set_free_variable_ne_of_id_ne hNe2)
        (set_free_variable_ne_of_id_ne hNe3)
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [body]
  have hBody :
      Γ ⊢ₘ[T] body :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hUnique :=
    ProofT.witness_sequences
      C S
      (Γ := Γ)
      verifier
      number conclusion base
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hBodyFresh (base + 4)
          hConclusionProofTraceFresh
          (free_id_offset_ne_base base 4 (by decide))
          (free_id_offset_ne_offset base 4 1 (by decide))
          (free_id_offset_ne_offset base 4 2 (by decide))
          (free_id_offset_ne_offset base 4 3 (by decide)))
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hBodyFresh (base + 6)
          hConclusionProofRowCodeFresh
          (free_id_offset_ne_base base 6 (by decide))
          (free_id_offset_ne_offset base 6 1 (by decide))
          (free_id_offset_ne_offset base 6 2 (by decide))
          (free_id_offset_ne_offset base 6 3 (by decide)))
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hBodyFresh (base + 7)
          hConclusionProofRowTraceFresh
          (free_id_offset_ne_base base 7 (by decide))
          (free_id_offset_ne_offset base 7 1 (by decide))
          (free_id_offset_ne_offset base 7 2 (by decide))
          (free_id_offset_ne_offset base 7 3 (by decide)))
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hBodyFresh (base + 9)
          hConclusionCertificateTraceFresh
          (free_id_offset_ne_base base 9 (by decide))
          (free_id_offset_ne_offset base 9 1 (by decide))
          (free_id_offset_ne_offset base 9 2 (by decide))
          (free_id_offset_ne_offset base 9 3 (by decide)))
      hBody
  simpa [Γ, body] using hUnique

/-! ## 四个证明码见证的统一消去 -/

/--
若打开后的证明码见证体在空上下文中推出一个不含四个见证变量的目标，
则完整 numeral 证明码条件在任意上下文中也推出该目标。

证明先在空上下文逐层提升四次存在量词，再把所得闭合蕴含弱化到调用方
上下文；因此调用方上下文本身不需要额外的新鲜性假设。
-/
theorem ProofT.code_elim
    {T : SetTheory}
    (C : ProofT.FiniteCore T)
    {Γ : Context signature}
    (verifier : ObjectCertificateVerifier)
    (number : Nat)
    (conclusion : SetTerm)
    (base : FreeVarId)
    (target : SetFormula)
    (hTargetSequenceFresh :
      (SetSort.set, base) ∉
        Formula.freeSupport target)
    (hTargetCertificatesFresh :
      (SetSort.set, base + 1) ∉
        Formula.freeSupport target)
    (hTargetFormulaCodeFresh :
      (SetSort.set, base + 2) ∉
        Formula.freeSupport target)
    (hTargetCertificateCodeFresh :
      (SetSort.set, base + 3) ∉
        Formula.freeSupport target)
    (hWitnessImp :
      ([] : Context signature)
        ⊢ₘ[T]
          proof_witness
              verifier
              (numₘ(number)) conclusion
              (x#base) (x#(base + 1))
              (x#(base + 2)) (x#(base + 3))
              base ⟶ₘ target)
    (hCondition :
      Γ ⊢ₘ[T]
        proof_condition
          verifier
          (numₘ(number)) conclusion base) :
    Γ ⊢ₘ[T] target := by
  let body : SetFormula :=
    proof_witness
      verifier
      (numₘ(number)) conclusion
      (x#base) (x#(base + 1))
      (x#(base + 2)) (x#(base + 3))
      base
  let certificateCodeBody : SetFormula :=
    CertifiedProof.proof_code_component_bound
        (numₘ(number)) (x#(base + 3)) ∧ₘ
      body
  let certificateCodeExists : SetFormula :=
    ∃ₘ[SetSort.set, base + 3], certificateCodeBody
  let formulaCodeBody : SetFormula :=
    CertifiedProof.proof_code_component_bound
        (numₘ(number)) (x#(base + 2)) ∧ₘ
      certificateCodeExists
  let formulaCodeExists : SetFormula :=
    ∃ₘ[SetSort.set, base + 2], formulaCodeBody
  let certificatesBody : SetFormula :=
    (x#(base + 1) ∈ₘ seq₊_spaceₘ(ωₘ)) ∧ₘ
      formulaCodeExists
  let certificatesExists : SetFormula :=
    ∃ₘ[SetSort.set, base + 1], certificatesBody
  let sequenceBody : SetFormula :=
    (x#base ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
      certificatesExists
  let sequenceExists : SetFormula :=
    ∃ₘ[SetSort.set, base], sequenceBody
  have hTheoryFresh
      (id : FreeVarId) :
      ∀ formula, T formula →
        (SetSort.set, id) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(C.theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hEmptyFresh
      (id : FreeVarId) :
      ∀ formula, formula ∈ ([] : Context signature) →
        (SetSort.set, id) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    exact False.elim (List.not_mem_nil hFormula)
  have hBodyImp :
      ([] : Context signature)
        ⊢ₘ[T]
          body ⟶ₘ target := by
    simpa [body] using hWitnessImp
  have hConjRightImp
      (left right : SetFormula)
      (hLeft : Formula.Admissible left)
      (hRight : Formula.Admissible right) :
      ([] : Context signature)
        ⊢ₘ[T]
          (left ∧ₘ right) ⟶ₘ right := by
    apply FirstOrder.Derives.deduction
      (hAntecedentCheck :=
        Formula.check_admissible_complete
          (Formula.Admissible.conj hLeft hRight))
    exact FirstOrder.Derives.conjElimRight
      (FirstOrder.Derives.assumption
        (T := T)
        (Γ := [(left ∧ₘ right)])
        (φ := left ∧ₘ right)
        (by simp))
  have hBodyAdmissible :
      Formula.Admissible body :=
    Formula.Admissible.imp_left hBodyImp.admissible
  have hCertificateCodeBoundAdmissible :
      Formula.Admissible
        (CertifiedProof.proof_code_component_bound
          (numₘ(number)) (x#(base + 3))) := by
    simpa [CertifiedProof.proof_code_component_bound] using
      membership_formula_admissible
        (set_variable_admissible (base + 3))
        (successor_term_admissible
          (numₘ(number))
          (finite_numeral_term_admissible number))
  have hCertificateCodeBodyImp :
      ([] : Context signature)
        ⊢ₘ[T]
          certificateCodeBody ⟶ₘ target := by
    apply Metatheory.Derives.imp_trans
      (ψ := body)
    · simpa [certificateCodeBody] using
        hConjRightImp
          (CertifiedProof.proof_code_component_bound
            (numₘ(number)) (x#(base + 3)))
          body hCertificateCodeBoundAdmissible hBodyAdmissible
    · exact hBodyImp
  have hCertificateCodeImp :
      ([] : Context signature)
        ⊢ₘ[T]
          certificateCodeExists ⟶ₘ target := by
    simpa [certificateCodeExists] using
      FirstOrder.Derives.exists_imp_of_imp
        (T := T)
        (Γ := ([] : Context signature))
        (sort := SetSort.set)
        (eigen := base + 3)
        (body := certificateCodeBody)
        (conclusion := target)
        (hTheoryFresh (base + 3))
        (hEmptyFresh (base + 3))
        hTargetCertificateCodeFresh
        hCertificateCodeBodyImp
  have hCertificateCodeExistsAdmissible :
      Formula.Admissible certificateCodeExists :=
    Formula.Admissible.imp_left hCertificateCodeImp.admissible
  have hFormulaCodeBoundAdmissible :
      Formula.Admissible
        (CertifiedProof.proof_code_component_bound
          (numₘ(number)) (x#(base + 2))) := by
    simpa [CertifiedProof.proof_code_component_bound] using
      membership_formula_admissible
        (set_variable_admissible (base + 2))
        (successor_term_admissible
          (numₘ(number))
          (finite_numeral_term_admissible number))
  have hFormulaCodeBodyImp :
      ([] : Context signature)
        ⊢ₘ[T]
          formulaCodeBody ⟶ₘ target := by
    apply Metatheory.Derives.imp_trans
      (ψ := certificateCodeExists)
    · simpa [formulaCodeBody] using
        hConjRightImp
          (CertifiedProof.proof_code_component_bound
            (numₘ(number)) (x#(base + 2)))
          certificateCodeExists
          hFormulaCodeBoundAdmissible
          hCertificateCodeExistsAdmissible
    · exact hCertificateCodeImp
  have hFormulaCodeImp :
      ([] : Context signature)
        ⊢ₘ[T]
          formulaCodeExists ⟶ₘ target := by
    simpa [formulaCodeExists] using
      FirstOrder.Derives.exists_imp_of_imp
        (T := T)
        (Γ := ([] : Context signature))
        (sort := SetSort.set)
        (eigen := base + 2)
        (body := formulaCodeBody)
        (conclusion := target)
        (hTheoryFresh (base + 2))
        (hEmptyFresh (base + 2))
        hTargetFormulaCodeFresh
        hFormulaCodeBodyImp
  have hFormulaCodeExistsAdmissible :
      Formula.Admissible formulaCodeExists :=
    Formula.Admissible.imp_left hFormulaCodeImp.admissible
  have hCertificatesGuardAdmissible :
      Formula.Admissible
        (x#(base + 1) ∈ₘ seq₊_spaceₘ(ωₘ)) := by
    prove_admissible
  have hCertificatesBodyImp :
      ([] : Context signature)
        ⊢ₘ[T]
          certificatesBody ⟶ₘ target := by
    apply Metatheory.Derives.imp_trans
      (ψ := formulaCodeExists)
    · simpa [certificatesBody] using
        hConjRightImp
          (x#(base + 1) ∈ₘ seq₊_spaceₘ(ωₘ))
          formulaCodeExists
          hCertificatesGuardAdmissible
          hFormulaCodeExistsAdmissible
    · exact hFormulaCodeImp
  have hCertificatesImp :
      ([] : Context signature)
        ⊢ₘ[T]
          certificatesExists ⟶ₘ target := by
    simpa [certificatesExists] using
      FirstOrder.Derives.exists_imp_of_imp
        (T := T)
        (Γ := ([] : Context signature))
        (sort := SetSort.set)
        (eigen := base + 1)
        (body := certificatesBody)
        (conclusion := target)
        (hTheoryFresh (base + 1))
        (hEmptyFresh (base + 1))
        hTargetCertificatesFresh
        hCertificatesBodyImp
  have hCertificatesExistsAdmissible :
      Formula.Admissible certificatesExists :=
    Formula.Admissible.imp_left hCertificatesImp.admissible
  have hSequenceGuardAdmissible :
      Formula.Admissible
        (x#base ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) := by
    prove_admissible
  have hSequenceBodyImp :
      ([] : Context signature)
        ⊢ₘ[T]
          sequenceBody ⟶ₘ target := by
    apply Metatheory.Derives.imp_trans
      (ψ := certificatesExists)
    · simpa [sequenceBody] using
        hConjRightImp
          (x#base ∈ₘ seq₊_spaceₘ(FormulaCodeₘ))
          certificatesExists
          hSequenceGuardAdmissible
          hCertificatesExistsAdmissible
    · exact hCertificatesImp
  have hSequenceImp :
      ([] : Context signature)
        ⊢ₘ[T]
          sequenceExists ⟶ₘ target := by
    simpa [sequenceExists] using
      FirstOrder.Derives.exists_imp_of_imp
        (T := T)
        (Γ := ([] : Context signature))
        (sort := SetSort.set)
        (eigen := base)
        (body := sequenceBody)
        (conclusion := target)
        (hTheoryFresh base)
        (hEmptyFresh base)
        hTargetSequenceFresh
        hSequenceBodyImp
  rw [proof_condition_eq_witness] at hCondition
  have hSequenceExists :
      Γ ⊢ₘ[T]
        sequenceExists := by
    simpa [sequenceExists, certificatesExists,
      formulaCodeExists, certificateCodeExists,
      sequenceBody, certificatesBody,
      formulaCodeBody, certificateCodeBody, body] using
      FirstOrder.Derives.conjElimRight hCondition
  have hSequenceImpAt :
      Γ ⊢ₘ[T]
        sequenceExists ⟶ₘ target :=
    FirstOrder.Derives.context_weaken
      (Γ := ([] : Context signature))
      (Δ := Γ)
      (by simp)
      hSequenceImp
  exact FirstOrder.Derives.impElim
    hSequenceImpAt hSequenceExists

/--
若四个打开见证组成的证明码体推出矛盾，则完整证明码条件为假。

该接口只依赖背景理论的闭句边界；具体 verifier 与见证变量基址均由调用方给出。
-/
theorem ProofT.code_neg_of_witness
    {T : SetTheory}
    (C : ProofT.FiniteCore T)
    (verifier : ObjectCertificateVerifier)
    (number : Nat)
    (conclusion : SetTerm)
    (base : FreeVarId)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (hWitnessImp :
      ([] : Context signature) ⊢ₘ[T]
        proof_witness
            verifier
            (numₘ(number)) conclusion
            (x#base) (x#(base + 1))
            (x#(base + 2)) (x#(base + 3))
            base ⟶ₘ
          Formula.falsum) :
    Derives T [] (
      ¬ₘ proof_condition
        verifier (numₘ(number)) conclusion base) := by
  have hConditionAdmissible :
      Formula.Admissible
        (proof_condition
          verifier (numₘ(number)) conclusion base) :=
    proof_condition_admissible
      verifier (numₘ(number)) conclusion base
      (finite_numeral_term_admissible number)
      hConclusion.1
  nd_apply FirstOrder.Derives.negIntro
    (T := T)
    (Γ := ([] : Context signature))
    (body :=
      proof_condition
        verifier (numₘ(number)) conclusion base)
    (hBodyCheck :=
      Formula.check_admissible_complete hConditionAdmissible)
  let condition : SetFormula :=
    proof_condition
      verifier (numₘ(number)) conclusion base
  let Γ : Context signature := [condition]
  have hCondition :
      Γ ⊢ₘ[T] condition :=
    FirstOrder.Derives.assumption (by simp [Γ])
  exact
    ProofT.code_elim
      C verifier number conclusion base Formula.falsum
      (by
        change (SetSort.set, base) ∉
          Formula.freeSupport (Formula.falsum : SetFormula)
        exact List.not_mem_nil)
      (by
        change (SetSort.set, base + 1) ∉
          Formula.freeSupport (Formula.falsum : SetFormula)
        exact List.not_mem_nil)
      (by
        change (SetSort.set, base + 2) ∉
          Formula.freeSupport (Formula.falsum : SetFormula)
        exact List.not_mem_nil)
      (by
        change (SetSort.set, base + 3) ∉
          Formula.freeSupport (Formula.falsum : SetFormula)
        exact List.not_mem_nil)
      hWitnessImp
      (by simpa [Γ, condition] using hCondition)

/--
规范见证体能够给出 checked 序列条件，而某个定义域位置的 checked 行已被否定时，
完整证明码条件为假。

该桥不固定 canonical 序列的构造；实例只需给出见证体到序列条件的运输和该位置
属于序列定义域的闭证明。
-/
theorem ProofT.code_neg_of_line
    {T : SetTheory}
    (C : ProofT.FiniteCore T)
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (number : Nat)
    (conclusion : SetTerm)
    (base : FreeVarId)
    (sequence certificates : SetTerm)
    (index : Nat)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hWitnessSequence :
      ∀ {Γ : Context signature},
        Γ ⊢ₘ[T]
          proof_witness
            verifier (numₘ(number)) conclusion
            (x#base) (x#(base + 1))
            (x#(base + 2)) (x#(base + 3)) base →
        Γ ⊢ₘ[T]
          ProofT.sequence_condition
            verifier sequence certificates)
    (hIndexDomain :
      Derives T [] (
        numₘ(index) ∈ₘ domₘ(sequence)))
    (hLineNeg :
      Derives T [] (
        ¬ₘ ProofT.line_instance
          verifier sequence certificates index)) :
    Derives T [] (
      ¬ₘ proof_condition
        verifier (numₘ(number)) conclusion base) := by
  apply
    ProofT.code_neg_of_witness
      C verifier number conclusion base hConclusion
  have hWitnessBodyAdmissible :
      Formula.Admissible
        (proof_witness
          verifier (numₘ(number)) conclusion
          (x#base) (x#(base + 1))
          (x#(base + 2)) (x#(base + 3)) base) :=
    proof_witness_admissible
      verifier (numₘ(number)) conclusion
      (x#base) (x#(base + 1))
      (x#(base + 2)) (x#(base + 3)) base
      (finite_numeral_term_admissible number)
      hConclusion.1
      (set_variable_admissible base)
      (set_variable_admissible (base + 1))
      (set_variable_admissible (base + 2))
      (set_variable_admissible (base + 3))
  nd_apply FirstOrder.Derives.impIntro
    (T := T)
    (Γ := ([] : Context signature))
    (hAntecedentCheck :=
      Formula.check_admissible_complete hWitnessBodyAdmissible)
  let witnessBody : SetFormula :=
    proof_witness
      verifier (numₘ(number)) conclusion
      (x#base) (x#(base + 1))
      (x#(base + 2)) (x#(base + 3)) base
  let Γ : Context signature := [witnessBody]
  have hWitness :
      Γ ⊢ₘ[T] witnessBody :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hSequenceCondition :
      Γ ⊢ₘ[T]
        ProofT.sequence_condition
          verifier sequence certificates :=
    hWitnessSequence (by simpa [witnessBody] using hWitness)
  have hIndexDomainAt :
      Γ ⊢ₘ[T] numₘ(index) ∈ₘ domₘ(sequence) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hIndexDomain
  have hLine :
      Γ ⊢ₘ[T]
        ProofT.line_instance
          verifier sequence certificates index :=
    ProofT.line_of_sequence
      verifier hTransport sequence certificates index
      hSequenceClosed hSequenceCondition hIndexDomainAt
  exact FirstOrder.Derives.negElim
    hLine
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hLineNeg)

/--
规范 proof 序列与证书序列的对象定义域被锁定到不同有限长度时，完整证明码条件为假。

实例只需把 witness 运输到参数化 sequence condition，并分别给出两条规范序列的
闭定义域计算。
-/
theorem ProofT.code_neg_of_length
    {T : SetTheory}
    (C : ProofT.FiniteCore T)
    (verifier : ObjectCertificateVerifier)
    (number : Nat)
    (conclusion : SetTerm)
    (base : FreeVarId)
    (sequence certificates : SetTerm)
    (sequenceLength certificateLength : Nat)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (hWitnessSequence :
      ∀ {Γ : Context signature},
        Γ ⊢ₘ[T]
          proof_witness
            verifier (numₘ(number)) conclusion
            (x#base) (x#(base + 1))
            (x#(base + 2)) (x#(base + 3)) base →
        Γ ⊢ₘ[T]
          ProofT.sequence_condition
            verifier sequence certificates)
    (hSequenceDomain :
      Derives T [] (
        domₘ(sequence) ≐ₘ numₘ(sequenceLength)))
    (hCertificateDomain :
      Derives T [] (
        domₘ(certificates) ≐ₘ numₘ(certificateLength)))
    (hLengthNe : sequenceLength ≠ certificateLength) :
    Derives T [] (
      ¬ₘ proof_condition
        verifier (numₘ(number)) conclusion base) := by
  apply
    ProofT.code_neg_of_witness
      C verifier number conclusion base hConclusion
  have hWitnessBodyAdmissible :
      Formula.Admissible
        (proof_witness
          verifier (numₘ(number)) conclusion
          (x#base) (x#(base + 1))
          (x#(base + 2)) (x#(base + 3)) base) :=
    proof_witness_admissible
      verifier (numₘ(number)) conclusion
      (x#base) (x#(base + 1))
      (x#(base + 2)) (x#(base + 3)) base
      (finite_numeral_term_admissible number)
      hConclusion.1
      (set_variable_admissible base)
      (set_variable_admissible (base + 1))
      (set_variable_admissible (base + 2))
      (set_variable_admissible (base + 3))
  nd_apply FirstOrder.Derives.impIntro
    (T := T)
    (Γ := ([] : Context signature))
    (hAntecedentCheck :=
      Formula.check_admissible_complete hWitnessBodyAdmissible)
  let witnessBody : SetFormula :=
    proof_witness
      verifier (numₘ(number)) conclusion
      (x#base) (x#(base + 1))
      (x#(base + 2)) (x#(base + 3)) base
  let Γ : Context signature := [witnessBody]
  have hWitness :
      Γ ⊢ₘ[T] witnessBody :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hSequenceCondition :
      Γ ⊢ₘ[T]
        ProofT.sequence_condition
          verifier sequence certificates :=
    hWitnessSequence (by simpa [witnessBody] using hWitness)
  have hBeforeForall :=
    FirstOrder.Derives.conjElimLeft hSequenceCondition
  have hBeforeZero :=
    FirstOrder.Derives.conjElimLeft hBeforeForall
  have hDomainEquality :
      Γ ⊢ₘ[T] domₘ(sequence) ≐ₘ domₘ(certificates) := by
    simpa [ProofT.sequence_condition,
      CertifiedProof.sequence_condition_with_ids] using
      FirstOrder.Derives.conjElimRight hBeforeZero
  have hSequenceDomainAt :
      Γ ⊢ₘ[T] domₘ(sequence) ≐ₘ numₘ(sequenceLength) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hSequenceDomain
  have hCertificateDomainAt :
      Γ ⊢ₘ[T] domₘ(certificates) ≐ₘ numₘ(certificateLength) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hCertificateDomain
  have hLengthEquality :
      Γ ⊢ₘ[T]
        numₘ(sequenceLength) ≐ₘ numₘ(certificateLength) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hSequenceDomainAt)
      (Metatheory.Derives.equality_trans
        hDomainEquality hCertificateDomainAt)
  exact FirstOrder.Derives.negElim hLengthEquality <|
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) (C.numeral_ne hLengthNe)

/-! ## 规范序列上的证明内容 -/

/--
固定 Rosser 编号下，打开的证明码见证体可运输为规范解码序列上的
`sequence_condition` 与 terminal。

两条序列等式来自前述有限规范化；对象证书 verifier 的替换只使用项目中
  既有的 `880/881` 外层编号与 `ProofT.CheckedSyntax` 的完整保留编号表。
-/
theorem ProofT.witness_content
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (S : ProofT.SequenceInversion T)
    {Γ : Context signature}
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (hSupport : ProofT.VerifierSupport verifier)
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (hBody :
      Γ ⊢ₘ[T]
        proof_witness
          verifier
          (numₘ(number)) conclusion
          (x#ProofT.condition_base)
          (x#(ProofT.condition_base + 1))
          (x#(ProofT.condition_base + 2))
          (x#(ProofT.condition_base + 3))
          ProofT.condition_base) :
    Γ ⊢ₘ[T]
      (ProofT.sequence_condition verifier
          (standard_sequence
            ((proof_sequence_decode
                (godel_unpair_value number).1).map
              standard_token_sequence))
          (standard_token_sequence
            (nat_sequence_decode
              (godel_unpair_value number).2))) ∧ₘ
        proof_sequence_terminal_condition
          (standard_sequence
            ((proof_sequence_decode
                (godel_unpair_value number).1).map
              standard_token_sequence))
          conclusion := by
  let rows : List (List Nat) :=
    proof_sequence_decode
      (godel_unpair_value number).1
  let certificates : List Nat :=
    nat_sequence_decode
      (godel_unpair_value number).2
  let sequence : SetTerm :=
    standard_sequence
      (rows.map standard_token_sequence)
  let certificateSequence : SetTerm :=
    standard_token_sequence certificates
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    dsimp [sequence]
    apply seq_admissible_m 0
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, hTokens, rfl⟩
    exact standard_token_sequence_admissible tokens
  have hSequenceClosed :
      Term.freeSupport sequence = [] := by
    dsimp [sequence]
    apply seq_support_nil_m 0
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, hTokens, rfl⟩
    exact standard_token_sequence_freeSupport_nil tokens
  have hCertificateSequence :
      Term.Admissible certificateSequence SetSort.set := by
    exact standard_token_sequence_admissible certificates
  have hCertificateSequenceClosed :
      Term.freeSupport certificateSequence = [] := by
    exact standard_token_sequence_freeSupport_nil certificates
  have hSequenceBoundary :
      GodelQuotation.Numbered.CodeBoundary sequence :=
    ⟨hSequence, hSequenceClosed⟩
  have hCertificateSequenceBoundary :
      GodelQuotation.Numbered.CodeBoundary
        certificateSequence :=
    ⟨hCertificateSequence, hCertificateSequenceClosed⟩
  have hUniqueImp :=
    ProofT.witness_sequences_imp
      C S
      verifier hTransport hSupport
      number conclusion ProofT.condition_base
      hConclusion.1
      (by rw [hConclusion.2]; exact List.not_mem_nil)
      (by rw [hConclusion.2]; exact List.not_mem_nil)
      (by rw [hConclusion.2]; exact List.not_mem_nil)
      (by rw [hConclusion.2]; exact List.not_mem_nil)
  have hUniqueImpAt :
      Γ ⊢ₘ[T]
        proof_witness
            verifier
            (numₘ(number)) conclusion
            (x#ProofT.condition_base)
            (x#(ProofT.condition_base + 1))
            (x#(ProofT.condition_base + 2))
            (x#(ProofT.condition_base + 3))
            ProofT.condition_base ⟶ₘ
          (((x#ProofT.condition_base) ≐ₘ
              sequence) ∧ₘ
            ((x#(ProofT.condition_base + 1)) ≐ₘ
              certificateSequence)) := by
    simpa [rows, certificates, sequence,
      certificateSequence] using
      FirstOrder.Derives.context_weaken
        (Γ := ([] : Context signature))
        (Δ := Γ)
        (by simp)
        hUniqueImp
  have hUnique :=
    FirstOrder.Derives.impElim hUniqueImpAt hBody
  have hSequenceEquality :
      Γ ⊢ₘ[T]
        (x#ProofT.condition_base) ≐ₘ
          sequence :=
    FirstOrder.Derives.conjElimLeft hUnique
  have hCertificateSequenceEquality :
      Γ ⊢ₘ[T]
        (x#(ProofT.condition_base + 1)) ≐ₘ
          certificateSequence :=
    FirstOrder.Derives.conjElimRight hUnique
  have hBodyLeft :=
    FirstOrder.Derives.conjElimLeft hBody
  have hSequenceAndProof :=
    FirstOrder.Derives.conjElimLeft hBodyLeft
  have hSequenceCondition :
      Γ ⊢ₘ[T]
        ProofT.sequence_condition verifier
          (x#ProofT.condition_base)
          (x#(ProofT.condition_base + 1)) := by
    simpa [proof_witness,
      ProofT.condition_base,
      ProofT.sequence_condition] using
      FirstOrder.Derives.conjElimLeft hSequenceAndProof
  have hBodyRight :=
    FirstOrder.Derives.conjElimRight hBody
  have hPairAndTerminal :=
    FirstOrder.Derives.conjElimRight hBodyRight
  have hTerminal :
      Γ ⊢ₘ[T]
        proof_sequence_terminal_condition
          (x#ProofT.condition_base)
          conclusion := by
    simpa [proof_witness,
      ProofT.condition_base] using
      FirstOrder.Derives.conjElimRight hPairAndTerminal
  have hVariableVerifierBase :
      ProofT.schema_base
          [(x#ProofT.condition_base) ·ₘ (x#900),
            (x#903)] =
        904 := by
    simp [ProofT.condition_base,
      ProofT.schema_base,
      FreshVariable.fresh_id,
      FreshVariable.formulas_bound,
      FreshVariable.formula_bound,
      FreshVariable.support_bound,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList]
  have hSequenceVerifierBase :
      ProofT.schema_base
          [sequence ·ₘ (x#900), (x#903)] =
        904 := by
    simp [ProofT.schema_base,
      FreshVariable.fresh_id,
      FreshVariable.formulas_bound,
      FreshVariable.formula_bound,
      FreshVariable.support_bound,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      hSequenceClosed]
  let sequenceBody : SetFormula :=
    ProofT.sequence_condition verifier
      (x#ProofT.condition_base)
      (x#(ProofT.condition_base + 1))
  have hSequenceBodyAtLeft :
      Γ ⊢ₘ[T]
        Formula.substituteFree SetSort.set
          ProofT.condition_base
          (x#ProofT.condition_base)
          sequenceBody := by
    simpa [sequenceBody,
      ProofT.formula_substitute_self] using
      hSequenceCondition
  have hSequenceSubstitution :
      Formula.substituteFree SetSort.set
          ProofT.condition_base sequence sequenceBody =
        ProofT.sequence_condition verifier
          sequence
          (x#(ProofT.condition_base + 1)) := by
    simpa [sequenceBody, ProofT.condition_base] using
      ProofT.sequence_condition_substitute
        verifier hTransport
        (x#ProofT.condition_base)
        (x#(ProofT.condition_base + 1))
        sequence
        sequence
        (x#(ProofT.condition_base + 1))
        ProofT.condition_base
        (by native_decide)
        hSequenceBoundary
        (by simp [Term.substituteFree, set_variable])
        (by simp [Term.substituteFree, set_variable,
          ProofT.condition_base])
        hVariableVerifierBase hSequenceVerifierBase
  have hSequenceTransport :
      Γ ⊢ₘ[T]
        Formula.substituteFree SetSort.set
          ProofT.condition_base sequence sequenceBody :=
    FirstOrder.Derives.eq_subst_m
      (sort := SetSort.set)
      (eigen := ProofT.condition_base)
      (left := x#ProofT.condition_base)
      (right := sequence)
      (body := sequenceBody)
      hSequenceEquality hSequenceBodyAtLeft
  have hSequenceConditionCanonical :
      Γ ⊢ₘ[T]
        ProofT.sequence_condition verifier
          sequence
          (x#(ProofT.condition_base + 1)) := by
    rw [hSequenceSubstitution] at hSequenceTransport
    exact hSequenceTransport
  let certificateBody : SetFormula :=
    ProofT.sequence_condition verifier
      sequence
      (x#(ProofT.condition_base + 1))
  have hCertificateBodyAtLeft :
      Γ ⊢ₘ[T]
        Formula.substituteFree SetSort.set
          (ProofT.condition_base + 1)
          (x#(ProofT.condition_base + 1))
          certificateBody := by
    simpa [certificateBody,
      ProofT.formula_substitute_self] using
      hSequenceConditionCanonical
  have hCertificateSubstitution :
      Formula.substituteFree SetSort.set
          (ProofT.condition_base + 1)
          certificateSequence certificateBody =
        ProofT.sequence_condition verifier
          sequence certificateSequence := by
    simpa [certificateBody,
      ProofT.condition_base] using
      ProofT.sequence_condition_substitute
        verifier hTransport
        sequence
        (x#(ProofT.condition_base + 1))
        certificateSequence
        sequence certificateSequence
        (ProofT.condition_base + 1)
        (by native_decide)
        hCertificateSequenceBoundary
        (GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
          hSequenceBoundary
          (ProofT.condition_base + 1)
          certificateSequence)
        (by simp [Term.substituteFree, set_variable])
        hSequenceVerifierBase hSequenceVerifierBase
  have hCertificateTransport :
      Γ ⊢ₘ[T]
        Formula.substituteFree SetSort.set
          (ProofT.condition_base + 1)
          certificateSequence certificateBody :=
    FirstOrder.Derives.eq_subst_m
      (sort := SetSort.set)
      (eigen := ProofT.condition_base + 1)
      (left := x#(ProofT.condition_base + 1))
      (right := certificateSequence)
      (body := certificateBody)
      hCertificateSequenceEquality
      hCertificateBodyAtLeft
  have hCanonicalSequenceCondition :
      Γ ⊢ₘ[T]
        ProofT.sequence_condition verifier
          sequence certificateSequence := by
    rw [hCertificateSubstitution] at hCertificateTransport
    exact hCertificateTransport
  let terminalBody : SetFormula :=
    proof_sequence_terminal_condition
      (x#ProofT.condition_base) conclusion
  have hTerminalBodyAtLeft :
      Γ ⊢ₘ[T]
        Formula.substituteFree SetSort.set
          ProofT.condition_base
          (x#ProofT.condition_base)
          terminalBody := by
    simpa [terminalBody,
      ProofT.formula_substitute_self] using hTerminal
  have hTerminalSubstitution :
      Formula.substituteFree SetSort.set
          ProofT.condition_base sequence terminalBody =
        proof_sequence_terminal_condition
          sequence conclusion := by
    simpa [terminalBody] using
      proof_sequence_terminal_condition_substitute
        (x#ProofT.condition_base)
        conclusion sequence
        sequence conclusion
        ProofT.condition_base
        (by simp [Term.substituteFree, set_variable])
        (GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
          hConclusion
          ProofT.condition_base sequence)
  have hTerminalTransport :
      Γ ⊢ₘ[T]
        Formula.substituteFree SetSort.set
          ProofT.condition_base sequence terminalBody :=
    FirstOrder.Derives.eq_subst_m
      (sort := SetSort.set)
      (eigen := ProofT.condition_base)
      (left := x#ProofT.condition_base)
      (right := sequence)
      (body := terminalBody)
      hSequenceEquality hTerminalBodyAtLeft
  have hCanonicalTerminal :
      Γ ⊢ₘ[T]
        proof_sequence_terminal_condition
          sequence conclusion := by
    rw [hTerminalSubstitution] at hTerminalTransport
    exact hTerminalTransport
  simpa [rows, certificates, sequence,
    certificateSequence] using
    FirstOrder.Derives.conjIntro
      hCanonicalSequenceCondition hCanonicalTerminal

/-! ## 规范解码长度拒绝 -/

/--
外部解码得到的证明行数与证书数不同时，完整 numeral 证明码条件被拒绝。

该定理把规范 witness 反演和两条标准序列定义域合同封装在一起；具体理论只需
提供有限证书算术、序列编码反演与对象 replay 三个正交核心。
-/
theorem ProofT.code_neg_of_decoded_length
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (S : ProofT.SequenceInversion T)
    (R : ProofT.ObjectReplay T)
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (hSupport : ProofT.VerifierSupport verifier)
    (number : Nat)
    (conclusion : SetTerm)
    (hConclusion :
      GodelQuotation.Numbered.CodeBoundary conclusion)
    (hLength :
      (proof_sequence_decode
          (godel_unpair_value number).1).length ≠
        (nat_sequence_decode
          (godel_unpair_value number).2).length) :
    Derives T [] (
      ¬ₘ proof_condition
        verifier (numₘ(number)) conclusion
        ProofT.condition_base) := by
  let rows : List (List Nat) :=
    proof_sequence_decode
      (godel_unpair_value number).1
  let certificates : List Nat :=
    nat_sequence_decode
      (godel_unpair_value number).2
  apply
    ProofT.code_neg_of_length
      C.toFiniteCore
      verifier number conclusion
      ProofT.condition_base
      (standard_sequence
        (rows.map standard_token_sequence))
      (standard_token_sequence certificates)
      rows.length certificates.length hConclusion
  · intro Γ hWitness
    have hCanonical :=
      ProofT.witness_content
        C S verifier hTransport hSupport
        number conclusion hConclusion
        (by simpa [rows, certificates] using hWitness)
    simpa [rows, certificates] using
      FirstOrder.Derives.conjElimLeft hCanonical
  · exact
      ProofT.rows_domain
        R (Γ := ([] : Context signature)) rows
  · exact
      R.standard_token_sequence_domain
        (Γ := ([] : Context signature)) certificates
  · simpa [rows, certificates] using hLength

/-! ## 规范证明行上的公式 replay -/

/--
规范二维证明序列的 sequence condition 在任意有效行上给出公式 replay 条件。

该引理只消费标准序列 replay、行定义域事实与 verifier 的公式条件合同；
不依赖 terminal、schema 插件或具体宿主理论。
-/
theorem ProofT.row_replay
    {T : SetTheory}
    (R : ProofT.ObjectReplay T)
    {Γ : Context signature}
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (rows : List (List Nat))
    (certificates : SetTerm)
    (index : Nat)
    (hIndex : index < rows.length)
    (hCondition :
      Γ ⊢ₘ[T]
        ProofT.sequence_condition verifier
          (standard_sequence
            (rows.map standard_token_sequence))
          certificates) :
    Γ ⊢ₘ[T]
      fs_formula_replay_condition
        (standard_token_sequence rows[index]) := by
  let sequence : SetTerm :=
    standard_sequence
      (rows.map standard_token_sequence)
  have hSequenceClosed :
      Term.freeSupport sequence = [] := by
    dsimp [sequence]
    apply seq_support_nil_m 0
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, _, rfl⟩
    exact standard_token_sequence_freeSupport_nil tokens
  have hIndexDomain :
      Γ ⊢ₘ[T]
        numₘ(index) ∈ₘ domₘ(sequence) := by
    simpa [sequence] using
      ProofT.row_index_mem
        R (Γ := Γ) rows index hIndex
  have hFormulaAndLine :=
    ProofT.formula_and_line_of_sequence
      verifier hTransport sequence certificates index
      hSequenceClosed
      (by simpa [sequence] using hCondition)
      hIndexDomain
  have hTransportAt :
      Γ ⊢ₘ[T]
        fs_formula_replay_condition
          (sequence ·ₘ numₘ(index)) := by
    rw [← hTransport.formula_condition]
    exact FirstOrder.Derives.conjElimLeft hFormulaAndLine
  have hApplication :
      Γ ⊢ₘ[T]
        (sequence ·ₘ numₘ(index)) ≐ₘ
          standard_token_sequence rows[index] := by
    simpa [sequence] using
      ProofT.row_apply
        R (Γ := Γ) rows index hIndex
  have hTransportIff :=
    fs_formula_replay_condition_iff_of_equality
      (sequence ·ₘ numₘ(index))
      (standard_token_sequence rows[index])
      (function_application_term_admissible
        sequence (numₘ(index))
        (by
          dsimp [sequence]
          apply seq_admissible_m 0
          intro element hElement
          rcases List.mem_map.mp hElement with
            ⟨tokens, _, rfl⟩
          exact standard_token_sequence_admissible tokens)
        (finite_numeral_term_admissible index))
      (standard_token_sequence_admissible rows[index])
      hApplication
  exact FirstOrder.Derives.iffElimRight
    hTransportIff hTransportAt

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
