import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay

/-!
# checked 一阶逻辑基础证书的精确反演

本模块只反演 `fs_logical_base_axiom_check` 的 tag 7–11。每个构造器保留
payload 的数值形状、字段 decoder、项载体检查以及最终公式结构；对象层回放
不需要退回到 `HilbertLogicalAxiom` 的反向实例。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open ProofCode
open GodelQuotation
open Rosser

set_option autoImplicit false

namespace CertifiedProof

/-- tag 7–11 的 checked 计算反演结果。 -/
inductive FSLogicalFirstOrderCheckWitness
    (formulaDecode : Nat → Option SetFormula)
    (formula : SetFormula) (payload : Nat) : Nat → Prop
  | specialization
      (eigen bodyCode carrierCode : Nat)
      (body carrier : SetFormula) (term : SetTerm)
      (hPayload :
        payload =
          godel_pair_value eigen
            (godel_pair_value bodyCode carrierCode))
      (hBody :
        formulaDecode bodyCode =
          some body)
      (hCarrier :
        formulaDecode carrierCode =
          some carrier)
      (hTerm :
        fs_term_carrier_decode carrier = some term)
      (hWellSorted :
        Term.check_wellSorted SetSort.set term = true)
      (hScoped :
        Term.check_scoped Scope.empty term = true)
      (hFormula :
        formula =
          Formula.imp
            (Formula.forallE SetSort.set
              (Formula.closeFreeAt SetSort.set eigen 0 body))
            (Formula.openAt SetSort.set 0 term
              (Formula.closeFreeAt SetSort.set eigen 0 body))) :
      FSLogicalFirstOrderCheckWitness
        formulaDecode formula payload 7
  | forall_distribution
      (eigen leftCode rightCode : Nat)
      (antecedent consequent : SetFormula)
      (hPayload :
        payload =
          godel_pair_value eigen
            (godel_pair_value leftCode rightCode))
      (hAntecedent :
        formulaDecode leftCode =
          some antecedent)
      (hConsequent :
        formulaDecode rightCode =
          some consequent)
      (hFormula :
        formula =
          Formula.imp
            (Formula.forallE SetSort.set
              (Formula.imp
                (Formula.closeFreeAt SetSort.set eigen 0 antecedent)
                (Formula.closeFreeAt SetSort.set eigen 0 consequent)))
            (Formula.imp
              (Formula.forallE SetSort.set
                (Formula.closeFreeAt SetSort.set eigen 0 antecedent))
              (Formula.forallE SetSort.set
                (Formula.closeFreeAt SetSort.set eigen 0 consequent)))) :
      FSLogicalFirstOrderCheckWitness
        formulaDecode formula payload 8
  | vacuous_forall
      (eigen bodyCode : Nat) (body : SetFormula)
      (hPayload :
        payload = godel_pair_value eigen bodyCode)
      (hBody :
        formulaDecode bodyCode =
          some body)
      (hFresh :
        (SetSort.set, eigen) ∉ Formula.freeSupport body)
      (hFormula :
        formula =
          Formula.imp body
            (Formula.forallE SetSort.set
              (Formula.closeFreeAt SetSort.set eigen 0 body))) :
      FSLogicalFirstOrderCheckWitness
        formulaDecode formula payload 9
  | equality_substitution
      (leftId rightId bodyCode : Nat) (body : SetFormula)
      (hPayload :
        payload =
          nat_sequence_code_value [leftId, rightId, bodyCode])
      (hBody :
        formulaDecode bodyCode =
          some body)
      (hFormula :
        formula =
          Formula.imp
            (Formula.equal
              (Term.var (.fvar SetSort.set leftId))
              (Term.var (.fvar SetSort.set rightId)))
            (Formula.imp body
              (Formula.substituteFree SetSort.set leftId
                (Term.var (.fvar SetSort.set rightId)) body))) :
      FSLogicalFirstOrderCheckWitness
        formulaDecode formula payload 10
  | equality_reflexivity
      (hFormula :
        formula =
          Formula.equal
            (Term.var (.fvar SetSort.set payload))
            (Term.var (.fvar SetSort.set payload))) :
      FSLogicalFirstOrderCheckWitness
        formulaDecode formula payload 11

/-- checked 基础证书通过且 tag 不超过 `11` 时，恢复 tag 7–11 的精确 payload。 -/
theorem fs_logical_base_axiom_check_with_first_order_witness
    {payloadDecode : Nat → Option (List SetFormula)}
    {formulaDecode : Nat → Option SetFormula}
    {formula : SetFormula} {certificate : Nat}
    (hCheck :
      fs_logical_base_axiom_check_with
        payloadDecode formulaDecode formula certificate = true)
    (hTagLower :
      7 ≤ (godel_unpair_value certificate).1)
    (hTagUpper :
      (godel_unpair_value certificate).1 ≤ 11) :
    FSLogicalFirstOrderCheckWitness
      formulaDecode formula
      (godel_unpair_value certificate).2
      (godel_unpair_value certificate).1 := by
  unfold fs_logical_base_axiom_check_with at hCheck
  generalize hPair :
      godel_unpair_value certificate = pair at hCheck hTagLower hTagUpper ⊢
  dsimp only at hCheck
  have hCases :
      pair.1 = 7 ∨ pair.1 = 8 ∨ pair.1 = 9 ∨
        pair.1 = 10 ∨ pair.1 = 11 := by
    omega
  rcases hCases with h7 | h8 | h9 | h10 | h11
  · rw [h7] at hCheck ⊢
    generalize hPayloadPair :
        godel_unpair_value pair.2 = payloadPair at hCheck
    generalize hFormulaCodes :
        godel_unpair_value payloadPair.2 = formulaCodes at hCheck
    rcases payloadPair with ⟨eigen, nestedCode⟩
    rcases formulaCodes with ⟨bodyCode, carrierCode'⟩
    cases hBody :
        formulaDecode bodyCode with
    | none =>
        simp [hBody] at hCheck
    | some body =>
        cases hCarrierFormula :
            formulaDecode carrierCode' with
        | none =>
            simp [hCarrierFormula] at hCheck
        | some carrier =>
            cases hTerm :
                fs_term_carrier_decode carrier with
            | none =>
                simp_all
            | some term =>
                simp [hBody, hCarrierFormula, hTerm] at hCheck
                exact .specialization eigen bodyCode carrierCode'
                  body carrier term
                  (by
                    have hNestedCode :
                        nestedCode =
                          godel_pair_value bodyCode carrierCode' := by
                      have hCode :=
                        (godel_unpair_value_spec nestedCode).symm
                      rw [hFormulaCodes] at hCode
                      simpa using hCode
                    have hCode :=
                      (godel_unpair_value_spec pair.2).symm
                    rw [hPayloadPair, hNestedCode] at hCode
                    simpa using hCode)
                  hBody hCarrierFormula hTerm
                  hCheck.1.1
                  hCheck.1.2
                  (fs_formula_code_eq_sound hCheck.2)
  · rw [h8] at hCheck ⊢
    generalize hPayloadPair :
        godel_unpair_value pair.2 = payloadPair at hCheck
    generalize hFormulaCodes :
        godel_unpair_value payloadPair.2 = formulaCodes at hCheck
    rcases payloadPair with ⟨eigen, nestedCode⟩
    rcases formulaCodes with ⟨leftCode, rightCode⟩
    cases hAntecedent :
        formulaDecode leftCode with
    | none =>
        simp [hAntecedent] at hCheck
    | some antecedent =>
        cases hConsequent :
            formulaDecode rightCode with
        | none =>
            simp [hConsequent] at hCheck
        | some consequent =>
            simp [hAntecedent, hConsequent] at hCheck
            exact .forall_distribution eigen leftCode rightCode
              antecedent consequent
              (by
                have hNestedCode :
                    nestedCode =
                      godel_pair_value leftCode rightCode := by
                  have hCode :=
                    (godel_unpair_value_spec nestedCode).symm
                  rw [hFormulaCodes] at hCode
                  simpa using hCode
                have hCode :=
                  (godel_unpair_value_spec pair.2).symm
                rw [hPayloadPair, hNestedCode] at hCode
                simpa using hCode)
              hAntecedent hConsequent
              (fs_formula_code_eq_sound hCheck)
  · rw [h9] at hCheck ⊢
    generalize hPayloadPair :
        godel_unpair_value pair.2 = payloadPair at hCheck
    rcases payloadPair with ⟨eigen, bodyCode⟩
    cases hBody :
        formulaDecode bodyCode with
    | none =>
        simp [hBody] at hCheck
    | some body =>
        simp [hBody] at hCheck
        exact .vacuous_forall eigen bodyCode body
          (by
            have hCode :=
              (godel_unpair_value_spec pair.2).symm
            rw [hPayloadPair] at hCode
            simpa using hCode)
          hBody
          hCheck.1
          (fs_formula_code_eq_sound hCheck.2)
  · rw [h10] at hCheck ⊢
    cases hSequence : nat_sequence_decode pair.2 with
    | nil =>
        simp [hSequence] at hCheck
    | cons leftId tail =>
        cases hTail : tail with
        | nil =>
            simp [hSequence, hTail] at hCheck
        | cons rightId tail =>
            cases hRest : tail with
            | nil =>
                simp [hSequence, hTail, hRest] at hCheck
            | cons bodyCode rest =>
                cases hRestTail : rest with
                | nil =>
                    cases hBody :
                        formulaDecode bodyCode with
                    | none =>
                        simp [hSequence, hTail, hRest,
                          hRestTail, hBody] at hCheck
                    | some body =>
                        simp [hSequence, hTail, hRest,
                          hRestTail, hBody] at hCheck
                        exact .equality_substitution
                          leftId rightId bodyCode body
                          (by
                            calc
                              pair.2 =
                                  nat_sequence_code_value
                                    (nat_sequence_decode pair.2) :=
                                (nat_sequence_code_value_decode
                                  pair.2).symm
                              _ = nat_sequence_code_value
                                  [leftId, rightId, bodyCode] := by
                                simp [hSequence, hTail, hRest,
                                  hRestTail])
                          hBody
                          (fs_formula_code_eq_sound hCheck)
                | cons extra rest =>
                    simp [hSequence, hTail, hRest,
                      hRestTail] at hCheck
  · rw [h11] at hCheck ⊢
    simp [fs_formula_code_eq] at hCheck
    exact .equality_reflexivity
      (GodelQuotation.SyntaxCoding.formula_encode_injective hCheck)

/-- 规范 checker 的一阶分支反演。 -/
theorem fs_logical_base_axiom_canonical_check_first_order_witness
    {formula : SetFormula} {certificate : Nat}
    (hCheck :
      fs_logical_base_axiom_canonical_check
        formula certificate = true)
    (hTagLower :
      7 ≤ (godel_unpair_value certificate).1)
    (hTagUpper :
      (godel_unpair_value certificate).1 ≤ 11) :
    FSLogicalFirstOrderCheckWitness
      fs_formula_token_code_decode formula
      (godel_unpair_value certificate).2
      (godel_unpair_value certificate).1 := by
  exact fs_logical_base_axiom_check_with_first_order_witness
    (by
      simpa [fs_logical_base_axiom_canonical_check] using hCheck)
    hTagLower hTagUpper

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
