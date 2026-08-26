import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay

/-!
# checked 命题逻辑基础证书的精确反演

本模块只反演 `fs_logical_base_axiom_check` 的 tag 0–6。结果保留原 payload 的
公式列表解码等式及最终公式结构，不降格为会遗失 payload 的 `HilbertBaseAxiom`。
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

/-- tag 0–6 的 checked 计算反演结果。 -/
inductive FSLogicalPropositionalCheckWitness
    (payloadDecode : Nat → Option (List SetFormula))
    (formula : SetFormula) (payload : Nat) : Nat → Prop
  | implication_distribution
      (antecedent middle consequent : SetFormula)
      (hPayload :
        payloadDecode payload =
          some [antecedent, middle, consequent])
      (hFormula :
        formula =
          Formula.imp
            (Formula.imp antecedent
              (Formula.imp middle consequent))
            (Formula.imp
              (Formula.imp antecedent middle)
              (Formula.imp antecedent consequent))) :
      FSLogicalPropositionalCheckWitness
        payloadDecode formula payload 0
  | self_implication
      (body : SetFormula)
      (hPayload :
        payloadDecode payload = some [body])
      (hFormula :
        formula = Formula.imp body (Formula.imp body body)) :
      FSLogicalPropositionalCheckWitness
        payloadDecode formula payload 1
  | weakening
      (body extra : SetFormula)
      (hPayload :
        payloadDecode payload = some [body, extra])
      (hFormula :
        formula = Formula.imp body (Formula.imp extra body)) :
      FSLogicalPropositionalCheckWitness
        payloadDecode formula payload 2
  | contradiction
      (body conclusion : SetFormula)
      (hPayload :
        payloadDecode payload = some [body, conclusion])
      (hFormula :
        formula =
          Formula.imp body
            (Formula.imp (Formula.neg body) conclusion)) :
      FSLogicalPropositionalCheckWitness
        payloadDecode formula payload 3
  | classical
      (body : SetFormula)
      (hPayload :
        payloadDecode payload = some [body])
      (hFormula :
        formula =
          Formula.imp
            (Formula.imp (Formula.neg body) body)
            body) :
      FSLogicalPropositionalCheckWitness
        payloadDecode formula payload 4
  | explosion
      (body conclusion : SetFormula)
      (hPayload :
        payloadDecode payload = some [body, conclusion])
      (hFormula :
        formula =
          Formula.imp (Formula.neg body)
            (Formula.imp body conclusion)) :
      FSLogicalPropositionalCheckWitness
        payloadDecode formula payload 5
  | case_analysis
      (body conclusion : SetFormula)
      (hPayload :
        payloadDecode payload = some [body, conclusion])
      (hFormula :
        formula =
          Formula.imp
            (Formula.imp body conclusion)
            (Formula.imp
              (Formula.imp (Formula.neg body) conclusion)
              conclusion)) :
      FSLogicalPropositionalCheckWitness
        payloadDecode formula payload 6

/--
checked 基础证书通过且 tag 不超过 `6` 时，恢复对应命题模式的精确 payload。

这里只读取可计算检查器，不调用任何 Hilbert 公理反向实例。
-/
theorem fs_logical_base_axiom_check_with_propositional_witness
    {payloadDecode : Nat → Option (List SetFormula)}
    {formulaDecode : Nat → Option SetFormula}
    {formula : SetFormula} {certificate : Nat}
    (hCheck :
      fs_logical_base_axiom_check_with
        payloadDecode formulaDecode formula certificate = true)
    (hTagBound :
      (godel_unpair_value certificate).1 ≤ 6) :
    FSLogicalPropositionalCheckWitness
      payloadDecode formula
      (godel_unpair_value certificate).2
      (godel_unpair_value certificate).1 := by
  unfold fs_logical_base_axiom_check_with at hCheck
  generalize hPair :
      godel_unpair_value certificate = pair at hCheck hTagBound ⊢
  dsimp only at hCheck
  have hCases :
      pair.1 = 0 ∨ pair.1 = 1 ∨ pair.1 = 2 ∨
        pair.1 = 3 ∨ pair.1 = 4 ∨ pair.1 = 5 ∨
          pair.1 = 6 := by
    omega
  rcases hCases with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · rw [h0] at hCheck ⊢
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons antecedent tail =>
            cases tail with
            | nil =>
                simp [hPayload] at hCheck
            | cons middle tail =>
                cases tail with
                | nil =>
                    simp [hPayload] at hCheck
                | cons consequent tail =>
                    cases tail with
                    | cons extra rest =>
                        simp [hPayload] at hCheck
                    | nil =>
                        simp [hPayload] at hCheck
                        exact
                          .implication_distribution
                            antecedent middle consequent hPayload
                            (fs_formula_code_eq_sound hCheck)
  · rw [h1] at hCheck ⊢
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons body tail =>
            cases tail with
            | cons extra rest =>
                simp [hPayload] at hCheck
            | nil =>
                simp [hPayload] at hCheck
                exact
                  .self_implication body hPayload
                    (fs_formula_code_eq_sound hCheck)
  · rw [h2] at hCheck ⊢
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons body tail =>
            cases tail with
            | nil =>
                simp [hPayload] at hCheck
            | cons extra tail =>
                cases tail with
                | cons rest more =>
                    simp [hPayload] at hCheck
                | nil =>
                    simp [hPayload] at hCheck
                    exact
                      .weakening body extra hPayload
                        (fs_formula_code_eq_sound hCheck)
  · rw [h3] at hCheck ⊢
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons body tail =>
            cases tail with
            | nil =>
                simp [hPayload] at hCheck
            | cons conclusion tail =>
                cases tail with
                | cons rest more =>
                    simp [hPayload] at hCheck
                | nil =>
                    simp [hPayload] at hCheck
                    exact
                      .contradiction body conclusion hPayload
                        (fs_formula_code_eq_sound hCheck)
  · rw [h4] at hCheck ⊢
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons body tail =>
            cases tail with
            | cons extra rest =>
                simp [hPayload] at hCheck
            | nil =>
                simp [hPayload] at hCheck
                exact
                  .classical body hPayload
                    (fs_formula_code_eq_sound hCheck)
  · rw [h5] at hCheck ⊢
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons body tail =>
            cases tail with
            | nil =>
                simp [hPayload] at hCheck
            | cons conclusion tail =>
                cases tail with
                | cons rest more =>
                    simp [hPayload] at hCheck
                | nil =>
                    simp [hPayload] at hCheck
                    exact
                      .explosion body conclusion hPayload
                        (fs_formula_code_eq_sound hCheck)
  · rw [h6] at hCheck ⊢
    cases hPayload :
        payloadDecode pair.2 with
    | none =>
        simp [hPayload] at hCheck
    | some payload =>
        cases payload with
        | nil =>
            simp [hPayload] at hCheck
        | cons body tail =>
            cases tail with
            | nil =>
                simp [hPayload] at hCheck
            | cons conclusion tail =>
                cases tail with
                | cons rest more =>
                    simp [hPayload] at hCheck
                | nil =>
                    simp [hPayload] at hCheck
                    exact
                      .case_analysis body conclusion hPayload
                        (fs_formula_code_eq_sound hCheck)

/-- 规范 checker 的命题分支反演。 -/
theorem fs_logical_base_axiom_canonical_check_propositional_witness
    {formula : SetFormula} {certificate : Nat}
    (hCheck :
      fs_logical_base_axiom_canonical_check
        formula certificate = true)
    (hTagBound :
      (godel_unpair_value certificate).1 ≤ 6) :
    FSLogicalPropositionalCheckWitness
      fs_formula_payload_decode formula
      (godel_unpair_value certificate).2
      (godel_unpair_value certificate).1 := by
  exact fs_logical_base_axiom_check_with_propositional_witness
    (by
      simpa [fs_logical_base_axiom_canonical_check] using hCheck)
    hTagBound

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
