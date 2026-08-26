import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.NumeralArithmetic

/-!
# ZFC 对象证书的负向回放

本模块只处理对象证书条件的纯语法拒绝方向。固定表分支先归约为有限析取的
逐项否定；具体证书编码只需证明其自然数码不可能等于表中任一证书码。
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

set_option autoImplicit false

/-! ## schema 证书的有界坐标反演 -/

/--
把“点属于某项的后继”沿该项到有限 numeral 的等式运输，并化为有限 numeral
成员。schema 证书的每一层边界都通过该接口交给有限消去器。
-/
private theorem fs_zfc_support_raw_member_numeral_successor_of_bound_equality
    {Γ : Context signature}
    (point bound : SetTerm)
    (value : Nat)
    (hPoint : Term.Admissible point SetSort.set)
    (hBound : Term.Admissible bound SetSort.set)
    (hMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        point ∈ₘ Sₘ(bound))
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        bound ≐ₘ numₘ(value)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      point ∈ₘ numₘ(value + 1) := by
  have hSuccessorEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        Sₘ(bound) ≐ₘ Sₘ(numₘ(value)) :=
    successor_term_congr_of_equality
      bound (numₘ(value))
      hBound (finite_numeral_term_admissible value)
      hEquality
  have hAtSuccessor :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        point ∈ₘ Sₘ(numₘ(value)) :=
    FirstOrder.Derives.iffElimRight
      (membership_right_iff_of_equality
        point (Sₘ(bound)) (Sₘ(numₘ(value)))
        hPoint
        (successor_term_admissible bound hBound)
        (successor_term_admissible
          (numₘ(value))
          (finite_numeral_term_admissible value))
        hSuccessorEquality)
      hMember
  simpa [finite_numeral_term, successor_term] using
    hAtSuccessor

/--
一次性打开五层对象存在见证。各层被消去的存在公式保留在局部上下文中，
因此最终分支可直接读取最内层 witness body；量词新鲜性由每层 canonical
closure 逐层传播。
-/
private theorem fs_zfc_support_raw_exists_five_elim_falsum
    {Γ : Context signature}
    (first second third fourth fifth : FreeVarId)
    (body : SetFormula)
    (hBody : Formula.Admissible body)
    (hFirstFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, first) ∉ Formula.freeSupport formula)
    (hSecondFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, second) ∉ Formula.freeSupport formula)
    (hThirdFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, third) ∉ Formula.freeSupport formula)
    (hFourthFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, fourth) ∉ Formula.freeSupport formula)
    (hFifthFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, fifth) ∉ Formula.freeSupport formula)
    (hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, first],
          ∃ₘ[SetSort.set, second],
            ∃ₘ[SetSort.set, third],
              ∃ₘ[SetSort.set, fourth],
                ∃ₘ[SetSort.set, fifth], body)
    (hCase :
      body ::
        (∃ₘ[SetSort.set, fifth], body) ::
        (∃ₘ[SetSort.set, fourth],
          ∃ₘ[SetSort.set, fifth], body) ::
        (∃ₘ[SetSort.set, third],
          ∃ₘ[SetSort.set, fourth],
            ∃ₘ[SetSort.set, fifth], body) ::
        (∃ₘ[SetSort.set, second],
          ∃ₘ[SetSort.set, third],
            ∃ₘ[SetSort.set, fourth],
              ∃ₘ[SetSort.set, fifth], body) :: Γ
        ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  let fifthExists : SetFormula :=
    ∃ₘ[SetSort.set, fifth], body
  let fourthExists : SetFormula :=
    ∃ₘ[SetSort.set, fourth], fifthExists
  let thirdExists : SetFormula :=
    ∃ₘ[SetSort.set, third], fourthExists
  let secondExists : SetFormula :=
    ∃ₘ[SetSort.set, second], thirdExists
  have hFifthExists :
      Formula.Admissible fifthExists := by
    simpa [fifthExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set fifth hBody
  have hFourthExists :
      Formula.Admissible fourthExists := by
    simpa [fourthExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set fourth hFifthExists
  have hThirdExists :
      Formula.Admissible thirdExists := by
    simpa [thirdExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set third hFourthExists
  have hSecondExists :
      Formula.Admissible secondExists := by
    simpa [secondExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set second hThirdExists
  have hTheoryFresh (id : FreeVarId) :
      ∀ formula, fs_zfc_support_raw_theory formula →
        (SetSort.set, id) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hFalsumFresh (id : FreeVarId) :
      (SetSort.set, id) ∉
        Formula.freeSupport (Formula.falsum : SetFormula) := by
    exact List.not_mem_nil
  nd_apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := first)
    (body := secondExists)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hSecondExists)
  · exact hTheoryFresh first
  · exact hFirstFresh
  · exact hFalsumFresh first
  · simpa [secondExists, thirdExists,
      fourthExists, fifthExists] using hExists
  · let Δ₁ : Context signature := secondExists :: Γ
    have hSecondExistsAt :
        Δ₁ ⊢ₘ[fs_zfc_support_raw_theory] secondExists :=
      FirstOrder.Derives.assumption (by simp [Δ₁])
    have hSecondOwnFresh :
        (SetSort.set, second) ∉
          Formula.freeSupport secondExists := by
      simpa [secondExists] using
        Formula.not_mem_freeSupport_closeFreeAt
          SetSort.set second 0 thirdExists
    nd_apply FirstOrder.Derives.exists_elim
      (T := fs_zfc_support_raw_theory)
      (Γ := Δ₁)
      (sort := SetSort.set)
      (eigen := second)
      (body := thirdExists)
      (conclusion := Formula.falsum)
      (hBodyCheck :=
        Formula.check_admissible_complete hThirdExists)
    · exact hTheoryFresh second
    · intro formula hFormula
      simp only [Δ₁, List.mem_cons] at hFormula
      rcases hFormula with rfl | hFormula
      · exact hSecondOwnFresh
      · exact hSecondFresh formula hFormula
    · exact hFalsumFresh second
    · exact hSecondExistsAt
    · let Δ₂ : Context signature := thirdExists :: Δ₁
      have hThirdExistsAt :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory] thirdExists :=
        FirstOrder.Derives.assumption (by simp [Δ₂])
      have hThirdOwnFresh :
          (SetSort.set, third) ∉
            Formula.freeSupport thirdExists := by
        simpa [thirdExists] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set third 0 fourthExists
      have hThirdFreshSecond :
          (SetSort.set, third) ∉
            Formula.freeSupport secondExists := by
        simpa [secondExists] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, third)
            SetSort.set second 0 thirdExists
            hThirdOwnFresh
      nd_apply FirstOrder.Derives.exists_elim
        (T := fs_zfc_support_raw_theory)
        (Γ := Δ₂)
        (sort := SetSort.set)
        (eigen := third)
        (body := fourthExists)
        (conclusion := Formula.falsum)
        (hBodyCheck :=
          Formula.check_admissible_complete hFourthExists)
      · exact hTheoryFresh third
      · intro formula hFormula
        simp only [Δ₂, Δ₁, List.mem_cons] at hFormula
        rcases hFormula with rfl | rfl | hFormula
        · exact hThirdOwnFresh
        · exact hThirdFreshSecond
        · exact hThirdFresh formula hFormula
      · exact hFalsumFresh third
      · exact hThirdExistsAt
      · let Δ₃ : Context signature := fourthExists :: Δ₂
        have hFourthExistsAt :
            Δ₃ ⊢ₘ[fs_zfc_support_raw_theory] fourthExists :=
          FirstOrder.Derives.assumption (by simp [Δ₃])
        have hFourthOwnFresh :
            (SetSort.set, fourth) ∉
              Formula.freeSupport fourthExists := by
          simpa [fourthExists] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set fourth 0 fifthExists
        have hFourthFreshThird :
            (SetSort.set, fourth) ∉
              Formula.freeSupport thirdExists := by
          simpa [thirdExists] using
            Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
              (SetSort.set, fourth)
              SetSort.set third 0 fourthExists
              hFourthOwnFresh
        have hFourthFreshSecond :
            (SetSort.set, fourth) ∉
              Formula.freeSupport secondExists := by
          simpa [secondExists] using
            Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
              (SetSort.set, fourth)
              SetSort.set second 0 thirdExists
              hFourthFreshThird
        nd_apply FirstOrder.Derives.exists_elim
          (T := fs_zfc_support_raw_theory)
          (Γ := Δ₃)
          (sort := SetSort.set)
          (eigen := fourth)
          (body := fifthExists)
          (conclusion := Formula.falsum)
          (hBodyCheck :=
            Formula.check_admissible_complete hFifthExists)
        · exact hTheoryFresh fourth
        · intro formula hFormula
          simp only [Δ₃, Δ₂, Δ₁,
            List.mem_cons] at hFormula
          rcases hFormula with
            rfl | rfl | rfl | hFormula
          · exact hFourthOwnFresh
          · exact hFourthFreshThird
          · exact hFourthFreshSecond
          · exact hFourthFresh formula hFormula
        · exact hFalsumFresh fourth
        · exact hFourthExistsAt
        · let Δ₄ : Context signature := fifthExists :: Δ₃
          have hFifthExistsAt :
              Δ₄ ⊢ₘ[fs_zfc_support_raw_theory] fifthExists :=
            FirstOrder.Derives.assumption (by simp [Δ₄])
          have hFifthOwnFresh :
              (SetSort.set, fifth) ∉
                Formula.freeSupport fifthExists := by
            simpa [fifthExists] using
              Formula.not_mem_freeSupport_closeFreeAt
                SetSort.set fifth 0 body
          have hFifthFreshFourth :
              (SetSort.set, fifth) ∉
                Formula.freeSupport fourthExists := by
            simpa [fourthExists] using
              Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
                (SetSort.set, fifth)
                SetSort.set fourth 0 fifthExists
                hFifthOwnFresh
          have hFifthFreshThird :
              (SetSort.set, fifth) ∉
                Formula.freeSupport thirdExists := by
            simpa [thirdExists] using
              Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
                (SetSort.set, fifth)
                SetSort.set third 0 fourthExists
                hFifthFreshFourth
          have hFifthFreshSecond :
              (SetSort.set, fifth) ∉
                Formula.freeSupport secondExists := by
            simpa [secondExists] using
              Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
                (SetSort.set, fifth)
                SetSort.set second 0 thirdExists
                hFifthFreshThird
          nd_apply FirstOrder.Derives.exists_elim
            (T := fs_zfc_support_raw_theory)
            (Γ := Δ₄)
            (sort := SetSort.set)
            (eigen := fifth)
            (body := body)
            (conclusion := Formula.falsum)
            (hBodyCheck :=
              Formula.check_admissible_complete hBody)
          · exact hTheoryFresh fifth
          · intro formula hFormula
            simp only [Δ₄, Δ₃, Δ₂, Δ₁,
              List.mem_cons] at hFormula
            rcases hFormula with
              rfl | rfl | rfl | rfl | hFormula
            · exact hFifthOwnFresh
            · exact hFifthFreshFourth
            · exact hFifthFreshThird
            · exact hFifthFreshSecond
            · exact hFifthFresh formula hFormula
          · exact hFalsumFresh fifth
          · exact hFifthExistsAt
          · simpa [Δ₄, Δ₃, Δ₂, Δ₁,
              secondExists, thirdExists,
              fourthExists, fifthExists] using hCase

/-- 将五层存在见证的反证分支封装为闭合否定。 -/
theorem fs_zfc_support_raw_exists_five_neg
    (first second third fourth fifth : FreeVarId)
    (body : SetFormula)
    (hBody : Formula.Admissible body)
    (hCase :
      body ::
        (∃ₘ[SetSort.set, fifth], body) ::
        (∃ₘ[SetSort.set, fourth],
          ∃ₘ[SetSort.set, fifth], body) ::
        (∃ₘ[SetSort.set, third],
          ∃ₘ[SetSort.set, fourth],
            ∃ₘ[SetSort.set, fifth], body) ::
        (∃ₘ[SetSort.set, second],
          ∃ₘ[SetSort.set, third],
            ∃ₘ[SetSort.set, fourth],
              ∃ₘ[SetSort.set, fifth], body) ::
        [(∃ₘ[SetSort.set, first],
          ∃ₘ[SetSort.set, second],
            ∃ₘ[SetSort.set, third],
              ∃ₘ[SetSort.set, fourth],
                ∃ₘ[SetSort.set, fifth], body)]
        ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ (∃ₘ[SetSort.set, first],
        ∃ₘ[SetSort.set, second],
          ∃ₘ[SetSort.set, third],
            ∃ₘ[SetSort.set, fourth],
              ∃ₘ[SetSort.set, fifth], body)) := by
  let fifthExists : SetFormula :=
    ∃ₘ[SetSort.set, fifth], body
  let fourthExists : SetFormula :=
    ∃ₘ[SetSort.set, fourth], fifthExists
  let thirdExists : SetFormula :=
    ∃ₘ[SetSort.set, third], fourthExists
  let secondExists : SetFormula :=
    ∃ₘ[SetSort.set, second], thirdExists
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, first], secondExists
  have hFifthOwnFresh :
      (SetSort.set, fifth) ∉
        Formula.freeSupport fifthExists := by
    simpa [fifthExists] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set fifth 0 body
  have hFifthFreshFourth :
      (SetSort.set, fifth) ∉
        Formula.freeSupport fourthExists := by
    simpa [fourthExists] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, fifth)
        SetSort.set fourth 0 fifthExists
        hFifthOwnFresh
  have hFifthFreshThird :
      (SetSort.set, fifth) ∉
        Formula.freeSupport thirdExists := by
    simpa [thirdExists] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, fifth)
        SetSort.set third 0 fourthExists
        hFifthFreshFourth
  have hFifthFreshSecond :
      (SetSort.set, fifth) ∉
        Formula.freeSupport secondExists := by
    simpa [secondExists] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, fifth)
        SetSort.set second 0 thirdExists
        hFifthFreshThird
  have hFifthFreshCondition :
      (SetSort.set, fifth) ∉
        Formula.freeSupport condition := by
    simpa [condition] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, fifth)
        SetSort.set first 0 secondExists
        hFifthFreshSecond
  have hFourthOwnFresh :
      (SetSort.set, fourth) ∉
        Formula.freeSupport fourthExists := by
    simpa [fourthExists] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set fourth 0 fifthExists
  have hFourthFreshThird :
      (SetSort.set, fourth) ∉
        Formula.freeSupport thirdExists := by
    simpa [thirdExists] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, fourth)
        SetSort.set third 0 fourthExists
        hFourthOwnFresh
  have hFourthFreshSecond :
      (SetSort.set, fourth) ∉
        Formula.freeSupport secondExists := by
    simpa [secondExists] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, fourth)
        SetSort.set second 0 thirdExists
        hFourthFreshThird
  have hFourthFreshCondition :
      (SetSort.set, fourth) ∉
        Formula.freeSupport condition := by
    simpa [condition] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, fourth)
        SetSort.set first 0 secondExists
        hFourthFreshSecond
  have hThirdOwnFresh :
      (SetSort.set, third) ∉
        Formula.freeSupport thirdExists := by
    simpa [thirdExists] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set third 0 fourthExists
  have hThirdFreshSecond :
      (SetSort.set, third) ∉
        Formula.freeSupport secondExists := by
    simpa [secondExists] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, third)
        SetSort.set second 0 thirdExists
        hThirdOwnFresh
  have hThirdFreshCondition :
      (SetSort.set, third) ∉
        Formula.freeSupport condition := by
    simpa [condition] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, third)
        SetSort.set first 0 secondExists
        hThirdFreshSecond
  have hSecondOwnFresh :
      (SetSort.set, second) ∉
        Formula.freeSupport secondExists := by
    simpa [secondExists] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set second 0 thirdExists
  have hSecondFreshCondition :
      (SetSort.set, second) ∉
        Formula.freeSupport condition := by
    simpa [condition] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, second)
        SetSort.set first 0 secondExists
        hSecondOwnFresh
  have hFirstFreshCondition :
      (SetSort.set, first) ∉
        Formula.freeSupport condition := by
    simpa [condition] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set first 0 secondExists
  have hSecondExists :
      Formula.Admissible secondExists := by
    have hFifth :
        Formula.Admissible fifthExists := by
      simpa [fifthExists] using
        Formula.Admissible.exists_closeFreeAt
          SetSort.set fifth hBody
    have hFourth :
        Formula.Admissible fourthExists := by
      simpa [fourthExists] using
        Formula.Admissible.exists_closeFreeAt
          SetSort.set fourth hFifth
    have hThird :
        Formula.Admissible thirdExists := by
      simpa [thirdExists] using
        Formula.Admissible.exists_closeFreeAt
          SetSort.set third hFourth
    simpa [secondExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set second hThird
  have hCondition :
      Formula.Admissible condition := by
    simpa [condition] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set first hSecondExists
  nd_apply FirstOrder.Derives.negIntro
    (T := fs_zfc_support_raw_theory)
    (Γ := ([] : Context signature))
    (body := condition)
    (hBodyCheck :=
      Formula.check_admissible_complete hCondition)
  let Γ : Context signature := [condition]
  have hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] condition :=
    FirstOrder.Derives.assumption (by simp [Γ])
  exact fs_zfc_support_raw_exists_five_elim_falsum
    first second third fourth fifth body hBody
    (by
      intro formula hFormula
      simp only [List.mem_singleton] at hFormula
      subst formula
      exact hFirstFreshCondition)
    (by
      intro formula hFormula
      simp only [List.mem_singleton] at hFormula
      subst formula
      exact hSecondFreshCondition)
    (by
      intro formula hFormula
      simp only [List.mem_singleton] at hFormula
      subst formula
      exact hThirdFreshCondition)
    (by
      intro formula hFormula
      simp only [List.mem_singleton] at hFormula
      subst formula
      exact hFourthFreshCondition)
    (by
      intro formula hFormula
      simp only [List.mem_singleton] at hFormula
      subst formula
      exact hFifthFreshCondition)
    (by
      simpa [condition, secondExists, thirdExists,
        fourthExists, fifthExists] using hExists)
    (by
      simpa [Γ, condition, secondExists, thirdExists,
        fourthExists, fifthExists] using hCase)

/--
由 schema 证书等式及逐层 successor 界，有限反演出参数个数与 body token 码。

结论分支只获得两个规范坐标等式和对应的宿主层证书码等式；中间 payload
枚举值不泄漏到接口中。证明完全是有限语法消去，不要求对象算术中的全局
Gödel 配对单射。
-/
theorem fs_zfc_support_raw_schema_certificate_coordinates_elim
    {Γ : Context signature}
    (raw schemaTag : Nat)
    (parameterCount bodyTokenCode : SetTerm)
    (conclusion : SetFormula)
    (hParameterCount :
      Term.Admissible parameterCount SetSort.set)
    (hBodyTokenCode :
      Term.Admissible bodyTokenCode SetSort.set)
    (hConclusion : Formula.Admissible conclusion)
    (hCertificateEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(schemaTag))
            parameterCount bodyTokenCode)
    (hBounds :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_zfc_schema_certificate_bounds
          (numₘ(raw)) (numₘ(schemaTag))
          parameterCount bodyTokenCode)
    (hBranch :
      ∀ parameterValue bodyTokenValue,
        raw =
          godel_pair_value 1
            (godel_pair_value schemaTag
              (godel_pair_value
                parameterValue bodyTokenValue)) →
        (bodyTokenCode ≐ₘ numₘ(bodyTokenValue)) ::
          (parameterCount ≐ₘ numₘ(parameterValue)) :: Γ
            ⊢ₘ[fs_zfc_support_raw_theory] conclusion) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] conclusion := by
  let bodyPayload : SetTerm :=
    fs_zfc_schema_body_payload_term
      parameterCount bodyTokenCode
  let schemaPayload : SetTerm :=
    fs_zfc_schema_payload_term
      (numₘ(schemaTag)) parameterCount bodyTokenCode
  have hBodyPayload :
      Term.Admissible bodyPayload SetSort.set := by
    simpa [bodyPayload] using
      fs_zfc_schema_body_payload_term_admissible
        parameterCount bodyTokenCode
        hParameterCount hBodyTokenCode
  have hSchemaPayload :
      Term.Admissible schemaPayload SetSort.set := by
    simpa [schemaPayload] using
      fs_zfc_schema_payload_term_admissible
        (numₘ(schemaTag)) parameterCount bodyTokenCode
        (finite_numeral_term_admissible schemaTag)
        hParameterCount hBodyTokenCode
  have hSchemaBound :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        schemaPayload ∈ₘ Sₘ(numₘ(raw)) := by
    simpa [fs_zfc_schema_certificate_bounds,
      schemaPayload, bodyPayload] using
      FirstOrder.Derives.conjElimLeft hBounds
  have hBodyBound :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        bodyPayload ∈ₘ Sₘ(schemaPayload) := by
    simpa [fs_zfc_schema_certificate_bounds,
      schemaPayload, bodyPayload] using
      FirstOrder.Derives.conjElimLeft
        (FirstOrder.Derives.conjElimRight hBounds)
  have hParameterBound :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        parameterCount ∈ₘ Sₘ(bodyPayload) := by
    simpa [fs_zfc_schema_certificate_bounds,
      schemaPayload, bodyPayload] using
      FirstOrder.Derives.conjElimLeft
        (FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight hBounds))
  have hBodyTokenBound :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        bodyTokenCode ∈ₘ Sₘ(bodyPayload) := by
    simpa [fs_zfc_schema_certificate_bounds,
      schemaPayload, bodyPayload] using
      FirstOrder.Derives.conjElimRight
        (FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight hBounds))
  have hSchemaMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        schemaPayload ∈ₘ numₘ(raw + 1) := by
    simpa [finite_numeral_term, successor_term] using
      hSchemaBound
  apply
    fs_zfc_support_raw_finite_numeral_member_elim_context
      (raw + 1) schemaPayload conclusion
      hSchemaPayload hConclusion hSchemaMember
  intro schemaValue _
  let schemaEquality : SetFormula :=
    schemaPayload ≐ₘ numₘ(schemaValue)
  let Δ : Context signature := schemaEquality :: Γ
  change Δ ⊢ₘ[fs_zfc_support_raw_theory] conclusion
  have hSchemaEquality :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        schemaPayload ≐ₘ numₘ(schemaValue) :=
    FirstOrder.Derives.assumption (by simp [Δ, schemaEquality])
  have hBodyBoundAt :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        bodyPayload ∈ₘ Sₘ(schemaPayload) :=
    FirstOrder.Derives.context_weaken_cons hBodyBound
  have hBodyMember :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        bodyPayload ∈ₘ numₘ(schemaValue + 1) :=
    fs_zfc_support_raw_member_numeral_successor_of_bound_equality
      bodyPayload schemaPayload schemaValue
      hBodyPayload hSchemaPayload
      hBodyBoundAt hSchemaEquality
  apply
    fs_zfc_support_raw_finite_numeral_member_elim_context
      (schemaValue + 1) bodyPayload conclusion
      hBodyPayload hConclusion hBodyMember
  intro bodyValue _
  let bodyEquality : SetFormula :=
    bodyPayload ≐ₘ numₘ(bodyValue)
  let Ε : Context signature := bodyEquality :: Δ
  change Ε ⊢ₘ[fs_zfc_support_raw_theory] conclusion
  have hBodyEquality :
      Ε ⊢ₘ[fs_zfc_support_raw_theory]
        bodyPayload ≐ₘ numₘ(bodyValue) :=
    FirstOrder.Derives.assumption (by simp [Ε, bodyEquality])
  have hParameterBoundAt :
      Ε ⊢ₘ[fs_zfc_support_raw_theory]
        parameterCount ∈ₘ Sₘ(bodyPayload) :=
    FirstOrder.Derives.context_weaken_cons
      (FirstOrder.Derives.context_weaken_cons
        hParameterBound)
  have hParameterMember :
      Ε ⊢ₘ[fs_zfc_support_raw_theory]
        parameterCount ∈ₘ numₘ(bodyValue + 1) :=
    fs_zfc_support_raw_member_numeral_successor_of_bound_equality
      parameterCount bodyPayload bodyValue
      hParameterCount hBodyPayload
      hParameterBoundAt hBodyEquality
  apply
    fs_zfc_support_raw_finite_numeral_member_elim_context
      (bodyValue + 1) parameterCount conclusion
      hParameterCount hConclusion hParameterMember
  intro parameterValue _
  let parameterEquality : SetFormula :=
    parameterCount ≐ₘ numₘ(parameterValue)
  let Ζ : Context signature := parameterEquality :: Ε
  change Ζ ⊢ₘ[fs_zfc_support_raw_theory] conclusion
  have hParameterEquality :
      Ζ ⊢ₘ[fs_zfc_support_raw_theory]
        parameterCount ≐ₘ numₘ(parameterValue) :=
    FirstOrder.Derives.assumption
      (by simp [Ζ, parameterEquality])
  have hBodyTokenBoundAt :
      Ζ ⊢ₘ[fs_zfc_support_raw_theory]
        bodyTokenCode ∈ₘ Sₘ(bodyPayload) :=
    FirstOrder.Derives.context_weaken_cons
      (FirstOrder.Derives.context_weaken_cons
        (FirstOrder.Derives.context_weaken_cons
          hBodyTokenBound))
  have hBodyEqualityAt :
      Ζ ⊢ₘ[fs_zfc_support_raw_theory]
        bodyPayload ≐ₘ numₘ(bodyValue) :=
    FirstOrder.Derives.context_weaken_cons hBodyEquality
  have hBodyTokenMember :
      Ζ ⊢ₘ[fs_zfc_support_raw_theory]
        bodyTokenCode ∈ₘ numₘ(bodyValue + 1) :=
    fs_zfc_support_raw_member_numeral_successor_of_bound_equality
      bodyTokenCode bodyPayload bodyValue
      hBodyTokenCode hBodyPayload
      hBodyTokenBoundAt hBodyEqualityAt
  apply
    fs_zfc_support_raw_finite_numeral_member_elim_context
      (bodyValue + 1) bodyTokenCode conclusion
      hBodyTokenCode hConclusion hBodyTokenMember
  intro bodyTokenValue _
  let bodyTokenEquality : SetFormula :=
    bodyTokenCode ≐ₘ numₘ(bodyTokenValue)
  let Η : Context signature := bodyTokenEquality :: Ζ
  change Η ⊢ₘ[fs_zfc_support_raw_theory] conclusion
  have hBodyTokenEquality :
      Η ⊢ₘ[fs_zfc_support_raw_theory]
        bodyTokenCode ≐ₘ numₘ(bodyTokenValue) :=
    FirstOrder.Derives.assumption
      (by simp [Η, bodyTokenEquality])
  have hParameterEqualityAt :
      Η ⊢ₘ[fs_zfc_support_raw_theory]
        parameterCount ≐ₘ numₘ(parameterValue) :=
    FirstOrder.Derives.context_weaken_cons
      hParameterEquality
  have hBodyComputed :
      Η ⊢ₘ[fs_zfc_support_raw_theory]
        bodyPayload ≐ₘ
          numₘ(godel_pair_value
            parameterValue bodyTokenValue) := by
    have hCongruence :
        Η ⊢ₘ[fs_zfc_support_raw_theory]
          bodyPayload ≐ₘ
            godel_pairₘ(⟨numₘ(parameterValue),
              numₘ(bodyTokenValue)⟩ₘ) := by
      simpa [bodyPayload,
        fs_zfc_schema_body_payload_term] using
        godel_pairing_term_congr_of_equalities
          parameterCount (numₘ(parameterValue))
          bodyTokenCode (numₘ(bodyTokenValue))
          hParameterCount
          (finite_numeral_term_admissible parameterValue)
          hBodyTokenCode
          (finite_numeral_term_admissible bodyTokenValue)
          hParameterEqualityAt hBodyTokenEquality
    exact Metatheory.Derives.equality_trans
      hCongruence
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Η) (by simp [Η, Ζ, Ε, Δ])
        (fs_zfc_support_raw_godel_pair_value_eq
          parameterValue bodyTokenValue))
  have hSchemaComputed :
      Η ⊢ₘ[fs_zfc_support_raw_theory]
        schemaPayload ≐ₘ
          numₘ(godel_pair_value schemaTag
            (godel_pair_value
              parameterValue bodyTokenValue)) := by
    have hCongruence :
        Η ⊢ₘ[fs_zfc_support_raw_theory]
          schemaPayload ≐ₘ
            godel_pairₘ(⟨numₘ(schemaTag),
              numₘ(godel_pair_value
                parameterValue bodyTokenValue)⟩ₘ) := by
      simpa [schemaPayload,
        fs_zfc_schema_payload_term] using
        godel_pairing_term_congr_of_equalities
          (numₘ(schemaTag)) (numₘ(schemaTag))
          bodyPayload
          (numₘ(godel_pair_value
            parameterValue bodyTokenValue))
          (finite_numeral_term_admissible schemaTag)
          (finite_numeral_term_admissible schemaTag)
          hBodyPayload
          (finite_numeral_term_admissible
            (godel_pair_value
              parameterValue bodyTokenValue))
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) (numₘ(schemaTag)))
          hBodyComputed
    exact Metatheory.Derives.equality_trans
      hCongruence
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Η) (by simp [Η, Ζ, Ε, Δ])
        (fs_zfc_support_raw_godel_pair_value_eq
          schemaTag
          (godel_pair_value
            parameterValue bodyTokenValue)))
  have hCertificateComputed :
      Η ⊢ₘ[fs_zfc_support_raw_theory]
        fs_zfc_schema_certificate_term
          (numₘ(schemaTag))
          parameterCount bodyTokenCode ≐ₘ
            numₘ(godel_pair_value 1
              (godel_pair_value schemaTag
                (godel_pair_value
                  parameterValue bodyTokenValue))) := by
    have hCongruence :
        Η ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_schema_certificate_term
            (numₘ(schemaTag))
            parameterCount bodyTokenCode ≐ₘ
              godel_pairₘ(⟨numₘ(1),
                numₘ(godel_pair_value schemaTag
                  (godel_pair_value
                    parameterValue bodyTokenValue))⟩ₘ) := by
      simpa [fs_zfc_schema_certificate_term] using
        godel_pairing_term_congr_of_equalities
          (numₘ(1)) (numₘ(1))
          schemaPayload
          (numₘ(godel_pair_value schemaTag
            (godel_pair_value
              parameterValue bodyTokenValue)))
          (finite_numeral_term_admissible 1)
          (finite_numeral_term_admissible 1)
          hSchemaPayload
          (finite_numeral_term_admissible
            (godel_pair_value schemaTag
              (godel_pair_value
                parameterValue bodyTokenValue)))
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) (numₘ(1)))
          hSchemaComputed
    exact Metatheory.Derives.equality_trans
      hCongruence
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Η) (by simp [Η, Ζ, Ε, Δ])
        (fs_zfc_support_raw_godel_pair_value_eq
          1
          (godel_pair_value schemaTag
            (godel_pair_value
              parameterValue bodyTokenValue))))
  have hCertificateEqualityAt :
      Η ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(schemaTag))
            parameterCount bodyTokenCode :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Η)
      (by
        intro formula hFormula
        simp only [Η, Ζ, Ε, Δ, List.mem_cons]
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr hFormula)
      hCertificateEquality
  have hNumeralEquality :
      Η ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          numₘ(godel_pair_value 1
            (godel_pair_value schemaTag
              (godel_pair_value
                parameterValue bodyTokenValue))) :=
    Metatheory.Derives.equality_trans
      hCertificateEqualityAt hCertificateComputed
  by_cases hCode :
      raw =
        godel_pair_value 1
          (godel_pair_value schemaTag
            (godel_pair_value
              parameterValue bodyTokenValue))
  · exact FirstOrder.Derives.context_weaken
      (Γ :=
        (bodyTokenCode ≐ₘ numₘ(bodyTokenValue)) ::
          (parameterCount ≐ₘ numₘ(parameterValue)) :: Γ)
      (Δ := Η)
      (by
        intro formula hFormula
        simp only [List.mem_cons] at hFormula
        simp only [Η, Ζ, Ε, Δ, bodyTokenEquality,
          parameterEquality, bodyEquality, schemaEquality,
          List.mem_cons]
        rcases hFormula with hFormula | hFormula
        · exact Or.inl hFormula
        · rcases hFormula with hFormula | hFormula
          · exact Or.inr <| Or.inl hFormula
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr hFormula)
      (hBranch parameterValue bodyTokenValue hCode)
  · exact FirstOrder.Derives.falsumElim
      (fs_zfc_support_raw_falsum_of_numeral_equality
        hCode hNumeralEquality)

/-!
当宿主层已经判定某 schema 标签下不存在任何匹配坐标时，坐标消去立即给出
对象层矛盾。该接口是后续 separation/collection 分支拒绝的直接内核。
-/
theorem fs_zfc_support_raw_schema_certificate_falsum_of_code_ne
    {Γ : Context signature}
    (raw schemaTag : Nat)
    (parameterCount bodyTokenCode : SetTerm)
    (hParameterCount :
      Term.Admissible parameterCount SetSort.set)
    (hBodyTokenCode :
      Term.Admissible bodyTokenCode SetSort.set)
    (hCertificateEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(schemaTag))
            parameterCount bodyTokenCode)
    (hBounds :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_zfc_schema_certificate_bounds
          (numₘ(raw)) (numₘ(schemaTag))
          parameterCount bodyTokenCode)
    (hInvalid :
      ∀ parameterValue bodyTokenValue,
        raw ≠
          godel_pair_value 1
            (godel_pair_value schemaTag
              (godel_pair_value
                parameterValue bodyTokenValue))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  apply fs_zfc_support_raw_schema_certificate_coordinates_elim
    raw schemaTag parameterCount bodyTokenCode
    Formula.falsum
    hParameterCount hBodyTokenCode
    Formula.Admissible.falsum
    hCertificateEquality hBounds
  intro parameterValue bodyTokenValue hCode
  exact (hInvalid parameterValue bodyTokenValue hCode).elim

/-! ## schema 分支的证书标签拒绝 -/

/-- 五层 canonical 存在闭包的整体合法性可反演回开放 witness body。 -/
theorem fs_zfc_exists_five_body_admissible
    (first second third fourth fifth : FreeVarId)
    (body : SetFormula)
    (hExists :
      Formula.Admissible
        (∃ₘ[SetSort.set, first],
          ∃ₘ[SetSort.set, second],
            ∃ₘ[SetSort.set, third],
              ∃ₘ[SetSort.set, fourth],
                ∃ₘ[SetSort.set, fifth], body)) :
    Formula.Admissible body := by
  have hFirst :=
    Formula.Admissible.exists_openAt
      (term := (x#first : SetTerm))
      SetSort.set hExists
      (set_variable_admissible first)
  have hSecondExists :
      Formula.Admissible
        (∃ₘ[SetSort.set, second],
          ∃ₘ[SetSort.set, third],
            ∃ₘ[SetSort.set, fourth],
              ∃ₘ[SetSort.set, fifth], body) := by
    simpa [Formula.openAt_closeFreeAt] using hFirst
  have hSecond :=
    Formula.Admissible.exists_openAt
      (term := (x#second : SetTerm))
      SetSort.set hSecondExists
      (set_variable_admissible second)
  have hThirdExists :
      Formula.Admissible
        (∃ₘ[SetSort.set, third],
          ∃ₘ[SetSort.set, fourth],
            ∃ₘ[SetSort.set, fifth], body) := by
    simpa [Formula.openAt_closeFreeAt] using hSecond
  have hThird :=
    Formula.Admissible.exists_openAt
      (term := (x#third : SetTerm))
      SetSort.set hThirdExists
      (set_variable_admissible third)
  have hFourthExists :
      Formula.Admissible
        (∃ₘ[SetSort.set, fourth],
          ∃ₘ[SetSort.set, fifth], body) := by
    simpa [Formula.openAt_closeFreeAt] using hThird
  have hFourth :=
    Formula.Admissible.exists_openAt
      (term := (x#fourth : SetTerm))
      SetSort.set hFourthExists
      (set_variable_admissible fourth)
  have hFifthExists :
      Formula.Admissible
        (∃ₘ[SetSort.set, fifth], body) := by
    simpa [Formula.openAt_closeFreeAt] using hFourth
  have hFifth :=
    Formula.Admissible.exists_openAt
      (term := (x#fifth : SetTerm))
      SetSort.set hFifthExists
      (set_variable_admissible fifth)
  simpa [Formula.openAt_closeFreeAt] using hFifth

def fs_zfc_separation_condition_open_rest
    (formula : SetTerm)
    (base : FreeVarId) : SetFormula :=
  let parameter := x#base
  let bodyTokenCode := x#(base + 1)
  let bodyCode := x#(base + 2)
  let shiftOne := x#(base + 3)
  let shiftTwo := x#(base + 4)
  let parameterOne := Sₘ(parameter)
  let core := fs_zfc_separation_core_code parameter shiftTwo
  (parameter ∈ₘ ωₘ) ∧ₘ
    ((nat_sequence_code_condition_with_ids
        bodyCode bodyTokenCode
        (base + 5) (base + 6)) ∧ₘ
      ((canonical_project_formula_code_condition_with_ids
          parameterOne bodyCode
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)) ∧ₘ
        ((canonical_project_shift_code_condition_with_ids
            parameter bodyCode shiftOne
            (base + 17) (base + 18) (base + 19)) ∧ₘ
          ((canonical_project_shift_code_condition_with_ids
              parameter shiftOne shiftTwo
              (base + 25) (base + 26) (base + 27)) ∧ₘ
            canonical_forall_prefix_code_condition_with_ids
              parameter core formula
              (base + 33) (base + 34)))))

def fs_zfc_separation_condition_open_body
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId) : SetFormula :=
  fs_zfc_schema_condition_open_body
    (numₘ(raw)) (numₘ(0))
    (x#base) (x#(base + 1))
    (fs_zfc_separation_condition_open_rest formula base)

theorem fs_zfc_separation_condition_exists_shape
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId) :
    fs_zfc_separation_condition_with_base
        formula (numₘ(raw)) base =
      (∃ₘ[SetSort.set, base],
        ∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4],
                fs_zfc_separation_condition_open_body
                  formula raw base) := by
  rfl

def fs_zfc_collection_condition_open_rest
    (formula : SetTerm)
    (base : FreeVarId) : SetFormula :=
  let parameter := x#base
  let bodyTokenCode := x#(base + 1)
  let bodyCode := x#(base + 2)
  let shiftOne := x#(base + 3)
  let shiftTwo := x#(base + 4)
  let parameterOne := Sₘ(parameter)
  let parameterTwo := Sₘ(parameterOne)
  let core :=
    fs_zfc_collection_core_code
      parameter shiftOne shiftTwo
  (parameter ∈ₘ ωₘ) ∧ₘ
    ((nat_sequence_code_condition_with_ids
        bodyCode bodyTokenCode
        (base + 5) (base + 6)) ∧ₘ
      ((canonical_project_formula_code_condition_with_ids
          parameterTwo bodyCode
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)) ∧ₘ
        ((canonical_project_shift_code_condition_with_ids
            parameter bodyCode shiftOne
            (base + 17) (base + 18) (base + 19)) ∧ₘ
          ((canonical_project_shift_code_condition_with_ids
              parameter shiftOne shiftTwo
              (base + 25) (base + 26) (base + 27)) ∧ₘ
            canonical_forall_prefix_code_condition_with_ids
              parameter core formula
              (base + 33) (base + 34)))))

def fs_zfc_collection_condition_open_body
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId) : SetFormula :=
  fs_zfc_schema_condition_open_body
    (numₘ(raw)) (numₘ(1))
    (x#base) (x#(base + 1))
    (fs_zfc_collection_condition_open_rest formula base)

theorem fs_zfc_collection_condition_exists_shape
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId) :
    fs_zfc_collection_condition_with_base
        formula (numₘ(raw)) base =
      (∃ₘ[SetSort.set, base],
        ∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4],
                fs_zfc_collection_condition_open_body
                  formula raw base) := by
  rfl

/--
若自然数证书码不是任何 separation schema 证书码，则对象层分离条件为假。
其余公式分类、shift 与前缀证书不需要反演。
-/
theorem fs_zfc_support_raw_separation_condition_with_base_neg_of_code_ne
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hInvalid :
      ∀ parameterValue bodyTokenValue,
        raw ≠
          godel_pair_value 1
            (godel_pair_value 0
              (godel_pair_value
                parameterValue bodyTokenValue))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_separation_condition_with_base
        formula (numₘ(raw)) base) := by
  let body : SetFormula :=
    fs_zfc_separation_condition_open_body formula raw base
  have hExistsAdmissible :
      Formula.Admissible
        (∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body) := by
    rw [← fs_zfc_separation_condition_exists_shape
      formula raw base]
    exact fs_zfc_separation_condition_with_base_admissible
      formula (numₘ(raw)) base
      hFormula (finite_numeral_term_admissible raw)
  have hBody : Formula.Admissible body :=
    fs_zfc_exists_five_body_admissible
      base (base + 1) (base + 2)
      (base + 3) (base + 4)
      body hExistsAdmissible
  have hCase :
      body ::
        (∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4], body) ::
        [(∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body)]
        ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
    let Γ : Context signature :=
      body ::
        (∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4], body) ::
        [(∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body)]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hCertificateEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            fs_zfc_schema_certificate_term
              (numₘ(0)) (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_separation_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hBounds :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_schema_certificate_bounds
            (numₘ(raw)) (numₘ(0))
            (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_separation_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hBodyAt)
    exact fs_zfc_support_raw_schema_certificate_falsum_of_code_ne
      raw 0 (x#base) (x#(base + 1))
      (set_variable_admissible base)
      (set_variable_admissible (base + 1))
      hCertificateEquality hBounds hInvalid
  rw [fs_zfc_separation_condition_exists_shape
    formula raw base]
  exact fs_zfc_support_raw_exists_five_neg
    base (base + 1) (base + 2)
    (base + 3) (base + 4)
    body hBody hCase

/--
若自然数证书码不是任何 collection schema 证书码，则对象层收集条件为假。
-/
theorem fs_zfc_support_raw_collection_condition_with_base_neg_of_code_ne
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hInvalid :
      ∀ parameterValue bodyTokenValue,
        raw ≠
          godel_pair_value 1
            (godel_pair_value 1
              (godel_pair_value
                parameterValue bodyTokenValue))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_collection_condition_with_base
        formula (numₘ(raw)) base) := by
  let body : SetFormula :=
    fs_zfc_collection_condition_open_body formula raw base
  have hExistsAdmissible :
      Formula.Admissible
        (∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body) := by
    rw [← fs_zfc_collection_condition_exists_shape
      formula raw base]
    exact fs_zfc_collection_condition_with_base_admissible
      formula (numₘ(raw)) base
      hFormula (finite_numeral_term_admissible raw)
  have hBody : Formula.Admissible body :=
    fs_zfc_exists_five_body_admissible
      base (base + 1) (base + 2)
      (base + 3) (base + 4)
      body hExistsAdmissible
  have hCase :
      body ::
        (∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4], body) ::
        [(∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body)]
        ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
    let Γ : Context signature :=
      body ::
        (∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4], body) ::
        [(∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body)]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hCertificateEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            fs_zfc_schema_certificate_term
              (numₘ(1)) (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_collection_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hBounds :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_schema_certificate_bounds
            (numₘ(raw)) (numₘ(1))
            (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_collection_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hBodyAt)
    exact fs_zfc_support_raw_schema_certificate_falsum_of_code_ne
      raw 1 (x#base) (x#(base + 1))
      (set_variable_admissible base)
      (set_variable_admissible (base + 1))
      hCertificateEquality hBounds hInvalid
  rw [fs_zfc_collection_condition_exists_shape
    formula raw base]
  exact fs_zfc_support_raw_exists_five_neg
    base (base + 1) (base + 2)
    (base + 3) (base + 4)
    body hBody hCase

/--
若自然数证书码不是任何 replacement schema 证书码，则 replacement 插件被拒绝。
十层 witness 由公共 closure 接口统一消去，拒绝只读取标签、参数和 body token 坐标。
-/
theorem fs_zfc_support_raw_replacement_condition_with_base_neg_of_code_ne
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hInvalid :
      ∀ parameterValue bodyTokenValue,
        raw ≠
          godel_pair_value 1
            (godel_pair_value 2
              (godel_pair_value
                parameterValue bodyTokenValue))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_condition_with_base
        formula (numₘ(raw)) base) := by
  let ids : List FreeVarId :=
    List.range 10 |>.map (base + ·)
  let body : SetFormula :=
    fs_zfc_replacement_condition_open_body
      formula (numₘ(raw)) base
  have hClosure :
      Formula.Admissible
        (ProofT.SchemaPlugin.witness_closure ids body) := by
    rw [← fs_zfc_replacement_condition_exists_shape
      formula (numₘ(raw)) base]
    exact fs_zfc_replacement_condition_with_base_admissible
      formula (numₘ(raw)) base
      hFormula (finite_numeral_term_admissible raw)
  have hBody : Formula.Admissible body :=
    ProofT.SchemaPlugin.witness_closure_body_admissible
      ids hClosure
  have hBodyNeg :
      Derives fs_zfc_support_raw_theory [] (¬ₘ body) := by
    nd_apply FirstOrder.Derives.negIntro
      (T := fs_zfc_support_raw_theory)
      (Γ := ([] : Context signature))
      (body := body)
      (hBodyCheck :=
        Formula.check_admissible_complete hBody)
    let Γ : Context signature := [body]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hCertificateEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            fs_zfc_schema_certificate_term
              (numₘ(2)) (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_replacement_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hBounds :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_schema_certificate_bounds
            (numₘ(raw)) (numₘ(2))
            (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_replacement_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hBodyAt)
    exact fs_zfc_support_raw_schema_certificate_falsum_of_code_ne
      raw 2 (x#base) (x#(base + 1))
      (set_variable_admissible base)
      (set_variable_admissible (base + 1))
      hCertificateEquality hBounds hInvalid
  rw [fs_zfc_replacement_condition_exists_shape
    formula (numₘ(raw)) base]
  exact ProofT.SchemaPlugin.witness_closure_neg
    (fun hAxiom =>
      (fs_zfc_support_raw_theory_sentence hAxiom).2)
    ids hBody hBodyNeg

/-! ## 完整对象 verifier 的标签拒绝 -/

/-- 固定表与任意插件表的全部分支均被否定时，总对象证书条件被否定。 -/
theorem fs_zfc_support_raw_object_certificate_condition_with_plugins_neg_of_branch_negs
    (plugins : List ProofT.SchemaPlugin)
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hFixedNeg :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ fs_zfc_fixed_axiom_table.condition
          formula certificate))
    (hSchemaNeg :
      ∀ plugin, plugin ∈ plugins →
        Derives fs_zfc_support_raw_theory [] (
          ¬ₘ plugin.condition_with_base
            formula certificate base)) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition_with_plugins
        plugins formula certificate base) := by
  let fixed : SetFormula :=
    fs_zfc_fixed_axiom_table.condition formula certificate
  let schemas : SetFormula :=
    ProofT.SchemaPlugin.condition_list
      plugins formula certificate base
  let condition : SetFormula :=
    fixed ∨ₘ schemas
  have hCondition :
      Formula.Admissible condition := by
    simpa [condition, fixed, schemas] using
      Formula.Admissible.disj
        (fs_zfc_fixed_axiom_table.condition_admissible
          formula certificate hFormula hCertificate)
        (ProofT.SchemaPlugin.condition_list_admissible
          plugins formula certificate base
          hFormula hCertificate)
  have hSchemasNeg :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ schemas) := by
    simpa [schemas] using
      ProofT.SchemaPlugin.condition_list_neg
        plugins formula certificate base
        hFormula hCertificate hSchemaNeg
  nd_apply FirstOrder.Derives.negIntro
    (T := fs_zfc_support_raw_theory)
    (Γ := ([] : Context signature))
    (body := condition)
    (hBodyCheck :=
      Formula.check_admissible_complete hCondition)
  let Γ : Context signature := [condition]
  have hConditionAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] condition :=
    FirstOrder.Derives.assumption (by simp [Γ])
  apply FirstOrder.Derives.disjElim hConditionAt
  · let Δ : Context signature := fixed :: Γ
    have hFixedAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] fixed :=
      FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := Δ) (φ := fixed)
        (by simp [Δ])
    have hFixedNegAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] ¬ₘ fixed :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp)
        (by simpa [fixed] using hFixedNeg)
    exact FirstOrder.Derives.negElim
      hFixedAt hFixedNegAt
  · let Δ : Context signature := schemas :: Γ
    have hSchemasAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] schemas :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hSchemasNegAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] ¬ₘ schemas :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) hSchemasNeg
    exact FirstOrder.Derives.negElim
      hSchemasAt hSchemasNegAt

/-- 当前 separation/collection presentation 的总分支拒绝。 -/
theorem fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_branch_negs
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hFixedNeg :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ fs_zfc_fixed_axiom_table.condition
          formula certificate))
    (hSchemaNeg :
      ∀ plugin, plugin ∈ fs_zfc_schema_plugins →
        Derives fs_zfc_support_raw_theory [] (
          ¬ₘ plugin.condition_with_base
            formula certificate base)) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition_with_base
        formula certificate base) := by
  exact
    fs_zfc_support_raw_object_certificate_condition_with_plugins_neg_of_branch_negs
      fs_zfc_schema_plugins formula certificate base
      hFormula hCertificate hFixedNeg hSchemaNeg

/-! ## schema 标签与固定表标签互斥 -/

private theorem fs_zfc_fixed_table_rows_from_certificate_tag_ne
    (certificateTag rowTag payload start : Nat)
    (formulas : List SetFormula)
    (hTag : certificateTag ≠ rowTag) :
    ∀ row,
      row ∈
          fs_zfc_fixed_table_rows_from
            (fun index =>
              godel_pair_value rowTag index)
            start formulas →
        godel_pair_value certificateTag payload ≠ row.1 := by
  induction formulas generalizing start with
  | nil =>
      intro row hRow
      simp [fs_zfc_fixed_table_rows_from] at hRow
  | cons formula formulas ih =>
      intro row hRow hEquality
      simp only [fs_zfc_fixed_table_rows_from,
        List.mem_cons] at hRow
      rcases hRow with rfl | hRow
      · exact hTag
          (godel_pair_value_eq_iff.mp hEquality).1
      · exact ih (start + 1) row hRow hEquality

/-- 外层标签为 `1` 的 schema 证书码不可能等于固定表的任一证书码。 -/
theorem fs_zfc_schema_certificate_code_ne_fixed_table_row
    (payload : Nat)
    {row : Nat × SetTerm}
    (hRow : row ∈ fs_zfc_fixed_table_rows) :
    godel_pair_value 1 payload ≠ row.1 := by
  unfold fs_zfc_fixed_table_rows at hRow
  simp only [List.mem_append] at hRow
  rcases hRow with hRow | hRow
  · rcases hRow with hRow | hRow
    · exact fs_zfc_fixed_table_rows_from_certificate_tag_ne
        1 0 payload 0
        fs_internal_encoding_finite_presentation.axioms
        (by omega) row hRow
    · exact fs_zfc_fixed_table_rows_from_certificate_tag_ne
        1 2 payload 0
        fs_project_definition_finite_presentation.axioms
        (by omega) row hRow
  · exact fs_zfc_fixed_table_rows_from_certificate_tag_ne
      1 3 payload 0
      (fs_zfc_fixed_axioms.map
        (fun sentence => fs_embed_project_sentence sentence))
      (by omega) row hRow

/--
任意 schema 外层证书码在对象层都排除固定公理表分支。该结论只依赖编码标签，
不依赖 schema body、参数个数或公式正确性。
-/
theorem fs_zfc_support_raw_fixed_table_condition_neg_of_schema_code
    (formula : SetTerm)
    (payload : Nat)
    (hFormula : Term.Admissible formula SetSort.set) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_fixed_axiom_table.condition
        formula (numₘ(godel_pair_value 1 payload))) := by
  exact
    ProofT.FixedAxiomTable.condition_rows_neg_of_certificate_ne
      ProofT.ZFC.numeral_arithmetic
      fs_zfc_fixed_table_rows formula
      (godel_pair_value 1 payload)
      hFormula
      (fun row hRow =>
        fs_zfc_fixed_table_rows_admissible hRow)
      (fun row hRow =>
        fs_zfc_schema_certificate_code_ne_fixed_table_row
          payload hRow)

/-- 三个证书命名空间均不匹配时，完整对象证书条件被否定。 -/
theorem fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_code_ne
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFixedInvalid :
      ∀ row, row ∈ fs_zfc_fixed_table_rows →
        raw ≠ row.1)
    (hSeparationInvalid :
      ∀ parameterValue bodyTokenValue,
        raw ≠
          godel_pair_value 1
            (godel_pair_value 0
              (godel_pair_value
                parameterValue bodyTokenValue)))
    (hCollectionInvalid :
      ∀ parameterValue bodyTokenValue,
        raw ≠
          godel_pair_value 1
            (godel_pair_value 1
              (godel_pair_value
                parameterValue bodyTokenValue))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition_with_base
        formula (numₘ(raw)) base) := by
  exact
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_branch_negs
      formula (numₘ(raw)) base
      hFormula (finite_numeral_term_admissible raw)
      (ProofT.FixedAxiomTable.condition_rows_neg_of_certificate_ne
        ProofT.ZFC.numeral_arithmetic
        fs_zfc_fixed_table_rows formula raw
        hFormula
        (fun row hRow =>
          fs_zfc_fixed_table_rows_admissible hRow)
        hFixedInvalid)
      (fs_zfc_schema_plugins_elim
        (fs_zfc_support_raw_separation_condition_with_base_neg_of_code_ne
          formula raw base hFormula hSeparationInvalid)
        (fs_zfc_support_raw_collection_condition_with_base_neg_of_code_ne
          formula raw base hFormula hCollectionInvalid))

/-- 固定表、分离与 replacement 命名空间均不匹配时，replacement presentation 被拒绝。 -/
theorem fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_code_ne
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFixedInvalid :
      ∀ row, row ∈ fs_zfc_fixed_table_rows →
        raw ≠ row.1)
    (hSeparationInvalid :
      ∀ parameterValue bodyTokenValue,
        raw ≠
          godel_pair_value 1
            (godel_pair_value 0
              (godel_pair_value
                parameterValue bodyTokenValue)))
    (hReplacementInvalid :
      ∀ parameterValue bodyTokenValue,
        raw ≠
          godel_pair_value 1
            (godel_pair_value 2
              (godel_pair_value
                parameterValue bodyTokenValue))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition_with_base
        formula (numₘ(raw)) base) := by
  exact
    fs_zfc_support_raw_object_certificate_condition_with_plugins_neg_of_branch_negs
      fs_zfc_replacement_schema_plugins
      formula (numₘ(raw)) base
      hFormula (finite_numeral_term_admissible raw)
      (ProofT.FixedAxiomTable.condition_rows_neg_of_certificate_ne
        ProofT.ZFC.numeral_arithmetic
        fs_zfc_fixed_table_rows formula raw
        hFormula
        (fun row hRow =>
          fs_zfc_fixed_table_rows_admissible hRow)
        hFixedInvalid)
      (fs_zfc_replacement_schema_plugins_elim
        (fs_zfc_support_raw_separation_condition_with_base_neg_of_code_ne
          formula raw base hFormula hSeparationInvalid)
        (fs_zfc_support_raw_replacement_condition_with_base_neg_of_code_ne
          formula raw base hFormula hReplacementInvalid))

private theorem fs_zfc_certificate_code_ne_fixed_table_row_of_outer_tag_ne
    (raw : Nat)
    (hZero : (godel_unpair_value raw).1 ≠ 0)
    (hTwo : (godel_unpair_value raw).1 ≠ 2)
    (hThree : (godel_unpair_value raw).1 ≠ 3)
    {row : Nat × SetTerm}
    (hRow : row ∈ fs_zfc_fixed_table_rows) :
    raw ≠ row.1 := by
  rw [← godel_unpair_value_spec raw]
  unfold fs_zfc_fixed_table_rows at hRow
  simp only [List.mem_append] at hRow
  rcases hRow with hRow | hRow
  · rcases hRow with hRow | hRow
    · exact fs_zfc_fixed_table_rows_from_certificate_tag_ne
        (godel_unpair_value raw).1 0
        (godel_unpair_value raw).2 0
        fs_internal_encoding_finite_presentation.axioms
        hZero row hRow
    · exact fs_zfc_fixed_table_rows_from_certificate_tag_ne
        (godel_unpair_value raw).1 2
        (godel_unpair_value raw).2 0
        fs_project_definition_finite_presentation.axioms
        hTwo row hRow
  · exact fs_zfc_fixed_table_rows_from_certificate_tag_ne
      (godel_unpair_value raw).1 3
      (godel_unpair_value raw).2 0
      (fs_zfc_fixed_axioms.map
        (fun sentence => fs_embed_project_sentence sentence))
      hThree row hRow

/-- 未知外层证书标签不可能满足对象 verifier。 -/
theorem fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_unknown_outer_tag
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hZero : (godel_unpair_value raw).1 ≠ 0)
    (hOne : (godel_unpair_value raw).1 ≠ 1)
    (hTwo : (godel_unpair_value raw).1 ≠ 2)
    (hThree : (godel_unpair_value raw).1 ≠ 3) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition_with_base
        formula (numₘ(raw)) base) := by
  apply
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_code_ne
      formula raw base hFormula
  · intro row hRow
    exact fs_zfc_certificate_code_ne_fixed_table_row_of_outer_tag_ne
      raw hZero hTwo hThree hRow
  · intro parameterValue bodyTokenValue hCode
    exact hOne <| (godel_pair_value_eq_iff.mp <|
      (godel_unpair_value_spec raw).trans hCode).1
  · intro parameterValue bodyTokenValue hCode
    exact hOne <| (godel_pair_value_eq_iff.mp <|
      (godel_unpair_value_spec raw).trans hCode).1

/-- schema 外层下未知的模式标签不可能满足对象 verifier。 -/
theorem fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_unknown_schema_tag
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hOuter : (godel_unpair_value raw).1 = 1)
    (hSeparation : (godel_unpair_value
      (godel_unpair_value raw).2).1 ≠ 0)
    (hCollection : (godel_unpair_value
      (godel_unpair_value raw).2).1 ≠ 1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition_with_base
        formula (numₘ(raw)) base) := by
  let payload : Nat := (godel_unpair_value raw).2
  have hRaw :
      raw = godel_pair_value 1 payload := by
    simpa [payload, hOuter] using
      (godel_unpair_value_spec raw).symm
  have hSeparationPayload :
      (godel_unpair_value payload).1 ≠ 0 := by
    simpa [payload] using hSeparation
  have hCollectionPayload :
      (godel_unpair_value payload).1 ≠ 1 := by
    simpa [payload] using hCollection
  apply
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_code_ne
      formula raw base hFormula
  · intro row hRow
    rw [hRaw]
    exact fs_zfc_schema_certificate_code_ne_fixed_table_row
      payload hRow
  · intro parameterValue bodyTokenValue hCode
    have hPayload :
        payload =
          godel_pair_value 0
            (godel_pair_value
              parameterValue bodyTokenValue) :=
      (godel_pair_value_eq_iff.mp
        (hRaw.symm.trans hCode)).2
    exact hSeparationPayload <| by
      rw [hPayload, godel_unpair_value_pair]
  · intro parameterValue bodyTokenValue hCode
    have hPayload :
        payload =
          godel_pair_value 1
            (godel_pair_value
              parameterValue bodyTokenValue) :=
      (godel_pair_value_eq_iff.mp
        (hRaw.symm.trans hCode)).2
    exact hCollectionPayload <| by
      rw [hPayload, godel_unpair_value_pair]

/-! ## 动态 fresh-base 包装 -/

/-- 闭合公式上的未知外层标签也被动态对象 verifier 拒绝。 -/
theorem fs_zfc_support_raw_object_certificate_condition_neg_of_unknown_outer_tag
    (formula : SetTerm)
    (raw : Nat)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hZero : (godel_unpair_value raw).1 ≠ 0)
    (hOne : (godel_unpair_value raw).1 ≠ 1)
    (hTwo : (godel_unpair_value raw).1 ≠ 2)
    (hThree : (godel_unpair_value raw).1 ≠ 3) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition
        formula (numₘ(raw))) := by
  simpa [fs_zfc_object_certificate_condition,
    ProofT.schema_base, FreshVariable.fresh_id,
    FreshVariable.formulas_bound, FreshVariable.formula_bound,
    FreshVariable.support_bound, Formula.freeSupport,
    Term.freeSupport, Term.freeSupportList,
    hFormulaClosed, finite_numeral_term_freeSupport] using
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_unknown_outer_tag
      formula raw 904 hFormula hZero hOne hTwo hThree

/-- 闭合公式上的未知 schema 标签也被动态对象 verifier 拒绝。 -/
theorem fs_zfc_support_raw_object_certificate_condition_neg_of_unknown_schema_tag
    (formula : SetTerm)
    (raw : Nat)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hOuter : (godel_unpair_value raw).1 = 1)
    (hSeparation : (godel_unpair_value
      (godel_unpair_value raw).2).1 ≠ 0)
    (hCollection : (godel_unpair_value
      (godel_unpair_value raw).2).1 ≠ 1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition
        formula (numₘ(raw))) := by
  simpa [fs_zfc_object_certificate_condition,
    ProofT.schema_base, FreshVariable.fresh_id,
    FreshVariable.formulas_bound, FreshVariable.formula_bound,
    FreshVariable.support_bound, Formula.freeSupport,
    Term.freeSupport, Term.freeSupportList,
    hFormulaClosed, finite_numeral_term_freeSupport] using
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_unknown_schema_tag
      formula raw 904 hFormula hOuter hSeparation hCollection

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
