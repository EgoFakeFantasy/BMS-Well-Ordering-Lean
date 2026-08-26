import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCPairingBound
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ObjectReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.NumeralArithmetic

/-!
# `ProofT.Core` 的 ZFC 实现

本模块证明 Rosser 负向内部化唯一需要的对象算术事实：对任意对象自然数
`point` 与标准 numeral `q`，`point` 要么不超过 `q`，要么严格大于 `q`。

当前 realization 使用一个 `Delta0` 纯成员关系分离实例与 `ω` 的最小归纳性。
公开接口只交付 `ProofT.Core`，不暴露分离见证、模式编码或回放轨迹。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

namespace ProofT
namespace ZFC

/--
候选切分集的纯项目语言模式。

两个参数依次表示右端标准 numeral 与其后继；主变量 `x` 满足
`x ∈ successor ∨ numeral ∈ x`。
-/
private def cut_schema :
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Delta0UnarySchema 2 where
  body :=
    .disj
      (.mem (.bound 0) (.bound 1))
      (.mem (.bound 2) (.bound 0))
  freeClosed := by
    simp [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
  delta0 := .disj (.mem _ _) (.mem _ _)

/-- ZFC raw 理论包含上述具体分离实例。 -/
private theorem cut_axiom :
    Derives fs_zfc_support_raw_theory [] (
      fs_embed_project_sentence
        (_root_.YesMetaZFC.SetTheory.Axioms.Schema.separation
          cut_schema.toUnarySchema)) := by
  apply FirstOrder.Derives.theory_mem
    (hFormulaCheck := Formula.check_admissible_complete <|
      (fs_embed_project_sentence_sentence
        (_root_.YesMetaZFC.SetTheory.Axioms.Schema.separation
          cut_schema.toUnarySchema)).1)
  exact Or.inr <| Or.inr <|
    ⟨_,
      _root_.YesMetaZFC.SetTheory.ZFC.Axiom.zf
        (_root_.YesMetaZFC.SetTheory.ZF.Axiom.separation
          cut_schema.toUnarySchema),
      rfl⟩

/-- 把项目分离句归一化为 FormalSystem 的显式量词形。 -/
private theorem cut_axiom_explicit :
    Derives fs_zfc_support_raw_theory [] (
      ∀ₘ[SetSort.set],
        ∀ₘ[SetSort.set],
          ∀ₘ[SetSort.set],
            ∃ₘ[SetSort.set],
              ∀ₘ[SetSort.set],
                (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
                  ((bₛ#0 ∈ₘ bₛ#2) ∧ₘ
                    ((bₛ#0 ∈ₘ bₛ#3) ∨ₘ
                      (bₛ#4 ∈ₘ bₛ#0)))) := by
  simpa [cut_schema,
    fs_embed_project_sentence,
    _root_.YesMetaZFC.SetTheory.Axioms.Schema.separation,
    _root_.YesMetaZFC.SetTheory.Axioms.Schema.separationCore,
    _root_.YesMetaZFC.SetTheory.Definitional.Project.Sentence.forallClosure,
    _root_.YesMetaZFC.SetTheory.Definitional.Formula.forallClosure,
    _root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo,
    _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
    _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.rename,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.bind,
    Function.comp_def,
    fs_embed_project_formula,
    fs_embed_project_term] using
      cut_axiom

/-- 固定标准边界后，ZFC 分离给出切分候选集。 -/
private theorem cut_exists
    (q : Nat) :
    Derives fs_zfc_support_raw_theory [] (
      ∃ₘ[SetSort.set],
        ∀ₘ[SetSort.set],
          (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
            ((bₛ#0 ∈ₘ ωₘ) ∧ₘ
              ((bₛ#0 ∈ₘ Sₘ(numₘ(q))) ∨ₘ
                (numₘ(q) ∈ₘ bₛ#0)))) := by
  have hFirst :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(q))
      cut_axiom_explicit
      (hTermCheck :=
        Term.check_admissible_complete
          (finite_numeral_term_admissible q))
  have hSecond :=
    FirstOrder.Derives.forall_elim
      (term := Sₘ(numₘ(q))) hFirst
      (hTermCheck :=
        Term.check_admissible_complete <|
          successor_term_admissible
            (numₘ(q)) (finite_numeral_term_admissible q))
  have hSource :=
    FirstOrder.Derives.forall_elim
      (term := ωₘ) hSecond
      (hTermCheck :=
        Term.check_admissible_complete omega_term_admissible)
  have hNumeralOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term (numₘ(q)) =
        numₘ(q) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term (numₘ(q))
      (finite_numeral_term_admissible q).2
  simpa [Formula.openAt, Formula.next_depth,
    Term.openAt, hNumeralOpen] using hSource

/-- `infinity_theory` 的对象证明统一提升到 ZFC raw 支持理论。 -/
private theorem derives_of_infinity
    {Γ : Context signature}
    {φ : SetFormula}
    (h : Γ ⊢ₘ[infinity_theory] φ) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] φ :=
  FirstOrder.Derives.theory_weaken
    (fun _ hFormula =>
      fs_zfc_support_raw_contains_infinity hFormula)
    h

/-! ## 候选集的归纳性 -/

private def cut_point_id : FreeVarId := 0

private def cut_candidate_id : FreeVarId := 1

private def cut_condition
    (q : Nat) (point : SetTerm) : SetFormula :=
  (point ∈ₘ Sₘ(numₘ(q))) ∨ₘ
    (numₘ(q) ∈ₘ point)

private def cut_spec
    (q : Nat) (candidate : SetTerm) : SetFormula :=
  ∀ₘ[SetSort.set],
    (bₛ#0 ∈ₘ candidate) ↔ₘ
      ((bₛ#0 ∈ₘ ωₘ) ∧ₘ
        cut_condition q bₛ#0)

private theorem cut_spec_admissible
    (q : Nat)
    (candidate : SetTerm)
    (hCandidate :
      Term.Admissible candidate SetSort.set) :
    Formula.Admissible
      (cut_spec q candidate) := by
  have hOpen :=
    Formula.Admissible.exists_openAt
      (σ := signature)
      (body :=
        ∀ₘ[SetSort.set],
          (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
            ((bₛ#0 ∈ₘ ωₘ) ∧ₘ
              ((bₛ#0 ∈ₘ Sₘ(numₘ(q))) ∨ₘ
                (numₘ(q) ∈ₘ bₛ#0))))
      (term := candidate)
      SetSort.set
      (cut_exists q).admissible
      hCandidate
  have hNumeralOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term (numₘ(q)) =
        numₘ(q) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term (numₘ(q))
      (finite_numeral_term_admissible q).2
  simpa [cut_spec,
    cut_condition,
    Formula.openAt, Formula.next_depth,
    Term.openAt, hNumeralOpen] using hOpen

private theorem cut_spec_at
    {Γ : Context signature}
    (q : Nat)
    (candidate point : SetTerm)
    (hCandidate :
      Term.Admissible candidate SetSort.set)
    (hPoint :
      Term.Admissible point SetSort.set)
    (hSpec :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        cut_spec q candidate) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (point ∈ₘ candidate) ↔ₘ
        ((point ∈ₘ ωₘ) ∧ₘ
          cut_condition q point) := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := point) hSpec
  have hCandidateOpen :
      Term.openAt SetSort.set 0 point candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 point candidate hCandidate.2
  have hOmegaOpen :
      Term.openAt SetSort.set 0 point ωₘ = ωₘ :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 point ωₘ omega_term_admissible.2
  have hNumeralOpen :
      Term.openAt SetSort.set 0 point (numₘ(q)) =
        numₘ(q) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 point (numₘ(q))
      (finite_numeral_term_admissible q).2
  simpa [cut_spec,
    cut_condition,
    Formula.openAt, Formula.next_depth,
    Term.openAt, hCandidateOpen, hOmegaOpen,
    hNumeralOpen] using hAt

private theorem successor_mem_omega
    {Γ : Context signature}
    (point : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        point ∈ₘ ωₘ) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Sₘ(point) ∈ₘ ωₘ := by
  have hStep :
      Derives fs_zfc_support_raw_theory [] (
        (point ∈ₘ ωₘ) ⟶ₘ
          (Sₘ(point) ∈ₘ ωₘ)) := by
    apply derives_of_infinity
    nd_apply FirstOrder.Derives.impIntro
    exact infinity_successor_term_mem_omega
      point hPoint
      (FirstOrder.Derives.assumption (by simp))
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by simp)
      hStep)
    hMember

private theorem cut_inductive
    (q : Nat) :
    let candidate :=
      x#cut_candidate_id
    let spec :=
      cut_spec q candidate
    [spec] ⊢ₘ[fs_zfc_support_raw_theory]
      is_inductive_set_formula candidate := by
  let candidate : SetTerm :=
    x#cut_candidate_id
  let point : SetTerm :=
    x#cut_point_id
  let spec : SetFormula :=
    cut_spec q candidate
  let Γ : Context signature := [spec]
  have hCandidate :
      Term.Admissible candidate SetSort.set := by
    simpa [candidate] using
      set_variable_admissible
        cut_candidate_id
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using
      set_variable_admissible
        cut_point_id
  have hSpecAdmissible :
      Formula.Admissible spec := by
    simpa [spec] using
      cut_spec_admissible
        q candidate hCandidate
  have hSpec :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] spec :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (hCheck :=
        Formula.check_admissible_complete
          hSpecAdmissible)
  have hZeroOmega :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∅ₘ ∈ₘ ωₘ := by
    simpa [finite_numeral_term] using
      FirstOrder.Derives.context_weaken
        (Γ := [])
        (Δ := Γ)
        (by simp)
        (derives_of_infinity
          (infinity_finite_numeral_mem_omega 0))
  have hZeroBound :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∅ₘ ∈ₘ Sₘ(numₘ(q)) := by
    simpa [finite_numeral_term] using
      FirstOrder.Derives.context_weaken
        (Γ := [])
        (Δ := Γ)
        (by simp)
        (fs_zfc_support_raw_derives_of_standard_sequence
          (standard_sequence_finite_numeral_mem_of_lt
            0 (q + 1) (by omega)))
  have hZeroSpec :=
    cut_spec_at
      q candidate ∅ₘ hCandidate
      empty_set_term_admissible hSpec
  have hZero :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∅ₘ ∈ₘ candidate :=
    FirstOrder.Derives.iffElimLeft hZeroSpec <|
      FirstOrder.Derives.conjIntro hZeroOmega <|
        FirstOrder.Derives.disjIntroLeft hZeroBound

  have hStepOpen :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (point ∈ₘ candidate) ⟶ₘ
          (Sₘ(point) ∈ₘ candidate) := by
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature :=
      (point ∈ₘ candidate) :: Γ
    have hPointMember :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          point ∈ₘ candidate :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hSpecΔ :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] spec :=
      FirstOrder.Derives.context_weaken_cons hSpec
    have hPointData :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (point ∈ₘ ωₘ) ∧ₘ
            cut_condition q point :=
      FirstOrder.Derives.iffElimRight
        (cut_spec_at
          q candidate point hCandidate hPoint hSpecΔ)
        hPointMember
    have hPointOmega :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          point ∈ₘ ωₘ :=
      FirstOrder.Derives.conjElimLeft hPointData
    have hSuccessorOmega :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          Sₘ(point) ∈ₘ ωₘ :=
      successor_mem_omega
        point hPoint hPointOmega
    have hPointCases :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          cut_condition q point :=
      FirstOrder.Derives.conjElimRight hPointData
    have hSuccessorCases :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          cut_condition q (Sₘ(point)) := by
      apply FirstOrder.Derives.disjElim hPointCases
      · let leftCase : SetFormula :=
          point ∈ₘ Sₘ(numₘ(q))
        let Λ : Context signature := leftCase :: Δ
        have hFinite :
            Λ ⊢ₘ[fs_zfc_support_raw_theory]
              point ∈ₘ numₘ(q + 1) := by
          simpa [leftCase, finite_numeral_term] using
            (FirstOrder.Derives.assumption
              (T := fs_zfc_support_raw_theory)
              (Γ := Λ)
              (φ := leftCase)
              (by simp [Λ]))
        apply
          ProofT.numeral_member_elim
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_empty_set_symbol
                hFormula)
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_successor_operator
                hFormula)
            (q + 1) point
            (cut_condition q (Sₘ(point)))
            hPoint
            (Formula.Admissible.disj
              (membership_formula_admissible
                (successor_term_admissible point hPoint)
                (successor_term_admissible
                  (numₘ(q))
                  (finite_numeral_term_admissible q)))
              (membership_formula_admissible
                (finite_numeral_term_admissible q)
                (successor_term_admissible point hPoint)))
            hFinite
        intro i hi
        let Ξ : Context signature :=
          (point ≐ₘ numₘ(i)) :: Λ
        have hEquality :
            Ξ ⊢ₘ[fs_zfc_support_raw_theory]
              point ≐ₘ numₘ(i) :=
          FirstOrder.Derives.assumption (by simp [Ξ])
        have hSuccessorEquality :
            Ξ ⊢ₘ[fs_zfc_support_raw_theory]
              Sₘ(point) ≐ₘ Sₘ(numₘ(i)) :=
          successor_term_congr_of_equality
            point (numₘ(i))
            hPoint
            (finite_numeral_term_admissible i)
            hEquality
        by_cases hiq : i = q
        · subst i
          apply FirstOrder.Derives.disjIntroRight
            (hLeftCheck :=
              Formula.check_admissible_complete <|
                membership_formula_admissible
                  (successor_term_admissible
                    point hPoint)
                  (successor_term_admissible
                    (numₘ(q))
                    (finite_numeral_term_admissible q)))
          have hGround :
              Ξ ⊢ₘ[fs_zfc_support_raw_theory]
                numₘ(q) ∈ₘ Sₘ(numₘ(q)) :=
            FirstOrder.Derives.context_weaken
              (Γ := [])
              (Δ := Ξ)
              (by simp)
              (fs_zfc_support_raw_derives_of_standard_sequence
                (standard_sequence_weaken_successor
                  (mem_successor_self
                    (numₘ(q))
                    (finite_numeral_term_admissible q))))
          exact FirstOrder.Derives.iffElimLeft
            (membership_right_iff_of_equality
              (numₘ(q))
              (Sₘ(point))
              (Sₘ(numₘ(q)))
              (finite_numeral_term_admissible q)
              (successor_term_admissible point hPoint)
              (successor_term_admissible
                (numₘ(q))
                (finite_numeral_term_admissible q))
              hSuccessorEquality)
            hGround
        · have hiqLt : i < q := by omega
          apply FirstOrder.Derives.disjIntroLeft
            (hRightCheck :=
              Formula.check_admissible_complete <|
                membership_formula_admissible
                  (finite_numeral_term_admissible q)
                  (successor_term_admissible
                    point hPoint))
          have hGround :
              Ξ ⊢ₘ[fs_zfc_support_raw_theory]
                Sₘ(numₘ(i)) ∈ₘ
                  Sₘ(numₘ(q)) := by
            simpa [finite_numeral_term] using
              FirstOrder.Derives.context_weaken
                (Γ := [])
                (Δ := Ξ)
                (by simp)
                (fs_zfc_support_raw_derives_of_standard_sequence
                  (standard_sequence_finite_numeral_mem_of_lt
                    (i + 1) (q + 1) (by omega)))
          exact FirstOrder.Derives.iffElimLeft
            (membership_left_iff_of_equality
              (Sₘ(point))
              (Sₘ(numₘ(i)))
              (Sₘ(numₘ(q)))
              (successor_term_admissible point hPoint)
              (successor_term_admissible
                (numₘ(i))
                (finite_numeral_term_admissible i))
              (successor_term_admissible
                (numₘ(q))
                (finite_numeral_term_admissible q))
              hSuccessorEquality)
            hGround
      · let rightCase : SetFormula :=
          numₘ(q) ∈ₘ point
        let Λ : Context signature := rightCase :: Δ
        have hMember :
            Λ ⊢ₘ[fs_zfc_support_raw_theory]
              numₘ(q) ∈ₘ point :=
          by
            simpa [rightCase] using
              (FirstOrder.Derives.assumption
                (T := fs_zfc_support_raw_theory)
                (Γ := Λ)
                (φ := rightCase)
                (by simp [Λ]))
        have hStep :
            Derives fs_zfc_support_raw_theory [] (
              (numₘ(q) ∈ₘ point) ⟶ₘ
                (numₘ(q) ∈ₘ Sₘ(point))) :=
          fs_zfc_support_raw_derives_of_standard_sequence
            (standard_sequence_weaken_successor
              (mem_successor_of_mem
                point (numₘ(q)) hPoint
                (finite_numeral_term_admissible q)))
        apply FirstOrder.Derives.disjIntroRight
          (hLeftCheck :=
            Formula.check_admissible_complete <|
              membership_formula_admissible
                (successor_term_admissible point hPoint)
                (successor_term_admissible
                  (numₘ(q))
                  (finite_numeral_term_admissible q)))
        exact
          FirstOrder.Derives.impElim
            (FirstOrder.Derives.context_weaken
              (Γ := [])
              (Δ := Λ)
              (by simp)
              hStep)
            hMember
    have hSuccessorSpec :=
      cut_spec_at
        q candidate (Sₘ(point))
        hCandidate
        (successor_term_admissible point hPoint)
        hSpecΔ
    exact FirstOrder.Derives.iffElimLeft
      hSuccessorSpec <|
        FirstOrder.Derives.conjIntro
          hSuccessorOmega hSuccessorCases

  have hStep :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[SetSort.set],
          (bₛ#0 ∈ₘ candidate) ⟶ₘ
            (Sₘ(bₛ#0) ∈ₘ candidate) := by
    have hGeneralized :=
      FirstOrder.Derives.forall_intro
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (sort := SetSort.set)
        (eigen := cut_point_id)
        (by
          intro formula hFormula
          rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
          exact List.not_mem_nil)
        (by
          intro formula hFormula
          simp only [Γ, List.mem_singleton] at hFormula
          subst formula
          simp [spec, cut_spec,
            cut_condition, candidate,
            cut_point_id,
            cut_candidate_id,
            Formula.freeSupport, Term.freeSupportList,
            Term.freeSupport,
            finite_numeral_term_freeSupport])
        hStepOpen
    simpa [point, candidate,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable,
      cut_point_id,
      cut_candidate_id] using
        hGeneralized
  have hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        is_inductive_set_condition candidate :=
    FirstOrder.Derives.conjIntro hZero hStep
  exact FirstOrder.Derives.iffElimLeft
    (FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by simp)
      (derives_of_infinity
        (infinity_is_inductive_set_definition_derives
          candidate hCandidate)))
    hCondition

/-! ## `ω` 的标准边界切分 -/

private theorem natural_cut_all
    (q : Nat) :
    Derives fs_zfc_support_raw_theory [] (
      ∀ₘ[SetSort.set],
        (bₛ#0 ∈ₘ ωₘ) ⟶ₘ
          cut_condition q bₛ#0) := by
  let candidate : SetTerm :=
    x#cut_candidate_id
  let point : SetTerm :=
    x#cut_point_id
  let spec : SetFormula :=
    cut_spec q candidate
  let conclusion : SetFormula :=
    ∀ₘ[SetSort.set],
      (bₛ#0 ∈ₘ ωₘ) ⟶ₘ
        cut_condition q bₛ#0
  have hCandidate :
      Term.Admissible candidate SetSort.set := by
    simpa [candidate] using
      set_variable_admissible
        cut_candidate_id
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using
      set_variable_admissible
        cut_point_id
  have hSpecAdmissible :
      Formula.Admissible spec := by
    simpa [spec] using
      cut_spec_admissible
        q candidate hCandidate
  have hNumeralClose
      (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth
          (numₘ(q)) =
        numₘ(q) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (numₘ(q))
      (finite_numeral_term_admissible q).2
      (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hExists :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set,
          cut_candidate_id], spec) := by
    simpa [spec, candidate,
      cut_spec,
      cut_condition,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, hNumeralClose,
      set_variable, set_bound_variable,
      cut_candidate_id,
      finite_numeral_term_freeSupport] using
        cut_exists q
  apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := [])
    (sort := SetSort.set)
    (eigen := cut_candidate_id)
    (body := spec)
    (conclusion := conclusion)
    (hBodyCheck :=
      Formula.check_admissible_complete hSpecAdmissible)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · simp
  · simp [conclusion, cut_condition,
      cut_candidate_id,
      Formula.freeSupport, Term.freeSupportList,
      Term.freeSupport,
      finite_numeral_term_freeSupport]
  · exact hExists
  · let Γ : Context signature := [spec]
    have hSpec :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] spec :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hInductive :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          is_inductive_set_formula candidate := by
      simpa [candidate, spec] using
        cut_inductive q
    have hOpen :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          (point ∈ₘ ωₘ) ⟶ₘ
            cut_condition q point := by
      nd_apply FirstOrder.Derives.impIntro
      let Δ : Context signature :=
        (point ∈ₘ ωₘ) :: Γ
      have hNatural :
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            point ∈ₘ ωₘ :=
        FirstOrder.Derives.assumption (by simp [Δ])
      have hCandidateMember :
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            point ∈ₘ candidate := by
        have hMinimality :=
          FirstOrder.Derives.context_weaken
            (Γ := [])
            (Δ := Δ)
            (by simp)
            (derives_of_infinity
              (infinity_omega_member_of_inductive_derives
                candidate point hCandidate hPoint))
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.impElim
            hMinimality
            (FirstOrder.Derives.context_weaken_cons
              hInductive))
          hNatural
      exact FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.iffElimRight
          (cut_spec_at
            q candidate point hCandidate hPoint
            (FirstOrder.Derives.context_weaken_cons hSpec))
          hCandidateMember
    have hGeneralized :=
      FirstOrder.Derives.forall_intro
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (sort := SetSort.set)
        (eigen := cut_point_id)
        (by
          intro formula hFormula
          rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
          exact List.not_mem_nil)
        (by
          intro formula hFormula
          simp only [Γ, List.mem_singleton] at hFormula
          subst formula
          simp [spec, cut_spec,
            cut_condition, candidate,
            cut_point_id,
            cut_candidate_id,
            Formula.freeSupport, Term.freeSupportList,
            Term.freeSupport,
            finite_numeral_term_freeSupport])
        hOpen
    simpa [conclusion, point,
      cut_condition,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, hNumeralClose,
      set_variable, set_bound_variable,
      cut_point_id,
      finite_numeral_term_freeSupport] using
        hGeneralized

/--
任意对象自然数相对标准 numeral `q` 可切分为 `point ≤ q` 或 `q < point`。

该接口只暴露二元成员关系；分离见证与归纳证明均被封装在模块内部。
-/
theorem natural_cut
    (q : Nat)
    (point : SetTerm)
    (hPoint : Term.Admissible point SetSort.set) :
    Derives fs_zfc_support_raw_theory [] (
      (point ∈ₘ ωₘ) ⟶ₘ
        ((point ∈ₘ Sₘ(numₘ(q))) ∨ₘ
          (numₘ(q) ∈ₘ point))) := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := point)
      (natural_cut_all q)
  have hOmegaOpen :
      Term.openAt SetSort.set 0 point ωₘ = ωₘ :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 point ωₘ omega_term_admissible.2
  have hNumeralOpen :
      Term.openAt SetSort.set 0 point (numₘ(q)) =
        numₘ(q) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 point (numₘ(q))
      (finite_numeral_term_admissible q).2
  simpa [cut_condition,
    Formula.openAt, Formula.next_depth,
    Term.openAt, hOmegaOpen, hNumeralOpen] using hAt

/-! ## 当前 ZFC 支持理论的 `ProofT.Core` 实例 -/

/--
ZFC raw 支持理论实现最小 ProofT 对象算术核心。

该实例只向上交付闭句边界、有限 numeral 消去和自然数切分；其余 quotation、
finite-sequence 与 schema 定义公理不进入 `ProofT.Core` 的公共签名。
-/
def core :
    ProofT.Core fs_zfc_support_raw_theory where
  toFiniteCore := {
    toNumeralArithmetic :=
      numeral_arithmetic
    theory_sentence := fs_zfc_support_raw_theory_sentence
    member_elim := by
      intro Γ bound point conclusion
        hPoint hConclusion hMember hBranch
      exact ProofT.numeral_member_elim
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_empty_set_symbol
            hFormula)
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_successor_operator
            hFormula)
        bound point conclusion
        hPoint hConclusion hMember hBranch
  }
  natural_cut :=
    natural_cut

/-- ZFC raw 支持理论实现证书标签与配对 payload 的有限反演核心。 -/
def certificate_core :
    ProofT.CertificateCore fs_zfc_support_raw_theory where
  toFiniteCore := core.toFiniteCore
  pair_value :=
    fs_zfc_support_raw_godel_pair_value_eq

/-- ZFC raw 宿主对 quotation 与逻辑规则定义层的直接包含实现。 -/
def object_replay :
    ProofT.ObjectReplay fs_zfc_support_raw_theory where
  godel_quotation :=
    fs_zfc_support_raw_contains_godel_quotation
  logical_rules :=
    fs_zfc_support_raw_contains_logical_rules

/-- ZFC raw 宿主实现未知对象自然数坐标的 Gödel 配对有限反演。 -/
def pairing_core :
    ProofT.PairingCore fs_zfc_support_raw_theory where
  toCertificateCore :=
    certificate_core
  numeral_natural := fun value =>
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_sequence_finite_numeral_mem_omega value)
  left_bound :=
    fs_zfc_support_raw_godel_pairing_left_bound_of_equality
  right_bound :=
    fs_zfc_support_raw_godel_pairing_right_bound_of_equality

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
