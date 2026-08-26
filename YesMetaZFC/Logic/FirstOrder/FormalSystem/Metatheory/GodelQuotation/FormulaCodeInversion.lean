import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.Freshness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.Opening
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.PredicateOpening
/-!
# 公式码最小闭包反演

本模块从 `FormulaCodeₘ` 的构造闭包、最小性和一个具体分离实例推出成员生成反演。
生成方程不是公式码定义公理的分量；分离只构造最小性证明所需的筛选集合。
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

/-- `FormulaCodeₘ` 包含于每个满足四类公式构造闭包的候选集合。 -/
theorem gq_formula_code_minimal :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 305],
        formula_code_closed_condition (x#305) ⟶ₘ
          FormulaCodeₘ ⊆ₘ x#305 := by
  have hAxiom :
      ⊢ₘ[formula_code_theory]
        formula_code_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hSetDefinition :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight hAxiom
  exact gq_weaken_formula_code <|
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight hSetDefinition

/--
对象理论中存在 `FormulaCodeₘ` 的一步生成成员筛选集。
这里只使用加入 `formula_code_theory` 的那一个分离实例。
-/
theorem gq_formula_code_generation_separation_exists :
    ⊢ₘ[godel_quotation_theory]
      formula_code_generation_predicate.separation_exists
        FormulaCodeₘ := by
  have hAxiom :
      ⊢ₘ[formula_code_theory]
        formula_code_generation_separation_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inr <| Or.inl rfl)
  exact gq_weaken_formula_code <|
    formula_code_generation_predicate.separation_exists_of_axiom
      FormulaCodeₘ formula_code_set_term_admissible hAxiom

/--
把分离谓词的元素参数代入一步生成条件。五个见证编号的新鲜性正是避免内部
存在量词捕获调用项所需的边界。
-/
private theorem gqi_generation_condition_substitute
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [306, 307, 308, 309, 310] [code]) :
    Formula.substituteFree SetSort.set 311 code
        (formula_code_generation_condition FormulaCodeₘ (x#311)) =
      formula_code_generation_condition FormulaCodeₘ code := by
  have hCommute (id : FreeVarId) (body : SetFormula)
      (hId : id ∈ [306, 307, 308, 309, 310]) :
      Formula.substituteFree SetSort.set 311 code
          (Formula.closeFreeAt SetSort.set id 0 body) =
        Formula.closeFreeAt SetSort.set id 0
          (Formula.substituteFree SetSort.set 311 code body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set 311 id 0 code body
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
        rcases hId with rfl | rfl | rfl | rfl | rfl <;> decide)
      hCode.2
      (hFresh code (by simp) id hId)).symm
  simp [formula_code_generation_condition,
    Formula.substituteFree, Term.substituteFree,
    set_variable,
    hCommute 306, hCommute 307, hCommute 308,
    hCommute 309, hCommute 310]

/-- 分离规格在任意 admissible 代码项处的逐点实例。 -/
private theorem gqi_generation_separation_member_iff
    {Γ : Context signature}
    (candidate code : SetTerm)
    (hCandidate : Term.Admissible candidate SetSort.set)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [306, 307, 308, 309, 310] [code])
    (hSpec :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_generation_predicate.separation_spec
          FormulaCodeₘ candidate) :
    Γ ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ candidate) ↔ₘ
        ((code ∈ₘ FormulaCodeₘ) ∧ₘ
          formula_code_generation_condition FormulaCodeₘ code) := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := code) hSpec
  have hCandidateOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term candidate = candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term candidate hCandidate.2
  have hFormulaCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term FormulaCodeₘ = FormulaCodeₘ :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term FormulaCodeₘ
      formula_code_set_term_admissible.2
  have hGenerationOpen :
      Formula.openAt SetSort.set 0 code
          (Formula.closeFreeAt SetSort.set 311 0
            (formula_code_generation_condition FormulaCodeₘ (x#311))) =
        formula_code_generation_condition FormulaCodeₘ code := by
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    exact gqi_generation_condition_substitute code hCode hFresh
  simpa [SetPredicate.separation_spec,
    formula_code_generation_predicate,
    Formula.openAt, Term.openAt,
    hCandidateOpen, hFormulaCodeOpen,
    hGenerationOpen] using hAt

/-- 一步生成条件保持候选项和代码项的 admissibility。 -/
private theorem gqi_generation_condition_admissible
    (candidate code : SetTerm)
    (hCandidate : Term.Admissible candidate SetSort.set)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (formula_code_generation_condition candidate code) := by
  prove_admissible

/-- 原子公式成员注入一步生成条件。 -/
private theorem gqi_generation_of_atomic
    {Γ : Context signature} (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hAtomic :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ AtomicCodeₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      formula_code_generation_condition FormulaCodeₘ code := by
  have hCheck :=
    Formula.check_certificate_of_admissible <|
      gqi_generation_condition_admissible
        FormulaCodeₘ code
        formula_code_set_term_admissible hCode
  rw [formula_code_generation_condition] at hCheck
  have hTailCheck :=
    (Formula.CheckCertificate.disj_iff.mp hCheck).2
  unfold formula_code_generation_condition
  exact FirstOrder.Derives.disjIntroLeft
    hAtomic (hRightCheck := hTailCheck)

/-- 已有公式码的否定构造注入一步生成条件。 -/
private theorem gqi_generation_of_negation
    {Γ : Context signature} (body : SetTerm)
    (hBody : Term.Admissible body SetSort.set)
    (hFresh : ReservedIdsFresh [306] [body])
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      formula_code_generation_condition
        FormulaCodeₘ (neg_codeₘ(body)) := by
  have hBodyFixed :
      Term.substituteFree SetSort.set 306 body body = body :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 306 body body
      (hFresh body (by simp) 306 (by simp))
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 306],
          (x#306 ∈ₘ FormulaCodeₘ) ∧ₘ
            (neg_codeₘ(body) ≐ₘ neg_codeₘ(x#306)) := by
    nd_apply FirstOrder.Derives.exists_intro
      (term := body)
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    simpa [Formula.substituteFree, Term.substituteFree,
      set_variable, hBodyFixed] using
      FirstOrder.Derives.conjIntro hBodyMember
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (neg_codeₘ(body)))
  have hCheck :=
    Formula.check_certificate_of_admissible <|
      gqi_generation_condition_admissible
        FormulaCodeₘ (neg_codeₘ(body))
        formula_code_set_term_admissible
        (negation_formula_code_term_admissible body hBody)
  rw [formula_code_generation_condition] at hCheck
  have hAtomicCheck :=
    (Formula.CheckCertificate.disj_iff.mp hCheck).1
  have hTailCheck :=
    (Formula.CheckCertificate.disj_iff.mp hCheck).2
  have hImplicationTailCheck :=
    (Formula.CheckCertificate.disj_iff.mp hTailCheck).2
  unfold formula_code_generation_condition
  exact FirstOrder.Derives.disjIntroRight
    (FirstOrder.Derives.disjIntroLeft
      hExists (hRightCheck := hImplicationTailCheck))
    (hLeftCheck := hAtomicCheck)

/-- 两个已有公式码的蕴含构造注入一步生成条件。 -/
private theorem gqi_generation_of_implication
    {Γ : Context signature} (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hFresh :
      ReservedIdsFresh [307, 308] [left, right])
    (hLeftMember :
      Γ ⊢ₘ[godel_quotation_theory]
        left ∈ₘ FormulaCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[godel_quotation_theory]
        right ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      formula_code_generation_condition
        FormulaCodeₘ (imp_codeₘ(left, right)) := by
  have hLeftFixed307 :
      Term.substituteFree SetSort.set 307 left left = left :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 307 left left
      (hFresh left (by simp) 307 (by simp))
  have hRightFixed307 :
      Term.substituteFree SetSort.set 307 left right = right :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 307 left right
      (hFresh right (by simp) 307 (by simp))
  have hLeftFixed308 :
      Term.substituteFree SetSort.set 308 right left = left :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 308 right left
      (hFresh left (by simp) 308 (by simp))
  have hRightFixed308 :
      Term.substituteFree SetSort.set 308 right right = right :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 308 right right
      (hFresh right (by simp) 308 (by simp))
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 307],
          ∃ₘ[SetSort.set, 308],
            (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
              (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
              (imp_codeₘ(left, right) ≐ₘ
                imp_codeₘ(x#307, x#308))) := by
    nd_apply FirstOrder.Derives.exists_intro
      (term := left)
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    nd_apply FirstOrder.Derives.exists_intro
      (term := right)
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 307 308 0 left _
      (by decide) hLeft.2
      (hFresh left (by simp) 308 (by simp))]
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    simpa [Formula.substituteFree, Term.substituteFree,
      set_variable, hLeftFixed307, hRightFixed307,
      hLeftFixed308, hRightFixed308] using
      FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro
          hLeftMember hRightMember)
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (imp_codeₘ(left, right)))
  have hCheck :=
    Formula.check_certificate_of_admissible <|
      gqi_generation_condition_admissible
        FormulaCodeₘ (imp_codeₘ(left, right))
        formula_code_set_term_admissible
        (implication_formula_code_term_admissible
          left right hLeft hRight)
  rw [formula_code_generation_condition] at hCheck
  have hAtomicCheck :=
    (Formula.CheckCertificate.disj_iff.mp hCheck).1
  have hTailCheck :=
    (Formula.CheckCertificate.disj_iff.mp hCheck).2
  have hNegationCheck :=
    (Formula.CheckCertificate.disj_iff.mp hTailCheck).1
  have hImplicationTailCheck :=
    (Formula.CheckCertificate.disj_iff.mp hTailCheck).2
  have hUniversalCheck :=
    (Formula.CheckCertificate.disj_iff.mp
      hImplicationTailCheck).2
  unfold formula_code_generation_condition
  exact FirstOrder.Derives.disjIntroRight
    (FirstOrder.Derives.disjIntroRight
      (FirstOrder.Derives.disjIntroLeft
        hExists (hRightCheck := hUniversalCheck))
      (hLeftCheck := hNegationCheck))
    (hLeftCheck := hAtomicCheck)

/-- 变量符号与已有公式码的全称构造注入一步生成条件。 -/
private theorem gqi_generation_of_universal
    {Γ : Context signature} (boundVariable body : SetTerm)
    (hVariable : Term.Admissible boundVariable SetSort.set)
    (hBody : Term.Admissible body SetSort.set)
    (hFresh :
      ReservedIdsFresh [309, 310] [boundVariable, body])
    (hVariableMember :
      Γ ⊢ₘ[godel_quotation_theory]
        boundVariable ∈ₘ VarSymₘ)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      formula_code_generation_condition
        FormulaCodeₘ
        (forall_codeₘ(boundVariable, body)) := by
  have hVariableFixed309 :
      Term.substituteFree SetSort.set 309
          boundVariable boundVariable =
        boundVariable :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 309 boundVariable boundVariable
      (hFresh boundVariable (by simp) 309 (by simp))
  have hBodyFixed309 :
      Term.substituteFree SetSort.set 309
          boundVariable body = body :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 309 boundVariable body
      (hFresh body (by simp) 309 (by simp))
  have hVariableFixed310 :
      Term.substituteFree SetSort.set 310 body boundVariable =
        boundVariable :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 310 body boundVariable
      (hFresh boundVariable (by simp) 310 (by simp))
  have hBodyFixed310 :
      Term.substituteFree SetSort.set 310 body body = body :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 310 body body
      (hFresh body (by simp) 310 (by simp))
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 309],
          ∃ₘ[SetSort.set, 310],
            (((x#309 ∈ₘ VarSymₘ) ∧ₘ
              (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
              (forall_codeₘ(boundVariable, body) ≐ₘ
                forall_codeₘ(x#309, x#310))) := by
    nd_apply FirstOrder.Derives.exists_intro
      (term := boundVariable)
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    nd_apply FirstOrder.Derives.exists_intro
      (term := body)
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 309 310 0 boundVariable _
      (by decide) hVariable.2
      (hFresh boundVariable (by simp) 310 (by simp))]
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    simpa [Formula.substituteFree, Term.substituteFree,
      set_variable, hVariableFixed309, hBodyFixed309,
      hVariableFixed310, hBodyFixed310] using
      FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro
          hVariableMember hBodyMember)
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (forall_codeₘ(boundVariable, body)))
  have hCheck :=
    Formula.check_certificate_of_admissible <|
      gqi_generation_condition_admissible
        FormulaCodeₘ
        (forall_codeₘ(boundVariable, body))
        formula_code_set_term_admissible
        (universal_formula_code_term_admissible
          boundVariable body hVariable hBody)
  rw [formula_code_generation_condition] at hCheck
  have hAtomicCheck :=
    (Formula.CheckCertificate.disj_iff.mp hCheck).1
  have hTailCheck :=
    (Formula.CheckCertificate.disj_iff.mp hCheck).2
  have hNegationCheck :=
    (Formula.CheckCertificate.disj_iff.mp hTailCheck).1
  have hImplicationTailCheck :=
    (Formula.CheckCertificate.disj_iff.mp hTailCheck).2
  have hImplicationCheck :=
    (Formula.CheckCertificate.disj_iff.mp
      hImplicationTailCheck).1
  unfold formula_code_generation_condition
  exact FirstOrder.Derives.disjIntroRight
    (FirstOrder.Derives.disjIntroRight
      (FirstOrder.Derives.disjIntroRight
        hExists (hLeftCheck := hImplicationCheck))
      (hLeftCheck := hNegationCheck))
    (hLeftCheck := hAtomicCheck)

/-- 最小性证明中使用的固定分离见证规格。 -/
private def gqi_filter_spec : SetFormula :=
  formula_code_generation_predicate.separation_spec
    FormulaCodeₘ (x#600)

private theorem gqi_filter_spec_admissible :
    Formula.Admissible gqi_filter_spec := by
  exact formula_code_generation_predicate.separation_spec_admissible
    formula_code_set_term_admissible
    (set_variable_admissible 600)

/-- 把逐点子集条件重新封装为对象层子集关系。 -/
private theorem gqi_subset_of_condition
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        subset_condition left right) :
    Γ ⊢ₘ[godel_quotation_theory]
      left ⊆ₘ right := by
  have hDefinition :
      Γ ⊢ₘ[godel_quotation_theory]
        (left ⊆ₘ right) ↔ₘ
          subset_condition left right :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_subset <|
          subset_definition_instance_derives_of_admissible
            left right hLeft hRight
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hCondition

/-- Gödel quotation 理论中的句子对任意 eigen 编号新鲜。 -/
private theorem gqi_theory_fresh (id : FreeVarId) :
    ∀ formula, godel_quotation_theory formula →
      (SetSort.set, id) ∉ Formula.freeSupport formula := by
  intro formula hFormula
  rw [(godel_quotation_theory_sentence hFormula).2]
  exact List.not_mem_nil

/-- 单个自由变量与一组不同的保留编号组成显式新鲜合同。 -/
private theorem gqi_reserved_ids_fresh_variable
    (ids : List FreeVarId) (variableId : FreeVarId)
    (hVariable :
      ∀ id, id ∈ ids → variableId ≠ id) :
    ReservedIdsFresh ids [x#variableId] :=
  reserved_ids_fresh_cons_variable
    variableId hVariable
    (reserved_ids_fresh_nil ids)

/-- 单项的逐编号新鲜证明封装成 `ReservedIdsFresh`。 -/
private theorem gqi_reserved_ids_fresh_single
    (ids : List FreeVarId) (term : SetTerm)
    (hFresh :
      ∀ id, id ∈ ids →
        (SetSort.set, id) ∉ Term.freeSupport term) :
    ReservedIdsFresh ids [term] := by
  intro candidate hCandidate id hId
  rw [List.mem_singleton] at hCandidate
  subst candidate
  exact hFresh id hId

/-- 一步生成筛选集包含全部原子公式码。 -/
private theorem gqi_filter_atomic_subset :
    [gqi_filter_spec] ⊢ₘ[godel_quotation_theory]
      AtomicCodeₘ ⊆ₘ x#600 := by
  let element : SetTerm := x#601
  let member : SetFormula :=
    element ∈ₘ AtomicCodeₘ
  let Γ : Context signature := [gqi_filter_spec]
  have hElement :
      Term.Admissible element SetSort.set := by
    simpa [element] using set_variable_admissible 601
  have hPointwise :
      Γ ⊢ₘ[godel_quotation_theory]
        member ⟶ₘ (element ∈ₘ x#600) := by
    have hMemberAdmissible :
        Formula.Admissible member := by
      simpa [member] using
        membership_formula_admissible hElement
          atomic_formula_code_set_term_admissible
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := member :: Γ
    have hAtomic :
        Δ ⊢ₘ[godel_quotation_theory]
          element ∈ₘ AtomicCodeₘ := by
      simpa [member] using
        (FirstOrder.Derives.assumption
          (T := godel_quotation_theory)
          (Γ := Δ) (φ := member) (by simp [Δ]))
    have hFormula :
        Δ ⊢ₘ[godel_quotation_theory]
          element ∈ₘ FormulaCodeₘ :=
      gq_subset_member
        AtomicCodeₘ FormulaCodeₘ element
        atomic_formula_code_set_term_admissible
        formula_code_set_term_admissible hElement
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            gq_atomic_formula_codes_subset_formula_codes)
        hAtomic
    have hGenerated :
        Δ ⊢ₘ[godel_quotation_theory]
          formula_code_generation_condition
            FormulaCodeₘ element :=
      gqi_generation_of_atomic
        element hElement hAtomic
    have hSpec :
        Δ ⊢ₘ[godel_quotation_theory]
          gqi_filter_spec :=
      FirstOrder.Derives.assumption (by simp [Δ, Γ])
    have hAt :=
      gqi_generation_separation_member_iff
        (x#600) element
        (set_variable_admissible 600) hElement
        (gqi_reserved_ids_fresh_variable
          [306, 307, 308, 309, 310] 601 <| by
            intro id hId
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at hId
            rcases hId with rfl | rfl | rfl | rfl | rfl <;>
              decide)
        (by simpa [gqi_filter_spec] using hSpec)
    exact FirstOrder.Derives.iffElimLeft
      hAt <|
        FirstOrder.Derives.conjIntro
          hFormula hGenerated
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 601)
      (body := member ⟶ₘ (element ∈ₘ x#600))
      (gqi_theory_fresh 601)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hPointwise
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        subset_condition AtomicCodeₘ (x#600) := by
    simpa [subset_condition, member, element,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable] using
      hGeneralized
  simpa [Γ] using
    gqi_subset_of_condition
      AtomicCodeₘ (x#600)
      atomic_formula_code_set_term_admissible
      (set_variable_admissible 600)
      hCondition

/-- 一步生成筛选集对否定构造封闭。 -/
private theorem gqi_filter_negation_closed :
    [gqi_filter_spec] ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 300],
        (x#300 ∈ₘ x#600) ⟶ₘ
          (neg_codeₘ(x#300) ∈ₘ x#600) := by
  let body : SetTerm := x#602
  let member : SetFormula :=
    body ∈ₘ x#600
  let Γ : Context signature := [gqi_filter_spec]
  have hBody :
      Term.Admissible body SetSort.set := by
    simpa [body] using set_variable_admissible 602
  have hNegation :
      Term.Admissible (neg_codeₘ(body)) SetSort.set :=
    negation_formula_code_term_admissible body hBody
  have hBodyFresh :
      ReservedIdsFresh
        [306, 307, 308, 309, 310] [body] := by
    simpa [body] using
      gqi_reserved_ids_fresh_variable
        [306, 307, 308, 309, 310] 602 (by
          intro id hId
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at hId
          rcases hId with rfl | rfl | rfl | rfl | rfl <;>
            decide)
  have hNegationFresh :
      ReservedIdsFresh
        [306, 307, 308, 309, 310]
        [neg_codeₘ(body)] :=
    gqi_reserved_ids_fresh_single
      [306, 307, 308, 309, 310]
      (neg_codeₘ(body)) <| by
        intro id hId
        have hFresh :=
          hBodyFresh body (by simp) id hId
        simpa [Term.freeSupport,
          Term.freeSupportList] using hFresh
  have hPointwise :
      Γ ⊢ₘ[godel_quotation_theory]
        member ⟶ₘ
          (neg_codeₘ(body) ∈ₘ x#600) := by
    have hMemberAdmissible :
        Formula.Admissible member := by
      simpa [member] using
        membership_formula_admissible
          hBody (set_variable_admissible 600)
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := member :: Γ
    have hMember :
        Δ ⊢ₘ[godel_quotation_theory]
          body ∈ₘ x#600 := by
      simpa [member] using
        (FirstOrder.Derives.assumption
          (T := godel_quotation_theory)
          (Γ := Δ) (φ := member) (by simp [Δ]))
    have hSpec :
        Δ ⊢ₘ[godel_quotation_theory]
          gqi_filter_spec :=
      FirstOrder.Derives.assumption (by simp [Δ, Γ])
    have hBodyAt :=
      gqi_generation_separation_member_iff
        (x#600) body
        (set_variable_admissible 600) hBody
        hBodyFresh
        (by simpa [gqi_filter_spec] using hSpec)
    have hBodyData :=
      FirstOrder.Derives.iffElimRight
        hBodyAt hMember
    have hBodyFormula :
        Δ ⊢ₘ[godel_quotation_theory]
          body ∈ₘ FormulaCodeₘ :=
      FirstOrder.Derives.conjElimLeft
        hBodyData
    have hNegationFormula :
        Δ ⊢ₘ[godel_quotation_theory]
          neg_codeₘ(body) ∈ₘ FormulaCodeₘ :=
      gq_formula_code_mem_negation
        body hBody hBodyFormula
    have hGenerated :
        Δ ⊢ₘ[godel_quotation_theory]
          formula_code_generation_condition
            FormulaCodeₘ (neg_codeₘ(body)) :=
      gqi_generation_of_negation
        body hBody
        (gqi_reserved_ids_fresh_single
          [306] body <| by
            intro id hId
            exact hBodyFresh body (by simp) id
              (by
                simp only [List.mem_singleton] at hId
                subst id
                simp))
        hBodyFormula
    have hNegationAt :=
      gqi_generation_separation_member_iff
        (x#600) (neg_codeₘ(body))
        (set_variable_admissible 600)
        hNegation hNegationFresh
        (by simpa [gqi_filter_spec] using hSpec)
    exact FirstOrder.Derives.iffElimLeft
      hNegationAt <|
        FirstOrder.Derives.conjIntro
          hNegationFormula hGenerated
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 602)
      (body := member ⟶ₘ
        (neg_codeₘ(body) ∈ₘ x#600))
      (gqi_theory_fresh 602)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hPointwise
  simpa [Γ, member, body,
    Formula.closeFreeAt, Term.closeFreeAt,
    set_variable, set_bound_variable] using
    hGeneralized

/-- 一步生成筛选集对蕴含构造封闭。 -/
private theorem gqi_filter_implication_closed :
    [gqi_filter_spec] ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 301],
        ∀ₘ[SetSort.set, 302],
          (((x#301 ∈ₘ x#600) ∧ₘ
            (x#302 ∈ₘ x#600)) ⟶ₘ
              (imp_codeₘ(x#301, x#302) ∈ₘ x#600)) := by
  let left : SetTerm := x#603
  let right : SetTerm := x#604
  let member : SetFormula :=
    (left ∈ₘ x#600) ∧ₘ
      (right ∈ₘ x#600)
  let Γ : Context signature := [gqi_filter_spec]
  have hLeft :
      Term.Admissible left SetSort.set := by
    simpa [left] using set_variable_admissible 603
  have hRight :
      Term.Admissible right SetSort.set := by
    simpa [right] using set_variable_admissible 604
  have hImplication :
      Term.Admissible
        (imp_codeₘ(left, right)) SetSort.set :=
    implication_formula_code_term_admissible
      left right hLeft hRight
  have hInputsFresh :
      ReservedIdsFresh
        [306, 307, 308, 309, 310]
        [left, right] := by
    simpa [left, right] using
      reserved_ids_fresh_cons_variable
        603 (by
          intro id hId
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at hId
          rcases hId with rfl | rfl | rfl | rfl | rfl <;>
            decide)
        (reserved_ids_fresh_cons_variable
          604 (by
            intro id hId
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at hId
            rcases hId with rfl | rfl | rfl | rfl | rfl <;>
              decide)
          (reserved_ids_fresh_nil
            [306, 307, 308, 309, 310]))
  have hImplicationFresh :
      ReservedIdsFresh
        [306, 307, 308, 309, 310]
        [imp_codeₘ(left, right)] :=
    gqi_reserved_ids_fresh_single
      [306, 307, 308, 309, 310]
      (imp_codeₘ(left, right)) <| by
        intro id hId
        have hLeftFresh :=
          hInputsFresh left (by simp) id hId
        have hRightFresh :=
          hInputsFresh right (by simp) id hId
        simp only [Term.freeSupport,
          Term.freeSupportList]
        intro hMember
        rcases List.mem_append.mp hMember with
          hMember | hMember
        · exact hLeftFresh hMember
        · exact hRightFresh hMember
  have hPointwise :
      Γ ⊢ₘ[godel_quotation_theory]
        member ⟶ₘ
          (imp_codeₘ(left, right) ∈ₘ x#600) := by
    have hMemberAdmissible :
        Formula.Admissible member := by
      simpa [member] using
        Formula.Admissible.conj
          (membership_formula_admissible
            hLeft (set_variable_admissible 600))
          (membership_formula_admissible
            hRight (set_variable_admissible 600))
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := member :: Γ
    have hMember :
        Δ ⊢ₘ[godel_quotation_theory] member :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hLeftMember :
        Δ ⊢ₘ[godel_quotation_theory]
          left ∈ₘ x#600 :=
      FirstOrder.Derives.conjElimLeft hMember
    have hRightMember :
        Δ ⊢ₘ[godel_quotation_theory]
          right ∈ₘ x#600 :=
      FirstOrder.Derives.conjElimRight hMember
    have hSpec :
        Δ ⊢ₘ[godel_quotation_theory]
          gqi_filter_spec :=
      FirstOrder.Derives.assumption (by simp [Δ, Γ])
    have hLeftAt :=
      gqi_generation_separation_member_iff
        (x#600) left
        (set_variable_admissible 600) hLeft
        (gqi_reserved_ids_fresh_single
          [306, 307, 308, 309, 310] left <| by
            intro id hId
            exact hInputsFresh left (by simp) id hId)
        (by simpa [gqi_filter_spec] using hSpec)
    have hRightAt :=
      gqi_generation_separation_member_iff
        (x#600) right
        (set_variable_admissible 600) hRight
        (gqi_reserved_ids_fresh_single
          [306, 307, 308, 309, 310] right <| by
            intro id hId
            exact hInputsFresh right (by simp) id hId)
        (by simpa [gqi_filter_spec] using hSpec)
    have hLeftFormula :
        Δ ⊢ₘ[godel_quotation_theory]
          left ∈ₘ FormulaCodeₘ :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.iffElimRight
          hLeftAt hLeftMember
    have hRightFormula :
        Δ ⊢ₘ[godel_quotation_theory]
          right ∈ₘ FormulaCodeₘ :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.iffElimRight
          hRightAt hRightMember
    have hImplicationFormula :
        Δ ⊢ₘ[godel_quotation_theory]
          imp_codeₘ(left, right) ∈ₘ FormulaCodeₘ :=
      gq_formula_code_mem_implication
        left right hLeft hRight
        hLeftFormula hRightFormula
    have hGenerated :
        Δ ⊢ₘ[godel_quotation_theory]
          formula_code_generation_condition
            FormulaCodeₘ
            (imp_codeₘ(left, right)) :=
      gqi_generation_of_implication
        left right hLeft hRight
        (by
          intro term hTerm id hId
          exact hInputsFresh term hTerm id <| by
            simp only [List.mem_cons,
              List.not_mem_nil, or_false] at hId ⊢
            rcases hId with rfl | rfl <;> simp)
        hLeftFormula hRightFormula
    have hImplicationAt :=
      gqi_generation_separation_member_iff
        (x#600) (imp_codeₘ(left, right))
        (set_variable_admissible 600)
        hImplication hImplicationFresh
        (by simpa [gqi_filter_spec] using hSpec)
    exact FirstOrder.Derives.iffElimLeft
      hImplicationAt <|
        FirstOrder.Derives.conjIntro
          hImplicationFormula hGenerated
  have hRightGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 604)
      (body := member ⟶ₘ
        (imp_codeₘ(left, right) ∈ₘ x#600))
      (gqi_theory_fresh 604)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hPointwise
  have hLeftGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 603)
      (body :=
        ∀ₘ[SetSort.set, 604],
          member ⟶ₘ
            (imp_codeₘ(left, right) ∈ₘ x#600))
      (gqi_theory_fresh 603)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hRightGeneralized
  simpa [Γ, member, left, right,
    Formula.closeFreeAt, Term.closeFreeAt,
    set_variable, set_bound_variable] using
    hLeftGeneralized

/-- 一步生成筛选集对全称公式构造封闭。 -/
private theorem gqi_filter_universal_closed :
    [gqi_filter_spec] ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 303],
        ∀ₘ[SetSort.set, 304],
          (((x#303 ∈ₘ VarSymₘ) ∧ₘ
            (x#304 ∈ₘ x#600)) ⟶ₘ
              (forall_codeₘ(x#303, x#304) ∈ₘ x#600)) := by
  let boundVariable : SetTerm := x#605
  let body : SetTerm := x#606
  let member : SetFormula :=
    (boundVariable ∈ₘ VarSymₘ) ∧ₘ
      (body ∈ₘ x#600)
  let Γ : Context signature := [gqi_filter_spec]
  have hVariable :
      Term.Admissible boundVariable SetSort.set := by
    simpa [boundVariable] using
      set_variable_admissible 605
  have hBody :
      Term.Admissible body SetSort.set := by
    simpa [body] using set_variable_admissible 606
  have hUniversal :
      Term.Admissible
        (forall_codeₘ(boundVariable, body)) SetSort.set :=
    universal_formula_code_term_admissible
      boundVariable body hVariable hBody
  have hInputsFresh :
      ReservedIdsFresh
        [306, 307, 308, 309, 310]
        [boundVariable, body] := by
    simpa [boundVariable, body] using
      reserved_ids_fresh_cons_variable
        605 (by
          intro id hId
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at hId
          rcases hId with rfl | rfl | rfl | rfl | rfl <;>
            decide)
        (reserved_ids_fresh_cons_variable
          606 (by
            intro id hId
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at hId
            rcases hId with rfl | rfl | rfl | rfl | rfl <;>
              decide)
          (reserved_ids_fresh_nil
            [306, 307, 308, 309, 310]))
  have hUniversalFresh :
      ReservedIdsFresh
        [306, 307, 308, 309, 310]
        [forall_codeₘ(boundVariable, body)] :=
    gqi_reserved_ids_fresh_single
      [306, 307, 308, 309, 310]
      (forall_codeₘ(boundVariable, body)) <| by
        intro id hId
        have hVariableFresh :=
          hInputsFresh boundVariable (by simp) id hId
        have hBodyFresh :=
          hInputsFresh body (by simp) id hId
        simp only [Term.freeSupport,
          Term.freeSupportList]
        intro hMember
        rcases List.mem_append.mp hMember with
          hMember | hMember
        · exact hVariableFresh hMember
        · exact hBodyFresh hMember
  have hPointwise :
      Γ ⊢ₘ[godel_quotation_theory]
        member ⟶ₘ
          (forall_codeₘ(boundVariable, body) ∈ₘ x#600) := by
    have hMemberAdmissible :
        Formula.Admissible member := by
      simpa [member] using
        Formula.Admissible.conj
          (membership_formula_admissible
            hVariable
            variable_symbol_set_term_admissible)
          (membership_formula_admissible
            hBody (set_variable_admissible 600))
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := member :: Γ
    have hMember :
        Δ ⊢ₘ[godel_quotation_theory] member :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hVariableMember :
        Δ ⊢ₘ[godel_quotation_theory]
          boundVariable ∈ₘ VarSymₘ :=
      FirstOrder.Derives.conjElimLeft hMember
    have hBodyMember :
        Δ ⊢ₘ[godel_quotation_theory]
          body ∈ₘ x#600 :=
      FirstOrder.Derives.conjElimRight hMember
    have hSpec :
        Δ ⊢ₘ[godel_quotation_theory]
          gqi_filter_spec :=
      FirstOrder.Derives.assumption (by simp [Δ, Γ])
    have hBodyAt :=
      gqi_generation_separation_member_iff
        (x#600) body
        (set_variable_admissible 600) hBody
        (gqi_reserved_ids_fresh_single
          [306, 307, 308, 309, 310] body <| by
            intro id hId
            exact hInputsFresh body (by simp) id hId)
        (by simpa [gqi_filter_spec] using hSpec)
    have hBodyFormula :
        Δ ⊢ₘ[godel_quotation_theory]
          body ∈ₘ FormulaCodeₘ :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.iffElimRight
          hBodyAt hBodyMember
    have hUniversalFormula :
        Δ ⊢ₘ[godel_quotation_theory]
          forall_codeₘ(boundVariable, body) ∈ₘ
            FormulaCodeₘ :=
      gq_formula_code_mem_universal
        boundVariable body hVariable hBody
        hVariableMember hBodyFormula
    have hGenerated :
        Δ ⊢ₘ[godel_quotation_theory]
          formula_code_generation_condition
            FormulaCodeₘ
            (forall_codeₘ(boundVariable, body)) :=
      gqi_generation_of_universal
        boundVariable body hVariable hBody
        (by
          intro term hTerm id hId
          exact hInputsFresh term hTerm id <| by
            simp only [List.mem_cons,
              List.not_mem_nil, or_false] at hId ⊢
            rcases hId with rfl | rfl <;> simp)
        hVariableMember hBodyFormula
    have hUniversalAt :=
      gqi_generation_separation_member_iff
        (x#600)
        (forall_codeₘ(boundVariable, body))
        (set_variable_admissible 600)
        hUniversal hUniversalFresh
        (by simpa [gqi_filter_spec] using hSpec)
    exact FirstOrder.Derives.iffElimLeft
      hUniversalAt <|
        FirstOrder.Derives.conjIntro
          hUniversalFormula hGenerated
  have hBodyGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 606)
      (body := member ⟶ₘ
        (forall_codeₘ(boundVariable, body) ∈ₘ x#600))
      (gqi_theory_fresh 606)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hPointwise
  have hVariableGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 605)
      (body :=
        ∀ₘ[SetSort.set, 606],
          member ⟶ₘ
            (forall_codeₘ(boundVariable, body) ∈ₘ x#600))
      (gqi_theory_fresh 605)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hBodyGeneralized
  simpa [Γ, member, boundVariable, body,
    Formula.closeFreeAt, Term.closeFreeAt,
    set_variable, set_bound_variable] using
    hVariableGeneralized

/-- 一步生成筛选集满足完整的四分量公式构造闭包。 -/
private theorem gqi_filter_closed :
    [gqi_filter_spec] ⊢ₘ[godel_quotation_theory]
      formula_code_closed_condition (x#600) := by
  unfold formula_code_closed_condition
  exact FirstOrder.Derives.conjIntro
    gqi_filter_atomic_subset <|
      FirstOrder.Derives.conjIntro
        gqi_filter_negation_closed <|
          FirstOrder.Derives.conjIntro
            gqi_filter_implication_closed
            gqi_filter_universal_closed

/-- 固定筛选见证代入公式闭包条件时穿过五个内部 binder。 -/
private theorem gqi_filter_closed_condition_substitute :
    Formula.substituteFree SetSort.set 305 (x#600)
        (formula_code_closed_condition (x#305)) =
      formula_code_closed_condition (x#600) := by
  have hFresh :
      ReservedIdsFresh [300, 301, 302, 303, 304]
        [x#600] :=
    gqi_reserved_ids_fresh_variable
      [300, 301, 302, 303, 304] 600 (by
        intro id hId
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hId
        rcases hId with rfl | rfl | rfl | rfl | rfl <;>
          decide)
  have hCommute (id : FreeVarId) (body : SetFormula)
      (hId : id ∈ [300, 301, 302, 303, 304]) :
      Formula.substituteFree SetSort.set 305 (x#600)
          (Formula.closeFreeAt SetSort.set id 0 body) =
        Formula.closeFreeAt SetSort.set id 0
          (Formula.substituteFree SetSort.set 305
            (x#600) body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set 305 id 0 (x#600) body
      (by
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hId
        rcases hId with rfl | rfl | rfl | rfl | rfl <;>
          decide)
      (set_variable_admissible 600).2
      (hFresh (x#600) (by simp) id hId)).symm
  simp [formula_code_closed_condition,
    Formula.substituteFree, Term.substituteFree,
    set_variable,
    hCommute 300, hCommute 301, hCommute 302,
    hCommute 303, hCommute 304]

/-- 公式码最小性把全部公式码压入一步生成筛选集。 -/
private theorem gqi_formula_codes_subset_filter :
    [gqi_filter_spec] ⊢ₘ[godel_quotation_theory]
      FormulaCodeₘ ⊆ₘ x#600 := by
  have hMinimal :
      [gqi_filter_spec] ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, 305],
          formula_code_closed_condition (x#305) ⟶ₘ
            FormulaCodeₘ ⊆ₘ x#305 :=
    FirstOrder.Derives.context_weaken_cons
      (assumption := gqi_filter_spec)
      gq_formula_code_minimal
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := x#600) hMinimal
  have hAt' :
      [gqi_filter_spec] ⊢ₘ[godel_quotation_theory]
        formula_code_closed_condition (x#600) ⟶ₘ
          FormulaCodeₘ ⊆ₘ x#600 := by
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.substituteFree, Term.substituteFree,
      set_variable, set_bound_variable,
      gqi_filter_closed_condition_substitute] using hAt
  exact FirstOrder.Derives.impElim
    hAt' gqi_filter_closed

/-- 把匿名分离存在式改写为最小性证明使用的固定 eigen 规格。 -/
private theorem gqi_filter_exists :
    ⊢ₘ[godel_quotation_theory]
      ∃ₘ[SetSort.set, 600], gqi_filter_spec := by
  have hPredicateClose :
      Formula.closeFreeAt SetSort.set 600 1
          formula_code_generation_predicate.body =
        formula_code_generation_predicate.body := by
    apply
      Formula.closeFreeAt_eq_self_of_scoped_of_le_of_not_mem
        (scope := Scope.push Scope.empty SetSort.set)
    · exact
        formula_code_generation_predicate.admissible_at.2
    · exact Nat.le_refl _
    · native_decide
  simpa [gqi_filter_spec,
    SetPredicate.separation_exists,
    SetPredicate.separation_spec,
    Formula.next_depth,
    Formula.closeFreeAt, Term.closeFreeAt,
    set_variable, set_bound_variable,
    hPredicateClose] using
    gq_formula_code_generation_separation_exists

/--
每个完整公式码都由原子公式、否定、蕴含或全称公式构造一步生成。

前提中的六个编号恰为生成定义的五个 binder 与最小性分离的 eigen；不要求代码
项闭合。
-/
theorem gq_formula_code_member_implies_generation_of_fresh
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [306, 307, 308, 309, 310, 600] [code]) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ FormulaCodeₘ) ⟶ₘ
        formula_code_generation_condition
          FormulaCodeₘ code := by
  let conclusion : SetFormula :=
    (code ∈ₘ FormulaCodeₘ) ⟶ₘ
      formula_code_generation_condition
        FormulaCodeₘ code
  have hCodeFresh :
      ReservedIdsFresh
        [306, 307, 308, 309, 310] [code] :=
    by
      intro term hTerm id hId
      apply hFresh term hTerm id
      simp only [List.mem_cons, List.not_mem_nil,
        or_false] at hId ⊢
      rcases hId with
        rfl | rfl | rfl | rfl | rfl <;>
          simp
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := [])
    (sort := SetSort.set)
    (eigen := 600)
    (body := gqi_filter_spec)
    (conclusion := conclusion)
  · exact gqi_theory_fresh 600
  · intro formula hFormula
    cases hFormula
  · have hCodeFresh600 :
        (SetSort.set, 600) ∉
          Term.freeSupport code := by
      exact hFresh code (by simp) 600 (by simp)
    have hFormulaCodeFresh600 :
        (SetSort.set, 600) ∉
          Term.freeSupport FormulaCodeₘ := by
      change (SetSort.set, 600) ∉ []
      exact List.not_mem_nil
    have hMemberFresh :
        (SetSort.set, 600) ∉
          Formula.freeSupport
            (code ∈ₘ FormulaCodeₘ) := by
      simp [Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList,
        hCodeFresh600]
    have hGenerationFresh :=
      gq_formula_code_generation_condition_fresh_600
        FormulaCodeₘ code
        hFormulaCodeFresh600 hCodeFresh600
    simpa [conclusion, Formula.freeSupport] using
      And.intro hMemberFresh hGenerationFresh
  · exact gqi_filter_exists
  · let Γ : Context signature := [gqi_filter_spec]
    have hMemberAdmissible :
        Formula.Admissible
          (code ∈ₘ FormulaCodeₘ) :=
      membership_formula_admissible
        hCode formula_code_set_term_admissible
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature :=
      (code ∈ₘ FormulaCodeₘ) :: Γ
    have hMember :
        Δ ⊢ₘ[godel_quotation_theory]
          code ∈ₘ FormulaCodeₘ :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hSubset :
        Δ ⊢ₘ[godel_quotation_theory]
          FormulaCodeₘ ⊆ₘ x#600 :=
      FirstOrder.Derives.context_weaken
        (Γ := [gqi_filter_spec])
        (Δ := Δ) (by simp [Δ, Γ])
        gqi_formula_codes_subset_filter
    have hFilterMember :
        Δ ⊢ₘ[godel_quotation_theory]
          code ∈ₘ x#600 :=
      gq_subset_member
        FormulaCodeₘ (x#600) code
        formula_code_set_term_admissible
        (set_variable_admissible 600)
        hCode hSubset hMember
    have hSpec :
        Δ ⊢ₘ[godel_quotation_theory]
          gqi_filter_spec :=
      FirstOrder.Derives.assumption
        (by simp [Δ, Γ])
    have hAt :=
      gqi_generation_separation_member_iff
        (x#600) code
        (set_variable_admissible 600)
        hCode hCodeFresh
        (by simpa [gqi_filter_spec] using hSpec)
    exact FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.iffElimRight
        hAt hFilterMember

/--
闭公式码上的生成反演是精确新鲜度接口的直接推论。
-/
theorem gq_formula_code_member_implies_generation
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hClosed : Term.freeSupport code = []) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ FormulaCodeₘ) ⟶ₘ
        formula_code_generation_condition
          FormulaCodeₘ code :=
  gq_formula_code_member_implies_generation_of_fresh
    code hCode <|
      reserved_ids_fresh_cons_closed hClosed <|
        reserved_ids_fresh_nil
          [306, 307, 308, 309, 310, 600]

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
