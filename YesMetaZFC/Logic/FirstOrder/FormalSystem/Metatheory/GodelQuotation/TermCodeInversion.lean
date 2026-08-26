import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCode
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Monotonicity
/-!
# 项码最小闭包反演

本模块从 `TermCodeₘ` 的三分量构造闭包、最小性和单个分离实例推出成员生成反演。
分离集合只用于对象理论中的最小性论证，不改变项码谓词的公开定义。
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

/-- `TermCodeₘ` 包含于每个满足三类项构造闭包的候选集合。 -/
theorem gq_term_code_minimal :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 215],
        term_code_closed_condition (x#215) ⟶ₘ
          TermCodeₘ ⊆ₘ x#215 := by
  have hAxiom :
      ⊢ₘ[term_code_set_theory]
        term_code_set_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inr <| Or.inl rfl)
  exact gq_weaken_term_code_set <|
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight hAxiom

/-- 对象理论中存在 `TermCodeₘ` 的一步生成成员筛选集。 -/
theorem gq_term_code_generation_separation_exists :
    ⊢ₘ[godel_quotation_theory]
      term_code_generation_predicate.separation_exists
        TermCodeₘ := by
  have hAxiom :
      ⊢ₘ[term_code_set_theory]
        term_code_generation_separation_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  exact gq_weaken_term_code_set <|
    term_code_generation_predicate.separation_exists_of_axiom
      TermCodeₘ term_code_set_term_admissible hAxiom

/-- 把分离谓词的元素参数代入一步生成条件。 -/
private theorem gtci_generation_condition_substitute
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [210, 211, 212, 213] [code]) :
    Formula.substituteFree SetSort.set 216 code
        (term_code_generation_condition TermCodeₘ (x#216)) =
      term_code_generation_condition TermCodeₘ code := by
  have hCommute (id : FreeVarId) (body : SetFormula)
      (hId : id ∈ [210, 211, 212, 213]) :
      Formula.substituteFree SetSort.set 216 code
          (Formula.closeFreeAt SetSort.set id 0 body) =
        Formula.closeFreeAt SetSort.set id 0
          (Formula.substituteFree SetSort.set 216 code body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set 216 id 0 code body
      (by
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hId
        rcases hId with rfl | rfl | rfl | rfl <;>
          decide)
      hCode.2
      (hFresh code (by simp) id hId)).symm
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set 216 code (numₘ(value)) =
        numₘ(value) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 216 code (numₘ(value))
      (by simp [finite_numeral_term_freeSupport])
  simp [term_code_generation_condition,
    term_application_from_condition,
    Formula.substituteFree, Term.substituteFree,
    set_variable,
    hNumeralFixed,
    hCommute 210, hCommute 211,
    hCommute 212, hCommute 213]

/-- 分离规格在任意 admissible 代码项处的逐点实例。 -/
private theorem gtci_generation_separation_member_iff
    {Γ : Context signature}
    (candidate code : SetTerm)
    (hCandidate : Term.Admissible candidate SetSort.set)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [210, 211, 212, 213] [code])
    (hSpec :
      Γ ⊢ₘ[godel_quotation_theory]
        term_code_generation_predicate.separation_spec
          TermCodeₘ candidate) :
    Γ ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ candidate) ↔ₘ
        ((code ∈ₘ TermCodeₘ) ∧ₘ
          term_code_generation_condition TermCodeₘ code) := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := code) hSpec
  have hCandidateOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term candidate = candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term candidate hCandidate.2
  have hTermCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term TermCodeₘ = TermCodeₘ :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term TermCodeₘ
      term_code_set_term_admissible.2
  have hGenerationOpen :
      Formula.openAt SetSort.set 0 code
          (Formula.closeFreeAt SetSort.set 216 0
            (term_code_generation_condition TermCodeₘ (x#216))) =
        term_code_generation_condition TermCodeₘ code := by
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    exact gtci_generation_condition_substitute
      code hCode hFresh
  simpa [SetPredicate.separation_spec,
    term_code_generation_predicate,
    Formula.openAt, Term.openAt,
    hCandidateOpen, hTermCodeOpen,
    hGenerationOpen] using hAt

/-- 一步生成条件保持候选项和代码项的 admissibility。 -/
private theorem gtci_generation_condition_admissible
    (candidate code : SetTerm)
    (hCandidate : Term.Admissible candidate SetSort.set)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (term_code_generation_condition candidate code) := by
  prove_admissible

/-- 变量符号成员注入一步生成条件。 -/
private theorem gtci_generation_of_variable
    {Γ : Context signature} (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ VarSymₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      term_code_generation_condition TermCodeₘ code := by
  have hCheck :=
    Formula.check_certificate_of_admissible <|
      gtci_generation_condition_admissible
        TermCodeₘ code
        term_code_set_term_admissible hCode
  rw [term_code_generation_condition] at hCheck
  have hTailCheck :=
    (Formula.CheckCertificate.disj_iff.mp hCheck).2
  unfold term_code_generation_condition
  exact FirstOrder.Derives.disjIntroLeft
    hMember (hRightCheck := hTailCheck)

/-- 常元符号成员注入一步生成条件。 -/
private theorem gtci_generation_of_constant
    {Γ : Context signature} (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ ConstSymₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      term_code_generation_condition TermCodeₘ code := by
  have hCheck :=
    Formula.check_certificate_of_admissible <|
      gtci_generation_condition_admissible
        TermCodeₘ code
        term_code_set_term_admissible hCode
  rw [term_code_generation_condition] at hCheck
  have hVariableCheck :=
    (Formula.CheckCertificate.disj_iff.mp hCheck).1
  have hTailCheck :=
    (Formula.CheckCertificate.disj_iff.mp hCheck).2
  have hApplicationCheck :=
    (Formula.CheckCertificate.disj_iff.mp hTailCheck).2
  unfold term_code_generation_condition
  exact FirstOrder.Derives.disjIntroRight
    (FirstOrder.Derives.disjIntroLeft
      hMember (hRightCheck := hApplicationCheck))
    (hLeftCheck := hVariableCheck)

/-- 一次函数应用条件注入一步生成条件。 -/
private theorem gtci_generation_of_application
    {Γ : Context signature} (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hApplication :
      Γ ⊢ₘ[godel_quotation_theory]
        term_application_from_condition TermCodeₘ code) :
    Γ ⊢ₘ[godel_quotation_theory]
      term_code_generation_condition TermCodeₘ code := by
  have hCheck :=
    Formula.check_certificate_of_admissible <|
      gtci_generation_condition_admissible
        TermCodeₘ code
        term_code_set_term_admissible hCode
  rw [term_code_generation_condition] at hCheck
  have hVariableCheck :=
    (Formula.CheckCertificate.disj_iff.mp hCheck).1
  have hTailCheck :=
    (Formula.CheckCertificate.disj_iff.mp hCheck).2
  have hConstantCheck :=
    (Formula.CheckCertificate.disj_iff.mp hTailCheck).1
  unfold term_code_generation_condition
  exact FirstOrder.Derives.disjIntroRight
    (FirstOrder.Derives.disjIntroRight
      hApplication (hLeftCheck := hConstantCheck))
    (hLeftCheck := hVariableCheck)

/-- 最小性证明中使用的固定分离见证规格。 -/
private def gtci_filter_spec : SetFormula :=
  term_code_generation_predicate.separation_spec
    TermCodeₘ (x#610)

private theorem gtci_filter_spec_admissible :
    Formula.Admissible gtci_filter_spec := by
  exact term_code_generation_predicate.separation_spec_admissible
    term_code_set_term_admissible
    (set_variable_admissible 610)

/-- 把逐点子集条件重新封装为对象层子集关系。 -/
private theorem gtci_subset_of_condition
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
private theorem gtci_theory_fresh (id : FreeVarId) :
    ∀ formula, godel_quotation_theory formula →
      (SetSort.set, id) ∉ Formula.freeSupport formula := by
  intro formula hFormula
  rw [(godel_quotation_theory_sentence hFormula).2]
  exact List.not_mem_nil

/-- 单个自由变量与一组不同的保留编号组成显式新鲜合同。 -/
private theorem gtci_reserved_ids_fresh_variable
    (ids : List FreeVarId) (variableId : FreeVarId)
    (hVariable :
      ∀ id, id ∈ ids → variableId ≠ id) :
    ReservedIdsFresh ids [x#variableId] :=
  reserved_ids_fresh_cons_variable
    variableId hVariable
    (reserved_ids_fresh_nil ids)

/--
一步生成筛选集包含任意基础符号集合。
该引理同时服务变量符号与常元符号两个闭包分量。
-/
private theorem gtci_filter_base_subset
    (source : SetTerm)
    (hSource : Term.Admissible source SetSort.set)
    (hSourceClosed : Term.freeSupport source = [])
    (hSourceTermCodes :
      ⊢ₘ[godel_quotation_theory]
        source ⊆ₘ TermCodeₘ)
    (hGenerate :
      ∀ {Γ : Context signature} (code : SetTerm),
        Term.Admissible code SetSort.set →
        Γ ⊢ₘ[godel_quotation_theory] code ∈ₘ source →
        Γ ⊢ₘ[godel_quotation_theory]
          term_code_generation_condition TermCodeₘ code) :
    [gtci_filter_spec] ⊢ₘ[godel_quotation_theory]
      source ⊆ₘ x#610 := by
  let code : SetTerm := x#611
  let member : SetFormula := code ∈ₘ source
  let Γ : Context signature := [gtci_filter_spec]
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using set_variable_admissible 611
  have hPointwise :
      Γ ⊢ₘ[godel_quotation_theory]
        member ⟶ₘ (code ∈ₘ x#610) := by
    have hMemberAdmissible :
        Formula.Admissible member := by
      simpa [member] using
        membership_formula_admissible hCode hSource
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := member :: Γ
    have hSourceMember :
        Δ ⊢ₘ[godel_quotation_theory]
          code ∈ₘ source := by
      simpa [member] using
        (FirstOrder.Derives.assumption
          (T := godel_quotation_theory)
          (Γ := Δ) (φ := member) (by simp [Δ]))
    have hTermMember :
        Δ ⊢ₘ[godel_quotation_theory]
          code ∈ₘ TermCodeₘ :=
      gq_subset_member
        source TermCodeₘ code
        hSource term_code_set_term_admissible hCode
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ]) hSourceTermCodes)
        hSourceMember
    have hGenerated :
        Δ ⊢ₘ[godel_quotation_theory]
          term_code_generation_condition TermCodeₘ code :=
      hGenerate code hCode hSourceMember
    have hSpec :
        Δ ⊢ₘ[godel_quotation_theory]
          gtci_filter_spec :=
      FirstOrder.Derives.assumption (by simp [Δ, Γ])
    have hAt :=
      gtci_generation_separation_member_iff
        (x#610) code
        (set_variable_admissible 610) hCode
        (gtci_reserved_ids_fresh_variable
          [210, 211, 212, 213] 611 <| by
            intro id hId
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at hId
            rcases hId with rfl | rfl | rfl | rfl <;>
              decide)
        (by simpa [gtci_filter_spec] using hSpec)
    exact FirstOrder.Derives.iffElimLeft
      hAt <|
        FirstOrder.Derives.conjIntro
          hTermMember hGenerated
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 611)
      (body := member ⟶ₘ (code ∈ₘ x#610))
      (gtci_theory_fresh 611)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hPointwise
  have hSourceClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 611 depth source = source :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 611 depth source hSource.2
      (by rw [hSourceClosed]; exact List.not_mem_nil)
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        subset_condition source (x#610) := by
    simpa [subset_condition, member, code,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable,
      hSourceClose] using hGeneralized
  simpa [Γ] using
    gtci_subset_of_condition
      source (x#610) hSource
      (set_variable_admissible 610)
      hCondition

/-- 一步生成筛选集包含全部变量符号。 -/
private theorem gtci_filter_variable_subset :
    [gtci_filter_spec] ⊢ₘ[godel_quotation_theory]
      VarSymₘ ⊆ₘ x#610 :=
  gtci_filter_base_subset
    VarSymₘ variable_symbol_set_term_admissible
    (by native_decide)
    gq_variable_symbols_subset_term_codes
    (fun code hCode hMember =>
      gtci_generation_of_variable code hCode hMember)

/-- 一步生成筛选集包含全部常元符号。 -/
private theorem gtci_filter_constant_subset :
    [gtci_filter_spec] ⊢ₘ[godel_quotation_theory]
      ConstSymₘ ⊆ₘ x#610 :=
  gtci_filter_base_subset
    ConstSymₘ constant_symbol_set_term_admissible
    (by native_decide)
    gq_constant_symbols_subset_term_codes
    (fun code hCode hMember =>
      gtci_generation_of_constant code hCode hMember)

/-- 分离规格直接给出筛选集包含于完整项码集合。 -/
private theorem gtci_filter_subset_term_codes :
    [gtci_filter_spec] ⊢ₘ[godel_quotation_theory]
      x#610 ⊆ₘ TermCodeₘ := by
  let code : SetTerm := x#612
  let member : SetFormula := code ∈ₘ x#610
  let Γ : Context signature := [gtci_filter_spec]
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using set_variable_admissible 612
  have hPointwise :
      Γ ⊢ₘ[godel_quotation_theory]
        member ⟶ₘ (code ∈ₘ TermCodeₘ) := by
    have hMemberAdmissible :
        Formula.Admissible member := by
      simpa [member] using
        membership_formula_admissible
          hCode (set_variable_admissible 610)
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := member :: Γ
    have hMember :
        Δ ⊢ₘ[godel_quotation_theory]
          code ∈ₘ x#610 := by
      simpa [member] using
        (FirstOrder.Derives.assumption
          (T := godel_quotation_theory)
          (Γ := Δ) (φ := member) (by simp [Δ]))
    have hSpec :
        Δ ⊢ₘ[godel_quotation_theory]
          gtci_filter_spec :=
      FirstOrder.Derives.assumption (by simp [Δ, Γ])
    have hAt :=
      gtci_generation_separation_member_iff
        (x#610) code
        (set_variable_admissible 610) hCode
        (gtci_reserved_ids_fresh_variable
          [210, 211, 212, 213] 612 <| by
            intro id hId
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at hId
            rcases hId with rfl | rfl | rfl | rfl <;>
              decide)
        (by simpa [gtci_filter_spec] using hSpec)
    exact FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.iffElimRight hAt hMember
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 612)
      (body := member ⟶ₘ (code ∈ₘ TermCodeₘ))
      (gtci_theory_fresh 612)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hPointwise
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        subset_condition (x#610) TermCodeₘ := by
    simpa [subset_condition, member, code,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable] using
      hGeneralized
  simpa [Γ] using
    gtci_subset_of_condition
      (x#610) TermCodeₘ
      (set_variable_admissible 610)
      term_code_set_term_admissible
      hCondition

/--
筛选集到完整项码集合的包含关系逐点提升一次函数应用条件。
这是应用分支唯一需要穿过三层存在量词与一层全称量词的单调性步骤。
-/
private theorem gtci_filter_application_mono :
    [gtci_filter_spec] ⊢ₘ[godel_quotation_theory]
      term_application_from_condition (x#610) (x#214) ⟶ₘ
        term_application_from_condition TermCodeₘ (x#214) := by
  let Γ : Context signature := [gtci_filter_spec]
  let domainMember : SetFormula :=
    x#213 ∈ₘ domₘ(x#212)
  let sourceMember : SetFormula :=
    (x#212 ·ₘ x#213) ∈ₘ x#610
  let targetMember : SetFormula :=
    (x#212 ·ₘ x#213) ∈ₘ TermCodeₘ
  let sourceValue : SetFormula :=
    domainMember ⟶ₘ sourceMember
  let targetValue : SetFormula :=
    domainMember ⟶ₘ targetMember
  let header : SetFormula :=
    (x#210 ∈ₘ ωₘ) ∧ₘ
      ((x#211 ∈ₘ ωₘ) ∧ₘ
        ((x#212 ∈ₘ seq₊_spaceₘ(CodeStrₘ)) ∧ₘ
          (domₘ(x#212) ≐ₘ Sₘ(x#210))))
  let equation : SetFormula :=
    x#214 ≐ₘ
      term_application_code_term
        (x#210) (x#211) (x#212)
  let sourceBody : SetFormula :=
    header ∧ₘ
      ((∀ₘ[SetSort.set, 213], sourceValue) ∧ₘ
        equation)
  let targetBody : SetFormula :=
    header ∧ₘ
      ((∀ₘ[SetSort.set, 213], targetValue) ∧ₘ
        equation)
  have hValue :
      Γ ⊢ₘ[godel_quotation_theory]
        sourceValue ⟶ₘ targetValue := by
    have hSourceValue :
        Formula.Admissible sourceValue := by
      dsimp [sourceValue, domainMember, sourceMember]
      prove_admissible
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := sourceValue :: Γ
    have hTargetValue :
        Formula.Admissible targetValue := by
      dsimp [targetValue, domainMember, targetMember]
      prove_admissible
    nd_apply FirstOrder.Derives.impIntro
    let Θ : Context signature := domainMember :: Δ
    have hSourceImp :
        Θ ⊢ₘ[godel_quotation_theory]
          sourceValue :=
      FirstOrder.Derives.assumption (by simp [Θ, Δ])
    have hDomain :
        Θ ⊢ₘ[godel_quotation_theory]
          domainMember :=
      FirstOrder.Derives.assumption (by simp [Θ])
    have hSourceMember :
        Θ ⊢ₘ[godel_quotation_theory]
          sourceMember :=
      FirstOrder.Derives.impElim hSourceImp hDomain
    have hSubset :
        Θ ⊢ₘ[godel_quotation_theory]
          x#610 ⊆ₘ TermCodeₘ :=
      FirstOrder.Derives.context_weaken
        (Γ := Γ) (Δ := Θ) (by simp [Θ, Δ, Γ])
        gtci_filter_subset_term_codes
    have hApplication :
        Term.Admissible
          (x#212 ·ₘ x#213) SetSort.set :=
      function_application_term_admissible
        (x#212) (x#213)
        (set_variable_admissible 212)
        (set_variable_admissible 213)
    simpa [targetMember, sourceMember] using
      gq_subset_member
        (x#610) TermCodeₘ
        (x#212 ·ₘ x#213)
        (set_variable_admissible 610)
        term_code_set_term_admissible
        hApplication hSubset
        (by simpa [sourceMember] using hSourceMember)
  have hValues :
      Γ ⊢ₘ[godel_quotation_theory]
        (∀ₘ[SetSort.set, 213], sourceValue) ⟶ₘ
          (∀ₘ[SetSort.set, 213], targetValue) :=
    FirstOrder.Metatheory.Derives.forall_imp_mono
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 213)
      (gtci_theory_fresh 213)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hValue
  have hBody :
      Γ ⊢ₘ[godel_quotation_theory]
        sourceBody ⟶ₘ targetBody := by
    have hSourceBody :
        Formula.Admissible sourceBody := by
      dsimp [sourceBody, header, sourceValue,
        domainMember, sourceMember, equation]
      prove_admissible
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := sourceBody :: Γ
    have hAssumption :
        Δ ⊢ₘ[godel_quotation_theory]
          sourceBody :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hHeader :
        Δ ⊢ₘ[godel_quotation_theory]
          header :=
      FirstOrder.Derives.conjElimLeft hAssumption
    have hTail :
        Δ ⊢ₘ[godel_quotation_theory]
          (∀ₘ[SetSort.set, 213], sourceValue) ∧ₘ
            equation :=
      FirstOrder.Derives.conjElimRight hAssumption
    have hSourceValues :
        Δ ⊢ₘ[godel_quotation_theory]
          ∀ₘ[SetSort.set, 213], sourceValue :=
      FirstOrder.Derives.conjElimLeft hTail
    have hEquation :
        Δ ⊢ₘ[godel_quotation_theory]
          equation :=
      FirstOrder.Derives.conjElimRight hTail
    have hTargetValues :
        Δ ⊢ₘ[godel_quotation_theory]
          ∀ₘ[SetSort.set, 213], targetValue :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken_cons
          (assumption := sourceBody) hValues)
        hSourceValues
    exact FirstOrder.Derives.conjIntro
      hHeader <|
        FirstOrder.Derives.conjIntro
          hTargetValues hEquation
  have hAt212 :=
    FirstOrder.Metatheory.Derives.exists_imp_mono
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 212)
      (gtci_theory_fresh 212)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hBody
  have hAt211 :=
    FirstOrder.Metatheory.Derives.exists_imp_mono
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 211)
      (gtci_theory_fresh 211)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hAt212
  have hAt210 :=
    FirstOrder.Metatheory.Derives.exists_imp_mono
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 210)
      (gtci_theory_fresh 210)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hAt211
  simpa [Γ, term_application_from_condition,
    sourceBody, targetBody, header, equation,
    sourceValue, targetValue,
    domainMember, sourceMember, targetMember] using
    hAt210

/-- 一次函数应用闭包的逐点实例。 -/
private theorem gtci_term_application_closed_instance
    {Γ : Context signature}
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [210, 211, 212, 213] [code]) :
    Γ ⊢ₘ[godel_quotation_theory]
      term_application_from_condition TermCodeₘ code ⟶ₘ
        code ∈ₘ TermCodeₘ := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := code) gq_term_application_closed
  have hSubstitute :
      Formula.substituteFree SetSort.set 214 code
          (term_application_from_condition TermCodeₘ (x#214)) =
        term_application_from_condition TermCodeₘ code := by
    have hCommute (id : FreeVarId) (body : SetFormula)
        (hId : id ∈ [210, 211, 212, 213]) :
        Formula.substituteFree SetSort.set 214 code
            (Formula.closeFreeAt SetSort.set id 0 body) =
          Formula.closeFreeAt SetSort.set id 0
            (Formula.substituteFree SetSort.set 214 code body) :=
      (Formula.closeFreeAt_substituteFree_comm
        SetSort.set 214 id 0 code body
        (by
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at hId
          rcases hId with rfl | rfl | rfl | rfl <;>
            decide)
        hCode.2
        (hFresh code (by simp) id hId)).symm
    have hNumeralFixed (value : Nat) :
        Term.substituteFree SetSort.set 214 code (numₘ(value)) =
          numₘ(value) :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set 214 code (numₘ(value))
        (by simp [finite_numeral_term_freeSupport])
    simp [term_application_from_condition,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hNumeralFixed,
      hCommute 210, hCommute 211,
      hCommute 212, hCommute 213]
  have hAt' :
      ⊢ₘ[godel_quotation_theory]
        term_application_from_condition TermCodeₘ code ⟶ₘ
          code ∈ₘ TermCodeₘ := by
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hSubstitute] using hAt
  exact FirstOrder.Derives.context_weaken
    (Γ := []) (Δ := Γ) (by simp) hAt'

/-- 一步生成筛选集对一次函数应用构造封闭。 -/
private theorem gtci_filter_application_closed :
    [gtci_filter_spec] ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 214],
        term_application_from_condition
            (x#610) (x#214) ⟶ₘ
          ((x#214) ∈ₘ x#610) := by
  let code : SetTerm := x#214
  let member : SetFormula :=
    term_application_from_condition (x#610) code
  let Γ : Context signature := [gtci_filter_spec]
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using set_variable_admissible 214
  have hFresh :
      ReservedIdsFresh [210, 211, 212, 213] [code] := by
    simpa [code] using
      gtci_reserved_ids_fresh_variable
        [210, 211, 212, 213] 214 (by
          intro id hId
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at hId
          rcases hId with rfl | rfl | rfl | rfl <;>
            decide)
  have hPointwise :
      Γ ⊢ₘ[godel_quotation_theory]
        member ⟶ₘ (code ∈ₘ x#610) := by
    have hMemberAdmissible :
        Formula.Admissible member := by
      dsimp [member, code]
      prove_admissible
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := member :: Γ
    have hSourceApplication :
        Δ ⊢ₘ[godel_quotation_theory]
          term_application_from_condition (x#610) code := by
      simpa [member] using
        (FirstOrder.Derives.assumption
          (T := godel_quotation_theory)
          (Γ := Δ) (φ := member) (by simp [Δ]))
    have hTargetApplication :
        Δ ⊢ₘ[godel_quotation_theory]
          term_application_from_condition TermCodeₘ code :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := Γ) (Δ := Δ) (by simp [Δ, Γ])
          (by simpa [code] using
            gtci_filter_application_mono))
        hSourceApplication
    have hTermMember :
        Δ ⊢ₘ[godel_quotation_theory]
          code ∈ₘ TermCodeₘ :=
      FirstOrder.Derives.impElim
        (gtci_term_application_closed_instance
          code hCode hFresh)
        hTargetApplication
    have hGenerated :
        Δ ⊢ₘ[godel_quotation_theory]
          term_code_generation_condition TermCodeₘ code :=
      gtci_generation_of_application
        code hCode hTargetApplication
    have hSpec :
        Δ ⊢ₘ[godel_quotation_theory]
          gtci_filter_spec :=
      FirstOrder.Derives.assumption (by simp [Δ, Γ])
    have hAt :=
      gtci_generation_separation_member_iff
        (x#610) code
        (set_variable_admissible 610) hCode hFresh
        (by simpa [gtci_filter_spec] using hSpec)
    exact FirstOrder.Derives.iffElimLeft hAt <|
      FirstOrder.Derives.conjIntro
        hTermMember hGenerated
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 214)
      (body := member ⟶ₘ (code ∈ₘ x#610))
      (gtci_theory_fresh 214)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        native_decide)
      hPointwise
  simpa [Γ, member, code,
    term_application_from_condition,
    Formula.closeFreeAt, Term.closeFreeAt,
    set_variable, set_bound_variable] using
    hGeneralized

/-- 一步生成筛选集满足完整的三分量项构造闭包。 -/
private theorem gtci_filter_closed :
    [gtci_filter_spec] ⊢ₘ[godel_quotation_theory]
      term_code_closed_condition (x#610) := by
  unfold term_code_closed_condition
  exact FirstOrder.Derives.conjIntro
    gtci_filter_variable_subset <|
      FirstOrder.Derives.conjIntro
        gtci_filter_constant_subset
        gtci_filter_application_closed

/-- 固定筛选见证代入项闭包条件时穿过应用闭包 binder。 -/
private theorem gtci_filter_closed_condition_substitute :
    Formula.substituteFree SetSort.set 215 (x#610)
        (term_code_closed_condition (x#215)) =
      term_code_closed_condition (x#610) := by
  have hOuterCommute (body : SetFormula) :
      Formula.substituteFree SetSort.set 215 (x#610)
          (Formula.closeFreeAt SetSort.set 214 0 body) =
        Formula.closeFreeAt SetSort.set 214 0
          (Formula.substituteFree SetSort.set 215
            (x#610) body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set 215 214 0 (x#610) body
      (by decide)
      (set_variable_admissible 610).2
      (by native_decide)).symm
  have hInnerCommute (id : FreeVarId) (body : SetFormula)
      (hId : id ∈ [210, 211, 212, 213]) :
      Formula.substituteFree SetSort.set 215 (x#610)
          (Formula.closeFreeAt SetSort.set id 0 body) =
        Formula.closeFreeAt SetSort.set id 0
          (Formula.substituteFree SetSort.set 215
            (x#610) body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set 215 id 0 (x#610) body
      (by
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hId
        rcases hId with rfl | rfl | rfl | rfl <;>
          decide)
      (set_variable_admissible 610).2
      (by
        have hNe : id ≠ 610 := by
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at hId
          rcases hId with rfl | rfl | rfl | rfl <;>
            decide
        simpa [Term.freeSupport,
          Term.freeSupportList, set_variable] using hNe)).symm
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set 215 (x#610) (numₘ(value)) =
        numₘ(value) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 215 (x#610) (numₘ(value))
      (by simp [finite_numeral_term_freeSupport])
  have hApplicationSubstitute :
      Formula.substituteFree SetSort.set 215 (x#610)
          (term_application_from_condition (x#215) (x#214)) =
        term_application_from_condition (x#610) (x#214) := by
    simp [term_application_from_condition,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hNumeralFixed,
      hInnerCommute 210, hInnerCommute 211,
      hInnerCommute 212, hInnerCommute 213]
  simp [term_code_closed_condition,
    Formula.substituteFree, Term.substituteFree,
    set_variable, hOuterCommute,
    hApplicationSubstitute]

/-- 项码最小性把全部项码压入一步生成筛选集。 -/
private theorem gtci_term_codes_subset_filter :
    [gtci_filter_spec] ⊢ₘ[godel_quotation_theory]
      TermCodeₘ ⊆ₘ x#610 := by
  have hMinimal :
      [gtci_filter_spec] ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, 215],
          term_code_closed_condition (x#215) ⟶ₘ
            TermCodeₘ ⊆ₘ x#215 :=
    FirstOrder.Derives.context_weaken_cons
      (assumption := gtci_filter_spec)
      gq_term_code_minimal
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := x#610) hMinimal
  have hAt' :
      [gtci_filter_spec] ⊢ₘ[godel_quotation_theory]
        term_code_closed_condition (x#610) ⟶ₘ
          TermCodeₘ ⊆ₘ x#610 := by
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.substituteFree, Term.substituteFree,
      set_variable, set_bound_variable,
      gtci_filter_closed_condition_substitute] using hAt
  exact FirstOrder.Derives.impElim
    hAt' gtci_filter_closed

/-- 把匿名分离存在式改写为最小性证明使用的固定 eigen 规格。 -/
private theorem gtci_filter_exists :
    ⊢ₘ[godel_quotation_theory]
      ∃ₘ[SetSort.set, 610], gtci_filter_spec := by
  have hPredicateClose :
      Formula.closeFreeAt SetSort.set 610 1
          term_code_generation_predicate.body =
        term_code_generation_predicate.body := by
    apply
      Formula.closeFreeAt_eq_self_of_scoped_of_le_of_not_mem
        (scope := Scope.push Scope.empty SetSort.set)
    · exact
        term_code_generation_predicate.admissible_at.2
    · exact Nat.le_refl _
    · native_decide
  simpa [gtci_filter_spec,
    SetPredicate.separation_exists,
    SetPredicate.separation_spec,
    Formula.next_depth,
    Formula.closeFreeAt, Term.closeFreeAt,
    set_variable, set_bound_variable,
    hPredicateClose] using
    gq_term_code_generation_separation_exists

/-- 一步生成条件不会引入候选项和代码项之外的 eigen `610`。 -/
private theorem gtci_generation_condition_fresh_610
    (candidate code : SetTerm)
    (hCandidate :
      (SetSort.set, 610) ∉ Term.freeSupport candidate)
    (hCode :
      (SetSort.set, 610) ∉ Term.freeSupport code) :
    (SetSort.set, 610) ∉
      Formula.freeSupport
        (term_code_generation_condition candidate code) := by
  let valueBody : SetFormula :=
    (x#213 ∈ₘ domₘ(x#212)) ⟶ₘ
      ((x#212 ·ₘ x#213) ∈ₘ candidate)
  let header : SetFormula :=
    (x#210 ∈ₘ ωₘ) ∧ₘ
      ((x#211 ∈ₘ ωₘ) ∧ₘ
        ((x#212 ∈ₘ seq₊_spaceₘ(CodeStrₘ)) ∧ₘ
          (domₘ(x#212) ≐ₘ Sₘ(x#210))))
  let equation : SetFormula :=
    code ≐ₘ
      term_application_code_term
        (x#210) (x#211) (x#212)
  let body : SetFormula :=
    header ∧ₘ
      ((∀ₘ[SetSort.set, 213], valueBody) ∧ₘ
        equation)
  let at212 : SetFormula :=
    ∃ₘ[SetSort.set, 212], body
  let at211 : SetFormula :=
    ∃ₘ[SetSort.set, 211], at212
  let at210 : SetFormula :=
    ∃ₘ[SetSort.set, 210], at211
  have hValueBody :
      (SetSort.set, 610) ∉
        Formula.freeSupport valueBody := by
    simp only [valueBody, Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList]
    intro hMember
    rcases List.mem_cons.mp hMember with
      h213 | hMember
    · exact (by decide : (610 : Nat) ≠ 213) <|
        congrArg Prod.snd h213
    rcases List.mem_cons.mp hMember with
      h212 | hMember
    · exact (by decide : (610 : Nat) ≠ 212) <|
        congrArg Prod.snd h212
    rcases List.mem_cons.mp hMember with
      h212' | hMember
    · exact (by decide : (610 : Nat) ≠ 212) <|
        congrArg Prod.snd h212'
    rcases List.mem_cons.mp hMember with
      h213' | hCandidateMember
    · exact (by decide : (610 : Nat) ≠ 213) <|
        congrArg Prod.snd h213'
    · exact hCandidate <| by
        simpa using hCandidateMember
  have hValueClosed :
      (SetSort.set, 610) ∉
        Formula.freeSupport
          (Formula.closeFreeAt SetSort.set 213 0
            valueBody) :=
    Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      (SetSort.set, 610) SetSort.set 213 0
      valueBody hValueBody
  have hValueForall :
      (SetSort.set, 610) ∉
        Formula.freeSupport
          (∀ₘ[SetSort.set, 213], valueBody) := by
    simpa [Formula.freeSupport] using hValueClosed
  have hHeader :
      (SetSort.set, 610) ∉
        Formula.freeSupport header := by
    native_decide
  have hEquation :
      (SetSort.set, 610) ∉
        Formula.freeSupport equation := by
    simp only [equation, Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList]
    intro hMember
    rcases List.mem_append.mp hMember with
      hCodeMember | hFixedMember
    · exact hCode hCodeMember
    · simp [finite_numeral_term_freeSupport] at hFixedMember
      have hNotFixed :
          (SetSort.set, 610) ∉
            [(SetSort.set, 210),
              (SetSort.set, 211),
              (SetSort.set, 212)] := by
        native_decide
      exact hNotFixed hFixedMember
  have hBody :
      (SetSort.set, 610) ∉
        Formula.freeSupport body := by
    simp only [body, Formula.freeSupport]
    intro hMember
    rcases List.mem_append.mp hMember with
      hHeaderMember | hTailMember
    · exact hHeader hHeaderMember
    · rcases List.mem_append.mp hTailMember with
        hValueMember | hEquationMember
      · exact hValueForall hValueMember
      · exact hEquation hEquationMember
  have hClose212 :
      (SetSort.set, 610) ∉
        Formula.freeSupport
          (Formula.closeFreeAt SetSort.set 212 0 body) :=
    Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      (SetSort.set, 610) SetSort.set 212 0
      body hBody
  have hAt212 :
      (SetSort.set, 610) ∉
        Formula.freeSupport at212 := by
    simpa [at212, Formula.freeSupport] using hClose212
  have hClose211 :
      (SetSort.set, 610) ∉
        Formula.freeSupport
          (Formula.closeFreeAt SetSort.set 211 0 at212) :=
    Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      (SetSort.set, 610) SetSort.set 211 0
      at212 hAt212
  have hAt211 :
      (SetSort.set, 610) ∉
        Formula.freeSupport at211 := by
    simpa [at211, Formula.freeSupport] using hClose211
  have hClose210 :
      (SetSort.set, 610) ∉
        Formula.freeSupport
          (Formula.closeFreeAt SetSort.set 210 0 at211) :=
    Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      (SetSort.set, 610) SetSort.set 210 0
      at211 hAt211
  have hApplication :
      (SetSort.set, 610) ∉
        Formula.freeSupport
          (term_application_from_condition candidate code) := by
    simpa [term_application_from_condition,
      at210, at211, at212, body, header,
      equation, valueBody, Formula.freeSupport] using
      hClose210
  simp only [term_code_generation_condition,
    Formula.freeSupport, Term.freeSupport,
    Term.freeSupportList]
  intro hMember
  rcases List.mem_append.mp hMember with
    hVariableMember | hTailMember
  · exact hCode <| by simpa using hVariableMember
  · rcases List.mem_append.mp hTailMember with
      hConstantMember | hApplicationMember
    · exact hCode <| by simpa using hConstantMember
    · exact hApplication hApplicationMember

/--
每个完整项码都由变量符号、常元符号或一次正元函数应用生成。

前提中的五个编号恰为项应用定义的四个 binder 与最小性分离的 eigen；不要求代码
项闭合。
-/
theorem gq_term_code_member_implies_generation_of_fresh
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [210, 211, 212, 213, 610] [code]) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ TermCodeₘ) ⟶ₘ
        term_code_generation_condition TermCodeₘ code := by
  let conclusion : SetFormula :=
    (code ∈ₘ TermCodeₘ) ⟶ₘ
      term_code_generation_condition TermCodeₘ code
  have hCodeFresh :
      ReservedIdsFresh [210, 211, 212, 213] [code] :=
    by
      intro term hTerm id hId
      apply hFresh term hTerm id
      simp only [List.mem_cons, List.not_mem_nil,
        or_false] at hId ⊢
      rcases hId with rfl | rfl | rfl | rfl <;>
        simp
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := [])
    (sort := SetSort.set)
    (eigen := 610)
    (body := gtci_filter_spec)
    (conclusion := conclusion)
  · exact gtci_theory_fresh 610
  · intro formula hFormula
    cases hFormula
  · have hCodeFresh610 :
        (SetSort.set, 610) ∉
          Term.freeSupport code := by
      exact hFresh code (by simp) 610 (by simp)
    have hTermCodeFresh610 :
        (SetSort.set, 610) ∉
          Term.freeSupport TermCodeₘ := by
      change (SetSort.set, 610) ∉ []
      exact List.not_mem_nil
    have hMemberFresh :
        (SetSort.set, 610) ∉
          Formula.freeSupport
            (code ∈ₘ TermCodeₘ) := by
      simp [Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList,
        hCodeFresh610]
    have hGenerationFresh :=
      gtci_generation_condition_fresh_610
        TermCodeₘ code
        hTermCodeFresh610 hCodeFresh610
    simpa [conclusion, Formula.freeSupport] using
      And.intro hMemberFresh hGenerationFresh
  · exact gtci_filter_exists
  · let Γ : Context signature := [gtci_filter_spec]
    have hMemberAdmissible :
        Formula.Admissible
          (code ∈ₘ TermCodeₘ) :=
      membership_formula_admissible
        hCode term_code_set_term_admissible
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature :=
      (code ∈ₘ TermCodeₘ) :: Γ
    have hMember :
        Δ ⊢ₘ[godel_quotation_theory]
          code ∈ₘ TermCodeₘ :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hSubset :
        Δ ⊢ₘ[godel_quotation_theory]
          TermCodeₘ ⊆ₘ x#610 :=
      FirstOrder.Derives.context_weaken
        (Γ := [gtci_filter_spec])
        (Δ := Δ) (by simp [Δ, Γ])
        gtci_term_codes_subset_filter
    have hFilterMember :
        Δ ⊢ₘ[godel_quotation_theory]
          code ∈ₘ x#610 :=
      gq_subset_member
        TermCodeₘ (x#610) code
        term_code_set_term_admissible
        (set_variable_admissible 610)
        hCode hSubset hMember
    have hSpec :
        Δ ⊢ₘ[godel_quotation_theory]
          gtci_filter_spec :=
      FirstOrder.Derives.assumption
        (by simp [Δ, Γ])
    have hAt :=
      gtci_generation_separation_member_iff
        (x#610) code
        (set_variable_admissible 610)
        hCode hCodeFresh
        (by simpa [gtci_filter_spec] using hSpec)
    exact FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.iffElimRight
        hAt hFilterMember

/--
闭项上的生成反演是精确新鲜度接口的直接推论。
-/
theorem gq_term_code_member_implies_generation
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hClosed : Term.freeSupport code = []) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ TermCodeₘ) ⟶ₘ
        term_code_generation_condition TermCodeₘ code :=
  gq_term_code_member_implies_generation_of_fresh
    code hCode <|
      reserved_ids_fresh_cons_closed hClosed <|
        reserved_ids_fresh_nil
          [210, 211, 212, 213, 610]

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
