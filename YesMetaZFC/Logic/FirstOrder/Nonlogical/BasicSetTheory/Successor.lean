import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Union
/-!
# 后继
后继的核心成员条件采用现代析取写法 `z = x ∨ z ∈ x`。文献中的
`¬(z = x) → z ∈ x` 作为对象经典逻辑下的等价接口保留。
后继存在性不作为新公理加入：规范见证直接取 `x ∪ {x, x}`，并由配对与并集规格
推出。函数符号 `Sₘ` 只作为该规范构造的定义扩张。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-- `element` 等于 `source` 或属于 `source`。 -/
def successor_member_condition (element source : SetTerm) :
    SetFormula := (element ≐ₘ source) ∨ₘ (element ∈ₘ source)
/-- 文献采用的后继成员条件。 -/
def successor_paper_condition (element source : SetTerm) :
    SetFormula := (¬ₘ (element ≐ₘ source)) ⟶ₘ (element ∈ₘ source)
/-- `candidate` 正好是 `source` 的后继。 -/
def successor_spec (source candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ candidate) ↔ₘ
      successor_member_condition bₛ#0 source
/-- 文献蕴含写法下的后继规格。 -/
def successor_paper_spec (source candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ candidate) ↔ₘ
      successor_paper_condition bₛ#0 source
/-- 对固定集合断言其后继存在。 -/
def successor_exists (source : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
        successor_member_condition bₛ#0 source
/-- 文献蕴含写法下的后继存在公式。 -/
def successor_paper_exists (source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
        successor_paper_condition bₛ#0 source
/-- 由配对与二元并给出的规范后继见证。 -/
abbrev successor_witness_term (source : SetTerm) :
    SetTerm :=
  source ∪ₘ {source, source}ₘ
/-- 后继存在性所需的既有配对与并集描述符理论。 -/
def successor_base_theory : SetTheory :=
  binary_union_operator_theory
/-- 后继函数符号的开放定义实例。 -/
def successor_definition_instance (source : SetTerm) :
    SetFormula :=
  Sₘ(source) ≐ₘ successor_witness_term source
/-- 后继函数符号的定义公理。 -/
def successor_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    successor_definition_instance (x#0)
/-- 在后继存在的既有理论上加入后继函数符号。 -/
def successor_operator_theory : SetTheory :=
  Theory.insert
    successor_definition_axiom
    successor_base_theory
/-- 后继项保持 proof-carrying 项边界。 -/
theorem successor_term_admissible (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    Term.Admissible (successor_term source) SetSort.set := by
  simpa using
    set_function_application_admissible
      .successor [⟨source, by assumption⟩]
      (by rfl) (by rfl)
/-- 后继项的合法性由源项证书直接计算。 -/
@[term_check]
theorem successor_term_check {source : SetTerm}
    (hSource : Term.CheckCertificate source SetSort.set) :
    Term.CheckCertificate (successor_term source) SetSort.set :=
  Term.check_admissible_complete <|
    successor_term_admissible source hSource.admissible
/-- 规范后继见证保持 proof-carrying 项边界。 -/
theorem successor_witness_term_admissible (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    Term.Admissible (successor_witness_term source) SetSort.set :=
  binary_union_term_admissible
    source {source, source}ₘ
    hSource (unordered_pair_term_admissible
      source source hSource hSource)
/-- 规范后继见证的合法性由源项证书直接计算。 -/
@[term_check]
theorem successor_witness_term_check {source : SetTerm}
    (hSource : Term.CheckCertificate source SetSort.set) :
    Term.CheckCertificate (successor_witness_term source) SetSort.set :=
  Term.check_admissible_complete <|
    successor_witness_term_admissible source hSource.admissible
/-- 后继成员条件在 admissible 元素项与源项处仍然 admissible。 -/
theorem successor_member_condition_admissible
    {element source : SetTerm} (hElement : Term.Admissible element SetSort.set) (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (successor_member_condition element source) :=
  Formula.Admissible.disj (Formula.Admissible.equal hElement hSource) (membership_formula_admissible hElement hSource)
/-- 文献后继成员条件在 admissible 元素项与源项处仍然 admissible。 -/
theorem successor_paper_condition_admissible
    {element source : SetTerm} (hElement : Term.Admissible element SetSort.set) (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (successor_paper_condition element source) :=
  Formula.Admissible.imp (Formula.Admissible.neg (Formula.Admissible.equal hElement hSource)) (membership_formula_admissible hElement hSource)
/-- 后继规格在 admissible 源项与候选项处仍然 admissible。 -/
theorem successor_spec_admissible
    {source candidate : SetTerm} (hSource : Term.Admissible source SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (successor_spec source candidate) := by
  prove_admissible
/-- 文献后继规格在 admissible 源项与候选项处仍然 admissible。 -/
theorem successor_paper_spec_admissible
    {source candidate : SetTerm} (hSource : Term.Admissible source SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (successor_paper_spec source candidate) := by
  unfold successor_paper_spec successor_paper_condition
  prove_admissible
/-- 后继存在式在 admissible 源项处仍然 admissible。 -/
theorem successor_exists_admissible
    {source : SetTerm} (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (successor_exists source) := by
  unfold successor_exists successor_member_condition
  prove_admissible
/-- 文献后继存在式在 admissible 源项处仍然 admissible。 -/
theorem successor_paper_exists_admissible
    {source : SetTerm} (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (successor_paper_exists source) := by
  unfold successor_paper_exists successor_paper_condition
  prove_admissible
/-- 后继函数符号的开放定义实例在 admissible 源项处仍然 admissible。 -/
theorem successor_definition_instance_admissible
    {source : SetTerm} (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (successor_definition_instance source) :=
  Formula.Admissible.equal (successor_term_admissible source hSource) (successor_witness_term_admissible source hSource)
/-- 后继函数符号定义公理满足公共良构性边界。 -/
theorem successor_definition_axiom_admissible :
    Formula.Admissible successor_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 后继存在的既有理论仍然 admissible。 -/
theorem successor_base_theory_admissible :
    Theory.Admissible successor_base_theory :=
  binary_union_operator_theory_admissible
/-- 后继描述符理论仍然 admissible。 -/
theorem successor_operator_theory_admissible :
    Theory.Admissible successor_operator_theory :=
  Theory.admissible_insert
    successor_definition_axiom_admissible
    successor_base_theory_admissible
/-- 后继描述符理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem successor_operator_theory_sentence
    {formula : SetFormula} (hFormula : successor_operator_theory formula) :
    Formula.Sentence formula := by
  constructor
  · exact successor_operator_theory_admissible
      formula hFormula
  · rcases hFormula with rfl | hFormula
    · native_decide
    · exact (binary_union_operator_theory_sentence
          hFormula).2
/-- 后继存在的既有理论中的每条公理都是闭公式。 -/
@[derive_close_sentence]
theorem successor_base_theory_sentence
    {formula : SetFormula} (hFormula : successor_base_theory formula) :
    Formula.Sentence formula :=
  binary_union_operator_theory_sentence hFormula
/-- 二元并描述符理论嵌入后继描述符理论。 -/
theorem binary_union_operator_theory_subset_successor_operator_theory
    {formula : SetFormula} (hFormula : binary_union_operator_theory formula) :
    successor_operator_theory formula :=
  Or.inr hFormula
/-- 外延理论嵌入后继描述符理论。 -/
theorem extensionality_theory_subset_successor_operator_theory
    {formula : SetFormula} (hFormula : extensionality_theory formula) :
    successor_operator_theory formula :=
  binary_union_operator_theory_subset_successor_operator_theory <|
    pairing_operator_theory_subset_binary_union_operator_theory <|
      Or.inr (Or.inr hFormula)
/-- 文献后继成员条件与现代析取条件在对象经典逻辑中等价。 -/
theorem successor_paper_condition_iff_member_condition (element source : SetTerm) (hElement : Term.Admissible element SetSort.set)
    (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ
      successor_paper_condition element source ↔ₘ
        successor_member_condition element source := by
  simpa [successor_paper_condition,
    successor_member_condition] using (Metatheory.Derives.neg_imp_disj_iff_m (σ := signature) (T := (Theory.empty : SetTheory)) (Γ := []) (φ := element ≐ₘ source)
      (ψ := element ∈ₘ source) (Formula.Admissible.equal hElement hSource) (membership_formula_admissible hElement hSource))
/-- 文献后继规格与现代后继规格在对象经典逻辑中等价。 -/
theorem successor_paper_spec_iff_spec (source candidate : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ
      successor_paper_spec source candidate ↔ₘ
        successor_spec source candidate := by
  let paper_body : SetFormula := (bₛ#0 ∈ₘ candidate) ↔ₘ
      successor_paper_condition bₛ#0 source
  let modern_body : SetFormula := (bₛ#0 ∈ₘ candidate) ↔ₘ
      successor_member_condition bₛ#0 source
  let element :=
    FreshVariable.fresh_id SetSort.set
      [paper_body, modern_body]
  let paper_point :=
    Formula.openAt SetSort.set 0 (x#element) paper_body
  let modern_point :=
    Formula.openAt SetSort.set 0 (x#element) modern_body
  have hElementFreshPaper : (SetSort.set, element) freshForₘ
        paper_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshModern : (SetSort.set, element) freshForₘ
        modern_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hSourceOpen :
      Term.openAt SetSort.set 0 (x#element) source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element)
      source hSource.2
  have hCandidateOpen :
      Term.openAt SetSort.set 0 (x#element) candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element)
      candidate hCandidate.2
  have hOpenedElement :
      Term.Admissible (Term.openAt SetSort.set 0 (x#element) bₛ#0)
        SetSort.set := by
    simpa [Term.openAt] using
      set_variable_admissible element
  have hOpenedSource :
      Term.Admissible (Term.openAt SetSort.set 0 (x#element) source)
        SetSort.set := by
    simpa [hSourceOpen] using hSource
  have hOpenedCandidate :
      Term.Admissible (Term.openAt SetSort.set 0 (x#element) candidate)
        SetSort.set := by
    simpa [hCandidateOpen] using hCandidate
  have hPointIff :
      ⊢ₘ paper_point ↔ₘ modern_point := by
    have hCondition :=
      successor_paper_condition_iff_member_condition (Term.openAt SetSort.set 0 (x#element) bₛ#0) (Term.openAt SetSort.set 0 (x#element) source)
        hOpenedElement hOpenedSource
    have hCongruence :=
      Metatheory.Derives.iff_right_congr_m (σ := signature) (T := (Theory.empty : SetTheory)) (Γ := []) (φ :=
          Term.openAt SetSort.set 0 (x#element) bₛ#0 ∈ₘ
            Term.openAt SetSort.set 0 (x#element) candidate) (membership_formula_admissible
          hOpenedElement hOpenedCandidate)
        hCondition
    simpa [paper_point, modern_point,
      paper_body, modern_body,
      successor_paper_condition,
      successor_member_condition,
      Formula.openAt, Term.openAt] using hCongruence
  have hClosed :
      ⊢ₘ (∀ₘ[SetSort.set, element], paper_point) ↔ₘ (∀ₘ[SetSort.set, element], modern_point) :=
    Metatheory.Derives.forall_iff_mono (T := (Theory.empty : SetTheory)) (Γ := []) (sort := SetSort.set) (eigen := element) (left := paper_point)
      (right := modern_point) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        cases hFormula)
      hPointIff
  simpa [successor_paper_spec,
    successor_spec, paper_point, modern_point,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 paper_body
      hElementFreshPaper,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 modern_body
      hElementFreshModern] using hClosed
/--
二元并规格与右侧单点集规格组合成后继规格。
量词实例化、命题重排与全称推广都显式走可信核，避免在这条基础桥上形成搜索自举。
-/
theorem binary_union_singleton_spec_implies_successor_spec (source singleton candidate : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hSingleton : Term.Admissible singleton SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ
      binary_union_spec source singleton candidate ⟶ₘ
        singleton_spec source singleton ⟶ₘ
          successor_spec source candidate := by
  let binary_formula :=
    binary_union_spec source singleton candidate
  let singleton_formula :=
    singleton_spec source singleton
  let result_body : SetFormula := (bₛ#0 ∈ₘ candidate) ↔ₘ
      successor_member_condition bₛ#0 source
  let element :=
    FreshVariable.fresh_id SetSort.set
      [binary_formula, singleton_formula, result_body]
  let point : SetFormula := (x#element ∈ₘ candidate) ↔ₘ
      successor_member_condition (x#element) source
  have hElementFreshBinary : (SetSort.set, element) freshForₘ
        binary_formula := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshSingleton : (SetSort.set, element) freshForₘ
        singleton_formula := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshResult : (SetSort.set, element) freshForₘ
        result_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hSourceOpen :
      Term.openAt SetSort.set 0 (x#element) source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element)
      source hSource.2
  have hSingletonOpen :
      Term.openAt SetSort.set 0 (x#element) singleton =
        singleton :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element)
      singleton hSingleton.2
  have hCandidateOpen :
      Term.openAt SetSort.set 0 (x#element) candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element)
      candidate hCandidate.2
  have hBinaryFormulaAdmissible :
      Formula.Admissible binary_formula := by
    dsimp [binary_formula]
    exact binary_union_spec_admissible
      hSource hSingleton hCandidate
  have hSingletonFormulaAdmissible :
      Formula.Admissible singleton_formula := by
    dsimp [singleton_formula]
    exact singleton_spec_admissible
      hSource hSingleton
  have hElementAdmissible :
      Term.Admissible (x#element) SetSort.set :=
    set_variable_admissible element
  have hElementMemCandidateAdmissible :
      Formula.Admissible (x#element ∈ₘ candidate) :=
    membership_formula_admissible
      hElementAdmissible hCandidate
  have hElementMemSourceAdmissible :
      Formula.Admissible (x#element ∈ₘ source) :=
    membership_formula_admissible
      hElementAdmissible hSource
  have hElementMemSingletonAdmissible :
      Formula.Admissible (x#element ∈ₘ singleton) :=
    membership_formula_admissible
      hElementAdmissible hSingleton
  have hElementEqSourceAdmissible :
      Formula.Admissible (x#element ≐ₘ source) :=
    Formula.Admissible.equal
      hElementAdmissible hSource
  have hSuccessorConditionAdmissible :
      Formula.Admissible (successor_member_condition (x#element) source) :=
    successor_member_condition_admissible
      hElementAdmissible hSource
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hBinaryFormula :
      [singleton_formula, binary_formula] ⊢ₘ
        binary_formula :=
    .assumption (by simp)
  have hSingletonFormula :
      [singleton_formula, binary_formula] ⊢ₘ
        singleton_formula :=
    .assumption (by simp)
  have hBinaryAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#element) hBinaryFormula
  have hSingletonAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#element) hSingletonFormula
  have hBinaryAt :
      [singleton_formula, binary_formula] ⊢ₘ (x#element ∈ₘ candidate) ↔ₘ ((x#element ∈ₘ source) ∨ₘ (x#element ∈ₘ singleton)) := by
    simpa [binary_formula, binary_union_spec,
      Formula.openAt, Term.openAt,
      hSourceOpen, hSingletonOpen,
      hCandidateOpen] using hBinaryAtRaw
  have hSingletonAt :
      [singleton_formula, binary_formula] ⊢ₘ (x#element ∈ₘ singleton) ↔ₘ (x#element ≐ₘ source) := by
    simpa [singleton_formula, singleton_spec,
      Formula.openAt, Term.openAt,
      hSourceOpen, hSingletonOpen] using hSingletonAtRaw
  have hPoint :
      [singleton_formula, binary_formula] ⊢ₘ
        point := by
    apply FirstOrder.Derives.iffIntro
    · have hBinaryAt' :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ candidate)
          hBinaryAt
      have hSingletonAt' :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ candidate)
          hSingletonAt
      have hChoice :=
        FirstOrder.Derives.iffElimRight
          hBinaryAt' (.assumption (by simp)
            )
      apply FirstOrder.Derives.disjElim hChoice
      · exact FirstOrder.Derives.disjIntroRight
          (.assumption (by simp))
      · have hSingletonAt'' :=
          FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ singleton)
            hSingletonAt'
        exact FirstOrder.Derives.disjIntroLeft
          (FirstOrder.Derives.iffElimRight
            hSingletonAt'' (.assumption (by simp)
              ))
    · have hBinaryAt' :=
        FirstOrder.Derives.context_weaken_cons (assumption :=
            successor_member_condition (x#element) source)
          hBinaryAt
      have hSingletonAt' :=
        FirstOrder.Derives.context_weaken_cons (assumption :=
            successor_member_condition (x#element) source)
          hSingletonAt
      have hChoice :
          successor_member_condition (x#element) source ::
              [singleton_formula, binary_formula] ⊢ₘ (x#element ≐ₘ source) ∨ₘ (x#element ∈ₘ source) :=
        .assumption (by
          simp [successor_member_condition])
      apply FirstOrder.Derives.disjElim hChoice
      · have hSingletonAt'' :=
          FirstOrder.Derives.context_weaken_cons (assumption := x#element ≐ₘ source)
            hSingletonAt'
        have hSingletonMembership :=
          FirstOrder.Derives.iffElimLeft
            hSingletonAt'' (.assumption (by simp)
              )
        have hBinaryAt'' :=
          FirstOrder.Derives.context_weaken_cons (assumption := x#element ≐ₘ source)
            hBinaryAt'
        exact FirstOrder.Derives.iffElimLeft
          hBinaryAt'' (FirstOrder.Derives.disjIntroRight
            hSingletonMembership)
      · have hBinaryAt'' :=
          FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ source)
            hBinaryAt'
        exact FirstOrder.Derives.iffElimLeft
          hBinaryAt'' (FirstOrder.Derives.disjIntroLeft
            (.assumption (by simp)))
  have hPointOpened :
      [singleton_formula, binary_formula] ⊢ₘ
        Formula.openAt SetSort.set 0 (x#element) result_body := by
    simpa [point, result_body,
      successor_member_condition,
      Formula.openAt, Term.openAt,
      hSourceOpen, hCandidateOpen] using hPoint
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [singleton_formula, binary_formula]) (sort := SetSort.set) (eigen := element)
      (body :=
        Formula.openAt SetSort.set 0 (x#element) result_body) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · exact hElementFreshSingleton
        · rcases List.mem_cons.mp hFormula with rfl | hFormula
          · exact hElementFreshBinary
          · exact False.elim (List.not_mem_nil hFormula))
      hPointOpened
  simpa [binary_formula, singleton_formula,
    successor_spec, result_body,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 result_body
      hElementFreshResult] using hGeneralized
/-- 规范见证 `source ∪ {source, source}` 满足后继规格。 -/
theorem successor_witness_spec_derives (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[successor_base_theory]
      successor_spec source (successor_witness_term source) := by
  let singleton := unordered_pair_term source source
  let witness := binary_union_term source singleton
  have hSingleton :
      Term.Admissible singleton SetSort.set :=
    unordered_pair_term_admissible
      source source hSource hSource
  have hWitness :
      Term.Admissible witness SetSort.set :=
    binary_union_term_admissible
      source singleton hSource hSingleton
  have hBinarySpec :
      ⊢ₘ[successor_base_theory]
        binary_union_spec source singleton witness := by
    simpa [successor_base_theory,
      singleton, witness] using
      binary_union_term_spec_derives
        source singleton hSource hSingleton
  have hPairSpec :
      ⊢ₘ[successor_base_theory]
        pair_spec source source singleton :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        pairing_operator_theory_subset_binary_union_operator_theory
          hFormula) (by
        simpa [successor_base_theory,
          singleton] using
          unordered_pair_term_spec_derives
            source source hSource hSource)
  have hSingletonBridge :
      ⊢ₘ[successor_base_theory]
        pair_spec source source singleton ↔ₘ
          singleton_spec source singleton :=
    FirstOrder.Derives.of_empty (pair_repeated_spec_iff_singleton_spec
        source singleton hSource hSingleton)
  have hSingletonSpec :
      ⊢ₘ[successor_base_theory]
        singleton_spec source singleton :=
    FirstOrder.Derives.iffElimRight
      hSingletonBridge hPairSpec
  have hBridge :
      ⊢ₘ[successor_base_theory]
        binary_union_spec source singleton witness ⟶ₘ
          singleton_spec source singleton ⟶ₘ
            successor_spec source witness :=
    FirstOrder.Derives.of_empty (binary_union_singleton_spec_implies_successor_spec
        source singleton witness
        hSource hSingleton hWitness)
  simpa [singleton, witness] using
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
        hBridge hBinarySpec)
      hSingletonSpec
/-- 配对与并集描述符理论推出每个集合都有后继。 -/
theorem successor_exists_derives (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[successor_base_theory]
      successor_exists source := by
  let witness := successor_witness_term source
  have hWitness :
      Term.Admissible witness SetSort.set :=
    successor_witness_term_admissible
      source hSource
  have hWitnessSpec :
      ⊢ₘ[successor_base_theory]
        successor_spec source witness := by
    simpa [witness] using
      successor_witness_spec_derives
        source hSource
  have hSourceOpenOne :
      Term.openAt SetSort.set 1 witness source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 witness source hSource.2
  nd_apply FirstOrder.Derives.exists_intro (term := witness)
  simpa [successor_exists, successor_spec,
    successor_member_condition,
    Formula.openAt, Formula.next_depth,
    Term.openAt, hSourceOpenOne] using hWitnessSpec
/-- 同一集合的两个后继候选必相等。 -/
theorem successor_unique (source left right : SetTerm) (hSource : Term.Admissible source SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory]
      successor_spec source left ⟶ₘ
        successor_spec source right ⟶ₘ (left ≐ₘ right) := by
  simpa [successor_spec,
    successor_member_condition,
    membership_specification] using
    membership_specification_unique
      left right ((bₛ#0 ≐ₘ source) ∨ₘ (bₛ#0 ∈ₘ source))
      hLeft hRight (successor_spec_admissible
        hSource hLeft) (successor_spec_admissible
        hSource hRight)
/-- 文献后继存在公式与现代后继存在公式等价。 -/
theorem successor_paper_exists_iff_exists (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ
      successor_paper_exists source ↔ₘ
        successor_exists source := by
  let paper_body : SetFormula :=
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
        successor_paper_condition bₛ#0 source
  let modern_body : SetFormula :=
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
        successor_member_condition bₛ#0 source
  let candidate :=
    FreshVariable.fresh_id SetSort.set
      [paper_body, modern_body]
  let paper_point :=
    Formula.openAt SetSort.set 0 (x#candidate) paper_body
  let modern_point :=
    Formula.openAt SetSort.set 0 (x#candidate) modern_body
  have hCandidateFreshPaper : (SetSort.set, candidate) freshForₘ
        paper_body := by
    dsimp [candidate]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hCandidateFreshModern : (SetSort.set, candidate) freshForₘ
        modern_body := by
    dsimp [candidate]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hSourceOpenOne :
      Term.openAt SetSort.set 1 (x#candidate) source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 (x#candidate)
      source hSource.2
  have hPointIff :
      ⊢ₘ paper_point ↔ₘ modern_point := by
    simpa [paper_point, modern_point,
      paper_body, modern_body,
      successor_paper_spec, successor_spec,
      successor_paper_condition,
      successor_member_condition,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hSourceOpenOne,
      set_variable, set_bound_variable] using
      successor_paper_spec_iff_spec
        source (x#candidate)
        hSource (set_variable_admissible candidate)
  have hClosed :
      ⊢ₘ (∃ₘ[SetSort.set, candidate], paper_point) ↔ₘ (∃ₘ[SetSort.set, candidate], modern_point) :=
    Metatheory.Derives.exists_iff_mono (T := (Theory.empty : SetTheory)) (Γ := []) (sort := SetSort.set) (eigen := candidate) (left := paper_point)
      (right := modern_point) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        cases hFormula)
      hPointIff
  simpa [successor_paper_exists,
    successor_exists, paper_point, modern_point,
    Formula.closeFreeAt_openAt
      SetSort.set candidate 0 paper_body
      hCandidateFreshPaper,
    Formula.closeFreeAt_openAt
      SetSort.set candidate 0 modern_body
      hCandidateFreshModern] using hClosed
/-- 文献蕴含写法下的后继存在性。 -/
theorem successor_paper_exists_derives (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[successor_base_theory]
      successor_paper_exists source := by
  have hBridge :
      ⊢ₘ[successor_base_theory]
        successor_paper_exists source ↔ₘ
          successor_exists source :=
    FirstOrder.Derives.of_empty (successor_paper_exists_iff_exists
        source hSource)
  exact FirstOrder.Derives.iffElimLeft
    hBridge (successor_exists_derives source hSource)
/-- 文献蕴含规格下的两个后继候选必相等。 -/
theorem successor_paper_unique (source left right : SetTerm) (hSource : Term.Admissible source SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory]
      successor_paper_spec source left ⟶ₘ
        successor_paper_spec source right ⟶ₘ (left ≐ₘ right) := by
  let left_paper := successor_paper_spec source left
  let right_paper := successor_paper_spec source right
  have hLeftPaperAdmissible :
      Formula.Admissible left_paper := by
    dsimp [left_paper]
    exact successor_paper_spec_admissible
      hSource hLeft
  have hRightPaperAdmissible :
      Formula.Admissible right_paper := by
    dsimp [right_paper]
    exact successor_paper_spec_admissible
      hSource hRight
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hLeftBridge :
      [right_paper, left_paper] ⊢ₘ[extensionality_theory]
        successor_paper_spec source left ↔ₘ
          successor_spec source left :=
    FirstOrder.Derives.of_empty (successor_paper_spec_iff_spec
        source left hSource hLeft)
  have hRightBridge :
      [right_paper, left_paper] ⊢ₘ[extensionality_theory]
        successor_paper_spec source right ↔ₘ
          successor_spec source right :=
    FirstOrder.Derives.of_empty (successor_paper_spec_iff_spec
        source right hSource hRight)
  have hLeftSpec :
      [right_paper, left_paper] ⊢ₘ[extensionality_theory]
        successor_spec source left :=
    FirstOrder.Derives.iffElimRight
      hLeftBridge (.assumption (by simp [left_paper])
        )
  have hRightSpec :
      [right_paper, left_paper] ⊢ₘ[extensionality_theory]
        successor_spec source right :=
    FirstOrder.Derives.iffElimRight
      hRightBridge (.assumption (by simp [right_paper])
        )
  have hUnique :
      [right_paper, left_paper] ⊢ₘ[extensionality_theory]
        successor_spec source left ⟶ₘ
          successor_spec source right ⟶ₘ (left ≐ₘ right) :=
    FirstOrder.Derives.context_weaken (by
        intro formula hFormula
        exact False.elim (List.not_mem_nil hFormula)) (successor_unique
        source left right
        hSource hLeft hRight)
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
      hUnique hLeftSpec)
    hRightSpec
/-- 后继定义公理可在任意 admissible 集合项处实例化。 -/
theorem successor_definition_instance_derives (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[successor_operator_theory]
      successor_definition_instance source := by
  have hAxiom :
      ⊢ₘ[successor_operator_theory]
        successor_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hInstance :=
    FirstOrder.Derives.forall_elim
      (term := source) hAxiom
  simpa [successor_definition_axiom,
    successor_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, successor_term,
    successor_witness_term,
    binary_union_term, unordered_pair_term] using hInstance
/-- 后继函数项按定义等于规范见证。 -/
theorem successor_term_eq_witness_derives (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[successor_operator_theory]
      Sₘ(source) ≐ₘ
        successor_witness_term source := by
  simpa [successor_definition_instance] using
    successor_definition_instance_derives
      source hSource
/-- 后继函数项满足现代后继规格。 -/
theorem successor_term_spec_derives (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[successor_operator_theory]
      successor_spec source Sₘ(source) := by
  let successor := successor_term source
  let witness := successor_witness_term source
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [Formula.equal source source]
  have hSuccessor :
      Term.Admissible successor SetSort.set :=
    successor_term_admissible source hSource
  have hWitness :
      Term.Admissible witness SetSort.set :=
    successor_witness_term_admissible
      source hSource
  have hDefinition :
      ⊢ₘ[successor_operator_theory]
        successor ≐ₘ witness := by
    simpa [successor, witness] using
      successor_term_eq_witness_derives
        source hSource
  have hWitnessSpec :
      ⊢ₘ[successor_operator_theory]
        successor_spec source witness :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula => Or.inr hFormula) (by
        simpa [successor_base_theory,
          witness] using
          successor_witness_spec_derives
            source hSource)
  have hParameterFreshSource : (SetSort.set, parameter) ∉
        Term.freeSupport source := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m
      SetSort.set source
  have hSourceFixedSuccessor :
      Term.substituteFree SetSort.set
          parameter successor source =
        source :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter successor source
      hParameterFreshSource
  have hSourceFixedWitness :
      Term.substituteFree SetSort.set
          parameter witness source =
        source :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter witness source
      hParameterFreshSource
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality (T := successor_operator_theory) (Γ := []) (sort := SetSort.set) (eigen := parameter)
      (left := successor) (right := witness) (body := successor_spec source (x#parameter))
      hDefinition
  have hCongruenceNormalized :
      ⊢ₘ[successor_operator_theory]
        successor_spec source successor ↔ₘ
          successor_spec source witness := by
    simpa [successor_spec,
      successor_member_condition,
      Formula.substituteFree,
      Term.substituteFree,
      hSourceFixedSuccessor,
      hSourceFixedWitness,
      set_variable] using hCongruence
  exact FirstOrder.Derives.iffElimLeft
    hCongruenceNormalized hWitnessSpec
/-- 后继项的成员关系等价于“等于原集合或属于原集合”。 -/
theorem successor_term_membership_iff (source element : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[successor_operator_theory] (element ∈ₘ Sₘ(source)) ↔ₘ
        successor_member_condition element source := by
  have hAt := FirstOrder.Derives.forall_elim
    (term := element) (successor_term_spec_derives source hSource)
  simpa [successor_spec, successor_member_condition,
    Formula.openAt, Term.openAt,
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element source hSource.2,
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 element (Sₘ(source)) (successor_term_admissible source hSource).2] using hAt
/-- 每个集合都属于它的后继。 -/
theorem mem_successor_self (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[successor_operator_theory]
      source ∈ₘ Sₘ(source) :=
  FirstOrder.Derives.iffElimLeft
    (successor_term_membership_iff source source hSource hSource)
    (FirstOrder.Derives.disjIntroLeft
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) source))
/-- 原集合的成员仍然属于其后继。 -/
theorem mem_successor_of_mem (source element : SetTerm) (hSource : Term.Admissible source SetSort.set) (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[successor_operator_theory] (element ∈ₘ source) ⟶ₘ (element ∈ₘ Sₘ(source)) := by
  have hContract :=
    successor_term_membership_iff
      source element hSource hElement
  have hMembershipAdmissible :
      Formula.Admissible (element ∈ₘ source) :=
    membership_formula_admissible
      hElement hSource
  nd_apply FirstOrder.Derives.impIntro
  have hContract' :=
    FirstOrder.Derives.context_weaken_cons (assumption := element ∈ₘ source)
      hContract
  apply FirstOrder.Derives.iffElimLeft
    hContract'
  exact FirstOrder.Derives.disjIntroRight
    (.assumption (by simp))
/--
一个集合项等于 `source` 的后继，当且仅当它满足现代后继规格。
-/
theorem successor_eq_iff_spec (source candidate : SetTerm) (hSource : Term.Admissible source SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[successor_operator_theory] (candidate ≐ₘ Sₘ(source)) ↔ₘ
        successor_spec source candidate := by
  let successor := successor_term source
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [Formula.equal source source]
  have hSuccessor :
      Term.Admissible successor SetSort.set :=
    successor_term_admissible source hSource
  have hParameterFreshSource : (SetSort.set, parameter) ∉
        Term.freeSupport source := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m
      SetSort.set source
  have hSourceFixedCandidate :
      Term.substituteFree SetSort.set
          parameter candidate source =
        source :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter candidate source
      hParameterFreshSource
  have hSourceFixedSuccessor :
      Term.substituteFree SetSort.set
          parameter successor source =
        source :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter successor source
      hParameterFreshSource
  have hEqualityAdmissible :
      Formula.Admissible (candidate ≐ₘ successor) :=
    Formula.Admissible.equal
      hCandidate hSuccessor
  have hCandidateSpecAdmissible :
      Formula.Admissible (successor_spec source candidate) :=
    successor_spec_admissible
      hSource hCandidate
  change
    ⊢ₘ[successor_operator_theory] (candidate ≐ₘ successor) ↔ₘ
        successor_spec source candidate
  apply FirstOrder.Derives.iffIntro
  · have hEquality :
        [candidate ≐ₘ successor]
          ⊢ₘ[successor_operator_theory]
            candidate ≐ₘ successor :=
      .assumption (by simp)
    have hCongruence :=
      Metatheory.Derives.equality_iff_of_equality (T := successor_operator_theory) (Γ := [candidate ≐ₘ successor]) (sort := SetSort.set) (eigen := parameter)
        (left := candidate) (right := successor) (body := successor_spec source (x#parameter))
        hEquality
    have hCongruenceNormalized :
        [candidate ≐ₘ successor]
          ⊢ₘ[successor_operator_theory]
            successor_spec source candidate ↔ₘ
              successor_spec source successor := by
      simpa [successor_spec,
        successor_member_condition,
        Formula.substituteFree,
        Term.substituteFree,
        hSourceFixedCandidate,
        hSourceFixedSuccessor,
        set_variable] using hCongruence
    have hSuccessorSpec :
        [candidate ≐ₘ successor]
          ⊢ₘ[successor_operator_theory]
            successor_spec source successor :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [successor] using
            successor_term_spec_derives
              source hSource)
    exact FirstOrder.Derives.iffElimLeft
      hCongruenceNormalized hSuccessorSpec
  · have hCandidateSpec :
        [successor_spec source candidate]
          ⊢ₘ[successor_operator_theory]
            successor_spec source candidate :=
      .assumption (by simp)
    have hSuccessorSpec :
        [successor_spec source candidate]
          ⊢ₘ[successor_operator_theory]
            successor_spec source successor :=
      FirstOrder.Derives.context_weaken_cons (by
          simpa [successor] using
            successor_term_spec_derives
              source hSource)
    have hUnique :
        [successor_spec source candidate]
          ⊢ₘ[successor_operator_theory]
            successor_spec source candidate ⟶ₘ
              successor_spec source successor ⟶ₘ (candidate ≐ₘ successor) :=
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            extensionality_theory_subset_successor_operator_theory
              hFormula) (successor_unique
            source candidate successor
            hSource hCandidate hSuccessor)
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
        hUnique hCandidateSpec)
      hSuccessorSpec
/--
一个集合项等于 `source` 的后继，当且仅当它满足文献蕴含规格。
-/
theorem successor_eq_iff_paper_spec (source candidate : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[successor_operator_theory] (candidate ≐ₘ Sₘ(source)) ↔ₘ
        successor_paper_spec source candidate := by
  have hModern :=
    successor_eq_iff_spec
      source candidate hSource hCandidate
  have hPaper :
      ⊢ₘ[successor_operator_theory]
        successor_paper_spec source candidate ↔ₘ
          successor_spec source candidate :=
    FirstOrder.Derives.of_empty (successor_paper_spec_iff_spec
        source candidate hSource hCandidate)
  have hEqualityAdmissible :
      Formula.Admissible (candidate ≐ₘ Sₘ(source)) :=
    Formula.Admissible.equal
      hCandidate (successor_term_admissible source hSource)
  have hPaperSpecAdmissible :
      Formula.Admissible (successor_paper_spec source candidate) :=
    successor_paper_spec_admissible
      hSource hCandidate
  apply FirstOrder.Derives.iffIntro
  · have hModern' :=
      FirstOrder.Derives.context_weaken_cons (assumption := candidate ≐ₘ Sₘ(source))
        hModern
    have hPaper' :=
      FirstOrder.Derives.context_weaken_cons (assumption := candidate ≐ₘ Sₘ(source))
        hPaper
    have hModernSpec :=
      FirstOrder.Derives.iffElimRight
        hModern' (.assumption (by simp)
          )
    exact FirstOrder.Derives.iffElimLeft
      hPaper' hModernSpec
  · have hModern' :=
      FirstOrder.Derives.context_weaken_cons (assumption :=
          successor_paper_spec source candidate)
        hModern
    have hPaper' :=
      FirstOrder.Derives.context_weaken_cons (assumption :=
          successor_paper_spec source candidate)
        hPaper
    have hModernSpec :=
      FirstOrder.Derives.iffElimRight
        hPaper' (.assumption (by simp)
          )
    exact FirstOrder.Derives.iffElimLeft
      hModern' hModernSpec
/-- 已证明的集合等式可直接提升为后继函数项等式。 -/
theorem successor_term_congr_of_equality
    {T : SetTheory} {Γ : Context signature} (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] Sₘ(left) ≐ₘ Sₘ(right) := by
  exact Metatheory.Derives.unary_term_constructor_congr_of_equality
    successor_term
    successor_term_admissible
    (by intros; simp [Term.substituteFree])
    left right hLeft hRight hEquality
/-- 后继函数项保持自由集合变量的等式。 -/
theorem successor_term_congr (left right : FreeVarId) :
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ (Sₘ(x#left) ≐ₘ Sₘ(x#right)) := by
  nd_apply FirstOrder.Derives.impIntro
  exact successor_term_congr_of_equality
    (x#left) (x#right)
    (set_variable_admissible left)
    (set_variable_admissible right)
    (.assumption (by simp))
/-- 等价的源集合可运输同一个候选对象的后继等式。 -/
theorem successor_eq_transport (left right candidate : FreeVarId) :
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ ((x#candidate ≐ₘ Sₘ(x#left)) ⟶ₘ (x#candidate ≐ₘ Sₘ(x#right))) := by
  let left_successor := successor_term (x#left)
  let right_successor := successor_term (x#right)
  have hLeftSuccessor :
      Term.Admissible left_successor SetSort.set :=
    successor_term_admissible (x#left) (set_variable_admissible left)
  have hRightSuccessor :
      Term.Admissible right_successor SetSort.set :=
    successor_term_admissible (x#right) (set_variable_admissible right)
  have hLeftAdmissible :=
    set_variable_admissible left
  have hRightAdmissible :=
    set_variable_admissible right
  have hCandidateAdmissible :=
    set_variable_admissible candidate
  have hSourceEqualityAdmissible :
      Formula.Admissible (x#left ≐ₘ x#right) :=
    Formula.Admissible.equal
      hLeftAdmissible hRightAdmissible
  have hCandidateEqualityAdmissible :
      Formula.Admissible (x#candidate ≐ₘ left_successor) :=
    Formula.Admissible.equal
      hCandidateAdmissible hLeftSuccessor
  change
    ⊢ₘ (x#left ≐ₘ x#right) ⟶ₘ ((x#candidate ≐ₘ left_successor) ⟶ₘ (x#candidate ≐ₘ right_successor))
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hSourceEquality :
      [x#candidate ≐ₘ left_successor,
          x#left ≐ₘ x#right] ⊢ₘ
        x#left ≐ₘ x#right :=
    .assumption (by simp)
  have hCandidateEquality :
      [x#candidate ≐ₘ left_successor,
          x#left ≐ₘ x#right] ⊢ₘ
        x#candidate ≐ₘ left_successor :=
    .assumption (by simp)
  have hSuccessorEquality :
      [x#candidate ≐ₘ left_successor,
          x#left ≐ₘ x#right] ⊢ₘ
        left_successor ≐ₘ right_successor := by
    simpa [left_successor,
      right_successor] using
      successor_term_congr_of_equality (T := (Theory.empty : SetTheory)) (Γ :=
          [x#candidate ≐ₘ left_successor,
            x#left ≐ₘ x#right]) (x#left) (x#right)
        hLeftAdmissible
        hRightAdmissible
        hSourceEquality
  exact Metatheory.Derives.equality_trans
    hCandidateEquality hSuccessorEquality
/-- 每个集合都有后继的全称闭包。 -/
theorem successor_exists_forall (source : FreeVarId) :
    ⊢ₘ[successor_base_theory]
      ∀ₘ[SetSort.set, source],
        successor_exists (x#source) := by
  have hOpen :
      ⊢ₘ[successor_base_theory]
        successor_exists (x#source) :=
    successor_exists_derives (x#source) (set_variable_admissible source)
  derive_close (source) using hOpen
/-- 文献蕴含写法下每个集合都有后继的全称闭包。 -/
theorem successor_paper_exists_forall (source : FreeVarId) :
    ⊢ₘ[successor_base_theory]
      ∀ₘ[SetSort.set, source],
        successor_paper_exists (x#source) := by
  have hOpen :
      ⊢ₘ[successor_base_theory]
        successor_paper_exists (x#source) :=
    successor_paper_exists_derives (x#source) (set_variable_admissible source)
  derive_close (source) using hOpen
/-- 现代后继候选图刻画的双变量全称闭包。 -/
theorem successor_eq_iff_spec_forall (source candidate : FreeVarId) :
    ⊢ₘ[successor_operator_theory]
      ∀ₘ[SetSort.set, source],
        ∀ₘ[SetSort.set, candidate], (x#candidate ≐ₘ Sₘ(x#source)) ↔ₘ
            successor_spec (x#source) (x#candidate) := by
  have hOpen :
      ⊢ₘ[successor_operator_theory] (x#candidate ≐ₘ Sₘ(x#source)) ↔ₘ
          successor_spec (x#source) (x#candidate) :=
    successor_eq_iff_spec (x#source) (x#candidate) (set_variable_admissible source) (set_variable_admissible candidate)
  derive_close (source, candidate) using hOpen
/-- 文献后继候选图刻画的双变量全称闭包。 -/
theorem successor_eq_iff_paper_spec_forall (source candidate : FreeVarId) :
    ⊢ₘ[successor_operator_theory]
      ∀ₘ[SetSort.set, source],
        ∀ₘ[SetSort.set, candidate], (x#candidate ≐ₘ Sₘ(x#source)) ↔ₘ
            successor_paper_spec (x#source) (x#candidate) := by
  have hOpen :
      ⊢ₘ[successor_operator_theory] (x#candidate ≐ₘ Sₘ(x#source)) ↔ₘ
          successor_paper_spec (x#source) (x#candidate) :=
    successor_eq_iff_paper_spec (x#source) (x#candidate) (set_variable_admissible source) (set_variable_admissible candidate)
  derive_close (source, candidate) using hOpen
/-- 后继函数项等式合同的双变量全称闭包。 -/
theorem successor_term_congr_forall (left right : FreeVarId) :
    ⊢ₘ[successor_operator_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right], (x#left ≐ₘ x#right) ⟶ₘ (Sₘ(x#left) ≐ₘ Sₘ(x#right)) := by
  derive_close (left, right) using
    successor_term_congr left right
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
