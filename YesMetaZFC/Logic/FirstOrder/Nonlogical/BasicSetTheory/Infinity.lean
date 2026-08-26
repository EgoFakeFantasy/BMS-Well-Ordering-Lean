import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.BasicFiniteTheory
/-!
# 无穷公理与最小归纳集
本模块建立无穷公理章节的定义设施：
* `infinity_axiom`：存在包含空集且对后继封闭的集合；
* `is_inductive_set_formula`：归纳集谓词，文献索引为 `Inf`；
* `coreₘ(set)`：给定归纳集中的最小归纳核，文献中的 `U` 只作为索引；
* `ωₘ`：满足归纳性与归纳核不变性的常元。
文献的 `ψ₄₄` 与 `Z₂[ψ₄₄]` 被压缩为 `inductive_core_spec` 的直接分离实例。
相关存在性、唯一性、极小化和 `ω` 的数学定理暂留文档索引，不在本模块中伪造
为证明。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 无穷公理 -/
/-- 存在包含空集且对后继封闭的集合。 -/
def infinity_axiom : SetFormula :=
  ∃ₘ[SetSort.set], ((∅ₘ ∈ₘ bₛ#0) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ⟶ₘ (Sₘ(bₛ#0) ∈ₘ bₛ#1)))
/-- 归纳集条件：包含空集并且对后继封闭。 -/
def is_inductive_set_condition (set : SetTerm) :
    SetFormula := (∅ₘ ∈ₘ set) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ set) ⟶ₘ (Sₘ(bₛ#0) ∈ₘ set))
/-- 归纳集谓词的开放定义实例；文献索引为 `Ξ₆₂`。 -/
def is_inductive_set_definition_instance (set : SetTerm) :
    SetFormula :=
  is_inductive_set_formula set ↔ₘ
    is_inductive_set_condition set
/-- 归纳集谓词定义公理。 -/
def is_inductive_set_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_inductive_set_definition_instance (x#0)
/-! ## 归纳核 -/
/--
归纳核的单元素条件。
该公式作为 `membership_specification` 的体使用。其外层成员在第二个绑定层
`bₛ#1`，而 `bₛ#0` 是被检查的归纳集。
-/
def inductive_core_member_condition (source : SetTerm) :
    SetFormula := ((bₛ#0 ∈ₘ source) ∧ₘ (∀ₘ[SetSort.set],
      is_inductive_set_formula bₛ#0 ⟶ₘ (bₛ#1 ∈ₘ bₛ#0)))
/-- 归纳核的成员规格；文献辅助式索引为 `Θ₁₄₁₁a`。 -/
def inductive_core_spec (source candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate (inductive_core_member_condition source)
/-- 对固定归纳集断言归纳核存在。 -/
def inductive_core_separation_exists (source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    inductive_core_spec source bₛ#1
/-- 任意集合参数上的归纳核分离实例。 -/
def inductive_core_separation_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    inductive_core_separation_exists (x#0)
/-- 归纳核函数符号的开放定义实例；文献索引为 `Ξ₆₃`。 -/
def inductive_core_definition_instance (source candidate : SetTerm) :
    SetFormula :=
  is_inductive_set_formula source ⟶ₘ ((candidate ≐ₘ coreₘ(source)) ↔ₘ
      inductive_core_spec source candidate)
/-- 归纳核函数符号定义公理。 -/
def inductive_core_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      inductive_core_definition_instance (x#0) (x#1)
/-! ## 常元 `ω` -/
/--
最小归纳集的无参数成员条件：当前元素属于每一个归纳集。

外层成员规格绑定元素为 `bₛ#1`，本层量词绑定候选归纳集为 `bₛ#0`。
-/
def least_inductive_member_condition : SetFormula :=
  ∀ₘ[SetSort.set],
    is_inductive_set_formula bₛ#0 ⟶ₘ
      (bₛ#1 ∈ₘ bₛ#0)

/-- 候选集合恰好由所有归纳集的公共元素组成。 -/
def least_inductive_spec (candidate : SetTerm) : SetFormula :=
  membership_specification
    candidate least_inductive_member_condition

/-- `ω` 的无常元规格：候选集归纳，且其归纳核等于自身。 -/
def omega_spec (candidate : SetTerm) : SetFormula :=
  is_inductive_set_formula candidate ∧ₘ
    (coreₘ(candidate) ≐ₘ candidate)

/-- 常元 `ω` 的开放定义实例；文献索引为 `Ξ₆₄`。 -/
def omega_definition_instance (candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ ωₘ) ↔ₘ
  omega_spec candidate
/-- 常元 `ω` 定义公理。 -/
def omega_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    omega_definition_instance (x#0)
/-! ## 理论组合 -/
/-- 加入无穷公理后的理论。 -/
def infinity_axiom_theory : SetTheory :=
  Theory.insert
    infinity_axiom
    basic_finite_theory
/-- 加入归纳集谓词后的理论。 -/
def inductive_set_theory : SetTheory :=
  Theory.insert
    is_inductive_set_definition_axiom
    infinity_axiom_theory
/-- 加入归纳核分离实例后的理论。 -/
def inductive_core_separation_theory : SetTheory :=
  Theory.insert
    inductive_core_separation_axiom
    inductive_set_theory
/-- 加入归纳核函数符号后的理论。 -/
def inductive_core_theory : SetTheory :=
  Theory.insert
    inductive_core_definition_axiom
    inductive_core_separation_theory
/--
`ω` 存在唯一性实际消费的最小有限背景。

归纳核定义公理中的函数项已经在归纳 guard 下给出核规格，因此本层不额外要求
归纳核分离实例，也不继承基本有穷理论的其他定义扩张。
-/
def omega_base_theory : SetTheory :=
  Theory.insert
    inductive_core_definition_axiom
    (Theory.insert
      is_inductive_set_definition_axiom
      (Theory.insert infinity_axiom extensionality_theory))
/-- 在最小 `ω` 背景上加入 `ω` 常元定义公理。 -/
def omega_operator_theory : SetTheory :=
  Theory.insert omega_definition_axiom omega_base_theory
/-- 加入 `ω` 常元后的无穷理论。 -/
def infinity_theory : SetTheory :=
  Theory.insert
    omega_definition_axiom
    inductive_core_theory
/-! ## proof-carrying 项边界 -/
/-- 归纳核项满足 proof-carrying 项边界。 -/
theorem inductive_core_term_admissible (set : SetTerm) (hSet : Term.Admissible set SetSort.set) :
    Term.Admissible (coreₘ(set))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .inductiveCore [⟨set, by assumption⟩]
      (by rfl) (by rfl)
/-- 归纳核项的合法性由参数项证书计算。 -/
@[term_check]
theorem inductive_core_term_check
    {set : SetTerm}
    (hSet : Term.CheckCertificate set SetSort.set) :
    Term.CheckCertificate (coreₘ(set)) SetSort.set :=
  Term.check_admissible_complete <|
    inductive_core_term_admissible set hSet.admissible
/-- `ω` 常元项满足 proof-carrying 项边界。 -/
theorem omega_term_admissible :
    Term.Admissible
      ωₘ
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .omega []
      (by rfl) (by rfl)
/-- `ω` 常元的合法性由零元纯函数检查直接决定。 -/
@[term_check]
theorem omega_term_check :
    Term.CheckCertificate ωₘ SetSort.set :=
  Term.check_admissible_complete omega_term_admissible
/-- 归纳集原子在 admissible 集合项处保持 admissible。 -/
theorem is_inductive_set_formula_admissible
    {set : SetTerm}
    (hSet : Term.Admissible set SetSort.set) :
    Formula.Admissible
      (is_inductive_set_formula set) := by
  prove_admissible

/-- 归纳核成员规格在 admissible 参数处保持 admissible。 -/
theorem inductive_core_spec_admissible
    {source candidate : SetTerm}
    (hSource : Term.Admissible source SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible
      (inductive_core_spec source candidate) := by
  prove_admissible

/-- 无参数最小归纳集规格在 admissible 候选项处保持 admissible。 -/
theorem least_inductive_spec_admissible
    {candidate : SetTerm}
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible
      (least_inductive_spec candidate) := by
  prove_admissible

/-- `ω` 的无常元规格在 admissible 候选项处保持 admissible。 -/
theorem omega_spec_admissible
    {candidate : SetTerm}
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (omega_spec candidate) := by
  exact Formula.Admissible.conj
    (is_inductive_set_formula_admissible hCandidate)
    (Formula.Admissible.equal
      (inductive_core_term_admissible candidate hCandidate)
      hCandidate)
/-! ## 良构性与闭理论边界 -/
theorem infinity_axiom_admissible :
    Formula.Admissible infinity_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_inductive_set_definition_axiom_admissible :
    Formula.Admissible
      is_inductive_set_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem inductive_core_separation_axiom_admissible :
    Formula.Admissible
      inductive_core_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem inductive_core_definition_axiom_admissible :
    Formula.Admissible
      inductive_core_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem omega_definition_axiom_admissible :
    Formula.Admissible
      omega_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem infinity_axiom_theory_admissible :
    Theory.Admissible infinity_axiom_theory :=
  Theory.admissible_insert
    infinity_axiom_admissible
    basic_finite_theory_admissible
theorem inductive_set_theory_admissible :
    Theory.Admissible inductive_set_theory :=
  Theory.admissible_insert
    is_inductive_set_definition_axiom_admissible
    infinity_axiom_theory_admissible
theorem inductive_core_separation_theory_admissible :
    Theory.Admissible
      inductive_core_separation_theory :=
  Theory.admissible_insert
    inductive_core_separation_axiom_admissible
    inductive_set_theory_admissible
theorem inductive_core_theory_admissible :
    Theory.Admissible inductive_core_theory :=
  Theory.admissible_insert
    inductive_core_definition_axiom_admissible
    inductive_core_separation_theory_admissible
theorem omega_base_theory_admissible :
    Theory.Admissible omega_base_theory :=
  Theory.admissible_insert
    inductive_core_definition_axiom_admissible
    (Theory.admissible_insert
      is_inductive_set_definition_axiom_admissible
      (Theory.admissible_insert
        infinity_axiom_admissible
        extensionality_theory_admissible))
theorem omega_operator_theory_admissible :
    Theory.Admissible omega_operator_theory :=
  Theory.admissible_insert
    omega_definition_axiom_admissible
    omega_base_theory_admissible
theorem infinity_theory_admissible :
    Theory.Admissible infinity_theory :=
  Theory.admissible_insert
    omega_definition_axiom_admissible
    inductive_core_theory_admissible
/-! ## 闭理论边界 -/
theorem infinity_axiom_sentence :
    Formula.Sentence infinity_axiom := by
  constructor
  · exact infinity_axiom_admissible
  · native_decide
@[derive_close_sentence]
theorem infinity_axiom_theory_sentence
    {formula : SetFormula} (hFormula : infinity_axiom_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · exact infinity_axiom_sentence
  · exact basic_finite_theory_sentence hFormula
@[derive_close_sentence]
theorem inductive_set_theory_sentence
    {formula : SetFormula} (hFormula : inductive_set_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_inductive_set_definition_axiom_admissible
    · native_decide
  · exact infinity_axiom_theory_sentence hFormula
@[derive_close_sentence]
theorem inductive_core_separation_theory_sentence
    {formula : SetFormula} (hFormula : inductive_core_separation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact inductive_core_separation_axiom_admissible
    · native_decide
  · exact inductive_set_theory_sentence hFormula
@[derive_close_sentence]
theorem inductive_core_theory_sentence
    {formula : SetFormula} (hFormula : inductive_core_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact inductive_core_definition_axiom_admissible
    · native_decide
  · exact inductive_core_separation_theory_sentence hFormula
@[derive_close_sentence]
theorem omega_base_theory_sentence
    {formula : SetFormula}
    (hFormula : omega_base_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · exact
      ⟨inductive_core_definition_axiom_admissible,
        by native_decide⟩
  · rcases hFormula with rfl | hFormula
    · exact
        ⟨is_inductive_set_definition_axiom_admissible,
          by native_decide⟩
    · rcases hFormula with rfl | hFormula
      · exact infinity_axiom_sentence
      · exact extensionality_theory_sentence hFormula
@[derive_close_sentence]
theorem omega_operator_theory_sentence
    {formula : SetFormula}
    (hFormula : omega_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · exact
      ⟨omega_definition_axiom_admissible,
        by native_decide⟩
  · exact omega_base_theory_sentence hFormula
@[derive_close_sentence]
theorem infinity_theory_sentence
    {formula : SetFormula} (hFormula : infinity_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact omega_definition_axiom_admissible
    · native_decide
  · exact inductive_core_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem basic_finite_theory_subset_infinity_axiom_theory
    {formula : SetFormula} (hFormula : basic_finite_theory formula) :
    infinity_axiom_theory formula :=
  Or.inr hFormula
theorem infinity_axiom_theory_subset_inductive_set_theory
    {formula : SetFormula} (hFormula : infinity_axiom_theory formula) :
    inductive_set_theory formula :=
  Or.inr hFormula
theorem inductive_set_theory_subset_inductive_core_separation_theory
    {formula : SetFormula} (hFormula : inductive_set_theory formula) :
    inductive_core_separation_theory formula :=
  Or.inr hFormula
theorem inductive_core_separation_theory_subset_inductive_core_theory
    {formula : SetFormula} (hFormula : inductive_core_separation_theory formula) :
    inductive_core_theory formula :=
  Or.inr hFormula
theorem inductive_core_theory_subset_infinity_theory
    {formula : SetFormula} (hFormula : inductive_core_theory formula) :
    infinity_theory formula :=
  Or.inr hFormula
/-! ## 归纳集定义合同 -/
/-- 归纳集谓词定义可在最弱的归纳集理论中实例化。 -/
theorem inductive_set_definition_derives
    (set : SetTerm)
    (hSet : Term.Admissible set SetSort.set) :
    ⊢ₘ[omega_base_theory]
      is_inductive_set_formula set ↔ₘ
        is_inductive_set_condition set := by
  have hAxiom :
      ⊢ₘ[omega_base_theory]
        is_inductive_set_definition_axiom :=
    FirstOrder.Derives.theory_mem
      (Or.inr <| Or.inl rfl)
  have hInstance :=
    FirstOrder.Derives.forall_elim
      (term := set) hAxiom
  simpa [is_inductive_set_definition_axiom,
    is_inductive_set_definition_instance,
    is_inductive_set_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable] using hInstance

/-- 归纳核函数定义可在归纳核理论中直接实例化。 -/
theorem inductive_core_definition_derives
    (source candidate : SetTerm)
    (hSource : Term.Admissible source SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[omega_base_theory]
      inductive_core_definition_instance
        source candidate := by
  have hAxiom :
      ⊢ₘ[omega_base_theory]
        inductive_core_definition_axiom :=
    FirstOrder.Derives.theory_mem (Or.inl rfl)
  have hSourceInstance :=
    FirstOrder.Derives.forall_elim
      (term := source) hAxiom
  have hCandidateInstance :=
    FirstOrder.Derives.forall_elim
      (term := candidate) hSourceInstance
  have hSourceOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term source = source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term source hSource.2
  simpa [inductive_core_definition_axiom,
    inductive_core_definition_instance,
    inductive_core_spec,
    membership_specification,
    inductive_core_member_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hSourceOpen] using
      hCandidateInstance

/--
归纳集的归纳核恰好由所有归纳集的公共元素组成。

源集成员条件在源归纳时是冗余的：属于所有归纳集已经蕴含属于该源集。
-/
theorem inductive_core_least_spec_derives
    (source : SetTerm)
    (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[omega_base_theory]
      is_inductive_set_formula source ⟶ₘ
        least_inductive_spec (coreₘ(source)) := by
  let inductiveSource : SetFormula :=
    is_inductive_set_formula source
  have hInductiveSource :
      Formula.Admissible inductiveSource := by
    simpa [inductiveSource] using
      is_inductive_set_formula_admissible hSource
  apply FirstOrder.Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hInductiveSource)
  let Γ : Context signature := [inductiveSource]
  have hInductive :
      Γ ⊢ₘ[omega_base_theory]
        inductiveSource :=
    FirstOrder.Derives.assumption_of_mem
      (by simp [Γ])
  have hCore :
      Term.Admissible (coreₘ(source)) SetSort.set :=
    inductive_core_term_admissible source hSource
  have hDefinition :
      Γ ⊢ₘ[omega_base_theory]
        inductive_core_definition_instance
          source (coreₘ(source)) :=
    (inductive_core_definition_derives
      source (coreₘ(source)) hSource hCore).context_weaken
        (by simp [Γ])
  have hDefinitionAt :
      Γ ⊢ₘ[omega_base_theory]
        ((coreₘ(source) ≐ₘ coreₘ(source)) ↔ₘ
          inductive_core_spec source (coreₘ(source))) :=
    FirstOrder.Derives.impElim hDefinition
      (by simpa [inductiveSource] using hInductive)
  have hCoreSpec :
      Γ ⊢ₘ[omega_base_theory]
        inductive_core_spec source (coreₘ(source)) :=
    FirstOrder.Derives.iffElimRight hDefinitionAt <|
      FirstOrder.Derives.eq_refl_m
        (T := omega_base_theory) (Γ := Γ)
        (coreₘ(source))
  let body : SetFormula :=
    (bₛ#0 ∈ₘ coreₘ(source)) ↔ₘ
      least_inductive_member_condition
  let element :=
    FreshVariable.fresh_id SetSort.set
      [inductiveSource, body]
  let everyInductive : SetFormula :=
    ∀ₘ[SetSort.set],
      is_inductive_set_formula bₛ#0 ⟶ₘ
        ((x#element) ∈ₘ bₛ#0)
  have hElementFreshInductive :
      (SetSort.set, element) freshForₘ
        inductiveSource := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hElementFreshBody :
      (SetSort.set, element) freshForₘ body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hSourceOpen (depth : Nat) :
      Term.openAt SetSort.set depth
          (x#element) source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth (x#element)
      source hSource.2
  have hCoreOpen (depth : Nat) :
      Term.openAt SetSort.set depth
          (x#element) (coreₘ(source)) =
        coreₘ(source) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth (x#element)
      (coreₘ(source)) hCore.2
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#element) hCoreSpec
  have hAt :
      Γ ⊢ₘ[omega_base_theory]
        (((x#element) ∈ₘ coreₘ(source)) ↔ₘ
          (((x#element) ∈ₘ source) ∧ₘ
            everyInductive)) := by
    simpa [inductive_core_spec,
      membership_specification,
      inductive_core_member_condition,
      everyInductive,
      Formula.openAt, Term.openAt,
      hSourceOpen, hCoreOpen] using hAtRaw
  have hOpened :
      Γ ⊢ₘ[omega_base_theory]
        (((x#element) ∈ₘ coreₘ(source)) ↔ₘ
          everyInductive) := by
    apply FirstOrder.Derives.iffIntro
    · have hAt' :=
        FirstOrder.Derives.context_weaken_cons
          (assumption :=
            (x#element) ∈ₘ coreₘ(source))
          hAt
      have hMember :
          (((x#element) ∈ₘ coreₘ(source)) :: Γ)
            ⊢ₘ[omega_base_theory]
              ((x#element) ∈ₘ coreₘ(source)) :=
        FirstOrder.Derives.assumption_of_mem
          (by simp)
      exact FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.iffElimRight
          hAt' hMember
    ·
      let Δ : Context signature :=
        everyInductive :: Γ
      have hEvery :
          Δ ⊢ₘ[omega_base_theory]
            everyInductive :=
        FirstOrder.Derives.assumption_of_mem
          (by simp [Δ])
      have hInductive' :
          Δ ⊢ₘ[omega_base_theory]
            inductiveSource :=
        hInductive.context_weaken
          (by simp [Γ, Δ])
      have hAtSourceRaw :=
        FirstOrder.Derives.forall_elim
          (term := source) hEvery
      have hAtSource :
          Δ ⊢ₘ[omega_base_theory]
            inductiveSource ⟶ₘ
              ((x#element) ∈ₘ source) := by
        simpa [everyInductive, inductiveSource,
          Formula.openAt, Term.openAt,
          hSourceOpen] using hAtSourceRaw
      have hMemberSource :
          Δ ⊢ₘ[omega_base_theory]
            ((x#element) ∈ₘ source) :=
        FirstOrder.Derives.impElim
          hAtSource hInductive'
      exact FirstOrder.Derives.iffElimLeft
        (hAt.context_weaken
          (by simp [Γ]))
        (FirstOrder.Derives.conjIntro
          hMemberSource hEvery)
  have hOpenedBody :
      Γ ⊢ₘ[omega_base_theory]
        Formula.openAt SetSort.set 0
          (x#element) body := by
    simpa [body, least_inductive_member_condition,
      everyInductive, Formula.openAt, Term.openAt,
      hCoreOpen] using hOpened
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := omega_base_theory) (Γ := Γ)
      (sort := SetSort.set) (eigen := element)
      (body :=
        Formula.openAt SetSort.set 0
          (x#element) body)
      (by
        intro formula hFormula
        rw [(omega_base_theory_sentence
          hFormula).2]
        simp)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hElementFreshInductive)
      hOpenedBody
  simpa [least_inductive_spec,
    membership_specification, body,
    Formula.closeFreeAt_openAt
      SetSort.set element 0 body
      hElementFreshBody] using hGeneralized

/-- 任意归纳集都包含空集。 -/
theorem inductive_set_empty_mem_derives
    (set : SetTerm)
    (hSet : Term.Admissible set SetSort.set) :
    ⊢ₘ[omega_base_theory]
      is_inductive_set_formula set ⟶ₘ
        (∅ₘ ∈ₘ set) := by
  have hInductive :
      Formula.Admissible
        (is_inductive_set_formula set) :=
    is_inductive_set_formula_admissible hSet
  apply FirstOrder.Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible hInductive)
  let Γ : Context signature :=
    [is_inductive_set_formula set]
  have hDefinition :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_formula set ↔ₘ
          is_inductive_set_condition set :=
    (inductive_set_definition_derives
      set hSet).context_weaken (by simp [Γ])
  have hAssumption :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_formula set :=
    FirstOrder.Derives.assumption_of_mem
      (by simp [Γ])
  exact FirstOrder.Derives.conjElimLeft <|
    FirstOrder.Derives.iffElimRight
      hDefinition hAssumption

/-- 归纳集对任意 admissible 对象项的后继封闭。 -/
theorem inductive_set_successor_mem_derives
    (set element : SetTerm)
    (hSet : Term.Admissible set SetSort.set)
    (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[omega_base_theory]
      is_inductive_set_formula set ⟶ₘ
        (element ∈ₘ set) ⟶ₘ
          (Sₘ(element) ∈ₘ set) := by
  have hInductive :
      Formula.Admissible
        (is_inductive_set_formula set) :=
    is_inductive_set_formula_admissible hSet
  have hMember :
      Formula.Admissible (element ∈ₘ set) :=
    membership_formula_admissible hElement hSet
  apply FirstOrder.Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible hInductive)
  apply FirstOrder.Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible hMember)
  let Γ : Context signature :=
    [element ∈ₘ set,
      is_inductive_set_formula set]
  have hDefinition :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_formula set ↔ₘ
          is_inductive_set_condition set :=
    (inductive_set_definition_derives
      set hSet).context_weaken (by simp [Γ])
  have hInductiveProof :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_formula set :=
    FirstOrder.Derives.assumption_of_mem
      (by simp [Γ])
  have hMemberProof :
      Γ ⊢ₘ[omega_base_theory]
        element ∈ₘ set :=
    FirstOrder.Derives.assumption_of_mem
      (by simp [Γ])
  have hClosure :
      Γ ⊢ₘ[omega_base_theory]
        ∀ₘ[SetSort.set],
          (bₛ#0 ∈ₘ set) ⟶ₘ
            (Sₘ(bₛ#0) ∈ₘ set) :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.iffElimRight
        hDefinition hInductiveProof
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := element) hClosure
  have hSetOpen (depth : Nat) :
      Term.openAt SetSort.set depth element set =
        set :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth element set hSet.2
  have hElementOpen (depth : Nat) :
      Term.openAt SetSort.set depth element element =
        element :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth element element hElement.2
  have hAt :
      Γ ⊢ₘ[omega_base_theory]
        (element ∈ₘ set) ⟶ₘ
          (Sₘ(element) ∈ₘ set) := by
    simpa [is_inductive_set_condition,
      Formula.openAt, Term.openAt,
      hSetOpen, hElementOpen] using hAtRaw
  exact FirstOrder.Derives.impElim
    hAt hMemberProof

/-- 空集属于每一个归纳集。 -/
theorem all_inductive_empty_mem_derives :
    ⊢ₘ[omega_base_theory]
      ∀ₘ[SetSort.set],
        is_inductive_set_formula bₛ#0 ⟶ₘ
          (∅ₘ ∈ₘ bₛ#0) := by
  let body : SetFormula :=
    is_inductive_set_formula bₛ#0 ⟶ₘ
      (∅ₘ ∈ₘ bₛ#0)
  let setId : FreeVarId := 0
  have hSetFresh :
      (SetSort.set, setId) freshForₘ body := by
    native_decide
  have hPoint :
      ⊢ₘ[omega_base_theory]
        Formula.openAt SetSort.set 0
          (x#setId) body := by
    simpa [body, setId,
      Formula.openAt, Term.openAt] using
      inductive_set_empty_mem_derives
        (x#setId)
        (set_variable_admissible setId)
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := omega_base_theory)
      (Γ := ([] : Context signature))
      (sort := SetSort.set) (eigen := setId)
      (body :=
        Formula.openAt SetSort.set 0
          (x#setId) body)
      (by
        intro formula hFormula
        rw [(omega_base_theory_sentence
          hFormula).2]
        simp)
      (by
        intro formula hFormula
        cases hFormula)
      hPoint
  simpa [body, setId,
    Formula.closeFreeAt_openAt
      SetSort.set setId 0 body hSetFresh] using
        hGeneralized

/-- 满足最小归纳集规格的集合包含空集。 -/
theorem least_inductive_empty_mem_derives
    (candidate : SetTerm)
    (hCandidate :
      Term.Admissible candidate SetSort.set) :
    ⊢ₘ[omega_base_theory]
      least_inductive_spec candidate ⟶ₘ
        (∅ₘ ∈ₘ candidate) := by
  have hSpecAdmissible :=
    least_inductive_spec_admissible hCandidate
  apply FirstOrder.Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hSpecAdmissible)
  let Γ : Context signature :=
    [least_inductive_spec candidate]
  have hSpec :
      Γ ⊢ₘ[omega_base_theory]
        least_inductive_spec candidate :=
    FirstOrder.Derives.assumption_of_mem
      (by simp [Γ])
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := ∅ₘ) hSpec
  have hCandidateOpen (depth : Nat) :
      Term.openAt SetSort.set depth ∅ₘ candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth ∅ₘ candidate hCandidate.2
  have hAt :
      Γ ⊢ₘ[omega_base_theory]
        ((∅ₘ ∈ₘ candidate) ↔ₘ
          (∀ₘ[SetSort.set],
            is_inductive_set_formula bₛ#0 ⟶ₘ
              (∅ₘ ∈ₘ bₛ#0))) := by
    simpa [least_inductive_spec,
      membership_specification,
      least_inductive_member_condition,
      Formula.openAt, Term.openAt,
      hCandidateOpen] using hAtRaw
  exact FirstOrder.Derives.iffElimLeft hAt <|
    all_inductive_empty_mem_derives.context_weaken
      (by simp)

/--
若一个元素属于每一个归纳集，则它的后继仍属于每一个归纳集。
-/
theorem all_inductive_successor_mem_derives
    (element : SetTerm)
    (hElement :
      Term.Admissible element SetSort.set) :
    ⊢ₘ[omega_base_theory]
      (∀ₘ[SetSort.set],
        is_inductive_set_formula bₛ#0 ⟶ₘ
          (element ∈ₘ bₛ#0)) ⟶ₘ
        (∀ₘ[SetSort.set],
          is_inductive_set_formula bₛ#0 ⟶ₘ
            (Sₘ(element) ∈ₘ bₛ#0)) := by
  let allElement : SetFormula :=
    ∀ₘ[SetSort.set],
      is_inductive_set_formula bₛ#0 ⟶ₘ
        (element ∈ₘ bₛ#0)
  have hAllElement :
      Formula.Admissible allElement := by
    dsimp [allElement]
    prove_admissible
  apply FirstOrder.Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible hAllElement)
  let Γ : Context signature := [allElement]
  have hAll :
      Γ ⊢ₘ[omega_base_theory]
        allElement :=
    FirstOrder.Derives.assumption_of_mem
      (by simp [Γ])
  let body : SetFormula :=
    is_inductive_set_formula bₛ#0 ⟶ₘ
      (Sₘ(element) ∈ₘ bₛ#0)
  let setId :=
    FreshVariable.fresh_id SetSort.set
      [allElement, body]
  have hSetFreshAll :
      (SetSort.set, setId) freshForₘ
        allElement := by
    dsimp [setId]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hSetFreshBody :
      (SetSort.set, setId) freshForₘ body := by
    dsimp [setId]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := x#setId) hAll
  have hElementOpen (depth : Nat) :
      Term.openAt SetSort.set depth
          (x#setId) element =
        element :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth (x#setId)
      element hElement.2
  have hAt :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_formula (x#setId) ⟶ₘ
          (element ∈ₘ x#setId) := by
    simpa [allElement,
      Formula.openAt, Term.openAt,
      hElementOpen] using hAtRaw
  have hStep :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_formula (x#setId) ⟶ₘ
          (element ∈ₘ x#setId) ⟶ₘ
            (Sₘ(element) ∈ₘ x#setId) :=
    (inductive_set_successor_mem_derives
      (x#setId) element
      (set_variable_admissible setId)
      hElement).context_weaken (by simp [Γ])
  have hPoint :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_formula (x#setId) ⟶ₘ
          (Sₘ(element) ∈ₘ x#setId) := by
    derive_prop
  have hOpened :
      Γ ⊢ₘ[omega_base_theory]
        Formula.openAt SetSort.set 0
          (x#setId) body := by
    simpa [body, Formula.openAt, Term.openAt,
      hElementOpen] using hPoint
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := omega_base_theory) (Γ := Γ)
      (sort := SetSort.set) (eigen := setId)
      (body :=
        Formula.openAt SetSort.set 0
          (x#setId) body)
      (by
        intro formula hFormula
        rw [(omega_base_theory_sentence
          hFormula).2]
        simp)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hSetFreshAll)
      hOpened
  simpa [body,
    Formula.closeFreeAt_openAt
      SetSort.set setId 0 body hSetFreshBody] using
        hGeneralized

/-- 满足最小归纳集规格的集合对后继封闭。 -/
theorem least_inductive_successor_mem_derives
    (candidate element : SetTerm)
    (hCandidate :
      Term.Admissible candidate SetSort.set)
    (hElement :
      Term.Admissible element SetSort.set) :
    ⊢ₘ[omega_base_theory]
      least_inductive_spec candidate ⟶ₘ
        (element ∈ₘ candidate) ⟶ₘ
          (Sₘ(element) ∈ₘ candidate) := by
  have hSpecAdmissible :=
    least_inductive_spec_admissible hCandidate
  have hMemberAdmissible :=
    membership_formula_admissible
      hElement hCandidate
  apply FirstOrder.Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hSpecAdmissible)
  apply FirstOrder.Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hMemberAdmissible)
  let Γ : Context signature :=
    [element ∈ₘ candidate,
      least_inductive_spec candidate]
  have hSpec :
      Γ ⊢ₘ[omega_base_theory]
        least_inductive_spec candidate :=
    FirstOrder.Derives.assumption_of_mem
      (by simp [Γ])
  have hMember :
      Γ ⊢ₘ[omega_base_theory]
        element ∈ₘ candidate :=
    FirstOrder.Derives.assumption_of_mem
      (by simp [Γ])
  have hCandidateOpenAtElement (depth : Nat) :
      Term.openAt SetSort.set depth
          element candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth element candidate
      hCandidate.2
  have hElementOpen (depth : Nat) :
      Term.openAt SetSort.set depth
          element element =
        element :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth element element
      hElement.2
  have hAtElementRaw :=
    FirstOrder.Derives.forall_elim
      (term := element) hSpec
  have hAtElement :
      Γ ⊢ₘ[omega_base_theory]
        ((element ∈ₘ candidate) ↔ₘ
          (∀ₘ[SetSort.set],
            is_inductive_set_formula bₛ#0 ⟶ₘ
              (element ∈ₘ bₛ#0))) := by
    simpa [least_inductive_spec,
      membership_specification,
      least_inductive_member_condition,
      Formula.openAt, Term.openAt,
      hCandidateOpenAtElement,
      hElementOpen] using hAtElementRaw
  have hEveryElement :
      Γ ⊢ₘ[omega_base_theory]
        ∀ₘ[SetSort.set],
          is_inductive_set_formula bₛ#0 ⟶ₘ
            (element ∈ₘ bₛ#0) :=
    FirstOrder.Derives.iffElimRight
      hAtElement hMember
  have hEverySuccessor :
      Γ ⊢ₘ[omega_base_theory]
        ∀ₘ[SetSort.set],
          is_inductive_set_formula bₛ#0 ⟶ₘ
            (Sₘ(element) ∈ₘ bₛ#0) :=
    FirstOrder.Derives.impElim
      ((all_inductive_successor_mem_derives
        element hElement).context_weaken
          (by simp [Γ]))
      hEveryElement
  have hSuccessor :
      Term.Admissible (Sₘ(element)) SetSort.set :=
    successor_term_admissible element hElement
  have hCandidateOpenAtSuccessor (depth : Nat) :
      Term.openAt SetSort.set depth
          (Sₘ(element)) candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth (Sₘ(element))
      candidate hCandidate.2
  have hSuccessorOpen (depth : Nat) :
      Term.openAt SetSort.set depth
          (Sₘ(element)) (Sₘ(element)) =
        Sₘ(element) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth (Sₘ(element))
      (Sₘ(element)) hSuccessor.2
  have hAtSuccessorRaw :=
    FirstOrder.Derives.forall_elim
      (term := Sₘ(element)) hSpec
  have hAtSuccessor :
      Γ ⊢ₘ[omega_base_theory]
        ((Sₘ(element) ∈ₘ candidate) ↔ₘ
          (∀ₘ[SetSort.set],
            is_inductive_set_formula bₛ#0 ⟶ₘ
              (Sₘ(element) ∈ₘ bₛ#0))) := by
    simpa [least_inductive_spec,
      membership_specification,
      least_inductive_member_condition,
      Formula.openAt, Term.openAt,
      hCandidateOpenAtSuccessor,
      hSuccessorOpen] using hAtSuccessorRaw
  exact FirstOrder.Derives.iffElimLeft
    hAtSuccessor hEverySuccessor

/-- 最小归纳集规格本身蕴含归纳性。 -/
theorem least_inductive_spec_inductive_derives
    (candidate : SetTerm)
    (hCandidate :
      Term.Admissible candidate SetSort.set) :
    ⊢ₘ[omega_base_theory]
      least_inductive_spec candidate ⟶ₘ
        is_inductive_set_formula candidate := by
  have hSpecAdmissible :=
    least_inductive_spec_admissible hCandidate
  apply FirstOrder.Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hSpecAdmissible)
  let Γ : Context signature :=
    [least_inductive_spec candidate]
  have hSpec :
      Γ ⊢ₘ[omega_base_theory]
        least_inductive_spec candidate :=
    FirstOrder.Derives.assumption_of_mem
      (by simp [Γ])
  have hEmpty :
      Γ ⊢ₘ[omega_base_theory]
        ∅ₘ ∈ₘ candidate :=
    FirstOrder.Derives.impElim
      ((least_inductive_empty_mem_derives
        candidate hCandidate).context_weaken
          (by simp [Γ]))
      hSpec
  let body : SetFormula :=
    (bₛ#0 ∈ₘ candidate) ⟶ₘ
      (Sₘ(bₛ#0) ∈ₘ candidate)
  let element :=
    FreshVariable.fresh_id SetSort.set
      [least_inductive_spec candidate, body]
  have hElementFreshSpec :
      (SetSort.set, element) freshForₘ
        least_inductive_spec candidate := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hElementFreshBody :
      (SetSort.set, element) freshForₘ body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hPoint :
      Γ ⊢ₘ[omega_base_theory]
        ((x#element) ∈ₘ candidate) ⟶ₘ
          (Sₘ(x#element) ∈ₘ candidate) :=
    FirstOrder.Derives.impElim
      ((least_inductive_successor_mem_derives
        candidate (x#element)
        hCandidate
        (set_variable_admissible element)).context_weaken
          (by simp [Γ]))
      hSpec
  have hCandidateOpen (depth : Nat) :
      Term.openAt SetSort.set depth
          (x#element) candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth (x#element)
      candidate hCandidate.2
  have hOpened :
      Γ ⊢ₘ[omega_base_theory]
        Formula.openAt SetSort.set 0
          (x#element) body := by
    simpa [body, Formula.openAt, Term.openAt,
      hCandidateOpen] using hPoint
  have hClosureRaw :=
    FirstOrder.Derives.forall_intro
      (T := omega_base_theory) (Γ := Γ)
      (sort := SetSort.set) (eigen := element)
      (body :=
        Formula.openAt SetSort.set 0
          (x#element) body)
      (by
        intro formula hFormula
        rw [(omega_base_theory_sentence
          hFormula).2]
        simp)
      (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact hElementFreshSpec)
      hOpened
  have hClosure :
      Γ ⊢ₘ[omega_base_theory]
        ∀ₘ[SetSort.set],
          (bₛ#0 ∈ₘ candidate) ⟶ₘ
            (Sₘ(bₛ#0) ∈ₘ candidate) := by
    simpa [body,
      Formula.closeFreeAt_openAt
        SetSort.set element 0 body
        hElementFreshBody] using hClosureRaw
  have hCondition :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_condition candidate := by
    simpa [is_inductive_set_condition] using
      FirstOrder.Derives.conjIntro
        hEmpty hClosure
  have hDefinition :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_formula candidate ↔ₘ
          is_inductive_set_condition candidate :=
    (inductive_set_definition_derives
      candidate hCandidate).context_weaken
        (by simp [Γ])
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hCondition

/-- 两个集合满足最小归纳集规格时由外延性相等。 -/
theorem least_inductive_spec_unique
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[omega_base_theory]
      least_inductive_spec left ⟶ₘ
        least_inductive_spec right ⟶ₘ
          (left ≐ₘ right) := by
  apply FirstOrder.Derives.theory_weaken
    (T := extensionality_theory)
  · intro formula hFormula
    repeat' apply Or.inr
    exact hFormula
  · simpa [least_inductive_spec] using
      membership_specification_unique
        left right least_inductive_member_condition
        hLeft hRight
        (least_inductive_spec_admissible hLeft)
        (least_inductive_spec_admissible hRight)

/-- 归纳集的归纳核仍是归纳集。 -/
theorem inductive_core_inductive_derives
    (source : SetTerm)
    (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[omega_base_theory]
      is_inductive_set_formula source ⟶ₘ
        is_inductive_set_formula (coreₘ(source)) := by
  have hCore :=
    inductive_core_term_admissible source hSource
  have hLeast :=
    inductive_core_least_spec_derives
      source hSource
  have hInductive :=
    least_inductive_spec_inductive_derives
      (coreₘ(source)) hCore
  derive_prop

/-- 归纳集的归纳核是归纳核算子的一个不动点。 -/
theorem inductive_core_fixed_derives
    (source : SetTerm)
    (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[omega_base_theory]
      is_inductive_set_formula source ⟶ₘ
        (coreₘ(coreₘ(source)) ≐ₘ coreₘ(source)) := by
  have hInductiveAdmissible :=
    is_inductive_set_formula_admissible hSource
  apply FirstOrder.Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hInductiveAdmissible)
  let Γ : Context signature :=
    [is_inductive_set_formula source]
  have hSourceInductive :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_formula source :=
    FirstOrder.Derives.assumption_of_mem
      (by simp [Γ])
  have hCore :
      Term.Admissible (coreₘ(source)) SetSort.set :=
    inductive_core_term_admissible source hSource
  have hDoubleCore :
      Term.Admissible
        (coreₘ(coreₘ(source))) SetSort.set :=
    inductive_core_term_admissible
      (coreₘ(source)) hCore
  have hLeastCore :
      Γ ⊢ₘ[omega_base_theory]
        least_inductive_spec (coreₘ(source)) :=
    FirstOrder.Derives.impElim
      ((inductive_core_least_spec_derives
        source hSource).context_weaken
          (by simp [Γ]))
      hSourceInductive
  have hCoreInductive :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_formula (coreₘ(source)) :=
    FirstOrder.Derives.impElim
      ((least_inductive_spec_inductive_derives
        (coreₘ(source)) hCore).context_weaken
          (by simp [Γ]))
      hLeastCore
  have hLeastDoubleCore :
      Γ ⊢ₘ[omega_base_theory]
        least_inductive_spec
          (coreₘ(coreₘ(source))) :=
    FirstOrder.Derives.impElim
      ((inductive_core_least_spec_derives
        (coreₘ(source)) hCore).context_weaken
          (by simp [Γ]))
      hCoreInductive
  have hUnique :
      Γ ⊢ₘ[omega_base_theory]
        least_inductive_spec
            (coreₘ(coreₘ(source))) ⟶ₘ
          least_inductive_spec (coreₘ(source)) ⟶ₘ
            (coreₘ(coreₘ(source)) ≐ₘ
              coreₘ(source)) :=
    (least_inductive_spec_unique
      (coreₘ(coreₘ(source))) (coreₘ(source))
      hDoubleCore hCore).context_weaken
        (by simp [Γ])
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.impElim
      hUnique hLeastDoubleCore)
    hLeastCore

/-- 任意归纳集的归纳核满足 `ω` 的无常元规格。 -/
theorem inductive_core_omega_spec_derives
    (source : SetTerm)
    (hSource : Term.Admissible source SetSort.set) :
    ⊢ₘ[omega_base_theory]
      is_inductive_set_formula source ⟶ₘ
        omega_spec (coreₘ(source)) := by
  have hInductive :=
    inductive_core_inductive_derives
      source hSource
  have hFixed :=
    inductive_core_fixed_derives
      source hSource
  simpa [omega_spec] using
    (show
      ⊢ₘ[omega_base_theory]
        is_inductive_set_formula source ⟶ₘ
          (is_inductive_set_formula (coreₘ(source)) ∧ₘ
            (coreₘ(coreₘ(source)) ≐ₘ
              coreₘ(source))) by
        derive_prop)

/-- `omega_spec` 在归纳核理论中是单值的。 -/
theorem omega_spec_unique
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[omega_base_theory]
      omega_spec left ⟶ₘ
        omega_spec right ⟶ₘ
          (left ≐ₘ right) := by
  have hLeftSpec :=
    omega_spec_admissible hLeft
  have hRightSpec :=
    omega_spec_admissible hRight
  apply FirstOrder.Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hLeftSpec)
  apply FirstOrder.Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hRightSpec)
  let Γ : Context signature :=
    [omega_spec right, omega_spec left]
  have hLeftProof :
      Γ ⊢ₘ[omega_base_theory]
        omega_spec left :=
    FirstOrder.Derives.assumption_of_mem
      (by simp [Γ])
  have hRightProof :
      Γ ⊢ₘ[omega_base_theory]
        omega_spec right :=
    FirstOrder.Derives.assumption_of_mem
      (by simp [Γ])
  have hLeftInductive :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_formula left := by
    simpa [omega_spec] using
      FirstOrder.Derives.conjElimLeft hLeftProof
  have hRightInductive :
      Γ ⊢ₘ[omega_base_theory]
        is_inductive_set_formula right := by
    simpa [omega_spec] using
      FirstOrder.Derives.conjElimLeft hRightProof
  have hLeftFixed :
      Γ ⊢ₘ[omega_base_theory]
        coreₘ(left) ≐ₘ left := by
    simpa [omega_spec] using
      FirstOrder.Derives.conjElimRight hLeftProof
  have hRightFixed :
      Γ ⊢ₘ[omega_base_theory]
        coreₘ(right) ≐ₘ right := by
    simpa [omega_spec] using
      FirstOrder.Derives.conjElimRight hRightProof
  have hCoreLeft :
      Term.Admissible (coreₘ(left)) SetSort.set :=
    inductive_core_term_admissible left hLeft
  have hCoreRight :
      Term.Admissible (coreₘ(right)) SetSort.set :=
    inductive_core_term_admissible right hRight
  have hLeastLeft :
      Γ ⊢ₘ[omega_base_theory]
        least_inductive_spec (coreₘ(left)) :=
    FirstOrder.Derives.impElim
      ((inductive_core_least_spec_derives
        left hLeft).context_weaken
          (by simp [Γ]))
      hLeftInductive
  have hLeastRight :
      Γ ⊢ₘ[omega_base_theory]
        least_inductive_spec (coreₘ(right)) :=
    FirstOrder.Derives.impElim
      ((inductive_core_least_spec_derives
        right hRight).context_weaken
          (by simp [Γ]))
      hRightInductive
  have hCoreEquality :
      Γ ⊢ₘ[omega_base_theory]
        coreₘ(left) ≐ₘ coreₘ(right) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        ((least_inductive_spec_unique
          (coreₘ(left)) (coreₘ(right))
          hCoreLeft hCoreRight).context_weaken
            (by simp [Γ]))
        hLeastLeft)
      hLeastRight
  exact Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm hLeftFixed)
    (Metatheory.Derives.equality_trans
      hCoreEquality hRightFixed)

/-- 无穷公理在归纳核理论中给出一个归纳集。 -/
theorem inductive_set_exists_derives :
    ⊢ₘ[omega_base_theory]
      ∃ₘ[SetSort.set],
        is_inductive_set_formula bₛ#0 := by
  let sourceId : FreeVarId := 0
  let rawBody : SetFormula :=
    (∅ₘ ∈ₘ bₛ#0) ∧ₘ
      (∀ₘ[SetSort.set],
        (bₛ#0 ∈ₘ bₛ#1) ⟶ₘ
          (Sₘ(bₛ#0) ∈ₘ bₛ#1))
  let sourceCondition : SetFormula :=
    Formula.openAt SetSort.set 0
      (x#sourceId) rawBody
  let conclusion : SetFormula :=
    ∃ₘ[SetSort.set],
      is_inductive_set_formula bₛ#0
  have hRawFresh :
      (SetSort.set, sourceId) freshForₘ
        rawBody := by
    native_decide
  have hInfinity :
      ⊢ₘ[omega_base_theory]
        infinity_axiom :=
    FirstOrder.Derives.theory_mem
      (Or.inr <| Or.inr <| Or.inl rfl)
  have hExists :
      ⊢ₘ[omega_base_theory]
        Formula.existsE SetSort.set
          (Formula.closeFreeAt SetSort.set
            sourceId 0 sourceCondition) := by
    simpa [infinity_axiom, rawBody,
      sourceCondition, is_inductive_set_condition,
      Formula.closeFreeAt_openAt
        SetSort.set sourceId 0 rawBody hRawFresh] using
          hInfinity
  have hCase :
      [sourceCondition]
        ⊢ₘ[omega_base_theory]
          conclusion := by
    have hSource :=
      set_variable_admissible sourceId
    have hCondition :
        [sourceCondition]
          ⊢ₘ[omega_base_theory]
            sourceCondition :=
      FirstOrder.Derives.assumption_of_mem
        (by simp)
    have hDefinition :
        [sourceCondition]
          ⊢ₘ[omega_base_theory]
            is_inductive_set_formula (x#sourceId) ↔ₘ
              is_inductive_set_condition (x#sourceId) :=
      (inductive_set_definition_derives
        (x#sourceId) hSource).context_weaken
          (by simp)
    have hCondition' :
        [sourceCondition]
          ⊢ₘ[omega_base_theory]
            is_inductive_set_condition
              (x#sourceId) := by
      simpa [sourceCondition, rawBody,
        is_inductive_set_condition,
        Formula.openAt, Term.openAt] using
          hCondition
    have hInductive :
        [sourceCondition]
          ⊢ₘ[omega_base_theory]
            is_inductive_set_formula
              (x#sourceId) :=
      FirstOrder.Derives.iffElimLeft
        hDefinition hCondition'
    apply FirstOrder.Derives.exists_intro
      (term := x#sourceId)
    simpa [conclusion,
      Formula.openAt, Term.openAt] using
        hInductive
  exact FirstOrder.Derives.exists_elim
    (by
      intro formula hFormula
      rw [(omega_base_theory_sentence
        hFormula).2]
      simp)
    (by
      intro formula hFormula
      cases hFormula)
    (by
      native_decide)
    hExists hCase

/-- `omega_spec` 在不含 `ω` 常元定义公理的归纳核理论中存在。 -/
theorem omega_spec_exists_derives :
    ⊢ₘ[omega_base_theory]
      ∃ₘ[SetSort.set],
        omega_spec bₛ#0 := by
  let sourceId : FreeVarId := 0
  let boundBody : SetFormula :=
    is_inductive_set_formula bₛ#0
  let sourceInductive : SetFormula :=
    Formula.openAt SetSort.set 0
      (x#sourceId) boundBody
  let conclusion : SetFormula :=
    ∃ₘ[SetSort.set],
      omega_spec bₛ#0
  have hBoundFresh :
      (SetSort.set, sourceId) freshForₘ
        boundBody := by
    native_decide
  have hExists :
      ⊢ₘ[omega_base_theory]
        Formula.existsE SetSort.set
          (Formula.closeFreeAt SetSort.set
            sourceId 0 sourceInductive) := by
    have hClose :
        Formula.closeFreeAt SetSort.set sourceId 0
            sourceInductive =
          boundBody := by
      dsimp [sourceInductive]
      exact Formula.closeFreeAt_openAt
        SetSort.set sourceId 0 boundBody
        hBoundFresh
    rw [hClose]
    simpa [boundBody] using
      inductive_set_exists_derives
  have hCase :
      [sourceInductive]
        ⊢ₘ[omega_base_theory]
          conclusion := by
    have hSource :=
      set_variable_admissible sourceId
    have hInductive :
        [sourceInductive]
          ⊢ₘ[omega_base_theory]
            is_inductive_set_formula
              (x#sourceId) := by
      simpa [sourceInductive, boundBody,
        Formula.openAt, Term.openAt] using
        (FirstOrder.Derives.assumption_of_mem
          (by simp) :
          [sourceInductive]
            ⊢ₘ[omega_base_theory]
              sourceInductive)
    have hCoreSpec :
        [sourceInductive]
          ⊢ₘ[omega_base_theory]
            omega_spec (coreₘ(x#sourceId)) :=
      FirstOrder.Derives.impElim
        ((inductive_core_omega_spec_derives
          (x#sourceId) hSource).context_weaken
            (by simp))
        hInductive
    apply FirstOrder.Derives.exists_intro
      (term := coreₘ(x#sourceId))
    simpa [conclusion, omega_spec,
      Formula.openAt, Term.openAt] using
        hCoreSpec
  exact FirstOrder.Derives.exists_elim
    (by
      intro formula hFormula
      rw [(omega_base_theory_sentence
        hFormula).2]
      simp)
    (by
      intro formula hFormula
      cases hFormula)
    (by
      native_decide)
    hExists hCase

/--
任意 admissible 集合项上的归纳集谓词定义实例。
该接口统一封装 `is_inductive_set_definition_axiom` 的全称实例化；调用方无需再展开
自由变量关闭、`openAt` 与零/后继条件。
-/
theorem infinity_is_inductive_set_definition_derives (set : SetTerm) (hSet : Term.Admissible set SetSort.set) :
    ⊢ₘ[infinity_theory]
      is_inductive_set_formula set ↔ₘ
        is_inductive_set_condition set := by
  have hDefinitionAxiom :
      ⊢ₘ[infinity_theory]
        is_inductive_set_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hDefinition :=
    FirstOrder.Derives.forall_elim
      (term := set) hDefinitionAxiom
  simpa [is_inductive_set_definition_axiom,
    is_inductive_set_definition_instance,
    is_inductive_set_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt, Formula.next_depth,
    Term.openAt, Term.closeFreeAt,
    Formula.substituteFree, Term.substituteFree,
    set_variable, set_bound_variable] using hDefinition
/-! ## `ω` 的归纳性与极小性 -/
/--
`ωₘ` 的定义实例。
后续归纳性、归纳核不变性与最小性都从同一份实例中投影，避免各模块重复展开
`omega_definition_axiom`。
-/
theorem infinity_omega_definition_derives :
    ⊢ₘ[infinity_theory] ((ωₘ ≐ₘ ωₘ) ↔ₘ (is_inductive_set_formula ωₘ ∧ₘ (coreₘ(ωₘ) ≐ₘ ωₘ))) := by
  have hOmegaAxiom :
      ⊢ₘ[infinity_theory] omega_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hOmegaInstance :=
    FirstOrder.Derives.forall_elim
      (term := ωₘ) hOmegaAxiom
  simpa [omega_definition_axiom, omega_definition_instance,
    omega_spec,
    Formula.openAt, Formula.closeFreeAt, Term.openAt,
    Term.closeFreeAt, set_variable, set_bound_variable] using
      hOmegaInstance
/-- `ωₘ` 在对象理论中是归纳集。 -/
theorem infinity_omega_inductive_derives :
    ⊢ₘ[infinity_theory]
      is_inductive_set_formula ωₘ := by
  have hReflexive :=
    FirstOrder.Derives.eq_refl_m
      (T := infinity_theory) (Γ := []) (sort := SetSort.set) ωₘ
  exact FirstOrder.Derives.conjElimLeft <|
    FirstOrder.Derives.iffElimRight
      infinity_omega_definition_derives hReflexive
/-- `ωₘ` 的零点与后继封闭条件。 -/
theorem infinity_omega_inductive_condition_derives :
    ⊢ₘ[infinity_theory]
      is_inductive_set_condition ωₘ :=
  FirstOrder.Derives.iffElimRight (infinity_is_inductive_set_definition_derives
      ωₘ omega_term_admissible)
    infinity_omega_inductive_derives
/--
对象自然数对后继封闭。

该接口接受任意 admissible 对象项，不要求它是外部 numeral；后续对象算术与
Gödel 编码可以直接复用这一层，而无需重新展开 `ωₘ` 的归纳集定义。
-/
theorem infinity_successor_term_mem_omega
    {Γ : Context signature}
    (source : SetTerm)
    (hSource : Term.Admissible source SetSort.set)
    (hSourceMem :
      Γ ⊢ₘ[infinity_theory] source ∈ₘ ωₘ) :
    Γ ⊢ₘ[infinity_theory] Sₘ(source) ∈ₘ ωₘ := by
  have hSuccessorClosure :
      Γ ⊢ₘ[infinity_theory]
        ∀ₘ[SetSort.set],
          (bₛ#0 ∈ₘ ωₘ) ⟶ₘ
            (Sₘ(bₛ#0) ∈ₘ ωₘ) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.conjElimRight
          infinity_omega_inductive_condition_derives
  have hAtSource :=
    FirstOrder.Derives.forall_elim
      (term := source) hSuccessorClosure
  have hSourceOpen :
      Term.openAt SetSort.set 0 source ωₘ = ωₘ :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 source ωₘ omega_term_admissible.2
  have hSuccessorOpen :
      Term.openAt SetSort.set 0 source source = source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 source source hSource.2
  exact FirstOrder.Derives.impElim
    (by
      simpa [Formula.openAt, Term.openAt,
        hSourceOpen, hSuccessorOpen] using hAtSource)
    hSourceMem
/-- `ωₘ` 等于自己的归纳核。 -/
theorem infinity_omega_core_eq_derives :
    ⊢ₘ[infinity_theory]
      coreₘ(ωₘ) ≐ₘ ωₘ := by
  have hReflexive :=
    FirstOrder.Derives.eq_refl_m
      (T := infinity_theory) (Γ := []) (sort := SetSort.set) ωₘ
  exact FirstOrder.Derives.conjElimRight <|
    FirstOrder.Derives.iffElimRight
      infinity_omega_definition_derives hReflexive
/-- `coreₘ(ωₘ)` 满足归纳核的逐点成员规格。 -/
theorem infinity_omega_core_spec_derives :
    ⊢ₘ[infinity_theory]
      inductive_core_spec ωₘ (coreₘ(ωₘ)) := by
  have hDefinitionAxiom :
      ⊢ₘ[infinity_theory]
        inductive_core_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inr (Or.inl rfl))
  have hSourceInstance :=
    FirstOrder.Derives.forall_elim
      (term := ωₘ) hDefinitionAxiom
  have hCoreAdmissible :
      Term.Admissible (coreₘ(ωₘ)) SetSort.set :=
    inductive_core_term_admissible
      ωₘ omega_term_admissible
  have hCandidateInstance :=
    FirstOrder.Derives.forall_elim
      (term := coreₘ(ωₘ)) hSourceInstance
  have hOmegaOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term ωₘ = ωₘ :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term ωₘ omega_term_admissible.2
  have hCoreOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term (coreₘ(ωₘ)) =
        coreₘ(ωₘ) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term (coreₘ(ωₘ))
      hCoreAdmissible.2
  have hDefinition :
      ⊢ₘ[infinity_theory]
        is_inductive_set_formula ωₘ ⟶ₘ (((coreₘ(ωₘ)) ≐ₘ coreₘ(ωₘ)) ↔ₘ
            inductive_core_spec ωₘ (coreₘ(ωₘ))) := by
    simpa [inductive_core_definition_axiom,
      inductive_core_definition_instance,
      inductive_core_spec,
      membership_specification,
      inductive_core_member_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      hOmegaOpen, hCoreOpen] using
        hCandidateInstance
  have hAtOmega :=
    FirstOrder.Derives.impElim
      hDefinition infinity_omega_inductive_derives
  exact FirstOrder.Derives.iffElimRight hAtOmega <|
    FirstOrder.Derives.eq_refl_m
      (T := infinity_theory) (Γ := []) (sort := SetSort.set) (coreₘ(ωₘ))
/--
`ωₘ` 的逐点极小性：若 `candidate` 是归纳集，则每个属于 `ωₘ` 的元素都属于
`candidate`。
这是后续对象层自然数归纳、有限截断和递归唯一性的公共入口；结论保持逐点形式，
调用方可以按需再全称化或包装成子集关系。
-/
theorem infinity_omega_member_of_inductive_derives (candidate element : SetTerm) (hCandidate : Term.Admissible candidate SetSort.set)
    (hElement : Term.Admissible element SetSort.set) :
    ⊢ₘ[infinity_theory]
      is_inductive_set_formula candidate ⟶ₘ (element ∈ₘ ωₘ) ⟶ₘ (element ∈ₘ candidate) := by
  let hInductive : SetFormula :=
    is_inductive_set_formula candidate
  let hNatural : SetFormula :=
    element ∈ₘ ωₘ
  have hInductiveAdmissible :
      Formula.Admissible hInductive := by
    dsimp [hInductive, is_inductive_set_formula]
    apply Formula.Admissible.rel
    simpa [signature] using (ArgsAdmissible.cons hCandidate
        ArgsAdmissible.nil)
  have hNaturalAdmissible :
      Formula.Admissible hNatural := by
    simpa [hNatural] using
      membership_formula_admissible
        hElement omega_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [hNatural, hInductive]
  have hInductiveAssumption :
      Γ ⊢ₘ[infinity_theory] hInductive :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hNaturalAssumption :
      Γ ⊢ₘ[infinity_theory] hNatural :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hCoreAdmissible :
      Term.Admissible (coreₘ(ωₘ)) SetSort.set :=
    inductive_core_term_admissible
      ωₘ omega_term_admissible
  have hCoreTransport :
      Γ ⊢ₘ[infinity_theory] (element ∈ₘ coreₘ(ωₘ)) ↔ₘ (element ∈ₘ ωₘ) :=
    membership_right_iff_of_equality
      element (coreₘ(ωₘ)) ωₘ
      hElement hCoreAdmissible omega_term_admissible (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ])
        infinity_omega_core_eq_derives)
  have hCoreMember :
      Γ ⊢ₘ[infinity_theory]
        element ∈ₘ coreₘ(ωₘ) :=
    FirstOrder.Derives.iffElimLeft
      hCoreTransport (by simpa [hNatural] using hNaturalAssumption)
  have hCoreSpecAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := element) (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ])
        infinity_omega_core_spec_derives)
  have hCoreSpecAt :
      Γ ⊢ₘ[infinity_theory] (element ∈ₘ coreₘ(ωₘ)) ↔ₘ ((element ∈ₘ ωₘ) ∧ₘ (∀ₘ[SetSort.set],
              is_inductive_set_formula bₛ#0 ⟶ₘ (element ∈ₘ bₛ#0))) := by
    simpa [inductive_core_spec,
      membership_specification,
      inductive_core_member_condition,
      Formula.openAt, Term.openAt] using
        hCoreSpecAtRaw
  have hEveryInductive :
      Γ ⊢ₘ[infinity_theory]
        ∀ₘ[SetSort.set],
          is_inductive_set_formula bₛ#0 ⟶ₘ (element ∈ₘ bₛ#0) :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.iffElimRight
        hCoreSpecAt hCoreMember
  have hAtCandidateRaw :=
    FirstOrder.Derives.forall_elim
      (term := candidate) hEveryInductive
  have hElementOpen :
      Term.openAt SetSort.set 0 candidate element =
        element :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 candidate element hElement.2
  have hAtCandidate :
      Γ ⊢ₘ[infinity_theory]
        is_inductive_set_formula candidate ⟶ₘ (element ∈ₘ candidate) := by
    simpa [Formula.openAt, Term.openAt,
      hElementOpen] using
      hAtCandidateRaw
  exact FirstOrder.Derives.impElim
    hAtCandidate (by simpa [hInductive] using hInductiveAssumption)
/-! ## 标准有限自然数 -/
/--
每个 Lean 层标准自然数 numeral 都属于对象理论的 `ωₘ`。
该结论只消费 `ωₘ` 的最小归纳集定义，不依赖有限序列、quotation 或任何后续
编码理论；因而符号编码、标准序列与算术编码可以共同复用这一基础入口。
-/
theorem infinity_finite_numeral_mem_omega (number : Nat) :
    ⊢ₘ[infinity_theory] numₘ(number) ∈ₘ ωₘ := by
  induction number with
  | zero =>
      exact FirstOrder.Derives.conjElimLeft
        infinity_omega_inductive_condition_derives
  | succ number ih =>
      have hSuccessorClosure :=
        FirstOrder.Derives.conjElimRight
          infinity_omega_inductive_condition_derives
      have hAtNumeral :=
        FirstOrder.Derives.forall_elim
          (term := numₘ(number)) hSuccessorClosure
      have hStep :
          ⊢ₘ[infinity_theory] (numₘ(number) ∈ₘ ωₘ) ⟶ₘ (Sₘ(numₘ(number)) ∈ₘ ωₘ) := by
        simpa [is_inductive_set_condition, Formula.openAt,
          Term.openAt, set_variable, set_bound_variable] using hAtNumeral
      have hNext := FirstOrder.Derives.impElim hStep ih
      simpa [finite_numeral_term] using hNext
/-!
## 待证明定理索引
本轮截图中的结论暂留为后续证明任务：
* 定理 5.1：归纳集存在性与归纳核的唯一性；
* 定理 5.2：归纳核保持归纳性并且与归纳集参数无关；
* 定理 5.3：`ω` 的存在性与唯一性；
* 后续 `ω` 的常元性质及自然数算术推导。
文献中的 `Θ₁₄₁₁a`、`Θ₁₄₁₁b` 与 `ψ₄₄` 已压缩进
`inductive_core_member_condition` 和 `inductive_core_separation_axiom`，不单独
进入公共签名。文献中的 `U` 不映射为同名函数符号，公共接口使用 `coreₘ`。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
