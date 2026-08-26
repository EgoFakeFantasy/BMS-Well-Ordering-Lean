import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Basic
/-!
# 分离公理与唯一性
谓词体直接使用一个 `SetSort.set` bound 变量作为待筛选元素；其余参数保持为 free
变量。这样分离公式完全沿 locally nameless scope 构造，不需要文献中的机械辅助
变量编号，也不会把对象语言公式整体交给定义展开。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-- 一个可放在单个集合元素 binder 下的 proof-carrying 谓词体。 -/
structure SetPredicate where
  body : SetFormula
  admissible_at :
    Formula.AdmissibleAt (Scope.push Scope.empty SetSort.set) body
namespace SetPredicate
/--
给定单元素 binder 下的 proof-carrying 谓词后，任意 admissible 候选项都可形成
纯成员规格。
该接口与 `separation_spec_admissible` 的区别在于不额外携带母集成员条件，供关系
代数、函数图等已经把界条件并入谓词体的构造复用。
-/
theorem membership_specification_admissible (predicate : SetPredicate) {candidate : SetTerm} (hCandidate : Term.Admissible
      candidate SetSort.set) :
    Formula.Admissible (membership_specification
        candidate predicate.body) := by
  have hPredicate := predicate.admissible_at
  prove_admissible
/-- 一个 proof-carrying 单元素谓词的纯成员规格具有 admissible 候选存在式。 -/
theorem membership_specification_exists_admissible (predicate : SetPredicate) :
    Formula.Admissible (∃ₘ[SetSort.set],
        ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ
            predicate.body) := by
  have hPredicate := predicate.admissible_at
  prove_admissible
/--
`target` 正好由 `source` 中满足 `predicate` 的元素组成。
`source` 与 `target` 应当是 bound-closed 项；谓词体中的 `bₛ#0` 表示当前元素。
-/
def separation_spec (predicate : SetPredicate) (source target : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ target) ↔ₘ ((bₛ#0 ∈ₘ source) ∧ₘ predicate.body)
/-- 对固定母集断言一个分离结果存在。 -/
def separation_exists (predicate : SetPredicate) (source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ source) ∧ₘ predicate.body)
/-- 为分离公理的母集选择一个不污染谓词参数的隐藏自由变量。 -/
def source_parameter (predicate : SetPredicate) : FreeVarId :=
  FreshVariable.fresh_id SetSort.set [predicate.body]
/-- 隐藏母集变量不在谓词体的自由变量支持中。 -/
theorem source_parameter_fresh (predicate : SetPredicate) : (SetSort.set, predicate.source_parameter) freshForₘ
      predicate.body := by
  dsimp [source_parameter]
  exact FreshVariable.fresh_id_not_mem_m (by simp)
/--
分离公理的一个公式实例。
母集先以对谓词参数新鲜的自由变量书写，再由公共关闭操作加入最外层全称量词。
-/
def separation_axiom (predicate : SetPredicate) : SetFormula :=
  ∀ₘ[SetSort.set, predicate.source_parameter],
    predicate.separation_exists (x#predicate.source_parameter)
/-- 在外延理论上加入一个给定谓词的分离公理实例。 -/
def separation_theory (predicate : SetPredicate) : SetTheory :=
  Theory.insert predicate.separation_axiom extensionality_theory
theorem separation_exists_admissible (predicate : SetPredicate) {source : SetTerm} (hSource : Term.Admissible source SetSort.set) :
    Formula.Admissible (predicate.separation_exists source) := by
  have hPredicate := predicate.admissible_at
  prove_admissible
/-- 固定母集与结果项后的分离规格满足公共 proof-layer 边界。 -/
theorem separation_spec_admissible (predicate : SetPredicate) {source target : SetTerm} (hSource : Term.Admissible source SetSort.set)
    (hTarget : Term.Admissible target SetSort.set) :
    Formula.Admissible (predicate.separation_spec source target) := by
  have hPredicate := predicate.admissible_at
  prove_admissible
/-- 分离公理实例满足公共 proof-carrying 良构性边界。 -/
theorem separation_axiom_admissible (predicate : SetPredicate) :
    Formula.Admissible predicate.separation_axiom := by
  apply Formula.Admissible.forall_closeFreeAt
  apply separation_exists_admissible
  exact ⟨
    TermWellSorted.fvar (σ := signature) SetSort.set
      predicate.source_parameter,
    TermScoped.fvar (σ := signature) (ctx := (Scope.empty : Scope signature))
      SetSort.set predicate.source_parameter⟩
/-- 参数化分离公理向自然演绎默认参数公开可计算合法证书。 -/
@[formula_check]
theorem separation_axiom_check (predicate : SetPredicate) :
    Formula.CheckCertificate predicate.separation_axiom :=
  Formula.check_certificate_of_admissible
    (separation_axiom_admissible predicate)
/-- 单个分离实例扩张后的理论仍然 admissible。 -/
theorem separation_theory_admissible (predicate : SetPredicate) :
    Theory.Admissible predicate.separation_theory :=
  Theory.admissible_insert (separation_axiom_admissible predicate)
    extensionality_theory_admissible
/-- 分离公理可在任意自由母集参数处给出一个结果集。 -/
theorem separation_exists_of_axiom
    {T : SetTheory} {Γ : Context signature} (predicate : SetPredicate) (source : SetTerm) (hSource : Term.Admissible source SetSort.set) (hAxiom :
      Γ ⊢ₘ[T] predicate.separation_axiom) :
    Γ ⊢ₘ[T] predicate.separation_exists source := by
  have hInstance :=
    FirstOrder.Derives.forall_elim
      (term := source) hAxiom
  have hBodyFixed :
      Formula.substituteFree SetSort.set
          predicate.source_parameter source
          predicate.body =
        predicate.body :=
    Formula.substituteFree_eq_self_of_not_mem
      SetSort.set predicate.source_parameter
      source predicate.body
      predicate.source_parameter_fresh
  simpa [separation_axiom,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    separation_exists, Formula.substituteFree,
    Term.substituteFree, hBodyFixed] using hInstance
/-- 分离理论成员可在任意自由母集参数处给出一个结果集。 -/
theorem separation_exists_derives (predicate : SetPredicate) (source : FreeVarId) :
    ⊢ₘ[predicate.separation_theory]
      predicate.separation_exists (x#source) := by
  exact separation_exists_of_axiom
    predicate (x#source) (set_variable_admissible source) (FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl))
/--
同一谓词从同一母集分离出的两个结果相等。
元素变量由 `separation_spec` 的 bound 层承担，因此接口不需要任何 freshness 参数。
-/
theorem separation_unique_of_admissible (predicate : SetPredicate) (source left right : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[extensionality_theory]
      predicate.separation_spec source left ⟶ₘ
        predicate.separation_spec source right ⟶ₘ (left ≐ₘ right) := by
  let left_spec :=
    predicate.separation_spec source left
  let right_spec :=
    predicate.separation_spec source right
  let agreement_body : SetFormula := (bₛ#0 ∈ₘ left) ↔ₘ (bₛ#0 ∈ₘ right)
  let element :=
    FreshVariable.fresh_id SetSort.set
      [left_spec, right_spec, agreement_body]
  have hElementFreshLeft : (SetSort.set, element) freshForₘ left_spec := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshRight : (SetSort.set, element) freshForₘ right_spec := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hElementFreshAgreement : (SetSort.set, element) freshForₘ agreement_body := by
    dsimp [element]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hSourceOpen :
      Term.openAt SetSort.set 0 (x#element) source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) source hSource.2
  have hLeftOpen :
      Term.openAt SetSort.set 0 (x#element) left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 (x#element) right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#element) right hRight.2
  have hLeftSpecAdmissible :
      Formula.Admissible left_spec := by
    dsimp [left_spec]
    exact predicate.separation_spec_admissible hSource hLeft
  have hRightSpecAdmissible :
      Formula.Admissible right_spec := by
    dsimp [right_spec]
    exact predicate.separation_spec_admissible hSource hRight
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hLeftAssumption :
      [right_spec, left_spec] ⊢ₘ
        left_spec :=
    .assumption (by simp)
  have hRightAssumption :
      [right_spec, left_spec] ⊢ₘ
        right_spec :=
    .assumption (by simp)
  have hLeftAt :=
    FirstOrder.Derives.forall_elim
      (term := (x#element : SetTerm)) hLeftAssumption
  have hRightAt :=
    FirstOrder.Derives.forall_elim
      (term := (x#element : SetTerm)) hRightAssumption
  let predicate_at : SetFormula :=
    Formula.openAt SetSort.set 0 (x#element) predicate.body
  let common : SetFormula := (x#element ∈ₘ source) ∧ₘ predicate_at
  have hElement := set_variable_admissible element
  have hElementMemLeft :
      Formula.Admissible (x#element ∈ₘ left) :=
    membership_formula_admissible hElement hLeft
  have hElementMemRight :
      Formula.Admissible (x#element ∈ₘ right) :=
    membership_formula_admissible hElement hRight
  have hLeftAtNormalized :
      [right_spec, left_spec] ⊢ₘ (x#element ∈ₘ left) ↔ₘ common := by
    simpa [left_spec, separation_spec, common, predicate_at,
      Formula.openAt, Term.openAt,
      hSourceOpen, hLeftOpen] using hLeftAt
  have hRightAtNormalized :
      [right_spec, left_spec] ⊢ₘ (x#element ∈ₘ right) ↔ₘ common := by
    simpa [right_spec, separation_spec, common, predicate_at,
      Formula.openAt, Term.openAt,
      hSourceOpen, hRightOpen] using hRightAt
  have hAgreementAtNormalized :
      [right_spec, left_spec] ⊢ₘ (x#element ∈ₘ left) ↔ₘ (x#element ∈ₘ right) := by
    apply FirstOrder.Derives.iffIntro
    · have hLeft :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ left)
          hLeftAtNormalized
      have hRight :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ left)
          hRightAtNormalized
      have hCommon :=
        FirstOrder.Derives.iffElimRight hLeft
          (.assumption (by simp))
      exact FirstOrder.Derives.iffElimLeft hRight hCommon
    · have hLeft :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ right)
          hLeftAtNormalized
      have hRight :=
        FirstOrder.Derives.context_weaken_cons (assumption := x#element ∈ₘ right)
          hRightAtNormalized
      have hCommon :=
        FirstOrder.Derives.iffElimRight hRight
          (.assumption (by simp))
      exact FirstOrder.Derives.iffElimLeft hLeft hCommon
  have hAgreementAt :
      [right_spec, left_spec] ⊢ₘ
        Formula.openAt SetSort.set 0 (x#element) agreement_body := by
    simpa [agreement_body, Formula.openAt, Term.openAt,
      hLeftOpen, hRightOpen] using
      hAgreementAtNormalized
  have hAgreementEmpty :
      [right_spec, left_spec] ⊢ₘ
        membership_agreement left right := by
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := (Theory.empty : SetTheory)) (Γ := [right_spec, left_spec]) (sort := SetSort.set) (eigen := element) (body :=
          Formula.openAt SetSort.set 0 (x#element) agreement_body) (by
          intro formula hFormula
          cases hFormula) (by
          intro formula hFormula
          rcases List.mem_cons.mp hFormula with rfl | hFormula
          · exact hElementFreshRight
          · rcases List.mem_cons.mp hFormula with rfl | hFormula
            · exact hElementFreshLeft
            · exact False.elim (List.not_mem_nil hFormula))
        hAgreementAt
    simpa [membership_agreement, agreement_body,
      Formula.closeFreeAt_openAt
        SetSort.set element 0 agreement_body
        hElementFreshAgreement] using hGeneralized
  have hAgreement :
      [right_spec, left_spec] ⊢ₘ[extensionality_theory]
        membership_agreement left right :=
    FirstOrder.Derives.theory_weaken (by simp [Theory.empty])
      hAgreementEmpty
  have hExtensionality :
      [right_spec, left_spec] ⊢ₘ[extensionality_theory]
        extensionality_instance left right :=
    FirstOrder.Derives.context_weaken_cons (assumption := right_spec) <|
      FirstOrder.Derives.context_weaken_cons (assumption := left_spec) <|
        extensionality_instance_derives_of_admissible
          left right hLeft hRight
  exact FirstOrder.Derives.impElim hExtensionality hAgreement
/-- 自由变量版本的分离唯一性接口。 -/
theorem separation_unique (predicate : SetPredicate) (source left right : FreeVarId) :
    ⊢ₘ[extensionality_theory]
      predicate.separation_spec (x#source) (x#left) ⟶ₘ
        predicate.separation_spec (x#source) (x#right) ⟶ₘ (x#left ≐ₘ x#right) :=
  separation_unique_of_admissible
    predicate (x#source) (x#left) (x#right) (set_variable_admissible source) (set_variable_admissible left) (set_variable_admissible right)
end SetPredicate
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
