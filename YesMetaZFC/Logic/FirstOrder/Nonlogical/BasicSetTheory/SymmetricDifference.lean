import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.PowerSetCoding
/-!
# 对称差运算
本模块建立集合对称差的公共对象语言函数项 `sym_diffₘ(left, right)`。定义直接采用
逐元素异或规格，并以 `left ∪ₘ right` 为分离母集。
文献记号 `Δ*` 保留为索引。有限自然数幂集上的对称差群、关系搬运和序结构结论
暂留文档，不把证明辅助公式提升为新的语法设施。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 对称差规格 -/
/-- 对称差的单元素成员条件。 -/
def symmetric_difference_member_condition (left right : SetTerm) :
    SetFormula := (((bₛ#0 ∈ₘ left) ∧ₘ
      ¬ₘ (bₛ#0 ∈ₘ right)) ∨ₘ ((bₛ#0 ∈ₘ right) ∧ₘ
      ¬ₘ (bₛ#0 ∈ₘ left)))
/-- 对称差的成员规格。 -/
def symmetric_difference_spec (left right candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate ((bₛ#0 ∈ₘ (left ∪ₘ right)) ∧ₘ
      symmetric_difference_member_condition left right)
/-- 对固定参数断言对称差存在。 -/
def symmetric_difference_separation_exists (left right : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    symmetric_difference_spec left right bₛ#1
/-- 任意两个集合上的对称差分离实例。 -/
def symmetric_difference_separation_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      symmetric_difference_separation_exists (x#0) (x#1)
/-- 对称差函数符号的开放定义实例；文献索引为 `Ξ₅₈`。 -/
def symmetric_difference_definition_instance (left right candidate : SetTerm) :
    SetFormula := (candidate ≐ₘ sym_diffₘ(left, right)) ↔ₘ
    symmetric_difference_spec left right candidate
/-- 对称差函数符号定义公理。 -/
def symmetric_difference_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        symmetric_difference_definition_instance (x#0) (x#1) (x#2)
/-! ## 理论组合 -/
/-- 加入对称差分离实例后的理论。 -/
def symmetric_difference_separation_theory : SetTheory :=
  Theory.insert
    symmetric_difference_separation_axiom
    power_set_bijection_theory
/-- 加入对称差函数符号后的理论。 -/
def symmetric_difference_theory : SetTheory :=
  Theory.insert
    symmetric_difference_definition_axiom
    symmetric_difference_separation_theory
/-! ## proof-carrying 项边界 -/
/-- 对称差项满足 proof-carrying 项边界。 -/
theorem symmetric_difference_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (sym_diffₘ(left, right))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .symmetricDifference [⟨left, by assumption⟩, ⟨right, by assumption⟩]
      (by rfl) (by rfl)
/-- 对称差项的合法性由两个参数项证书计算。 -/
@[term_check]
theorem symmetric_difference_term_check
    {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Term.CheckCertificate (sym_diffₘ(left, right)) SetSort.set :=
  Term.check_admissible_complete <|
    symmetric_difference_term_admissible
      left right hLeft.admissible hRight.admissible
/-! ## 良构性与闭理论边界 -/
theorem symmetric_difference_separation_axiom_admissible :
    Formula.Admissible
      symmetric_difference_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem symmetric_difference_definition_axiom_admissible :
    Formula.Admissible
      symmetric_difference_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem symmetric_difference_separation_theory_admissible :
    Theory.Admissible
      symmetric_difference_separation_theory :=
  Theory.admissible_insert
    symmetric_difference_separation_axiom_admissible
    power_set_bijection_theory_admissible
theorem symmetric_difference_theory_admissible :
    Theory.Admissible
      symmetric_difference_theory :=
  Theory.admissible_insert
    symmetric_difference_definition_axiom_admissible
    symmetric_difference_separation_theory_admissible
@[derive_close_sentence]
theorem symmetric_difference_separation_theory_sentence
    {formula : SetFormula} (hFormula : symmetric_difference_separation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact symmetric_difference_separation_axiom_admissible
    · native_decide
  · exact power_set_bijection_theory_sentence hFormula
@[derive_close_sentence]
theorem symmetric_difference_theory_sentence
    {formula : SetFormula} (hFormula : symmetric_difference_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact symmetric_difference_definition_axiom_admissible
    · native_decide
  · exact symmetric_difference_separation_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem power_set_bijection_theory_subset_symmetric_difference_separation_theory
    {formula : SetFormula} (hFormula : power_set_bijection_theory formula) :
    symmetric_difference_separation_theory formula :=
  Or.inr hFormula
theorem symmetric_difference_separation_theory_subset_symmetric_difference_theory
    {formula : SetFormula} (hFormula : symmetric_difference_separation_theory formula) :
    symmetric_difference_theory formula :=
  Or.inr hFormula
/-! ## 定义扩张的推导接口 -/
/-- 对称差定义公理可在任意三个 admissible 集合项处实例化。 -/
theorem symmetric_difference_definition_instance_derives (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[symmetric_difference_theory]
      symmetric_difference_definition_instance
        left right candidate := by
  have hAxiom :
      ⊢ₘ[symmetric_difference_theory]
        symmetric_difference_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hLeftInstance :=
    FirstOrder.Derives.forall_elim (term := left) hAxiom
  have hRightInstance :=
    FirstOrder.Derives.forall_elim (term := right) hLeftInstance
  have hCandidateInstance :=
    FirstOrder.Derives.forall_elim (term := candidate) hRightInstance
  have hLeftOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  have hCandidateOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term candidate hCandidate.2
  simpa [symmetric_difference_definition_axiom,
    symmetric_difference_definition_instance,
    symmetric_difference_spec,
    symmetric_difference_member_condition,
    membership_specification,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, symmetric_difference_term,
    binary_union_term, hLeftOpen, hRightOpen,
    hCandidateOpen] using hCandidateInstance
/-- 定义扩张中的规范对称差项满足其逐元素规格。 -/
theorem symmetric_difference_term_spec_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[symmetric_difference_theory]
      symmetric_difference_spec
        left right (sym_diffₘ(left, right)) := by
  exact FirstOrder.Derives.iffElimRight (symmetric_difference_definition_instance_derives
      left right (sym_diffₘ(left, right))
      hLeft hRight (symmetric_difference_term_admissible
        left right hLeft hRight))
    (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (sym_diffₘ(left, right)))
/-- 对称差规格在任意 admissible 成员项处的点态实例。 -/
theorem symmetric_difference_spec_membership_iff
    {T : SetTheory} {Γ : Context signature} (left right candidate member : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) (hMember : Term.Admissible member SetSort.set) (hSpec :
      Γ ⊢ₘ[T]
        symmetric_difference_spec left right candidate) :
    Γ ⊢ₘ[T] (member ∈ₘ candidate) ↔ₘ ((member ∈ₘ (left ∪ₘ right)) ∧ₘ (((member ∈ₘ left) ∧ₘ
              ¬ₘ (member ∈ₘ right)) ∨ₘ ((member ∈ₘ right) ∧ₘ
              ¬ₘ (member ∈ₘ left)))) := by
  have hAt :=
    FirstOrder.Derives.forall_elim (term := member) hSpec
  have hLeftOpen :
      Term.openAt SetSort.set 0 member left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 member left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 member right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 member right hRight.2
  have hCandidateOpen :
      Term.openAt SetSort.set 0 member candidate =
        candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 member candidate hCandidate.2
  simpa [symmetric_difference_spec,
    symmetric_difference_member_condition,
    membership_specification,
    Formula.openAt, Term.openAt,
    hLeftOpen, hRightOpen, hCandidateOpen] using hAt
/-!
## 待证明定理索引
* 定义 3.32：文献 `Δ*` 与公共项 `sym_diffₘ` 的对应合同；
* 定理 3.50：自然数幂集上的对称差与二值函数编码的相容性；
* 后续由 `chiₘ` 搬运到幂集上的群运算、关系和序结构。
纸面 `Θ₁₃₀₇`、`Θ₁₃₁₀a`、`Θ₁₃₁₀b` 与 `Θ₁₃₂₈a`--`Θ₁₃₂₈e`
只保留为证明索引；公共定义由 `symmetric_difference_spec` 和
`power_set_bijection_spec` 完整表达。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
