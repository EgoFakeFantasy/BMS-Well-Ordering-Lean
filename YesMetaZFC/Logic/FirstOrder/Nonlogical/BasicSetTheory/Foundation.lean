import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Ordinal
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure
/-!
# ε-极小公理模式
本模块把文献的“ε-极小原理”实现为真正的开放公理模式。输入是一个
proof-carrying `SetPredicate`：
* `bₛ#0` 表示被考察的集合；
* 其余参数保持为自由变量；
* 公理生成器自动关闭全部自由参数；
* 生成结果同时携带 admissibility 与 sentence 证明。
文献中的 `n ≤ 2050` 只服务于纸面有限编号，不进入核心接口。这里允许任意有限
自由变量支持，也不把后续使用到的三个具体公式写成特判分支。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 标准有限编码所需的有限基础接口 -/
/--
成员关系反自反公理。
完整正则公理当然推出该句；编码层实际只消费这一条有限后果，因此把它单独暴露为
有限支持接口，避免为标准有限序列的良基性永久携带整个谓词模式。
-/
def membership_irreflexive_axiom : SetFormula :=
  ∀ₘ[SetSort.set], ¬ₘ (bₛ#0 ∈ₘ bₛ#0)
/-- 只含成员反自反公理的有限理论。 -/
def membership_irreflexive_theory : SetTheory :=
  Theory.singleton membership_irreflexive_axiom
/-- 成员反自反公理满足公共句法边界。 -/
theorem membership_irreflexive_axiom_admissible :
    Formula.Admissible membership_irreflexive_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 成员反自反公理是闭句。 -/
theorem membership_irreflexive_axiom_sentence :
    Formula.Sentence membership_irreflexive_axiom :=
  ⟨membership_irreflexive_axiom_admissible, by native_decide⟩
/-- 成员反自反有限理论只含闭句。 -/
@[derive_close_sentence]
theorem membership_irreflexive_theory_sentence
    {formula : SetFormula} (hFormula : membership_irreflexive_theory formula) :
    Formula.Sentence formula := by
  rw [membership_irreflexive_theory, Theory.singleton] at hFormula
  subst formula
  exact membership_irreflexive_axiom_sentence
/-- 成员反自反接口是单公理有限理论。 -/
theorem membership_irreflexive_theory_finitely_axiomatized :
    Theory.FinitelyAxiomatized membership_irreflexive_theory :=
  Theory.finitely_axiomatized_singleton _
/-- 任意 admissible 闭项都可实例化成员反自反公理。 -/
theorem membership_irreflexive_instance_derives (term : SetTerm) (hTerm : Term.Admissible term SetSort.set) :
    ⊢ₘ[membership_irreflexive_theory]
      ¬ₘ (term ∈ₘ term) := by
  have hAxiom :
      ⊢ₘ[membership_irreflexive_theory]
        membership_irreflexive_axiom :=
    FirstOrder.Derives.theory_mem (by simp [membership_irreflexive_theory, Theory.singleton])
  have hInstance :=
    FirstOrder.Derives.forall_elim (term := term) hAxiom
  simpa [membership_irreflexive_axiom,
    Formula.openAt, Term.openAt] using hInstance
namespace SetPredicate
/--
ε-极小原理的开放核心。
若存在满足 `predicate` 的集合，则存在一个同样满足它的集合，使其任何成员都不再
满足该谓词。第二个存在量词下的 `bₛ#0` 是候选极小元；最内层全称量词下，
`bₛ#0` 是候选的成员，`bₛ#1` 是候选本身。
-/
def epsilon_minimal_core (predicate : SetPredicate) :
    SetFormula := (∃ₘ[SetSort.set], predicate.body) ⟶ₘ (∃ₘ[SetSort.set],
      predicate.body ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ⟶ₘ
            ¬ₘ predicate.body))
/--
由任意良构谓词生成闭的 ε-极小公理。
闭包参数直接取开放核心的完整自由变量支持，允许重复成员而不影响语义。
-/
def epsilon_minimal_axiom (predicate : SetPredicate) :
    SetFormula :=
  Metatheory.Formula.forall_close (Formula.freeSupport predicate.epsilon_minimal_core).eraseDups
    predicate.epsilon_minimal_core
/-- ε-极小原理的开放核心满足 proof-carrying 公式边界。 -/
theorem epsilon_minimal_core_admissible (predicate : SetPredicate) :
    Formula.Admissible
      predicate.epsilon_minimal_core := by
  have hPredicate := predicate.admissible_at
  prove_admissible
/-- 每个模式实例都是闭的 admissible 句子。 -/
theorem epsilon_minimal_axiom_sentence (predicate : SetPredicate) :
    Formula.Sentence
      predicate.epsilon_minimal_axiom :=
  Metatheory.Formula.forall_close_eraseDups_freeSupport_sentence
    predicate.epsilon_minimal_core (epsilon_minimal_core_admissible predicate)
/-- 每个模式实例满足公共 admissibility 边界。 -/
theorem epsilon_minimal_axiom_admissible (predicate : SetPredicate) :
    Formula.Admissible
      predicate.epsilon_minimal_axiom := (epsilon_minimal_axiom_sentence predicate).1
/-- 参数化 ε-极小公理向自然演绎默认参数公开可计算合法证书。 -/
@[formula_check]
theorem epsilon_minimal_axiom_check (predicate : SetPredicate) :
    Formula.CheckCertificate
      predicate.epsilon_minimal_axiom :=
  Formula.check_certificate_of_admissible
    predicate.epsilon_minimal_axiom_admissible
end SetPredicate
/-! ## 公理模式与理论组合 -/
/--
全部 ε-极小公理实例组成的理论模式。
成员证书显式携带生成它的 `SetPredicate`，因此自动化和后续证明层可以恢复原始
谓词，而不需要依赖公式字符串或文献编号。
-/
def epsilon_minimal_schema : SetTheory :=
  fun formula =>
    ∃ predicate : SetPredicate,
      formula = predicate.epsilon_minimal_axiom
/-- 在序数与自然数定义理论上加入 ε-极小公理模式。 -/
def foundation_theory : SetTheory :=
  fun formula =>
    ordinal_natural_theory formula ∨
      epsilon_minimal_schema formula
/-- 任意生成的 ε-极小公理都属于模式理论。 -/
theorem epsilon_minimal_axiom_mem (predicate : SetPredicate) :
    epsilon_minimal_schema
      predicate.epsilon_minimal_axiom :=
  ⟨predicate, rfl⟩
/-- 任意生成的 ε-极小公理都属于最终基础理论。 -/
theorem epsilon_minimal_axiom_mem_foundation_theory (predicate : SetPredicate) :
    foundation_theory
      predicate.epsilon_minimal_axiom :=
  Or.inr (epsilon_minimal_axiom_mem predicate)
/-- ε-极小公理模式中的每个成员都满足公共良构性边界。 -/
theorem epsilon_minimal_schema_admissible :
    Theory.Admissible
      epsilon_minimal_schema := by
  intro formula hFormula
  rcases hFormula with ⟨predicate, rfl⟩
  exact predicate.epsilon_minimal_axiom_admissible
/-- 加入 ε-极小公理模式后的理论仍然 admissible。 -/
theorem foundation_theory_admissible :
    Theory.Admissible
      foundation_theory := by
  intro formula hFormula
  rcases hFormula with hFormula | hFormula
  · exact ordinal_natural_theory_admissible
      formula hFormula
  · exact epsilon_minimal_schema_admissible
      formula hFormula
/-! ## 闭理论边界 -/
/-- ε-极小公理模式中的每个成员都是闭句。 -/
@[derive_close_sentence]
theorem epsilon_minimal_schema_sentence
    {formula : SetFormula} (hFormula : epsilon_minimal_schema formula) :
    Formula.Sentence formula := by
  rcases hFormula with ⟨predicate, rfl⟩
  exact predicate.epsilon_minimal_axiom_sentence
/-- 最终基础理论中的每条公理都是闭句。 -/
@[derive_close_sentence]
theorem foundation_theory_sentence
    {formula : SetFormula} (hFormula : foundation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with hFormula | hFormula
  · exact ordinal_natural_theory_sentence hFormula
  · exact epsilon_minimal_schema_sentence hFormula
/-! ## 理论嵌入与直接消费接口 -/
theorem ordinal_natural_theory_subset_foundation_theory
    {formula : SetFormula} (hFormula : ordinal_natural_theory formula) :
    foundation_theory formula :=
  Or.inl hFormula
theorem epsilon_minimal_schema_subset_foundation_theory
    {formula : SetFormula} (hFormula : epsilon_minimal_schema formula) :
    foundation_theory formula :=
  Or.inr hFormula
/-- 任意模式实例都可由最终基础理论直接调用。 -/
theorem epsilon_minimal_axiom_derives (predicate : SetPredicate) :
    ⊢ₘ[foundation_theory]
      predicate.epsilon_minimal_axiom :=
  FirstOrder.Derives.theory_mem (epsilon_minimal_axiom_mem_foundation_theory predicate)
/-!
## 待证明定理索引
文献在本模式上给出的结论暂留为后续证明任务：
* 定理 3.29：不存在两元素成员循环；
* 推论 3.6：单点集不属于其元素，且后继运算保持不等；
* 定理 3.30：每个非空集合含有与自身不交的成员；
* 推论 3.7：每个非空传递集含有空集。
文献中的 `ψ₁₆`、`ψ₁₇`、`ψ₁₈` 只是 `SetPredicate` 的具体实例。后续证明时应直接
构造对应谓词并消费 `epsilon_minimal_axiom_derives`，不为这些结论增加专用公理。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
