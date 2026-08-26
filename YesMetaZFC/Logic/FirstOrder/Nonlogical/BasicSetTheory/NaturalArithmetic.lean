import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalSetTheory
/-!
# 基础无穷集合与自然数算术设施
本模块吸收无穷集合章节剩余的基础定义层：
* 自然数加法、乘法、幂与截断减法；
* 集合上的有限序列空间、递归序列空间与 `ω`-递归序列；
* 无限、可数、不可数与可数无限谓词；
* `ω × ω` 上的典型序以及 Gödel 配对编码。
所有公共名称都采用现代记号。文献中的 `+`、乘法、幂、`YXXL`、`DGXL`、
`DGDY`、`Δ`、`GP` 等只保留在注释索引中。文献中的 `ψ` 辅助公式与本节
后续定理暂留证明层，不把一次性证明展开污染公共签名。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 自然数算术 -/
/-- 加法递归图的条件。 -/
def natural_addition_graph_condition (left right result graph : SetTerm) :
    SetFormula :=
  is_mapping_formula graph (Sₘ(left)) ωₘ ∧ₘ ((graph ·ₘ ∅ₘ ≐ₘ right) ∧ₘ ((∀ₘ[SetSort.set], (bₛ#0 ∈ₘ left) ⟶ₘ ((graph ·ₘ Sₘ(bₛ#0)) ≐ₘ
              Sₘ(graph ·ₘ bₛ#0))) ∧ₘ (graph ·ₘ left ≐ₘ result)))
/--
加法存在见证的 locally nameless 版本。
外层 `bₛ#0` 是递归图；进入内部指标量词后，递归图必须提升为 `bₛ#1`。
把这一层显式写出可避免匿名存在量词下的变量捕获。
-/
def natural_addition_bound_graph_condition (left right result : SetTerm) :
    SetFormula :=
  is_mapping_formula bₛ#0 (Sₘ(left)) ωₘ ∧ₘ ((bₛ#0 ·ₘ ∅ₘ ≐ₘ right) ∧ₘ ((∀ₘ[SetSort.set], (bₛ#0 ∈ₘ left) ⟶ₘ ((bₛ#1 ·ₘ Sₘ(bₛ#0)) ≐ₘ
              Sₘ(bₛ#1 ·ₘ bₛ#0))) ∧ₘ (bₛ#0 ·ₘ left ≐ₘ result)))
/-- 加法项的递归规格。 -/
def natural_addition_spec (left right result : SetTerm) :
    SetFormula := (result ∈ₘ ωₘ) ∧ₘ (∃ₘ[SetSort.set],
      natural_addition_bound_graph_condition
        left right result)
/-- 自然数加法定义实例；文献索引为 `Ξ₆₉`。 -/
def natural_addition_definition_instance (left right result : SetTerm) :
    SetFormula := ((left ∈ₘ ωₘ) ∧ₘ (right ∈ₘ ωₘ)) ⟶ₘ ((result ≐ₘ (left +ₘ right)) ↔ₘ
      natural_addition_spec left right result)
/-- 自然数加法定义公理。 -/
def natural_addition_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        natural_addition_definition_instance (x#0) (x#1) (x#2)
/-- 乘法递归图的条件。 -/
def natural_multiplication_graph_condition (left right result graph : SetTerm) :
    SetFormula :=
  is_mapping_formula graph (Sₘ(left)) ωₘ ∧ₘ ((graph ·ₘ ∅ₘ ≐ₘ ∅ₘ) ∧ₘ ((∀ₘ[SetSort.set], (bₛ#0 ∈ₘ left) ⟶ₘ ((graph ·ₘ Sₘ(bₛ#0)) ≐ₘ ((graph ·ₘ bₛ#0) +ₘ right))) ∧ₘ
        (graph ·ₘ left ≐ₘ result)))
/-- 乘法存在见证的无捕获 locally nameless 版本。 -/
def natural_multiplication_bound_graph_condition (left right result : SetTerm) :
    SetFormula :=
  is_mapping_formula bₛ#0 (Sₘ(left)) ωₘ ∧ₘ ((bₛ#0 ·ₘ ∅ₘ ≐ₘ ∅ₘ) ∧ₘ ((∀ₘ[SetSort.set], (bₛ#0 ∈ₘ left) ⟶ₘ ((bₛ#1 ·ₘ Sₘ(bₛ#0)) ≐ₘ ((bₛ#1 ·ₘ bₛ#0) +ₘ right))) ∧ₘ
        (bₛ#0 ·ₘ left ≐ₘ result)))
/-- 乘法项的递归规格。 -/
def natural_multiplication_spec (left right result : SetTerm) :
    SetFormula := (result ∈ₘ ωₘ) ∧ₘ (∃ₘ[SetSort.set],
      natural_multiplication_bound_graph_condition
        left right result)
/-- 自然数乘法定义实例；文献索引为 `Ξ₇₀`。 -/
def natural_multiplication_definition_instance (left right result : SetTerm) :
    SetFormula := ((left ∈ₘ ωₘ) ∧ₘ (right ∈ₘ ωₘ)) ⟶ₘ ((result ≐ₘ (left *ₘ right)) ↔ₘ
      natural_multiplication_spec left right result)
/-- 自然数乘法定义公理。 -/
def natural_multiplication_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        natural_multiplication_definition_instance (x#0) (x#1) (x#2)
/-- 幂运算递归图的条件。 -/
def natural_exponentiation_graph_condition (base exponent result graph : SetTerm) :
    SetFormula :=
  is_mapping_formula graph (Sₘ(exponent)) ωₘ ∧ₘ ((graph ·ₘ ∅ₘ ≐ₘ Sₘ(∅ₘ)) ∧ₘ ((∀ₘ[SetSort.set], (bₛ#0 ∈ₘ exponent) ⟶ₘ ((graph ·ₘ Sₘ(bₛ#0)) ≐ₘ
              ((graph ·ₘ bₛ#0) *ₘ base))) ∧ₘ (graph ·ₘ exponent ≐ₘ result)))
/-- 幂运算存在见证的无捕获 locally nameless 版本。 -/
def natural_exponentiation_bound_graph_condition (base exponent result : SetTerm) :
    SetFormula :=
  is_mapping_formula bₛ#0 (Sₘ(exponent)) ωₘ ∧ₘ ((bₛ#0 ·ₘ ∅ₘ ≐ₘ Sₘ(∅ₘ)) ∧ₘ ((∀ₘ[SetSort.set], (bₛ#0 ∈ₘ exponent) ⟶ₘ ((bₛ#1 ·ₘ Sₘ(bₛ#0)) ≐ₘ
              ((bₛ#1 ·ₘ bₛ#0) *ₘ base))) ∧ₘ (bₛ#0 ·ₘ exponent ≐ₘ result)))
/-- 幂运算项的递归规格。 -/
def natural_exponentiation_spec (base exponent result : SetTerm) :
    SetFormula := (result ∈ₘ ωₘ) ∧ₘ (∃ₘ[SetSort.set],
      natural_exponentiation_bound_graph_condition
        base exponent result)
/-- 自然数幂定义实例；文献索引为 `Ξ₇₁`。 -/
def natural_exponentiation_definition_instance (base exponent result : SetTerm) :
    SetFormula := ((base ∈ₘ ωₘ) ∧ₘ (exponent ∈ₘ ωₘ)) ⟶ₘ ((result ≐ₘ base ^ₘ exponent) ↔ₘ
      natural_exponentiation_spec base exponent result)
/-- 自然数幂定义公理。 -/
def natural_exponentiation_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        natural_exponentiation_definition_instance (x#0) (x#1) (x#2)
/-- 截断减法递归图的条件。 -/
def natural_difference_graph_condition (left right result graph : SetTerm) :
    SetFormula :=
  is_mapping_formula graph (Sₘ(right)) ωₘ ∧ₘ ((graph ·ₘ ∅ₘ ≐ₘ left) ∧ₘ ((∀ₘ[SetSort.set], (bₛ#0 ∈ₘ right) ⟶ₘ (((graph ·ₘ bₛ#0 ≐ₘ ∅ₘ) ∧ₘ
                (graph ·ₘ Sₘ(bₛ#0) ≐ₘ ∅ₘ)) ∨ₘ (∃ₘ[SetSort.set], ((graph ·ₘ bₛ#1 ≐ₘ Sₘ(bₛ#0)) ∧ₘ (graph ·ₘ Sₘ(bₛ#1) ≐ₘ bₛ#0))))) ∧ₘ (graph ·ₘ right ≐ₘ result)))
/-- 截断减法项的递归规格。 -/
def natural_difference_spec (left right result : SetTerm) :
    SetFormula := (result ∈ₘ ωₘ) ∧ₘ (∃ₘ[SetSort.set],
      natural_difference_graph_condition
        left right result bₛ#0)
/-- 自然数截断减法定义实例；文献索引为 `Ξ₇₉`。 -/
def natural_difference_definition_instance (left right result : SetTerm) :
    SetFormula := ((left ∈ₘ ωₘ) ∧ₘ (right ∈ₘ ωₘ)) ⟶ₘ ((result ≐ₘ (left -ₘ right)) ↔ₘ
      natural_difference_spec left right result)
/-- 自然数截断减法定义公理。 -/
def natural_difference_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        natural_difference_definition_instance (x#0) (x#1) (x#2)
/-! ## 有限序列与递归序列 -/
/-- 有限序列成员条件：它是某个自然数段到 `source` 的映射。 -/
def finite_sequence_member_condition (source sequence : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set], ((bₛ#0 ∈ₘ ωₘ) ∧ₘ
      is_mapping_formula sequence bₛ#0 source)
/--
有限序列空间的成员规格。
外层全称量词绑定候选序列，内层存在量词绑定其有限定义域，因此映射条件中的
候选序列必须写作 `bₛ#1`，定义域写作 `bₛ#0`。这里不把外层 `bₛ#0` 直接传入
会再开 binder 的 `finite_sequence_member_condition`，以免 locally nameless 捕获。
-/
def finite_sequence_space_spec (source candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ candidate) ↔ₘ (∃ₘ[SetSort.set], ((bₛ#0 ∈ₘ ωₘ) ∧ₘ
          is_mapping_formula bₛ#1 bₛ#0 source))
/-- 有限序列空间函数项的开放定义实例；文献索引为 `YXXL`。 -/
def finite_sequence_space_definition_instance (source candidate : SetTerm) :
    SetFormula := (source ≠ₘ ∅ₘ) ⟶ₘ ((candidate ≐ₘ seq_spaceₘ(source)) ↔ₘ
      finite_sequence_space_spec source candidate)
/-- 有限序列空间定义公理。 -/
def finite_sequence_space_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      finite_sequence_space_definition_instance (x#0) (x#1)
/-- 递归序列成员的步进条件。 -/
def recursive_sequence_step_condition (source seed recursion sequence : SetTerm) :
    SetFormula := (⟨∅ₘ, seed⟩ₘ ∈ₘ sequence) ∧ₘ (∀ₘ[SetSort.set], ((bₛ#0 ∈ₘ domₘ(sequence)) ∧ₘ (Sₘ(bₛ#0) ∈ₘ domₘ(sequence))) ⟶ₘ (∃ₘ[SetSort.set],
          ∃ₘ[SetSort.set], ((bₛ#0 ∈ₘ source) ∧ₘ ((bₛ#1 ∈ₘ source) ∧ₘ ((⟨bₛ#2, bₛ#1⟩ₘ ∈ₘ sequence) ∧ₘ ((⟨Sₘ(bₛ#2), bₛ#0⟩ₘ ∈ₘ sequence) ∧ₘ (⟨⟨bₛ#1, bₛ#2⟩ₘ,
                      bₛ#0⟩ₘ ∈ₘ recursion)))))))
/-- 递归序列空间的成员规格。 -/
def recursive_sequence_member_condition (source seed recursion sequence : SetTerm) :
    SetFormula :=
  finite_sequence_member_condition source sequence ∧ₘ
    recursive_sequence_step_condition
      source seed recursion sequence
/-- 递归序列空间规格。 -/
def recursive_sequence_space_spec (source seed recursion candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ candidate) ↔ₘ
      recursive_sequence_member_condition
        source seed recursion bₛ#0
/-- 递归序列空间函数项的开放定义实例；文献索引为 `DGXL`。 -/
def recursive_sequence_space_definition_instance (source seed recursion candidate : SetTerm) :
    SetFormula := ((seed ∈ₘ source) ∧ₘ
      is_mapping_formula recursion (source ×ₘ ωₘ) source) ⟶ₘ ((candidate ≐ₘ
        rec_seq_spaceₘ(source, seed, recursion)) ↔ₘ
      recursive_sequence_space_spec
        source seed recursion candidate)
/-- 递归序列空间定义公理。 -/
def recursive_sequence_space_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          recursive_sequence_space_definition_instance (x#0) (x#1) (x#2) (x#3)
/-- `ω`-递归序列的规格。 -/
def omega_recursive_sequence_spec (source seed recursion candidate : SetTerm) :
    SetFormula :=
  candidate ≐ₘ
    ⋃ₘ rec_seq_spaceₘ(source, seed, recursion)
/-- `ω`-递归序列函数项的开放定义实例；文献索引为 `DGDY`。 -/
def omega_recursive_sequence_definition_instance (source seed recursion candidate : SetTerm) :
    SetFormula := ((seed ∈ₘ source) ∧ₘ
      is_mapping_formula recursion (source ×ₘ ωₘ) source) ⟶ₘ ((candidate ≐ₘ
        ω_rec_seqₘ(source, seed, recursion)) ↔ₘ
      omega_recursive_sequence_spec
        source seed recursion candidate)
/-- `ω`-递归序列函数定义公理。 -/
def omega_recursive_sequence_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          omega_recursive_sequence_definition_instance (x#0) (x#1) (x#2) (x#3)
/-! ## 无限性与可数性 -/
/-- 无限集条件：不与任何自然数等势。文献索引为 `WuQn`。 -/
def is_infinite_condition (set : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ ωₘ) ⟶ₘ
      ¬ₘ (set ≈ₘ bₛ#0)
/-- 可数集条件：存在从 `ω` 到该集合的满射。文献索引为 `KeSu`。 -/
def is_countable_condition (set : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    is_surjective_formula bₛ#0 ωₘ set
/-- 不可数集条件。文献索引为 `BKeS`。 -/
def is_uncountable_condition (set : SetTerm) :
    SetFormula :=
  ¬ₘ is_countable_condition set
/-- 可数无限集条件：与 `ω` 等势。文献索引为 `KSWQ`。 -/
def is_countably_infinite_condition (set : SetTerm) :
    SetFormula :=
  set ≈ₘ ωₘ
/-- 无限集谓词定义实例。 -/
def is_infinite_definition_instance (set : SetTerm) :
    SetFormula :=
  infiniteₘ(set) ↔ₘ
    is_infinite_condition set
/-- 可数集谓词定义实例。 -/
def is_countable_definition_instance (set : SetTerm) :
    SetFormula :=
  countableₘ(set) ↔ₘ
    is_countable_condition set
/-- 不可数集谓词定义实例。 -/
def is_uncountable_definition_instance (set : SetTerm) :
    SetFormula :=
  uncountableₘ(set) ↔ₘ
    is_uncountable_condition set
/-- 可数无限集谓词定义实例。 -/
def is_countably_infinite_definition_instance (set : SetTerm) :
    SetFormula :=
  countably_infiniteₘ(set) ↔ₘ
    is_countably_infinite_condition set
/-- 无限集谓词定义公理。 -/
def is_infinite_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_infinite_definition_instance (x#0)
/-- 可数集谓词定义公理。 -/
def is_countable_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_countable_definition_instance (x#0)
/-- 不可数集谓词定义公理。 -/
def is_uncountable_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_uncountable_definition_instance (x#0)
/-- 可数无限集谓词定义公理。 -/
def is_countably_infinite_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_countably_infinite_definition_instance (x#0)
/-! ## `ω × ω` 的典型序与 Gödel 编码 -/
/-- 两个自然数的非严格小于等价式。 -/
def natural_leq_condition (left right : SetTerm) :
    SetFormula := (left ≐ₘ right) ∨ₘ (left ∈ₘ right)
/-- `ω × ω` 上的典型序条件；文献索引为 `Θω`。 -/
def omega_pair_less_condition (left right : SetTerm) :
    SetFormula := ((left ∈ₘ (ωₘ ×ₘ ωₘ)) ∧ₘ (right ∈ₘ (ωₘ ×ₘ ωₘ))) ⟶ₘ ((¬ₘ (maxεₘ(ωₘ, left) ∈ₘ maxεₘ(ωₘ, right))) ⟶ₘ
      ((¬ₘ ((maxεₘ(ωₘ, left) ≐ₘ maxεₘ(ωₘ, right)) ∧ₘ ((left)₀ₘ ∈ₘ (right)₀ₘ))) ⟶ₘ ((maxεₘ(ωₘ, left) ≐ₘ maxεₘ(ωₘ, right)) ∧ₘ (((left)₀ₘ ≐ₘ (right)₀ₘ) ∧ₘ
            ((left)₁ₘ ∈ₘ (right)₁ₘ)))))
/-- `ω × ω` 典型序定义实例；文献索引为 `Ξ₈₁`。 -/
def omega_pair_less_definition_instance (left right : SetTerm) :
    SetFormula :=
  omega_pair_less_formula left right ↔ₘ
    omega_pair_less_condition left right
/-- `ω × ω` 典型序定义公理。 -/
def omega_pair_less_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      omega_pair_less_definition_instance (x#0) (x#1)
/-- Gödel 配对函数条件；文献索引为 `GP`。 -/
def godel_pairing_condition (pair candidate : SetTerm) :
    SetFormula := (candidate ∈ₘ ωₘ) ∧ₘ ((((pair)₀ₘ ∈ₘ (pair)₁ₘ) ⟶ₘ (candidate ≐ₘ (((pair)₁ₘ ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ (pair)₀ₘ))) ∧ₘ
      ((natural_leq_condition (pair)₁ₘ (pair)₀ₘ) ⟶ₘ (candidate ≐ₘ ((((pair)₀ₘ ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ (pair)₀ₘ) +ₘ (pair)₁ₘ))))
/-- Gödel 配对函数定义实例；文献索引为 `Ξ₈₂`。 -/
def godel_pairing_definition_instance (pair candidate : SetTerm) :
    SetFormula := (pair ∈ₘ (ωₘ ×ₘ ωₘ)) ⟶ₘ ((candidate ≐ₘ godel_pairₘ(pair)) ↔ₘ
      godel_pairing_condition pair candidate)
/-- Gödel 配对函数定义公理。 -/
def godel_pairing_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      godel_pairing_definition_instance (x#0) (x#1)
/-! ## 理论组合 -/
/-- 加入自然数加法定义后的理论。 -/
def natural_addition_theory : SetTheory :=
  Theory.insert
    natural_addition_definition_axiom
    natural_set_theory
/-- 加入自然数乘法定义后的理论。 -/
def natural_multiplication_theory : SetTheory :=
  Theory.insert
    natural_multiplication_definition_axiom
    natural_addition_theory
/-- 加入自然数幂定义后的理论。 -/
def natural_exponentiation_theory : SetTheory :=
  Theory.insert
    natural_exponentiation_definition_axiom
    natural_multiplication_theory
/-- 加入无限性谓词后的理论。 -/
def infinite_predicate_theory : SetTheory :=
  Theory.insert
    is_infinite_definition_axiom
    natural_exponentiation_theory
/-- 加入可数性谓词后的理论。 -/
def countable_predicate_theory : SetTheory :=
  Theory.insert
    is_countable_definition_axiom
    infinite_predicate_theory
/-- 加入不可数性谓词后的理论。 -/
def uncountable_predicate_theory : SetTheory :=
  Theory.insert
    is_uncountable_definition_axiom
    countable_predicate_theory
/-- 加入可数无限谓词后的理论。 -/
def countably_infinite_predicate_theory : SetTheory :=
  Theory.insert
    is_countably_infinite_definition_axiom
    uncountable_predicate_theory
/-- 基础基数分类理论。 -/
def cardinality_classification_theory : SetTheory :=
  countably_infinite_predicate_theory
/-- 加入有限序列空间定义后的理论。 -/
def finite_sequence_space_theory : SetTheory :=
  Theory.insert
    finite_sequence_space_definition_axiom
    cardinality_classification_theory
/-- 加入递归序列空间定义后的理论。 -/
def recursive_sequence_space_theory : SetTheory :=
  Theory.insert
    recursive_sequence_space_definition_axiom
    finite_sequence_space_theory
/-- 加入 `ω`-递归序列定义后的理论。 -/
def omega_recursive_sequence_theory : SetTheory :=
  Theory.insert
    omega_recursive_sequence_definition_axiom
    recursive_sequence_space_theory
/-- 加入自然数截断减法定义后的理论。 -/
def natural_difference_theory : SetTheory :=
  Theory.insert
    natural_difference_definition_axiom
    omega_recursive_sequence_theory
/-- 加入 `ω × ω` 典型序后的理论。 -/
def omega_pair_order_theory : SetTheory :=
  Theory.insert
    omega_pair_less_definition_axiom
    natural_difference_theory
/-- 加入 Gödel 配对函数后的理论。 -/
def godel_pairing_theory : SetTheory :=
  Theory.insert
    godel_pairing_definition_axiom
    omega_pair_order_theory
/-- 基础无穷集合与自然数算术层的稳定入口。 -/
def natural_arithmetic_theory : SetTheory :=
  godel_pairing_theory
/-! ## proof-carrying 项边界 -/
/-- 二元自然数项的 proof-carrying 良构性公共模板。 -/
theorem natural_addition_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (left +ₘ right) SetSort.set := by
  simpa using
    set_function_application_admissible
      .naturalAddition [⟨left, by assumption⟩, ⟨right, by assumption⟩]
      (by rfl) (by rfl)
/-- 自然数加法项的合法性由两个参数证书直接计算。 -/
@[term_check]
theorem natural_addition_term_check {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Term.CheckCertificate (left +ₘ right) SetSort.set :=
  Term.check_admissible_complete <|
    natural_addition_term_admissible left right
      hLeft.admissible hRight.admissible
theorem natural_multiplication_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (left *ₘ right) SetSort.set := by
  simpa using
    set_function_application_admissible
      .naturalMultiplication [⟨left, by assumption⟩, ⟨right, by assumption⟩]
      (by rfl) (by rfl)
/-- 自然数乘法项的合法性由两个参数证书直接计算。 -/
@[term_check]
theorem natural_multiplication_term_check {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Term.CheckCertificate (left *ₘ right) SetSort.set :=
  Term.check_admissible_complete <|
    natural_multiplication_term_admissible left right
      hLeft.admissible hRight.admissible
theorem natural_exponentiation_term_admissible (base exponent : SetTerm) (hBase : Term.Admissible base SetSort.set)
    (hExponent : Term.Admissible exponent SetSort.set) :
    Term.Admissible (base ^ₘ exponent) SetSort.set := by
  simpa using
    set_function_application_admissible
      .naturalExponentiation [⟨base, by assumption⟩, ⟨exponent, by assumption⟩]
      (by rfl) (by rfl)
/-- 自然数幂项的合法性由底数与指数证书直接计算。 -/
@[term_check]
theorem natural_exponentiation_term_check {base exponent : SetTerm}
    (hBase : Term.CheckCertificate base SetSort.set)
    (hExponent : Term.CheckCertificate exponent SetSort.set) :
    Term.CheckCertificate (base ^ₘ exponent) SetSort.set :=
  Term.check_admissible_complete <|
    natural_exponentiation_term_admissible base exponent
      hBase.admissible hExponent.admissible
theorem finite_sequence_space_term_admissible (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    Term.Admissible (seq_spaceₘ(source)) SetSort.set := by
  simpa using
    set_function_application_admissible
      .finiteSequenceSpace [⟨source, by assumption⟩]
      (by rfl) (by rfl)
/-- 有限序列空间项的合法性由源集合证书直接计算。 -/
@[term_check]
theorem finite_sequence_space_term_check {source : SetTerm}
    (hSource : Term.CheckCertificate source SetSort.set) :
    Term.CheckCertificate (seq_spaceₘ(source)) SetSort.set :=
  Term.check_admissible_complete <|
    finite_sequence_space_term_admissible source hSource.admissible
theorem recursive_sequence_space_term_admissible (source seed recursion : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hSeed : Term.Admissible seed SetSort.set) (hRecursion : Term.Admissible recursion SetSort.set) :
    Term.Admissible (rec_seq_spaceₘ(source, seed, recursion))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .recursiveSequenceSpace [⟨source, by assumption⟩, ⟨seed, by assumption⟩, ⟨recursion, by assumption⟩]
      (by rfl) (by rfl)
/-- 递归序列空间项的合法性由三个参数证书直接计算。 -/
@[term_check]
theorem recursive_sequence_space_term_check {source seed recursion : SetTerm}
    (hSource : Term.CheckCertificate source SetSort.set)
    (hSeed : Term.CheckCertificate seed SetSort.set)
    (hRecursion : Term.CheckCertificate recursion SetSort.set) :
    Term.CheckCertificate
      (rec_seq_spaceₘ(source, seed, recursion)) SetSort.set :=
  Term.check_admissible_complete <|
    recursive_sequence_space_term_admissible source seed recursion
      hSource.admissible hSeed.admissible hRecursion.admissible
theorem omega_recursive_sequence_term_admissible (source seed recursion : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hSeed : Term.Admissible seed SetSort.set) (hRecursion : Term.Admissible recursion SetSort.set) :
    Term.Admissible (ω_rec_seqₘ(source, seed, recursion))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .omegaRecursiveSequence [⟨source, by assumption⟩, ⟨seed, by assumption⟩, ⟨recursion, by assumption⟩]
      (by rfl) (by rfl)
/-- `ω`-递归序列项的合法性由三个参数证书直接计算。 -/
@[term_check]
theorem omega_recursive_sequence_term_check {source seed recursion : SetTerm}
    (hSource : Term.CheckCertificate source SetSort.set)
    (hSeed : Term.CheckCertificate seed SetSort.set)
    (hRecursion : Term.CheckCertificate recursion SetSort.set) :
    Term.CheckCertificate
      (ω_rec_seqₘ(source, seed, recursion)) SetSort.set :=
  Term.check_admissible_complete <|
    omega_recursive_sequence_term_admissible source seed recursion
      hSource.admissible hSeed.admissible hRecursion.admissible
theorem natural_difference_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (left -ₘ right) SetSort.set := by
  simpa using
    set_function_application_admissible
      .naturalDifference [⟨left, by assumption⟩, ⟨right, by assumption⟩]
      (by rfl) (by rfl)
/-- 自然数截断减法项的合法性由两个参数证书直接计算。 -/
@[term_check]
theorem natural_difference_term_check {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set) :
    Term.CheckCertificate (left -ₘ right) SetSort.set :=
  Term.check_admissible_complete <|
    natural_difference_term_admissible left right
      hLeft.admissible hRight.admissible
theorem godel_pairing_term_admissible (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    Term.Admissible (godel_pairₘ(pair)) SetSort.set := by
  simpa using
    set_function_application_admissible
      .godelPairing [⟨pair, by assumption⟩]
      (by rfl) (by rfl)
/-- Gödel 配对项的合法性由有序对证书直接计算。 -/
@[term_check]
theorem godel_pairing_term_check {pair : SetTerm}
    (hPair : Term.CheckCertificate pair SetSort.set) :
    Term.CheckCertificate (godel_pairₘ(pair)) SetSort.set :=
  Term.check_admissible_complete <|
    godel_pairing_term_admissible pair hPair.admissible
/-- Gödel 配对项对两个坐标分别满足通用等词合同。 -/
theorem godel_pairing_term_congr_of_equalities
    {T : SetTheory} {Γ : Context signature} (firstLeft firstRight secondLeft secondRight : SetTerm) (hFirstLeft : Term.Admissible firstLeft SetSort.set)
    (hFirstRight : Term.Admissible firstRight SetSort.set) (hSecondLeft : Term.Admissible secondLeft SetSort.set)
    (hSecondRight : Term.Admissible secondRight SetSort.set) (hFirstEquality :
      Γ ⊢ₘ[T] firstLeft ≐ₘ firstRight) (hSecondEquality :
      Γ ⊢ₘ[T] secondLeft ≐ₘ secondRight) :
    Γ ⊢ₘ[T]
      godel_pairₘ(⟨firstLeft, secondLeft⟩ₘ) ≐ₘ
        godel_pairₘ(⟨firstRight, secondRight⟩ₘ) := by
  exact Metatheory.Derives.binary_term_constructor_congr_of_equalities
    (fun first second => godel_pairₘ(⟨first, second⟩ₘ))
    (fun first second hFirst hSecond =>
      godel_pairing_term_admissible
        (⟨first, second⟩ₘ)
        (ordered_pair_term_admissible
          first second hFirst hSecond))
    (by intros; simp [Term.substituteFree])
    firstLeft firstRight secondLeft secondRight
    hFirstLeft hFirstRight hSecondLeft hSecondRight
    hFirstEquality hSecondEquality
/-! ## 良构性与闭理论边界 -/
theorem natural_addition_definition_axiom_admissible :
    Formula.Admissible
      natural_addition_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem natural_multiplication_definition_axiom_admissible :
    Formula.Admissible
      natural_multiplication_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem natural_exponentiation_definition_axiom_admissible :
    Formula.Admissible
      natural_exponentiation_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem natural_difference_definition_axiom_admissible :
    Formula.Admissible
      natural_difference_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_sequence_space_definition_axiom_admissible :
    Formula.Admissible
      finite_sequence_space_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem recursive_sequence_space_definition_axiom_admissible :
    Formula.Admissible
      recursive_sequence_space_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem omega_recursive_sequence_definition_axiom_admissible :
    Formula.Admissible
      omega_recursive_sequence_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_infinite_definition_axiom_admissible :
    Formula.Admissible
      is_infinite_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_countable_definition_axiom_admissible :
    Formula.Admissible
      is_countable_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_uncountable_definition_axiom_admissible :
    Formula.Admissible
      is_uncountable_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_countably_infinite_definition_axiom_admissible :
    Formula.Admissible
      is_countably_infinite_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem omega_pair_less_definition_axiom_admissible :
    Formula.Admissible
      omega_pair_less_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem godel_pairing_definition_axiom_admissible :
    Formula.Admissible
      godel_pairing_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem natural_addition_theory_admissible :
    Theory.Admissible natural_addition_theory :=
  Theory.admissible_insert
    natural_addition_definition_axiom_admissible
    natural_set_theory_admissible
theorem natural_multiplication_theory_admissible :
    Theory.Admissible natural_multiplication_theory :=
  Theory.admissible_insert
    natural_multiplication_definition_axiom_admissible
    natural_addition_theory_admissible
theorem natural_exponentiation_theory_admissible :
    Theory.Admissible natural_exponentiation_theory :=
  Theory.admissible_insert
    natural_exponentiation_definition_axiom_admissible
    natural_multiplication_theory_admissible
theorem infinite_predicate_theory_admissible :
    Theory.Admissible infinite_predicate_theory :=
  Theory.admissible_insert
    is_infinite_definition_axiom_admissible
    natural_exponentiation_theory_admissible
theorem countable_predicate_theory_admissible :
    Theory.Admissible countable_predicate_theory :=
  Theory.admissible_insert
    is_countable_definition_axiom_admissible
    infinite_predicate_theory_admissible
theorem uncountable_predicate_theory_admissible :
    Theory.Admissible uncountable_predicate_theory :=
  Theory.admissible_insert
    is_uncountable_definition_axiom_admissible
    countable_predicate_theory_admissible
theorem countably_infinite_predicate_theory_admissible :
    Theory.Admissible countably_infinite_predicate_theory :=
  Theory.admissible_insert
    is_countably_infinite_definition_axiom_admissible
    uncountable_predicate_theory_admissible
theorem cardinality_classification_theory_admissible :
    Theory.Admissible cardinality_classification_theory :=
  countably_infinite_predicate_theory_admissible
theorem finite_sequence_space_theory_admissible :
    Theory.Admissible finite_sequence_space_theory :=
  Theory.admissible_insert
    finite_sequence_space_definition_axiom_admissible
    cardinality_classification_theory_admissible
theorem recursive_sequence_space_theory_admissible :
    Theory.Admissible recursive_sequence_space_theory :=
  Theory.admissible_insert
    recursive_sequence_space_definition_axiom_admissible
    finite_sequence_space_theory_admissible
theorem omega_recursive_sequence_theory_admissible :
    Theory.Admissible omega_recursive_sequence_theory :=
  Theory.admissible_insert
    omega_recursive_sequence_definition_axiom_admissible
    recursive_sequence_space_theory_admissible
theorem natural_difference_theory_admissible :
    Theory.Admissible natural_difference_theory :=
  Theory.admissible_insert
    natural_difference_definition_axiom_admissible
    omega_recursive_sequence_theory_admissible
theorem omega_pair_order_theory_admissible :
    Theory.Admissible omega_pair_order_theory :=
  Theory.admissible_insert
    omega_pair_less_definition_axiom_admissible
    natural_difference_theory_admissible
theorem godel_pairing_theory_admissible :
    Theory.Admissible godel_pairing_theory :=
  Theory.admissible_insert
    godel_pairing_definition_axiom_admissible
    omega_pair_order_theory_admissible
theorem natural_arithmetic_theory_admissible :
    Theory.Admissible natural_arithmetic_theory :=
  godel_pairing_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem natural_addition_theory_sentence
    {formula : SetFormula} (hFormula : natural_addition_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact natural_addition_definition_axiom_admissible
    · native_decide
  · exact natural_set_theory_sentence hFormula
@[derive_close_sentence]
theorem natural_multiplication_theory_sentence
    {formula : SetFormula} (hFormula : natural_multiplication_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact natural_multiplication_definition_axiom_admissible
    · native_decide
  · exact natural_addition_theory_sentence hFormula
@[derive_close_sentence]
theorem natural_exponentiation_theory_sentence
    {formula : SetFormula} (hFormula : natural_exponentiation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact natural_exponentiation_definition_axiom_admissible
    · native_decide
  · exact natural_multiplication_theory_sentence hFormula
@[derive_close_sentence]
theorem infinite_predicate_theory_sentence
    {formula : SetFormula} (hFormula : infinite_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_infinite_definition_axiom_admissible
    · native_decide
  · exact natural_exponentiation_theory_sentence hFormula
@[derive_close_sentence]
theorem countable_predicate_theory_sentence
    {formula : SetFormula} (hFormula : countable_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_countable_definition_axiom_admissible
    · native_decide
  · exact infinite_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem uncountable_predicate_theory_sentence
    {formula : SetFormula} (hFormula : uncountable_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_uncountable_definition_axiom_admissible
    · native_decide
  · exact countable_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem countably_infinite_predicate_theory_sentence
    {formula : SetFormula} (hFormula : countably_infinite_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_countably_infinite_definition_axiom_admissible
    · native_decide
  · exact uncountable_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem cardinality_classification_theory_sentence
    {formula : SetFormula} (hFormula : cardinality_classification_theory formula) :
    Formula.Sentence formula :=
  countably_infinite_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem finite_sequence_space_theory_sentence
    {formula : SetFormula} (hFormula : finite_sequence_space_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact finite_sequence_space_definition_axiom_admissible
    · native_decide
  · exact cardinality_classification_theory_sentence hFormula
@[derive_close_sentence]
theorem recursive_sequence_space_theory_sentence
    {formula : SetFormula} (hFormula : recursive_sequence_space_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact recursive_sequence_space_definition_axiom_admissible
    · native_decide
  · exact finite_sequence_space_theory_sentence hFormula
@[derive_close_sentence]
theorem omega_recursive_sequence_theory_sentence
    {formula : SetFormula} (hFormula : omega_recursive_sequence_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact omega_recursive_sequence_definition_axiom_admissible
    · native_decide
  · exact recursive_sequence_space_theory_sentence hFormula
@[derive_close_sentence]
theorem natural_difference_theory_sentence
    {formula : SetFormula} (hFormula : natural_difference_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact natural_difference_definition_axiom_admissible
    · native_decide
  · exact omega_recursive_sequence_theory_sentence hFormula
@[derive_close_sentence]
theorem omega_pair_order_theory_sentence
    {formula : SetFormula} (hFormula : omega_pair_order_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact omega_pair_less_definition_axiom_admissible
    · native_decide
  · exact natural_difference_theory_sentence hFormula
@[derive_close_sentence]
theorem godel_pairing_theory_sentence
    {formula : SetFormula} (hFormula : godel_pairing_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact godel_pairing_definition_axiom_admissible
    · native_decide
  · exact omega_pair_order_theory_sentence hFormula
@[derive_close_sentence]
theorem natural_arithmetic_theory_sentence
    {formula : SetFormula} (hFormula : natural_arithmetic_theory formula) :
    Formula.Sentence formula :=
  godel_pairing_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem natural_set_theory_subset_natural_addition_theory
    {formula : SetFormula} (hFormula : natural_set_theory formula) :
    natural_addition_theory formula :=
  Or.inr hFormula
theorem natural_addition_theory_subset_natural_multiplication_theory
    {formula : SetFormula} (hFormula : natural_addition_theory formula) :
    natural_multiplication_theory formula :=
  Or.inr hFormula
theorem natural_multiplication_theory_subset_natural_exponentiation_theory
    {formula : SetFormula} (hFormula : natural_multiplication_theory formula) :
    natural_exponentiation_theory formula :=
  Or.inr hFormula
theorem natural_exponentiation_theory_subset_infinite_predicate_theory
    {formula : SetFormula} (hFormula : natural_exponentiation_theory formula) :
    infinite_predicate_theory formula :=
  Or.inr hFormula
theorem infinite_predicate_theory_subset_countable_predicate_theory
    {formula : SetFormula} (hFormula : infinite_predicate_theory formula) :
    countable_predicate_theory formula :=
  Or.inr hFormula
theorem countable_predicate_theory_subset_uncountable_predicate_theory
    {formula : SetFormula} (hFormula : countable_predicate_theory formula) :
    uncountable_predicate_theory formula :=
  Or.inr hFormula
theorem uncountable_predicate_theory_subset_countably_infinite_predicate_theory
    {formula : SetFormula} (hFormula : uncountable_predicate_theory formula) :
    countably_infinite_predicate_theory formula :=
  Or.inr hFormula
theorem cardinality_classification_theory_subset_finite_sequence_space_theory
    {formula : SetFormula} (hFormula : cardinality_classification_theory formula) :
    finite_sequence_space_theory formula :=
  Or.inr hFormula
theorem finite_sequence_space_theory_subset_recursive_sequence_space_theory
    {formula : SetFormula} (hFormula : finite_sequence_space_theory formula) :
    recursive_sequence_space_theory formula :=
  Or.inr hFormula
theorem recursive_sequence_space_theory_subset_omega_recursive_sequence_theory
    {formula : SetFormula} (hFormula : recursive_sequence_space_theory formula) :
    omega_recursive_sequence_theory formula :=
  Or.inr hFormula
theorem omega_recursive_sequence_theory_subset_natural_difference_theory
    {formula : SetFormula} (hFormula : omega_recursive_sequence_theory formula) :
    natural_difference_theory formula :=
  Or.inr hFormula
theorem natural_difference_theory_subset_omega_pair_order_theory
    {formula : SetFormula} (hFormula : natural_difference_theory formula) :
    omega_pair_order_theory formula :=
  Or.inr hFormula
theorem omega_pair_order_theory_subset_godel_pairing_theory
    {formula : SetFormula} (hFormula : omega_pair_order_theory formula) :
    godel_pairing_theory formula :=
  Or.inr hFormula
/-! ## 自然数运算的对象闭性 -/
/-- 加法定义公理可在三个 admissible 对象项处直接实例化。 -/
theorem natural_addition_definition_instance_derives (left right result : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hResult : Term.Admissible result SetSort.set) :
    ⊢ₘ[natural_addition_theory]
      natural_addition_definition_instance left right result := by
  have hAxiom :
      ⊢ₘ[natural_addition_theory]
        natural_addition_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hLeftInstance := FirstOrder.Derives.forall_elim
    (term := left) hAxiom
  have hRightInstance := FirstOrder.Derives.forall_elim
    (term := right) hLeftInstance
  have hResultInstance := FirstOrder.Derives.forall_elim
    (term := result) hRightInstance
  have hLeftOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  simpa [natural_addition_definition_axiom,
    natural_addition_definition_instance,
    natural_addition_spec,
    natural_addition_bound_graph_condition,
    natural_addition_graph_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hLeftOpen, hRightOpen] using
      hResultInstance
/-- 两个参数的已证明等式可组合为自然加法项等式。 -/
theorem natural_addition_term_congr_of_equalities
    {T : SetTheory} {Γ : Context signature} (left_first right_first left_second right_second : SetTerm) (hLeftFirst : Term.Admissible left_first SetSort.set)
    (hRightFirst : Term.Admissible right_first SetSort.set) (hLeftSecond : Term.Admissible left_second SetSort.set)
    (hRightSecond : Term.Admissible right_second SetSort.set) (hFirstEquality : Γ ⊢ₘ[T] left_first ≐ₘ right_first)
    (hSecondEquality : Γ ⊢ₘ[T] left_second ≐ₘ right_second) :
    Γ ⊢ₘ[T] (left_first +ₘ left_second) ≐ₘ (right_first +ₘ right_second) := by
  exact Metatheory.Derives.binary_term_constructor_congr_of_equalities
    (fun left right => left +ₘ right)
    (fun left right hLeft hRight =>
      natural_addition_term_admissible left right hLeft hRight)
    (by intros; simp [Term.substituteFree])
    left_first right_first left_second right_second
    hLeftFirst hRightFirst hLeftSecond hRightSecond
    hFirstEquality hSecondEquality
/-- 两个对象自然数的和仍属于对象理论的 `ωₘ`。 -/
theorem natural_addition_term_mem_omega
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeftTerm : Term.Admissible left SetSort.set)
    (hRightTerm : Term.Admissible right SetSort.set)
    (hLeft :
      Γ ⊢ₘ[natural_addition_theory] left ∈ₘ ωₘ)
    (hRight :
      Γ ⊢ₘ[natural_addition_theory] right ∈ₘ ωₘ) :
    Γ ⊢ₘ[natural_addition_theory]
      (left +ₘ right) ∈ₘ ωₘ := by
  have hResultTerm :=
    natural_addition_term_admissible
      left right hLeftTerm hRightTerm
  have hDefinition :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        natural_addition_definition_instance_derives
          left right (left +ₘ right)
          hLeftTerm hRightTerm hResultTerm
  have hContract :=
    FirstOrder.Derives.impElim hDefinition
      (FirstOrder.Derives.conjIntro hLeft hRight)
  have hReflexive :=
    FirstOrder.Derives.eq_refl_m
      (T := natural_addition_theory) (Γ := Γ)
      (sort := SetSort.set) (left +ₘ right)
  have hSpecification :=
    FirstOrder.Derives.iffElimRight hContract hReflexive
  exact FirstOrder.Derives.conjElimLeft hSpecification
/-- 乘法定义公理可在三个 admissible 对象项处直接实例化。 -/
theorem natural_multiplication_definition_instance_derives (left right result : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hResult : Term.Admissible result SetSort.set) :
    ⊢ₘ[natural_multiplication_theory]
      natural_multiplication_definition_instance left right result := by
  have hAxiom :
      ⊢ₘ[natural_multiplication_theory]
        natural_multiplication_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hLeftInstance := FirstOrder.Derives.forall_elim
    (term := left) hAxiom
  have hRightInstance := FirstOrder.Derives.forall_elim
    (term := right) hLeftInstance
  have hResultInstance := FirstOrder.Derives.forall_elim
    (term := result) hRightInstance
  have hLeftOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  simpa [natural_multiplication_definition_axiom,
    natural_multiplication_definition_instance,
    natural_multiplication_spec,
    natural_multiplication_bound_graph_condition,
    natural_multiplication_graph_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hLeftOpen, hRightOpen] using
      hResultInstance
/-- 两个对象自然数的积仍属于对象理论的 `ωₘ`。 -/
theorem natural_multiplication_term_mem_omega
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeftTerm : Term.Admissible left SetSort.set)
    (hRightTerm : Term.Admissible right SetSort.set)
    (hLeft :
      Γ ⊢ₘ[natural_multiplication_theory] left ∈ₘ ωₘ)
    (hRight :
      Γ ⊢ₘ[natural_multiplication_theory] right ∈ₘ ωₘ) :
    Γ ⊢ₘ[natural_multiplication_theory]
      (left *ₘ right) ∈ₘ ωₘ := by
  have hResultTerm :=
    natural_multiplication_term_admissible
      left right hLeftTerm hRightTerm
  have hDefinition :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        natural_multiplication_definition_instance_derives
          left right (left *ₘ right)
          hLeftTerm hRightTerm hResultTerm
  have hContract :=
    FirstOrder.Derives.impElim hDefinition
      (FirstOrder.Derives.conjIntro hLeft hRight)
  have hReflexive :=
    FirstOrder.Derives.eq_refl_m
      (T := natural_multiplication_theory) (Γ := Γ)
      (sort := SetSort.set) (left *ₘ right)
  have hSpecification :=
    FirstOrder.Derives.iffElimRight hContract hReflexive
  exact FirstOrder.Derives.conjElimLeft hSpecification
/-- 幂运算定义公理可在三个 admissible 对象项处直接实例化。 -/
theorem natural_exponentiation_definition_instance_derives (base exponent result : SetTerm) (hBase : Term.Admissible base SetSort.set)
    (hExponent : Term.Admissible exponent SetSort.set) (hResult : Term.Admissible result SetSort.set) :
    ⊢ₘ[natural_exponentiation_theory]
      natural_exponentiation_definition_instance
        base exponent result := by
  have hAxiom :
      ⊢ₘ[natural_exponentiation_theory]
        natural_exponentiation_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hBaseInstance := FirstOrder.Derives.forall_elim
    (term := base) hAxiom
  have hExponentInstance := FirstOrder.Derives.forall_elim
    (term := exponent) hBaseInstance
  have hResultInstance := FirstOrder.Derives.forall_elim
    (term := result) hExponentInstance
  have hBaseOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term base = base :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term base hBase.2
  have hExponentOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term exponent = exponent :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term exponent hExponent.2
  simpa [natural_exponentiation_definition_axiom,
    natural_exponentiation_definition_instance,
    natural_exponentiation_spec,
    natural_exponentiation_bound_graph_condition,
    natural_exponentiation_graph_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hBaseOpen, hExponentOpen] using
      hResultInstance
/-- Gödel 配对定义公理可在两个 admissible 对象项处直接实例化。 -/
theorem godel_pairing_definition_instance_derives (pair candidate : SetTerm) (hPair : Term.Admissible pair SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[godel_pairing_theory]
      godel_pairing_definition_instance pair candidate := by
  have hAxiom :
      ⊢ₘ[godel_pairing_theory]
        godel_pairing_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hPairInstance := FirstOrder.Derives.forall_elim
    (term := pair) hAxiom
  have hCandidateInstance := FirstOrder.Derives.forall_elim
    (term := candidate) hPairInstance
  have hPairOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term pair hPair.2
  simpa [godel_pairing_definition_axiom,
    godel_pairing_definition_instance,
    godel_pairing_condition, natural_leq_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hPairOpen] using
      hCandidateInstance
/-- 两个对象自然数的幂仍属于对象理论的 `ωₘ`。 -/
theorem natural_exponentiation_term_mem_omega
    {Γ : Context signature}
    (base exponent : SetTerm)
    (hBaseTerm : Term.Admissible base SetSort.set)
    (hExponentTerm : Term.Admissible exponent SetSort.set)
    (hBase :
      Γ ⊢ₘ[natural_exponentiation_theory] base ∈ₘ ωₘ)
    (hExponent :
      Γ ⊢ₘ[natural_exponentiation_theory] exponent ∈ₘ ωₘ) :
    Γ ⊢ₘ[natural_exponentiation_theory]
      (base ^ₘ exponent) ∈ₘ ωₘ := by
  have hResultTerm := natural_exponentiation_term_admissible
    base exponent hBaseTerm hExponentTerm
  have hDefinition :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        natural_exponentiation_definition_instance_derives
          base exponent (base ^ₘ exponent)
          hBaseTerm hExponentTerm hResultTerm
  have hContract := FirstOrder.Derives.impElim hDefinition (FirstOrder.Derives.conjIntro hBase hExponent)
  have hReflexive :=
    FirstOrder.Derives.eq_refl_m
      (T := natural_exponentiation_theory) (Γ := Γ)
      (sort := SetSort.set) (base ^ₘ exponent)
  have hSpecification :=
    FirstOrder.Derives.iffElimRight hContract hReflexive
  exact FirstOrder.Derives.conjElimLeft hSpecification
/-!
## 待证明定理索引
以下内容暂留后续证明层：
* 自然数加法、乘法和幂的交换律、结合律、递归唯一性与闭性；
* 鸽巢原理及其在有限序列、可数性和不可数性上的推论；
* 有限序列空间、递归序列空间与 `ω`-递归序列的存在性、唯一性；
* 自然数截断减法的基本性质；
* `ω × ω` 典型序、Gödel 配对以及后续有限序列编码定理。
文献中的 `ψ₅₉`、`ψ₆₈`、`ψ₆₉`、`ψ₇₁a`、`ψ₇₂`--`ψ₇₆` 与
`Θ_add`、`Θ_mul`、`Θ_exp`、`Θ_dgdy`、`Θω` 等，仅作为后续证明的
公式索引，不新增一次性公共谓词。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
