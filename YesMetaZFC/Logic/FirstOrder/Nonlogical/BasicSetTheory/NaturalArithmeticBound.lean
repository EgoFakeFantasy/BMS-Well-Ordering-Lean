import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmetic

/-!
# 对象自然数运算的有限上界

现有 `natural_exponentiation_theory` 只给出递归图定义与自然数闭性，不包含对象
归纳或幂的增长律。本模块把编码反演实际需要的最弱一般算术事实独立成扩展层：
若 `1 < base` 且 `index` 是自然数，则 `index < base ^ (index + 1)`。
若两个底数都大于 `1`，则左右指数还同时小于对应两个幂的乘积。

这些公理不含 Gödel 编码、token 或具体素数。后续把对象元理论保守回 ZFC 时，
只需在 ZFC 中证明这些封闭算术公式，而不必迁移 quotation 证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

set_option autoImplicit false

/-! ## 增长律公式 -/

/--
自然加法结果同时支配两个操作数的开放实例。

`point ∈ S(left)` 与 `point ∈ S(right)` 分别表示 `point ≤ left` 和
`point ≤ right`；结论表示 `point ≤ left + right`。
-/
def natural_addition_upper_bound_instance
    (point left right : SetTerm) : SetFormula :=
  ((point ∈ₘ ωₘ) ∧ₘ
      ((left ∈ₘ ωₘ) ∧ₘ
        ((right ∈ₘ ωₘ) ∧ₘ
          ((point ∈ₘ Sₘ(left)) ∨ₘ
            (point ∈ₘ Sₘ(right)))))) ⟶ₘ
    (point ∈ₘ Sₘ(left +ₘ right))

/-- 自然加法共同上界的闭公理。 -/
def natural_addition_upper_bound_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        natural_addition_upper_bound_instance
          (x#0) (x#1) (x#2)

/--
正左加法把右侧的非严格上界提升为严格上界。

`∅ ∈ left` 表示 `0 < left`；若 `point ≤ right`，则
`point < left + right`。
-/
def natural_positive_left_addition_strict_bound_instance
    (point left right : SetTerm) : SetFormula :=
  ((point ∈ₘ ωₘ) ∧ₘ
      ((left ∈ₘ ωₘ) ∧ₘ
        ((right ∈ₘ ωₘ) ∧ₘ
          ((∅ₘ ∈ₘ left) ∧ₘ
            (point ∈ₘ Sₘ(right)))))) ⟶ₘ
    (point ∈ₘ (left +ₘ right))

/-- 正左加法严格上界的闭公理。 -/
def natural_positive_left_addition_strict_bound_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        natural_positive_left_addition_strict_bound_instance
          (x#0) (x#1) (x#2)

/--
自然数非严格次序与严格次序的混合传递实例。

`point ∈ S(middle)` 表示 `point ≤ middle`，`middle ∈ upper` 表示
`middle < upper`；结论是 `point < upper`。
-/
def natural_le_lt_transitivity_instance
    (point middle upper : SetTerm) : SetFormula :=
  ((middle ∈ₘ ωₘ) ∧ₘ
      ((upper ∈ₘ ωₘ) ∧ₘ
        ((point ∈ₘ Sₘ(middle)) ∧ₘ
          (middle ∈ₘ upper)))) ⟶ₘ
    (point ∈ₘ upper)

/-- 自然数 `≤`-`<` 混合传递的闭公理。 -/
def natural_le_lt_transitivity_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        natural_le_lt_transitivity_instance
          (x#0) (x#1) (x#2)

/--
Gödel 配对值同时支配两个自然数坐标。

该合同只暴露编码反演需要的有限上界，不承诺配对函数的全局反函数。
-/
def natural_godel_pairing_coordinate_bound_instance
    (left right : SetTerm) : SetFormula :=
  ((left ∈ₘ ωₘ) ∧ₘ (right ∈ₘ ωₘ)) ⟶ₘ
    ((left ∈ₘ
        Sₘ(godel_pairₘ(⟨left, right⟩ₘ))) ∧ₘ
      (right ∈ₘ
        Sₘ(godel_pairₘ(⟨left, right⟩ₘ))))

/-- Gödel 配对坐标上界的闭公理。 -/
def natural_godel_pairing_coordinate_bound_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      natural_godel_pairing_coordinate_bound_instance
        (x#0) (x#1)

/--
自然幂索引上界的开放实例。

对象自然数使用 von Neumann 表示，因此 `numₘ(1) ∈ₘ base` 表示 `1 < base`，
而结论 `index ∈ₘ base ^ₘ Sₘ(index)` 表示严格上界。
-/
def natural_exponentiation_index_bound_instance
    (base index : SetTerm) : SetFormula :=
  ((base ∈ₘ ωₘ) ∧ₘ
      ((index ∈ₘ ωₘ) ∧ₘ (numₘ(1) ∈ₘ base))) ⟶ₘ
    (index ∈ₘ (base ^ₘ Sₘ(index)))

/-- 自然幂索引上界的闭公理。 -/
def natural_exponentiation_index_bound_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      natural_exponentiation_index_bound_instance
        (x#0) (x#1)

/--
两个正增长幂乘积的索引上界实例。

该公式不预设底数互素，也不绑定任何 Gödel 素数；严格正的另一因子只用于把各自
幂的索引上界提升到乘积。
-/
def natural_exponent_product_index_bound_instance
    (leftBase leftIndex rightBase rightIndex : SetTerm) :
    SetFormula :=
  ((leftBase ∈ₘ ωₘ) ∧ₘ
      ((leftIndex ∈ₘ ωₘ) ∧ₘ
        ((numₘ(1) ∈ₘ leftBase) ∧ₘ
          ((rightBase ∈ₘ ωₘ) ∧ₘ
            ((rightIndex ∈ₘ ωₘ) ∧ₘ
              (numₘ(1) ∈ₘ rightBase)))))) ⟶ₘ
    ((leftIndex ∈ₘ
        ((leftBase ^ₘ Sₘ(leftIndex)) *ₘ
          (rightBase ^ₘ Sₘ(rightIndex)))) ∧ₘ
      (rightIndex ∈ₘ
        ((leftBase ^ₘ Sₘ(leftIndex)) *ₘ
          (rightBase ^ₘ Sₘ(rightIndex)))))

/-- 两个幂乘积索引上界的闭公理。 -/
def natural_exponent_product_index_bound_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          natural_exponent_product_index_bound_instance
            (x#0) (x#1) (x#2) (x#3)

/-! ## 理论边界 -/

/--
在自然幂递归定义上加入索引上界。

该层刻意独立于 `natural_arithmetic_theory` 的后续有限序列和配对设施，使需要
幂增长的模块只承担这一条额外算术强度。
-/
def natural_exponentiation_bound_theory : SetTheory :=
  Theory.insert
    natural_exponentiation_index_bound_axiom
    (Theory.insert
      natural_exponent_product_index_bound_axiom
      natural_exponentiation_theory)

/--
在幂增长层上加入有限序列反演所需的两条加法上界。

该理论仍是纯对象算术层；有限序列与 quotation 只消费它，不参与其定义。
-/
def natural_addition_bound_theory : SetTheory :=
  Theory.insert
    natural_addition_upper_bound_axiom
    (Theory.insert
      natural_positive_left_addition_strict_bound_axiom
      (Theory.insert
        natural_le_lt_transitivity_axiom
        (Theory.insert
          natural_godel_pairing_coordinate_bound_axiom
          natural_exponentiation_bound_theory)))

theorem natural_addition_upper_bound_axiom_admissible :
    Formula.Admissible
      natural_addition_upper_bound_axiom := by
  apply Formula.check_admissible_sound
  native_decide

theorem
    natural_positive_left_addition_strict_bound_axiom_admissible :
    Formula.Admissible
      natural_positive_left_addition_strict_bound_axiom := by
  apply Formula.check_admissible_sound
  native_decide

theorem natural_le_lt_transitivity_axiom_admissible :
    Formula.Admissible
      natural_le_lt_transitivity_axiom := by
  apply Formula.check_admissible_sound
  native_decide

theorem
    natural_godel_pairing_coordinate_bound_axiom_admissible :
    Formula.Admissible
      natural_godel_pairing_coordinate_bound_axiom := by
  apply Formula.check_admissible_sound
  native_decide

theorem natural_exponentiation_index_bound_axiom_admissible :
    Formula.Admissible
      natural_exponentiation_index_bound_axiom := by
  apply Formula.check_admissible_sound
  native_decide

theorem natural_exponent_product_index_bound_axiom_admissible :
    Formula.Admissible
      natural_exponent_product_index_bound_axiom := by
  apply Formula.check_admissible_sound
  native_decide

theorem natural_exponentiation_bound_theory_admissible :
    Theory.Admissible
      natural_exponentiation_bound_theory :=
  Theory.admissible_insert
    natural_exponentiation_index_bound_axiom_admissible
    (Theory.admissible_insert
      natural_exponent_product_index_bound_axiom_admissible
      natural_exponentiation_theory_admissible)

theorem natural_addition_bound_theory_admissible :
    Theory.Admissible natural_addition_bound_theory :=
  Theory.admissible_insert
    natural_addition_upper_bound_axiom_admissible
    (Theory.admissible_insert
      natural_positive_left_addition_strict_bound_axiom_admissible
      (Theory.admissible_insert
        natural_le_lt_transitivity_axiom_admissible
        (Theory.admissible_insert
          natural_godel_pairing_coordinate_bound_axiom_admissible
          natural_exponentiation_bound_theory_admissible)))

@[derive_close_sentence]
theorem natural_exponentiation_bound_theory_sentence
    {formula : SetFormula}
    (hFormula : natural_exponentiation_bound_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact
        natural_exponentiation_index_bound_axiom_admissible
    · native_decide
  · exact
      match hFormula with
      | Or.inl hProduct =>
          hProduct ▸
            ⟨natural_exponent_product_index_bound_axiom_admissible,
              by native_decide⟩
       | Or.inr hBase =>
           natural_exponentiation_theory_sentence hBase

@[derive_close_sentence]
theorem natural_addition_bound_theory_sentence
    {formula : SetFormula}
    (hFormula : natural_addition_bound_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · exact
      ⟨natural_addition_upper_bound_axiom_admissible,
        by native_decide⟩
  · exact
      match hFormula with
      | Or.inl hStrict =>
          hStrict ▸
            ⟨natural_positive_left_addition_strict_bound_axiom_admissible,
              by native_decide⟩
      | Or.inr hTransOrBase =>
          match hTransOrBase with
          | Or.inl hTrans =>
              hTrans ▸
                ⟨natural_le_lt_transitivity_axiom_admissible,
                  by native_decide⟩
          | Or.inr hPairOrBase =>
              match hPairOrBase with
              | Or.inl hPair =>
                  hPair ▸
                    ⟨natural_godel_pairing_coordinate_bound_axiom_admissible,
                      by native_decide⟩
              | Or.inr hBase =>
                  natural_exponentiation_bound_theory_sentence
                    hBase

theorem natural_exponentiation_theory_subset_bound_theory
    {formula : SetFormula}
    (hFormula : natural_exponentiation_theory formula) :
    natural_exponentiation_bound_theory formula :=
  Or.inr <| Or.inr hFormula

theorem natural_exponentiation_bound_theory_subset_addition_bound_theory
    {formula : SetFormula}
    (hFormula : natural_exponentiation_bound_theory formula) :
    natural_addition_bound_theory formula :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr hFormula

/-! ## 公理实例化 -/

/-- 加法共同上界公理可在任意三个 admissible 对象项处直接实例化。 -/
theorem natural_addition_upper_bound_instance_derives
    (point left right : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[natural_addition_bound_theory]
      natural_addition_upper_bound_instance
        point left right := by
  have hAxiom :
      ⊢ₘ[natural_addition_bound_theory]
        natural_addition_upper_bound_axiom :=
    FirstOrder.Derives.theory_mem (Or.inl rfl)
  have hPointInstance :=
    FirstOrder.Derives.forall_elim
      (term := point) hAxiom
  have hLeftInstance :=
    FirstOrder.Derives.forall_elim
      (term := left) hPointInstance
  have hRightInstance :=
    FirstOrder.Derives.forall_elim
      (term := right) hLeftInstance
  have hPointOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term point = point :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term point hPoint.2
  have hLeftOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  simpa [natural_addition_upper_bound_axiom,
    natural_addition_upper_bound_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hPointOpen, hLeftOpen,
    hRightOpen] using hRightInstance

/--
正左加法严格上界公理可在任意三个 admissible 对象项处直接实例化。
-/
theorem
    natural_positive_left_addition_strict_bound_instance_derives
    (point left right : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[natural_addition_bound_theory]
      natural_positive_left_addition_strict_bound_instance
        point left right := by
  have hAxiom :
      ⊢ₘ[natural_addition_bound_theory]
        natural_positive_left_addition_strict_bound_axiom :=
    FirstOrder.Derives.theory_mem
      (Or.inr <| Or.inl rfl)
  have hPointInstance :=
    FirstOrder.Derives.forall_elim
      (term := point) hAxiom
  have hLeftInstance :=
    FirstOrder.Derives.forall_elim
      (term := left) hPointInstance
  have hRightInstance :=
    FirstOrder.Derives.forall_elim
      (term := right) hLeftInstance
  have hPointOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term point = point :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term point hPoint.2
  have hLeftOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  simpa [natural_positive_left_addition_strict_bound_axiom,
    natural_positive_left_addition_strict_bound_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hPointOpen, hLeftOpen,
    hRightOpen] using hRightInstance

/--
自然数 `≤`-`<` 混合传递公理可在任意三个 admissible 对象项处直接实例化。
-/
theorem natural_le_lt_transitivity_instance_derives
    (point middle upper : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hMiddle : Term.Admissible middle SetSort.set)
    (hUpper : Term.Admissible upper SetSort.set) :
    ⊢ₘ[natural_addition_bound_theory]
      natural_le_lt_transitivity_instance
        point middle upper := by
  have hAxiom :
      ⊢ₘ[natural_addition_bound_theory]
        natural_le_lt_transitivity_axiom :=
    FirstOrder.Derives.theory_mem
      (Or.inr <| Or.inr <| Or.inl rfl)
  have hPointInstance :=
    FirstOrder.Derives.forall_elim
      (term := point) hAxiom
  have hMiddleInstance :=
    FirstOrder.Derives.forall_elim
      (term := middle) hPointInstance
  have hUpperInstance :=
    FirstOrder.Derives.forall_elim
      (term := upper) hMiddleInstance
  have hPointOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term point = point :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term point hPoint.2
  have hMiddleOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term middle = middle :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term middle hMiddle.2
  have hUpperOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term upper = upper :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term upper hUpper.2
  simpa [natural_le_lt_transitivity_axiom,
    natural_le_lt_transitivity_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hPointOpen,
    hMiddleOpen, hUpperOpen] using
      hUpperInstance

/--
Gödel 配对坐标上界公理可在任意两个 admissible 对象项处直接实例化。
-/
theorem natural_godel_pairing_coordinate_bound_instance_derives
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[natural_addition_bound_theory]
      natural_godel_pairing_coordinate_bound_instance
        left right := by
  have hAxiom :
      ⊢ₘ[natural_addition_bound_theory]
        natural_godel_pairing_coordinate_bound_axiom :=
    FirstOrder.Derives.theory_mem
      (Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)
  have hLeftInstance :=
    FirstOrder.Derives.forall_elim
      (term := left) hAxiom
  have hRightInstance :=
    FirstOrder.Derives.forall_elim
      (term := right) hLeftInstance
  have hLeftOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  simpa [natural_godel_pairing_coordinate_bound_axiom,
    natural_godel_pairing_coordinate_bound_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hLeftOpen, hRightOpen] using
      hRightInstance

/-- 索引上界公理可在任意两个 admissible 对象项处直接实例化。 -/
theorem natural_exponentiation_index_bound_instance_derives
    (base index : SetTerm)
    (hBase : Term.Admissible base SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[natural_exponentiation_bound_theory]
      natural_exponentiation_index_bound_instance
        base index := by
  have hAxiom :
      ⊢ₘ[natural_exponentiation_bound_theory]
        natural_exponentiation_index_bound_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hBaseInstance :=
    FirstOrder.Derives.forall_elim
      (term := base) hAxiom
  have hIndexInstance :=
    FirstOrder.Derives.forall_elim
      (term := index) hBaseInstance
  have hBaseOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term base =
        base :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term base hBase.2
  have hIndexOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term index =
        index :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term index hIndex.2
  have hOneOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term (numₘ(1)) =
        numₘ(1) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term (numₘ(1))
      (finite_numeral_term_admissible 1).2
  have hOneClose
      (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth
          (numₘ(1)) =
        numₘ(1) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (numₘ(1))
      (finite_numeral_term_admissible 1).2
      (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  simpa [natural_exponentiation_index_bound_axiom,
    natural_exponentiation_index_bound_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hBaseOpen, hIndexOpen,
    hOneOpen, hOneClose] using
      hIndexInstance

/-- 幂乘积索引上界公理可在任意四个 admissible 对象项处直接实例化。 -/
theorem natural_exponent_product_index_bound_instance_derives
    (leftBase leftIndex rightBase rightIndex : SetTerm)
    (hLeftBase : Term.Admissible leftBase SetSort.set)
    (hLeftIndex : Term.Admissible leftIndex SetSort.set)
    (hRightBase : Term.Admissible rightBase SetSort.set)
    (hRightIndex : Term.Admissible rightIndex SetSort.set) :
    ⊢ₘ[natural_exponentiation_bound_theory]
      natural_exponent_product_index_bound_instance
        leftBase leftIndex rightBase rightIndex := by
  have hAxiom :
      ⊢ₘ[natural_exponentiation_bound_theory]
        natural_exponent_product_index_bound_axiom :=
    FirstOrder.Derives.theory_mem
      (Or.inr <| Or.inl rfl)
  have hLeftBaseInstance :=
    FirstOrder.Derives.forall_elim
      (term := leftBase) hAxiom
  have hLeftIndexInstance :=
    FirstOrder.Derives.forall_elim
      (term := leftIndex) hLeftBaseInstance
  have hRightBaseInstance :=
    FirstOrder.Derives.forall_elim
      (term := rightBase) hLeftIndexInstance
  have hRightIndexInstance :=
    FirstOrder.Derives.forall_elim
      (term := rightIndex) hRightBaseInstance
  have hLeftBaseOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term leftBase =
        leftBase :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term leftBase hLeftBase.2
  have hLeftIndexOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term leftIndex =
        leftIndex :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term leftIndex hLeftIndex.2
  have hRightBaseOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term rightBase =
        rightBase :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term rightBase hRightBase.2
  have hRightIndexOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term rightIndex =
        rightIndex :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term rightIndex hRightIndex.2
  have hOneOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term (numₘ(1)) =
        numₘ(1) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term (numₘ(1))
      (finite_numeral_term_admissible 1).2
  have hOneClose
      (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth
          (numₘ(1)) =
        numₘ(1) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (numₘ(1))
      (finite_numeral_term_admissible 1).2
      (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  simpa [natural_exponent_product_index_bound_axiom,
    natural_exponent_product_index_bound_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hLeftBaseOpen,
    hLeftIndexOpen, hRightBaseOpen,
    hRightIndexOpen, hOneOpen, hOneClose] using
      hRightIndexInstance

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
