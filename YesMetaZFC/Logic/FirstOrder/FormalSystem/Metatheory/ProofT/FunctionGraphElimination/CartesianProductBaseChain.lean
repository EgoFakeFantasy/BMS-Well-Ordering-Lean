import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.CartesianProduct
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.BinaryUnion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.OrderedPair
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.PowerSet
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Singleton
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Union

/-!
# 笛卡尔积基础理论的证明级消去

笛卡尔积分离规格本身仍含有序对函数，不能直接套用普通的单符号理论并入。
本模块只处理其基础理论：先消去基础理论中的有序对定义，保留幂集与二元并
两个独立的函数扩张，给后续依赖型规格编译留下准确的中间边界。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace CartesianProductBaseChain

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

/-- 笛卡尔积基础理论中除有序对外的两个支撑理论。 -/
def support_theory : SetTheory :=
  Theory.union power_set_operator_theory
    binary_union_operator_theory

private theorem support_sentence
    {φ : SetFormula} (hφ : support_theory φ) :
    Formula.Sentence φ := by
  rcases hφ with hφ | hφ
  · exact power_set_operator_theory_sentence hφ
  · exact binary_union_operator_theory_sentence hφ

private theorem support_avoids_ordered_pair
    {φ : SetFormula} (hφ : support_theory φ) :
    FormulaAvoids FunctionSymbol.orderedPair φ := by
  change power_set_operator_theory φ ∨
    binary_union_operator_theory φ at hφ
  rcases hφ with hφ | hφ
  · simp only [power_set_operator_theory,
      power_set_theory, subset_theory,
      extensionality_theory, Theory.insert,
      Theory.singleton] at hφ
    repeat'
      first
      | obtain hφ | hφ := hφ
      | subst φ
    all_goals
      apply checkFormulaAvoids_sound
      native_decide
  · simp only [binary_union_operator_theory,
      binary_union_base_theory,
      pairing_operator_theory, pairing_theory,
      union_operator_theory, union_theory,
      extensionality_theory, Theory.insert,
      Theory.union, Theory.singleton] at hφ
    repeat'
      first
      | obtain hφ | hφ := hφ
      | subst φ
    all_goals
      apply checkFormulaAvoids_sound
      native_decide

/-- 消去有序对后保留的中间图理论。 -/
def reduct_theory : SetTheory :=
  Theory.union singleton_operator_theory
    support_theory

/-- 笛卡尔积基础理论的有序对图提升。 -/
def base_lift :
    TheoryPresentation OrderedPair.data :=
  OrderedPair.theory_presentation.union_right
    support_theory support_sentence
    support_avoids_ordered_pair

/-- 笛卡尔积基础理论中的矛盾可回传到有序对已消去的中间理论。 -/
theorem derives_falsum
    (h :
      Derives cartesian_product_base_theory []
        Formula.falsum) :
    Derives reduct_theory []
      Formula.falsum := by
  simpa [base_lift, reduct_theory,
      cartesian_product_base_theory,
      support_theory] using
    base_lift.derives_falsum
      SetSort.set h

/-- 中间理论一致时，笛卡尔积基础理论保持一致。 -/
theorem consistent
    (h : Derives.Consistent reduct_theory []) :
    Derives.Consistent
      cartesian_product_base_theory [] := by
  intro hBase
  exact h (derives_falsum hBase)

/-! ## 继续消去二元并 -/

/-- 二元并消去前仍保留的单点集与幂集支撑理论。 -/
def binary_support_theory : SetTheory :=
  Theory.union singleton_operator_theory
    power_set_operator_theory

private theorem binary_support_sentence
    {φ : SetFormula} (hφ : binary_support_theory φ) :
    Formula.Sentence φ := by
  rcases hφ with hφ | hφ
  · exact singleton_operator_theory_sentence hφ
  · exact power_set_operator_theory_sentence hφ

private theorem binary_support_avoids_binary_union
    {φ : SetFormula} (hφ : binary_support_theory φ) :
    FormulaAvoids FunctionSymbol.binaryUnion φ := by
  change singleton_operator_theory φ ∨
    power_set_operator_theory φ at hφ
  rcases hφ with hφ | hφ
  · simp only [singleton_operator_theory,
      pairing_operator_theory, pairing_theory,
      extensionality_theory, Theory.insert,
      Theory.singleton] at hφ
    repeat'
      first
      | obtain hφ | hφ := hφ
      | subst φ
    all_goals
      apply checkFormulaAvoids_sound
      native_decide
  · simp only [power_set_operator_theory,
      power_set_theory, subset_theory,
      extensionality_theory, Theory.insert,
      Theory.singleton] at hφ
    repeat'
      first
      | obtain hφ | hφ := hφ
      | subst φ
    all_goals
      apply checkFormulaAvoids_sound
      native_decide

/-- 二元并消去后保留的图理论。 -/
def binary_reduct_theory : SetTheory :=
  Theory.union binary_support_theory
    (BinaryUnion.graph_presentation).theory

private theorem binary_reduct_sentence
    {φ : SetFormula} (hφ : binary_reduct_theory φ) :
    Formula.Sentence φ := by
  rcases hφ with hφ | hφ
  · exact binary_support_sentence hφ
  · exact (BinaryUnion.graph_presentation).theory_sentence hφ

/-- 有序对已消去的中间理论中的二元并图提升。 -/
def binary_lift :
    TheoryPresentation BinaryUnion.data where
  graph :=
    (BinaryUnion.graph_presentation).theory_weaken
      binary_reduct_theory
      (fun _ hφ => Or.inr hφ)
      binary_reduct_sentence
  source := reduct_theory
  compile_axiom := by
    intro φ hφ
    change singleton_operator_theory φ ∨
      (power_set_operator_theory φ ∨
        binary_union_operator_theory φ) at hφ
    rcases hφ with hφ | hφ
    · rw [formula_eq_of_sentence_avoids
        BinaryUnion.data φ
        (binary_support_avoids_binary_union
          (Or.inl hφ))
        (singleton_operator_theory_sentence hφ)]
      exact Derives.theory_mem
        (T := binary_reduct_theory)
        (Or.inl (Or.inl hφ))
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            (singleton_operator_theory_sentence hφ).1)
    · rcases hφ with hφ | hφ
      · rw [formula_eq_of_sentence_avoids
          BinaryUnion.data φ
          (binary_support_avoids_binary_union
            (Or.inr hφ))
          (power_set_operator_theory_sentence hφ)]
        exact Derives.theory_mem
          (T := binary_reduct_theory)
          (Or.inl (Or.inr hφ))
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              (power_set_operator_theory_sentence hφ).1)
      · exact Derives.theory_weaken
          (fun _ hφ => Or.inr hφ)
          ((BinaryUnion.theory_presentation).compile_axiom hφ)

/-- 中间理论中的矛盾可回传到二元并已消去的图理论。 -/
theorem reduct_derives_falsum
    (h : Derives reduct_theory []
      Formula.falsum) :
    Derives binary_reduct_theory []
      Formula.falsum :=
  binary_lift.derives_falsum
    SetSort.set h

/-- 二元并消去后的图理论一致时，中间理论保持一致。 -/
theorem reduct_consistent
    (h : Derives.Consistent
      binary_reduct_theory []) :
    Derives.Consistent reduct_theory [] := by
  intro hReduct
  exact h (reduct_derives_falsum hReduct)

/-! ## 继续消去幂集 -/

/-- 幂集消去后保留的支撑图理论。 -/
def power_reduct_theory : SetTheory :=
  Theory.union power_set_theory
    (Theory.union singleton_operator_theory
      (BinaryUnion.graph_presentation).theory)

private theorem power_reduct_sentence
    {φ : SetFormula} (hφ : power_reduct_theory φ) :
    Formula.Sentence φ := by
  rcases hφ with hφ | hφ
  · exact power_set_operator_theory_sentence
      (Or.inr hφ)
  · rcases hφ with hφ | hφ
    · exact singleton_operator_theory_sentence hφ
    · exact (BinaryUnion.graph_presentation).theory_sentence hφ

private theorem power_support_avoids_power_set
    {φ : SetFormula}
    (hφ :
      singleton_operator_theory φ ∨
        (BinaryUnion.graph_presentation).theory φ) :
    FormulaAvoids FunctionSymbol.powerSet φ := by
  rcases hφ with hφ | hφ
  · simp only [singleton_operator_theory,
      pairing_operator_theory, pairing_theory,
      extensionality_theory, Theory.insert,
      Theory.singleton] at hφ
    repeat'
      first
      | obtain hφ | hφ := hφ
      | subst φ
    all_goals
      apply checkFormulaAvoids_sound
      native_decide
  · change binary_union_base_theory φ at hφ
    simp only [binary_union_base_theory,
      pairing_operator_theory, pairing_theory,
      union_operator_theory, union_theory,
      extensionality_theory, Theory.insert,
      Theory.union, Theory.singleton] at hφ
    repeat'
      first
      | obtain hφ | hφ := hφ
      | subst φ
    all_goals
      apply checkFormulaAvoids_sound
      native_decide

/-- 幂集函数在二元并中间理论上的图提升。 -/
def power_lift :
    TheoryPresentation PowerSet.data where
  graph :=
    (PowerSet.graph_presentation).theory_weaken
      power_reduct_theory
      (fun _ hφ => Or.inl hφ)
      power_reduct_sentence
  source := binary_reduct_theory
  compile_axiom := by
    intro φ hφ
    rcases hφ with hφ | hφ
    · rcases hφ with hφ | hφ
      · rw [formula_eq_of_sentence_avoids
          PowerSet.data φ
          (power_support_avoids_power_set
            (Or.inl hφ))
          (singleton_operator_theory_sentence hφ)]
        exact Derives.theory_mem
          (T := power_reduct_theory)
          (Or.inr (Or.inl hφ))
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              (singleton_operator_theory_sentence hφ).1)
      · exact Derives.theory_weaken
          (fun _ hφ => Or.inl hφ)
          ((PowerSet.theory_presentation).compile_axiom hφ)
    · rw [formula_eq_of_sentence_avoids
        PowerSet.data φ
        (power_support_avoids_power_set
          (Or.inr hφ))
        ((BinaryUnion.graph_presentation).theory_sentence hφ)]
      exact Derives.theory_mem
        (T := power_reduct_theory)
        (Or.inr (Or.inr hφ))
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            ((BinaryUnion.graph_presentation).theory_sentence hφ).1)

/-- 二元并中间理论的矛盾可回传到幂集已消去的图理论。 -/
theorem binary_reduct_derives_falsum
    (h : Derives binary_reduct_theory []
      Formula.falsum) :
    Derives power_reduct_theory []
      Formula.falsum :=
  power_lift.derives_falsum
    SetSort.set h

/-- 幂集消去后的图理论一致时，二元并中间理论保持一致。 -/
theorem binary_reduct_consistent
    (h : Derives.Consistent
      power_reduct_theory []) :
    Derives.Consistent binary_reduct_theory [] := by
  intro hBinary
  exact h (binary_reduct_derives_falsum hBinary)

/-! ## 继续消去单点集 -/

/-- 单点集消去后保留幂集与二元并基础理论。 -/
def singleton_reduct_theory : SetTheory :=
  Theory.union power_set_theory
    (BinaryUnion.graph_presentation).theory

private theorem singleton_reduct_sentence
    {φ : SetFormula} (hφ : singleton_reduct_theory φ) :
    Formula.Sentence φ := by
  rcases hφ with hφ | hφ
  · exact power_set_operator_theory_sentence (Or.inr hφ)
  · exact (BinaryUnion.graph_presentation).theory_sentence hφ

private theorem singleton_reduct_avoids_singleton
    {φ : SetFormula}
    (hφ :
      power_set_theory φ ∨
        (BinaryUnion.graph_presentation).theory φ) :
    FormulaAvoids FunctionSymbol.singleton φ := by
  rcases hφ with hφ | hφ
  · simp only [power_set_theory, subset_theory,
      extensionality_theory, Theory.insert,
      Theory.singleton] at hφ
    repeat'
      first
      | obtain hφ | hφ := hφ
      | subst φ
    all_goals
      apply checkFormulaAvoids_sound
      native_decide
  · change binary_union_base_theory φ at hφ
    simp only [binary_union_base_theory,
      pairing_operator_theory, pair_definition_axiom,
      pairing_theory, pairing_axiom,
      union_operator_theory, union_definition_axiom,
      union_theory, union_axiom,
      extensionality_theory, Theory.insert,
      Theory.union, Theory.singleton] at hφ
    repeat'
      first
      | obtain hφ | hφ := hφ
      | subst φ
    all_goals
      apply checkFormulaAvoids_sound
      native_decide

/-- 单点集定义在幂集与二元并基础理论上的图提升。 -/
def singleton_lift :
    TheoryPresentation Singleton.data where
  graph :=
    Singleton.graph_presentation.theory_weaken
      singleton_reduct_theory
      (fun _ hφ => Or.inr (Or.inl hφ))
      singleton_reduct_sentence
  source := power_reduct_theory
  compile_axiom := by
    intro φ hφ
    change power_set_theory φ ∨
      (singleton_operator_theory φ ∨
        binary_union_base_theory φ) at hφ
    rcases hφ with hφ | hφ
    · rw [formula_eq_of_sentence_avoids
        Singleton.data φ
        (singleton_reduct_avoids_singleton
          (Or.inl hφ))
        (power_set_operator_theory_sentence (Or.inr hφ))]
      exact Derives.theory_mem
        (T := singleton_reduct_theory)
        (Or.inl hφ)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            (power_set_operator_theory_sentence (Or.inr hφ)).1)
    · rcases hφ with hφ | hφ
      · exact Derives.theory_weaken
          (fun _ hφ => Or.inr (Or.inl hφ))
          (Singleton.theory_presentation.compile_axiom hφ)
      · rw [formula_eq_of_sentence_avoids
          Singleton.data φ
          (singleton_reduct_avoids_singleton
            (Or.inr hφ))
          (binary_union_operator_theory_sentence (Or.inr hφ))]
        exact Derives.theory_mem
          (T := singleton_reduct_theory)
          (Or.inr hφ)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              (binary_union_operator_theory_sentence (Or.inr hφ)).1)

/-- 幂集与二元并基础理论中的矛盾可回传到单点集已消去理论。 -/
theorem power_reduct_derives_falsum
    (h : Derives power_reduct_theory []
      Formula.falsum) :
    Derives singleton_reduct_theory []
      Formula.falsum :=
  singleton_lift.derives_falsum
    SetSort.set h

/-- 单点集已消去理论一致时，幂集与二元并基础理论保持一致。 -/
theorem singleton_reduct_consistent
    (h : Derives.Consistent
      singleton_reduct_theory []) :
    Derives.Consistent power_reduct_theory [] := by
  intro hPower
  exact h (power_reduct_derives_falsum hPower)

/-! ## 消去二元并依赖树中的一元并与无序对 -/

/-- 笛卡尔积基础层最后保留的幂集、配对与并集理论。 -/
def zf_reduct_theory : SetTheory :=
  Theory.union power_set_theory
    (Theory.union pairing_theory union_theory)

private theorem zf_reduct_sentence
    {φ : SetFormula} (hφ : zf_reduct_theory φ) :
    Formula.Sentence φ := by
  rcases hφ with hφ | hφ
  · exact power_set_operator_theory_sentence (Or.inr hφ)
  · rcases hφ with hφ | hφ
    · exact pairing_operator_theory_sentence (Or.inr hφ)
    · exact union_operator_theory_sentence (Or.inr hφ)

private theorem pairing_operator_avoids_union
    {φ : SetFormula} (hφ : pairing_operator_theory φ) :
    FormulaAvoids FunctionSymbol.union φ := by
  rcases hφ with rfl | hφ
  · simpa [pair_definition_axiom] using
      formula_avoids_forall_close
        FunctionSymbol.union
        [(SetSort.set, 0), (SetSort.set, 1),
          (SetSort.set, 2)]
        (pair_definition_instance
          (x#0) (x#1) (x#2)) <| by
            simp [pair_definition_instance,
              pair_spec, pair_member_condition,
              unordered_pair_term,
              FormulaAvoids, TermsAvoid, TermAvoids]
  · rcases hφ with rfl | hφ
    · simpa [pairing_axiom] using
        formula_avoids_forall_close
          FunctionSymbol.union
          [(SetSort.set, 0), (SetSort.set, 1)]
          (pair_exists (x#0) (x#1)) <| by
            simp [pair_exists, pair_member_condition,
              FormulaAvoids, TermsAvoid, TermAvoids]
    · change φ = extensionality_axiom at hφ
      subst φ
      simpa [extensionality_axiom] using
        formula_avoids_forall_close
          FunctionSymbol.union
          [(SetSort.set, 0), (SetSort.set, 1)]
          (extensionality_instance
            (x#0) (x#1)) <| by
              simp [extensionality_instance,
                agreement_to_equality,
                membership_agreement,
                FormulaAvoids, TermsAvoid, TermAvoids]

private theorem union_theory_avoids_unordered_pair
    {φ : SetFormula} (hφ : union_theory φ) :
    FormulaAvoids FunctionSymbol.unorderedPair φ := by
  rcases hφ with rfl | hφ
  · simpa [union_axiom] using
      formula_avoids_forall_close
        FunctionSymbol.unorderedPair
        [(SetSort.set, 0)]
        (union_exists (x#0)) <| by
          simp [union_exists,
            FormulaAvoids, TermsAvoid, TermAvoids]
  · change φ = extensionality_axiom at hφ
    subst φ
    simpa [extensionality_axiom] using
      formula_avoids_forall_close
        FunctionSymbol.unorderedPair
        [(SetSort.set, 0), (SetSort.set, 1)]
        (extensionality_instance
          (x#0) (x#1)) <| by
            simp [extensionality_instance,
              agreement_to_equality,
              membership_agreement,
              FormulaAvoids, TermsAvoid, TermAvoids]

private theorem power_set_avoids_union
    {φ : SetFormula} (hφ : power_set_theory φ) :
    FormulaAvoids FunctionSymbol.union φ := by
  simp only [power_set_theory, subset_theory,
    extensionality_theory, Theory.insert,
    Theory.singleton] at hφ
  repeat'
    first
    | obtain hφ | hφ := hφ
    | subst φ
  all_goals
    apply checkFormulaAvoids_sound
    native_decide

private theorem power_set_avoids_unordered_pair
    {φ : SetFormula} (hφ : power_set_theory φ) :
    FormulaAvoids FunctionSymbol.unorderedPair φ := by
  simp only [power_set_theory, subset_theory,
    extensionality_theory, Theory.insert,
    Theory.singleton] at hφ
  repeat'
    first
    | obtain hφ | hφ := hφ
    | subst φ
  all_goals
    apply checkFormulaAvoids_sound
    native_decide

/-- 先消去二元并基础层中的一元并函数。 -/
def union_inner_lift :
    TheoryPresentation Union.data :=
  Union.theory_presentation.union_left
    pairing_operator_theory
    pairing_operator_theory_sentence
    pairing_operator_avoids_union

/-- 再消去二元并基础层中的无序对函数。 -/
def pair_inner_lift :
    TheoryPresentation UnorderedPair.data :=
  UnorderedPair.theory_presentation.union_right
    union_theory
    (fun hφ =>
      union_operator_theory_sentence (Or.inr hφ))
    union_theory_avoids_unordered_pair

/-- 将幂集左支接到一元并消去链上。 -/
def union_lift :
    TheoryPresentation Union.data :=
  union_inner_lift.union_left
    power_set_theory
    (fun hφ => power_set_operator_theory_sentence (Or.inr hφ))
    power_set_avoids_union

/-- 将幂集左支接到无序对消去链上。 -/
def pair_lift :
    TheoryPresentation UnorderedPair.data :=
  pair_inner_lift.union_left
    power_set_theory
    (fun hφ => power_set_operator_theory_sentence (Or.inr hφ))
    power_set_avoids_unordered_pair

/-! ## 任意公式的组合编译 -/

/-- 笛卡尔积基础层函数图消去对闭公式给出的组合编译。 -/
def compile_formula (φ : SetFormula) : SetFormula :=
  formula UnorderedPair.data
    (formula Union.data
      (formula Singleton.data
        (formula PowerSet.data
          (formula BinaryUnion.data
            (formula OrderedPair.data φ)))))

/-- 笛卡尔积基础理论中的任意 checked 闭证明可翻译到纯存在公理理论。 -/
theorem derives
    {φ : SetFormula}
    (h :
      Derives cartesian_product_base_theory [] φ) :
    Derives zf_reduct_theory [] (compile_formula φ) := by
  have hOrdered :=
    base_lift.derives SetSort.set h
  have hBinary :=
    binary_lift.derives SetSort.set hOrdered
  have hPower :=
    power_lift.derives SetSort.set hBinary
  have hSingleton :=
    singleton_lift.derives SetSort.set hPower
  have hUnionSource :
      Derives union_lift.source []
        (formula Singleton.data
          (formula PowerSet.data
            (formula BinaryUnion.data
              (formula OrderedPair.data φ)))) := by
    simpa [union_lift, union_inner_lift,
      singleton_reduct_theory,
      BinaryUnion.graph_presentation,
      binary_union_base_theory] using
      hSingleton
  have hUnion :=
    union_lift.derives SetSort.set hUnionSource
  have hPairSource :
      Derives pair_lift.source []
        (formula Union.data
          (formula Singleton.data
            (formula PowerSet.data
              (formula BinaryUnion.data
                (formula OrderedPair.data φ))))) := by
    simpa [union_lift, union_inner_lift,
      pair_lift, pair_inner_lift] using
      hUnion
  have hPair :=
    pair_lift.derives SetSort.set hPairSource
  simpa [compile_formula, pair_lift, pair_inner_lift,
    zf_reduct_theory] using hPair

/-- 单点集已消去理论中的矛盾可回传到纯存在公理理论。 -/
theorem singleton_reduct_derives_falsum
    (h : Derives singleton_reduct_theory []
      Formula.falsum) :
    Derives zf_reduct_theory []
      Formula.falsum := by
  have hSource :
      Derives union_lift.source []
        Formula.falsum := by
    simpa [union_lift, union_inner_lift,
      singleton_reduct_theory,
      BinaryUnion.graph_presentation,
      binary_union_base_theory] using
      h
  have hUnion :=
    union_lift.derives_falsum
      SetSort.set hSource
  have hPairSource :
      Derives pair_lift.source []
        Formula.falsum := by
    simpa [union_lift, union_inner_lift,
      pair_lift, pair_inner_lift] using
      hUnion
  have hPair :=
    pair_lift.derives_falsum
      SetSort.set hPairSource
  simpa [pair_lift, pair_inner_lift,
    zf_reduct_theory] using
    hPair

/-- 纯存在公理理论一致时，单点集已消去理论保持一致。 -/
theorem zf_reduct_consistent
    (h : Derives.Consistent zf_reduct_theory []) :
    Derives.Consistent singleton_reduct_theory [] := by
  intro hSingleton
  exact h (singleton_reduct_derives_falsum hSingleton)

/-- 幂集与二元并基础层中的矛盾可直接回传到纯存在公理理论。 -/
theorem power_reduct_to_zf_derives_falsum
    (h : Derives power_reduct_theory []
      Formula.falsum) :
    Derives zf_reduct_theory []
      Formula.falsum :=
  singleton_reduct_derives_falsum
    (power_reduct_derives_falsum h)

/-- 纯存在公理理论一致时，完整的当前基础消去链保持一致。 -/
theorem power_reduct_consistent
    (h : Derives.Consistent zf_reduct_theory []) :
    Derives.Consistent power_reduct_theory [] :=
  singleton_reduct_consistent
    (zf_reduct_consistent h)

/-- 笛卡尔积基础理论中的矛盾沿完整函数依赖树回传到纯存在公理理论。 -/
theorem zf_derives_falsum
    (h :
      Derives cartesian_product_base_theory []
        Formula.falsum) :
    Derives zf_reduct_theory []
      Formula.falsum := by
  simpa [compile_formula, FunctionGraphElimination.formula] using
    derives h

/-- 纯存在公理理论一致时，笛卡尔积全部基础函数定义保持一致。 -/
theorem base_consistent
    (h : Derives.Consistent zf_reduct_theory []) :
    Derives.Consistent
      cartesian_product_base_theory [] :=
  consistent <|
    reduct_consistent <|
      binary_reduct_consistent <|
        power_reduct_consistent h

end CartesianProductBaseChain
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
