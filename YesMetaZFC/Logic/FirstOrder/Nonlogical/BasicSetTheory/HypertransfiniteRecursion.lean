import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmetic
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure
/-!
# 替换模式与超限递归定义设施

本模块把替换模式和递归步直接表示为带参数上下文的内在类型公式。公式的排序、
作用域、参数位置以及量词关闭顺序全部由类型核确定，不再携带变量编号、新鲜性
扫描、`Admissible` 或句子证书。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 上下文嵌入 -/

/-! 将一组外部参数整体放入若干新 free 槽之后。 -/
def prefix_free_renaming {free pre : SetContext} :
    VariableRenaming free (pre ++ free) :=
  match pre with
  | [] => VariableRenaming.id
  | introduced :: rest =>
      VariableRenaming.comp
        (VariableRenaming.weaken introduced)
        (prefix_free_renaming (pre := rest) (free := free))

def prefix_free_substitution {free pre : SetContext} :
    VariableSubstitution signature free [] (pre ++ free) :=
  fun entry => .fvar (prefix_free_renaming (pre := pre) entry)

/-! ## 替换模式 -/

/-!
替换关系的公式参数。

自由变量从顶部开始依次表示输出、输入，剩余槽位由 `parameterContext` 记录。
因此任何替换实例都天然具有确定的排序和作用域。
-/
structure ReplacementPredicate where
  parameterContext : SetContext
  body : SetOpenFormula (SetSort.set :: SetSort.set :: parameterContext)

/-! 在指定目标上下文中实例化替换关系的输入与输出。 -/
def replacement_body_at {pre : SetContext}
    (predicate : ReplacementPredicate)
    (input output : SetTerm [] (pre ++ predicate.parameterContext)) :
    SetOpenFormula (pre ++ predicate.parameterContext) :=
  predicate.body.substituteFree
    (VariableSubstitution.cons output
      (VariableSubstitution.cons input
        (prefix_free_substitution
          (free := predicate.parameterContext) (pre := pre))))

/-! 替换公理模式的函数性条件。 -/
def replacement_functionality_core (predicate : ReplacementPredicate) :
    SetOpenFormula predicate.parameterContext :=
  let input : SetOpenTerm
      ([SetSort.set, SetSort.set, SetSort.set] ++ predicate.parameterContext) :=
    .fvar (.there (.there .here))
  let left : SetOpenTerm
      ([SetSort.set, SetSort.set, SetSort.set] ++ predicate.parameterContext) :=
    .fvar (.there .here)
  let right : SetOpenTerm
      ([SetSort.set, SetSort.set, SetSort.set] ++ predicate.parameterContext) :=
    .fvar .here
  let body :=
    ((replacement_body_at predicate input left) ∧ₘ
      replacement_body_at predicate input right) ⟶ₘ
      (left ≐ₘ right)
  body.forallFreeTop SetSort.set
    |>.forallFreeTop SetSort.set
    |>.forallFreeTop SetSort.set

/-! 替换公理模式的像集存在条件。 -/
def replacement_collection_core (predicate : ReplacementPredicate) :
    SetOpenFormula predicate.parameterContext :=
  let source : SetOpenTerm
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ predicate.parameterContext) :=
    .fvar (.there (.there (.there .here)))
  let target : SetOpenTerm
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ predicate.parameterContext) :=
    .fvar (.there (.there .here))
  let member : SetOpenTerm
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ predicate.parameterContext) :=
    .fvar (.there .here)
  let witness : SetOpenTerm
      ([SetSort.set, SetSort.set, SetSort.set, SetSort.set] ++ predicate.parameterContext) :=
    .fvar .here
  let body :=
    (member ∈ₘ target) ↔ₘ
      ((witness ∈ₘ source) ∧ₘ
        replacement_body_at predicate witness member)
  body.existsFreeTop SetSort.set
    |>.forallFreeTop SetSort.set
    |>.existsFreeTop SetSort.set
    |>.forallFreeTop SetSort.set

/-! 替换公理模式的开放核心与闭实例。 -/
def replacement_axiom_core (predicate : ReplacementPredicate) :
    SetOpenFormula predicate.parameterContext :=
  replacement_functionality_core predicate ⟶ₘ
    replacement_collection_core predicate

def replacement_axiom (predicate : ReplacementPredicate) : SetSentence :=
  Metatheory.Formula.forall_close (replacement_axiom_core predicate)

def replacement_schema : SetTheory :=
  fun formula => ∃ predicate : ReplacementPredicate,
    formula = replacement_axiom predicate

def replacement_theory : SetTheory :=
  fun formula => natural_arithmetic_theory formula ∨
    replacement_schema formula

theorem replacement_schema_mem (predicate : ReplacementPredicate) :
    replacement_schema (replacement_axiom predicate) :=
  ⟨predicate, rfl⟩

theorem natural_arithmetic_theory_subset_replacement_theory
    {formula : SetSentence} (hFormula : natural_arithmetic_theory formula) :
    replacement_theory formula :=
  Or.inl hFormula

theorem replacement_schema_subset_replacement_theory
    {formula : SetSentence} (hFormula : replacement_schema formula) :
    replacement_theory formula :=
  Or.inr hFormula

/-! ## 超限递归定义契约 -/

/-!
递归步的公式参数。

自由变量从顶部开始依次表示下一值、当前值、指标，剩余槽位由
`parameterContext` 记录。这样递归步实例化只需给出三个同上下文项。
-/
structure RecursiveStep where
  parameterContext : SetContext
  body : SetOpenFormula
    (SetSort.set :: SetSort.set :: SetSort.set :: parameterContext)

def recursive_step_body_at {pre : SetContext}
    (step : RecursiveStep)
    (index current next : SetTerm [] (pre ++ step.parameterContext)) :
    SetOpenFormula (pre ++ step.parameterContext) :=
  step.body.substituteFree
    (VariableSubstitution.cons next
      (VariableSubstitution.cons current
        (VariableSubstitution.cons index
          (prefix_free_substitution
            (free := step.parameterContext) (pre := pre)))))

/-! 后继位置上的递归步条件。 -/
def transfinite_recursion_step_condition_at {pre : SetContext}
    (step : RecursiveStep)
    (sequence : SetOpenTerm (pre ++ step.parameterContext)) :
    SetOpenFormula (pre ++ step.parameterContext) :=
  let index : SetOpenTerm
      (SetSort.set :: (pre ++ step.parameterContext)) :=
    .fvar .here
  let deepIndex : SetOpenTerm
      ([SetSort.set, SetSort.set] ++ (pre ++ step.parameterContext)) :=
    .fvar (.there .here)
  let next : SetOpenTerm
      ([SetSort.set, SetSort.set] ++ (pre ++ step.parameterContext)) :=
    .fvar .here
  let sequenceOne : SetOpenTerm
      (SetSort.set :: (pre ++ step.parameterContext)) :=
    @Term.weakenFree signature [] (pre ++ step.parameterContext)
      SetSort.set SetSort.set sequence
  let sequenceDeep : SetOpenTerm
      ([SetSort.set, SetSort.set] ++ (pre ++ step.parameterContext)) :=
    @Term.weakenFree signature []
      (SetSort.set :: (pre ++ step.parameterContext))
      SetSort.set SetSort.set sequenceOne
  let successorIndex : SetOpenTerm
      ([SetSort.set, SetSort.set] ++ (pre ++ step.parameterContext)) :=
    successor_term deepIndex
  let nextCondition :=
    ((sequenceDeep ·ₘ successorIndex) ≐ₘ next) ↔ₘ
      recursive_step_body_at step
        (pre := [SetSort.set, SetSort.set] ++ pre)
        deepIndex (sequenceDeep ·ₘ deepIndex) next
  let nextForall := nextCondition.forallFreeTop SetSort.set
  ((index ∈ₘ ωₘ) ⟶ₘ nextForall).forallFreeTop SetSort.set

def transfinite_recursion_step_condition (step : RecursiveStep)
    (sequence : SetOpenTerm step.parameterContext) :
    SetOpenFormula step.parameterContext :=
  transfinite_recursion_step_condition_at (pre := []) step sequence

/-!
以 `ω` 为定义域的递归序列规格。该定义是参数化开放公式，调用方的参数上下文
由递归步本身携带。
-/
def transfinite_recursion_spec_at {pre : SetContext}
    (step : RecursiveStep)
    (seed sequence : SetOpenTerm (pre ++ step.parameterContext)) :
    SetOpenFormula (pre ++ step.parameterContext) :=
  is_function_formula sequence ∧ₘ
    ((domₘ(sequence) ≐ₘ ωₘ) ∧ₘ
      (((sequence ·ₘ numₘ(0)) ≐ₘ seed) ∧ₘ
        transfinite_recursion_step_condition_at (pre := pre) step sequence))

def transfinite_recursion_spec (step : RecursiveStep)
    (seed sequence : SetOpenTerm step.parameterContext) :
    SetOpenFormula step.parameterContext :=
  transfinite_recursion_spec_at (pre := []) step seed sequence

def transfinite_recursion_definition_instance {pre : SetContext}
    (step : RecursiveStep)
    (seed candidate : SetOpenTerm (pre ++ step.parameterContext)) :
    SetOpenFormula (pre ++ step.parameterContext) :=
  transfinite_recursion_spec_at (pre := pre) step seed candidate

def transfinite_recursion_definition (step : RecursiveStep)
    (seed : SetOpenTerm step.parameterContext) :
    SetOpenFormula step.parameterContext :=
  let candidate : SetOpenTerm
      (SetSort.set :: step.parameterContext) :=
    .fvar .here
  (transfinite_recursion_definition_instance (pre := [SetSort.set]) step
      (@Term.weakenFree signature [] step.parameterContext
        SetSort.set SetSort.set seed) candidate).existsFreeTop SetSort.set

/-! 超限递归层不新增独立公理，只消费替换理论。 -/
def hypertransfinite_recursion_theory : SetTheory :=
  replacement_theory

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
