import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.ThirdOrderSemantics
import YesMetaZFC.Automation.ModelClosure

/-!
# 可定义关系集合与笛卡尔积的原 Z₂ 对象推导

目标只使用纯隶属语言。两个母集及关系图均显式量化，原关系公式的参数
全称闭包；没有额外关系符号或幂集前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableRelationImageDerives

open Logic FirstOrder SecondOrderObjectSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def insert_m {Δ : SortContext ℒ} : VariableSubstitution ℒ (.set :: .set :: Δ)
    [.set, .set, .set, .set, .set, .set] Δ
  | _, .here => .bvar (.there .here)
  | _, .there .here => .bvar .here
  | _, .there (.there v) => .fvar v

private def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [.set, .set, .set, .set, .set, .set] Δ :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ)
    [.set, .set, .set, .set, .set, .set] Δ from .map (fun v => nomatch v) insert_m)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set (.forallE .set (.existsE .set (.forallE .set
    (.iff (member_m (.bvar .here) (.bvar (.there .here)))
      (.existsE .set (.existsE .set (.conj
        (member_m (.bvar (.there .here)) (.bvar (.there (.there (.there (.there (.there .here)))))))
        (.conj (member_m (.bvar .here) (.bvar (.there (.there (.there (.there .here))))))
          (.conj (body_m φ) (ordered_m (.bvar (.there .here)) (.bvar .here)
            (.bvar (.there (.there .here)))))))))))))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

private theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (a b f p x y : 𝒩.Carrier .set) :
    (body_m φ).satisfies ((((((η.pushBound a).pushBound b).pushBound f).pushBound p).pushBound x).pushBound y) ↔
      φ.satisfies ((η.pushFree y).pushFree x) := by
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

theorem schema_generic_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) :
    (schema_m φ).satisfies η ↔ ∀ a b : 𝒩.Carrier .set, ∃ f, ∀ p,
      ThirdOrderSemantics.member_l 𝒩 p f ↔ ∃ x y,
        ThirdOrderSemantics.member_l 𝒩 x a ∧ ThirdOrderSemantics.member_l 𝒩 y b ∧
        φ.satisfies ((η.pushFree y).pushFree x) ∧ ThirdOrderSemantics.ordered_l x y p := by
  simp only [schema_m, Formula.satisfies, member_m,
    ThirdOrderSemantics.ordered_formula_l, Arguments.eval, Term.eval]
  change (∀ a b : 𝒩.Carrier .set, ∃ f, ∀ p,
    ThirdOrderSemantics.member_l 𝒩 p f ↔ ∃ x y,
      ThirdOrderSemantics.member_l 𝒩 x a ∧ ThirdOrderSemantics.member_l 𝒩 y b ∧
      (body_m φ).satisfies ((((((η.pushBound a).pushBound b).pushBound f).pushBound p).pushBound x).pushBound y) ∧
      ThirdOrderSemantics.ordered_l x y p) ↔ _
  simp_rw [body_formula_l]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

theorem schema_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) :
    (schema_m φ).satisfies η ↔ ∀ a b : SecondOrderQuotient.type_l hℳ, ∃ f, ∀ p,
      SecondOrderQuotient.mem_l hℳ p f ↔ ∃ x y,
        SecondOrderQuotient.mem_l hℳ x a ∧ SecondOrderQuotient.mem_l hℳ y b ∧
        φ.satisfies ((η.pushFree y).pushFree x) ∧ SecondOrderPairObjects.ordered_l hℳ x y p := by
  simp only [schema_m, Formula.satisfies, member_m, ordered_l, Arguments.eval, Term.eval]
  change (∀ a b : SecondOrderQuotient.type_l hℳ, ∃ f, ∀ p,
    SecondOrderQuotient.mem_l hℳ p f ↔ ∃ x y,
      SecondOrderQuotient.mem_l hℳ x a ∧ SecondOrderQuotient.mem_l hℳ y b ∧
      (body_m φ).satisfies ((((((η.pushBound a).pushBound b).pushBound f).pushBound p).pushBound x).pushBound y) ∧
      SecondOrderPairObjects.ordered_l hℳ x y p) ↔ _
  simp_rw [body_formula_l]

theorem models_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) : (schema_m φ).satisfies η :=
  (schema_formula_l hℳ φ η).mpr (SecondOrderDefinableRelationImage.exists_l hℳ φ η)

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  exact (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr (models_l hℳ φ)

/-- 取恒真关系得到实际笛卡尔积，而不是所有子集组成的幂集。 -/
def product_m : Sentence ℒ := sentence_m (Δ := []) (.equal (.fvar .here) (.fvar .here))

theorem product_derives_m :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m product_m) :=
  derives_m _

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableRelationImageDerives
