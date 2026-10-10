import BMSConstructibleBridge.SecondOrderSeparation
import BMSConstructibleBridge.SecondOrderAxioms
import YesMetaZFC.Automation.ModelClosure

/-!
# 完整分离模式的二阶对象推导

源公式可含任意量词和全部有限参数。先构造其实际纯集合论分离闭句，再核验
任意内部商模型及任意参数环境，最后对原图翻译回传真实对象推导。
这里不是仅对根编号做理解，也没有把模式实例视为固定高度 BM4 证明生成器。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSeparationAxiom

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic GraphTranslation
open SecondOrderInterpretation

set_option autoImplicit false

universe u

private def insert {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: Δ) [.set, .set, .set] Δ
  | _, .here => .bvar .here
  | _, .there v => .fvar v

private def body {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [.set, .set, .set] Δ :=
  φ.substitute (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v) insert)

/-- 原参数保持自由；三个绑定集合依次是候选元素、分离子集、母集。 -/
def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set <| .existsE .set <| .forallE .set <|
    .iff (.rel .membership (.cons (.bvar .here) (.cons (.bvar (.there .here)) .nil)))
      (.conj (.rel .membership (.cons (.bvar .here) (.cons (.bvar (.there (.there .here))) .nil)))
        (body φ))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private theorem body_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (a b c : SecondOrderQuotient.type_l hℳ) :
    Formula.satisfies (((η.pushBound a).pushBound b).pushBound c) (body φ) ↔
      Formula.satisfies (η.pushFree c) φ := by
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => Formula.satisfies η φ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v <;> rfl

theorem schema_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) :
    Formula.satisfies η (schema_m φ) ↔
      ∀ a : SecondOrderQuotient.type_l hℳ, ∃ b, ∀ c,
        SecondOrderQuotient.mem_l hℳ c b ↔
          SecondOrderQuotient.mem_l hℳ c a ∧ Formula.satisfies (η.pushFree c) φ := by
  simp only [schema_m, Formula.satisfies]
  change (∀ a : SecondOrderQuotient.type_l hℳ, ∃ b, ∀ c,
    SecondOrderQuotient.mem_l hℳ c b ↔ SecondOrderQuotient.mem_l hℳ c a ∧
      Formula.satisfies (((η.pushBound a).pushBound b).pushBound c) (body φ)) ↔ _
  simp_rw [body_l hℳ]

theorem models_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) :
    Formula.satisfies η (schema_m φ) := by
  rw [schema_l]
  obtain ⟨ρ, τ, rfl⟩ := source_surj_l hℳ η
  intro a
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨C, hC⟩ := SecondOrderSeparation.exists_l hℳ φ τ A
  refine ⟨SecondOrderQuotient.mk_l hℳ C, fun b => ?_⟩
  obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
  change SecondOrderGraph.mem_l B C ↔ SecondOrderGraph.mem_l B A ∧ _
  refine (hC B).trans (and_congr Iff.rfl ?_)
  refine (SecondOrderInterpretation.form_l hℳ φ (fun v => nomatch v) (push_l B τ)).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => Formula.satisfies η φ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v <;> rfl

/-- 整个任意参数分离闭模式的原图翻译，由对象二阶算术真正推出。 -/
theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives theory_m [] (form_m (sentence_m φ)) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff (schema_m φ)).mpr
  exact models_l hℳ φ

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSeparationAxiom
