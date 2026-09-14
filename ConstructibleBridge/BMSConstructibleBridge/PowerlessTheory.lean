import YesMetaZFC.SetTheory.Collection
import YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
import YesMetaZFC.SetTheory.Definitional.Project.FromFirstOrder
import BMSConstructibleBridge.SecondOrderWeakSetTheory

/-!
# 完整分离与收集的无幂集核心

基础闭句复用已核验的纯集合论公式，再经上游反向语法桥进入 Project。
分离和收集直接复用上游模式，不加入幂集或选择，也不改动既有 ZF 接口。
这样避开旧 notation 生成的原生闭合证书，不放宽三项标准公理审计。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTheory

open Logic FirstOrder
open SetTheory.Definitional.Project

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

universe u

/-- 反向语法桥的闭合证书由结构证明产生，不使用原生计算。 -/
def project_m (φ : FirstOrder.Sentence ℒ) : SetTheory.Definitional.Project.Sentence :=
  .ofFormula (FromFirstOrder.translate (bound := []) (free := []) (depth := 0)
    (fun v => nomatch v) (fun v => nomatch v) φ)
    (FromFirstOrder.freeClosed _ _ φ)

/-- 外延性先于依赖外延性的语义往返桥；闭合性直接由内核判定。 -/
def extensionality_m : SetTheory.Definitional.Project.Sentence :=
  .ofFormula (.forallE (.forallE (.imp
    (.forallE (.iff (.mem (.bound 0) (.bound 2)) (.mem (.bound 0) (.bound 1))))
    (SetTheory.Definitional.Project.Formula.extensionalEq (.bound 1) (.bound 0)))))
    (by simp [SetTheory.Definitional.Formula.FreeClosed])

inductive axiom_m : SetTheory.Definitional.Project.Theory where
  | extensionality : axiom_m extensionality_m
  | empty : axiom_m (project_m SecondOrderAxioms.empty_m)
  | pairing : axiom_m (project_m SecondOrderPairSet.formula_m)
  | union : axiom_m (project_m SecondOrderUnion.formula_m)
  | infinity : axiom_m (project_m SecondOrderInfinityAxiom.formula_m)
  | foundation : axiom_m (project_m SecondOrderFoundation.formula_m)
  | separation {n : Nat} (φ : UnarySchema n) : axiom_m (SetTheory.Axioms.Schema.separation φ)
  | collection {n : Nat} (φ : BinarySchema n) : axiom_m (SetTheory.Axioms.Schema.collection φ)

def theory_m : FirstOrder.Theory ℒ := fo_theory axiom_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 往返 Project 的基础闭句保持原语义，不因更换闭合证书改变公理。 -/
theorem sentence_l (hℳ : SetTheory.Extensional (FirstOrderSemantics.reduct ℳ))
    (φ : FirstOrder.Sentence ℒ) : (fo_sentence (project_m φ)).TrueIn ℳ ↔ φ.TrueIn ℳ := by
  rw [FirstOrderSemantics.sentence_correct hℳ]
  constructor
  · intro h
    obtain ⟨a⟩ := ℳ.nonempty SetTheory.SetSort.set
    let η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) 0 := { bound := Fin.elim0, free := fun _ => a }
    exact (FromFirstOrder.correct hℳ φ (fun v => nomatch v) (fun v => nomatch v)
      Env.empty η (fun v => nomatch v) (fun v => nomatch v)).mp (h η.free)
  · intro h f
    let η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) 0 := { bound := Fin.elim0, free := f }
    exact (FromFirstOrder.correct hℳ φ (fun v => nomatch v) (fun v => nomatch v)
      Env.empty η (fun v => nomatch v) (fun v => nomatch v)).mpr h

theorem ext_l (hℳ : FirstOrder.Theory.Models ℳ theory_m) :
    SetTheory.Extensional (FirstOrderSemantics.reduct ℳ) := by
  have h := hℳ _ ⟨_, axiom_m.extensionality, rfl⟩
  simp only [FirstOrder.Formula.TrueIn, fo_sentence, extensionality_m,
    SetTheory.Definitional.Project.Sentence.ofFormula, fo_formula, fo_mem, fo_term, fo_bound_variable,
    FirstOrder.Formula.satisfies, Arguments.eval, FirstOrder.Term.eval,
    SetTheory.Definitional.Project.Formula.extensionalEq,
    SetTheory.Definitional.Project.Formula.pairArguments] at h
  change ∀ a b : ℳ.Carrier SetTheory.SetSort.set,
    (∀ x, (FirstOrderSemantics.reduct ℳ).mem x a ↔ (FirstOrderSemantics.reduct ℳ).mem x b) → a = b at h
  exact ⟨h⟩

theorem project_l (hℳ : FirstOrder.Theory.Models ℳ theory_m) :
    (FirstOrderSemantics.reduct ℳ).Models axiom_m :=
  (FirstOrderSemantics.models_iff (ext_l hℳ) axiom_m).mp hℳ

theorem axiom_l (hℳ : FirstOrder.Theory.Models ℳ theory_m) {φ : FirstOrder.Sentence ℒ}
    (h : axiom_m (project_m φ)) : φ.TrueIn ℳ :=
  (sentence_l (ext_l hℳ) φ).mp (hℳ _ ⟨_, h, rfl⟩)

/-- 所有公式与参数的收集，不使用幂集、外部良基或输出唯一性。 -/
theorem collection_l (hℳ : FirstOrder.Theory.Models ℳ theory_m) {n : Nat}
    (φ : BinarySchema n) (η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) n)
    (A : (FirstOrderSemantics.reduct ℳ).Domain)
    (h : ∀ x, (FirstOrderSemantics.reduct ℳ).mem x A → ∃ y,
      SetTheory.Definitional.Project.Formula.satisfies ((η.push x).push y) φ.body) :
    ∃ B, ∀ x, (FirstOrderSemantics.reduct ℳ).mem x A → ∃ y,
      (FirstOrderSemantics.reduct ℳ).mem y B ∧
        SetTheory.Definitional.Project.Formula.satisfies ((η.push x).push y) φ.body := by
  have h₀ := (project_l hℳ).2 _ (axiom_m.collection φ) η.free
  have h₁ : SetTheory.Definitional.Project.Formula.satisfies η
      (SetTheory.Axioms.Schema.collectionCore φ) := by
    have h₂ := (SetTheory.Definitional.Project.Formula.satisfies_forallClosure_iff
      η.free (SetTheory.Axioms.Schema.collectionCore φ)).mp h₀
    exact h₂ η.bound
  exact (SetTheory.Axioms.Schema.collection_sat_iff_d η φ).mp h₁ A h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTheory
