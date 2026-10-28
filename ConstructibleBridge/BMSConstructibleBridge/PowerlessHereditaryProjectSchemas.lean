import BMSConstructibleBridge.PowerlessHereditaryFullCollection
import BMSConstructibleBridge.PowerlessProjectEnvironment

/-! # 原 Project 模式在实际遗传子模型中的解释

背景原 Z₂，逐项消费原 PowerlessTheory 的 UnarySchema / BinarySchema
以及原公理闭句。绑定参数、开放后的自由槽和模型 universe 全部沿
既有环境桥核验，不以相似的 ℒ 模式替代源公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryProjectSchemas

open Logic FirstOrder PowerlessBMSQuotientCoding
open SetTheory.Definitional.Project
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessHereditaryStructure.type_l PowerlessHereditaryStructure.structure_l FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₁" => PowerlessHereditaryStructure.structure_l hℳ B hBase
local notation "N" => PowerlessHereditaryStructure.type_l hℳ B

theorem separation_l
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    {n : Nat} (φ : UnarySchema n) :
    (fo_sentence (SetTheory.Axioms.Schema.separation φ)).TrueIn 𝒩₁ := by
  have hExt := PowerlessHereditaryStructure.ext_l hℳ B hBase
  apply (FirstOrderSemantics.sentence_correct hExt _).mpr
  intro f
  apply (SetTheory.Definitional.Project.Formula.satisfies_forallClosure_iff f
    (SetTheory.Axioms.Schema.separationCore φ)).mpr
  intro g
  let η : SetTheory.Env (FirstOrderSemantics.reduct 𝒩₁) n := ⟨g, f⟩
  let ξ := PowerlessSourceOpening.env_l (PowerlessProjectEnvironment.env_l η)
  let ψ := PowerlessSourceOpening.form_m (fo_formula φ.body φ.freeClosed)
  have hRead (x : N) : ψ.satisfies (ξ.pushFree x) ↔
      SetTheory.Definitional.Project.Formula.satisfies (η.push x) φ.body := by
    have hOpen := PowerlessSourceOpening.formula_l (fo_formula φ.body φ.freeClosed)
      ((PowerlessProjectEnvironment.env_l η).pushBound x)
    have hProject := PowerlessProjectEnvironment.formula_l hExt φ.body φ.freeClosed (η.push x)
    simpa only [PowerlessSourceOpening.push_l, PowerlessProjectEnvironment.push_l] using hOpen.trans hProject
  apply (SetTheory.Axioms.Schema.separation_sat_iff_d η φ).mpr
  intro A
  obtain ⟨Y, hY⟩ := PowerlessHereditaryFullSeparation.exists_l hB hNonempty ψ ξ A
  exact ⟨Y, fun x => (hY x).trans (and_congr Iff.rfl (hRead x))⟩

theorem collection_l (K : source_coding_l hℳ)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    {n : Nat} (φ : BinarySchema n) :
    (fo_sentence (SetTheory.Axioms.Schema.collection φ)).TrueIn 𝒩₁ := by
  have hExt := PowerlessHereditaryStructure.ext_l hℳ B hBase
  apply (FirstOrderSemantics.sentence_correct hExt _).mpr
  intro f
  apply (SetTheory.Definitional.Project.Formula.satisfies_forallClosure_iff f
    (SetTheory.Axioms.Schema.collectionCore φ)).mpr
  intro g
  let η : SetTheory.Env (FirstOrderSemantics.reduct 𝒩₁) n := ⟨g, f⟩
  let ξ := PowerlessSourceOpening.env_l (PowerlessProjectEnvironment.env_l η)
  let ψ := PowerlessSourceOpening.form_m (fo_formula φ.body φ.freeClosed)
  have hRead (x y : N) : ψ.satisfies ((ξ.pushFree x).pushFree y) ↔
      SetTheory.Definitional.Project.Formula.satisfies ((η.push x).push y) φ.body := by
    have hOpen := PowerlessSourceOpening.formula_l (fo_formula φ.body φ.freeClosed)
      (((PowerlessProjectEnvironment.env_l η).pushBound x).pushBound y)
    have hProject := PowerlessProjectEnvironment.formula_l hExt φ.body φ.freeClosed ((η.push x).push y)
    simpa only [PowerlessSourceOpening.push_l, PowerlessProjectEnvironment.push_l] using hOpen.trans hProject
  apply (SetTheory.Axioms.Schema.collection_sat_iff_d η φ).mpr
  intro A hSome
  obtain ⟨C, hC⟩ := PowerlessHereditaryFullCollection.exists_l K hB hNonempty ψ ξ A (by
    intro x hx
    obtain ⟨y, hy⟩ := hSome x hx
    exact ⟨y, (hRead x y).mpr hy⟩)
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨y, hyC, hy⟩ := hC x hx
  exact ⟨y, hyC, (hRead x y).mp hy⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryProjectSchemas
