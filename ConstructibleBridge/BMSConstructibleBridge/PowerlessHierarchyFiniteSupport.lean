import BMSConstructibleBridge.PowerlessFiniteSupport
import BMSConstructibleBridge.PowerlessHierarchyPresentation
import YesMetaZFC.Automation.ModelClosure

/-!
# 原累计层次图存在闭句的有限核心支持

公理支持的目标是原 hierarchy_m；参数保持任意内部 ω、序数和编码对象。
不把层次图存在或递归良基性加入理论，只从已有核心递归定理提取支持。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyFiniteSupport

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
  .imp (SecondOrderOmegaSyntax.omega_m (.fvar .here))
    (.imp (PowerlessOrdinal.ordinal_m (.fvar (.there (.there (.there (.there (.there (.there .here))))))))
      (.existsE .set (PowerlessHierarchyPresentation.hierarchy_m (.fvar .here) (.fvar (.there .here))
        (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there (.there (.there (.there .here))))))
        (.bvar .here) (.fvar (.there (.there (.there (.there (.there (.there .here))))))))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close formula_m

theorem sentence_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mpr
  intro η
  simp only [formula_m, Formula.satisfies, omega_formula_l,
    PowerlessOrdinal.ordinal_formula_l hℳ, PowerlessHierarchyPresentation.hierarchy_formula_l hℳ]
  intro hω hα
  obtain ⟨f, hf, _⟩ := PowerlessEvaluationHierarchy.exists_unique_l hℳ hω hα
    (η.freeVal (.there .here)) (η.freeVal (.there (.there .here)))
    (η.freeVal (.there (.there (.there .here))))
    (η.freeVal (.there (.there (.there (.there .here)))))
    (η.freeVal (.there (.there (.there (.there (.there .here))))))
  exact ⟨f, hf⟩

theorem finite_m : Nonempty (Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m) :=
  PowerlessFiniteSupport.finite_m (fun _ hℳ => sentence_l hℳ)

noncomputable def support_m : Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m :=
  Classical.choice finite_m

def theory_m : Theory ℒ := Theory.ofList support_m.sentences

theorem core_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : Theory.Models ℳ theory_m :=
  fun φ hφ => hℳ φ (support_m.subset φ hφ)

theorem satisfies_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (hℳ : Theory.Models ℳ theory_m)
    (η : Env ℳ [] [.set, .set, .set, .set, .set, .set, .set]) : formula_m.satisfies η :=
  (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mp
    (support_m.derivation.semantically_entails ℳ hℳ) η

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyFiniteSupport
