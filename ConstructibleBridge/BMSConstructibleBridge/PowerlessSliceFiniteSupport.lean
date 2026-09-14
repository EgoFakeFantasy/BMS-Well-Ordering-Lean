import BMSConstructibleBridge.PowerlessFiniteSupport
import BMSConstructibleBridge.PowerlessEvaluationSlice
import YesMetaZFC.Automation.ModelClosure

/-! # 原求值切片存在闭句的有限核心支持

固定原公式经完整核心的语义定理取得原 Hilbert 推导，再抽出有限列表。
成员结构仅需满足该列表，不假定完整分离或收集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSliceFiniteSupport

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  .existsE .set (PowerlessEvaluationSlice.slice_m (.fvar .here) (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close formula_m

theorem sentence_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mpr
  intro η
  simpa only [formula_m, Formula.satisfies, PowerlessEvaluationSlice.slice_formula_l, Term.eval, Env.pushBound, Assignment.push] using
    (PowerlessEvaluationSlice.exists_l hℳ (η.freeVal .here) (η.freeVal (.there .here))
      (η.freeVal (.there (.there .here))) (η.freeVal (.there (.there (.there .here))))
      (η.freeVal (.there (.there (.there (.there .here))))))

theorem finite_m : Nonempty (Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m) :=
  PowerlessFiniteSupport.finite_m (fun _ hℳ => sentence_l hℳ)

noncomputable def support_m : Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m :=
  Classical.choice finite_m

def theory_m : Theory ℒ := Theory.ofList support_m.sentences

theorem core_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : Theory.Models ℳ theory_m :=
  fun φ hφ => hℳ φ (support_m.subset φ hφ)

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ theory_m) (ω A F c f : carrier_l ℳ) :
    ∃ Y, PowerlessEvaluationSlice.slice_l ω A F c f Y := by
  let η : Env ℳ [] [.set, .set, .set, .set, .set] :=
    ((((Env.empty.pushFree f).pushFree c).pushFree F).pushFree A).pushFree ω
  have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mp
    (support_m.derivation.semantically_entails ℳ hℳ) η
  simpa only [formula_m, Formula.satisfies, PowerlessEvaluationSlice.slice_formula_l, Term.eval, Env.pushBound,
    η, Env.pushFree, Assignment.push] using h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSliceFiniteSupport
