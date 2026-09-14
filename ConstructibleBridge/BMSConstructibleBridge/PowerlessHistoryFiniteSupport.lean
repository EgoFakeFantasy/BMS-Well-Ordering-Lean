import BMSConstructibleBridge.PowerlessFiniteSupport
import BMSConstructibleBridge.PowerlessOrdinalHistoryCut
import YesMetaZFC.Automation.ModelClosure

/-!
# 任意序数前史存在闭句的有限核心支持

正文是原 history_l 的纯公式呈现，保留全部候选有序对与图值量词。
不将前史限制到有限图，也不要求输入是函数或序数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHistoryFiniteSupport

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def history_m {Γ Δ : SortContext ℒ} (H f a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) :=
    ((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.iff
    (SecondOrderObjectSyntax.member_m (.bvar .here) (H.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.existsE .set (.conj
      (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))
      (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (w a))
        (SecondOrderObjectSyntax.value_m (w f) (.bvar (.there .here)) (.bvar .here)))))))

theorem history_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (H f a : Term ℒ Γ Δ .set) :
    (history_m H f a).satisfies η ↔ PowerlessOrdinalRecursion.history_l (H.eval η) (f.eval η) (a.eval η) := by
  simp only [history_m, PowerlessOrdinalRecursion.history_l, Formula.satisfies,
    ordered_formula_l, value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def formula_m : Formula ℒ [] [.set, .set] :=
  .existsE .set (history_m (.bvar .here) (.fvar .here) (.fvar (.there .here)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close formula_m

theorem sentence_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mpr
  intro η
  simpa only [formula_m, Formula.satisfies, history_formula_l, Term.eval, Env.pushBound, Assignment.push] using
    (PowerlessOrdinalHistoryCut.exists_l hℳ (η.freeVal .here) (η.freeVal (.there .here)))

theorem finite_m : Nonempty (Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m) :=
  PowerlessFiniteSupport.finite_m (fun _ hℳ => sentence_l hℳ)

noncomputable def support_m : Derives.FiniteTheorySupport PowerlessTheory.theory_m [] sentence_m :=
  Classical.choice finite_m

def theory_m : Theory ℒ := Theory.ofList support_m.sentences

theorem core_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : Theory.Models ℳ theory_m :=
  fun φ hφ => hℳ φ (support_m.subset φ hφ)

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ theory_m) (f a : carrier_l ℳ) :
    ∃ H, PowerlessOrdinalRecursion.history_l H f a := by
  let η : Env ℳ [] [.set, .set] := (Env.empty.pushFree a).pushFree f
  have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff formula_m).mp
    (support_m.derivation.semantically_entails ℳ hℳ) η
  simpa only [formula_m, Formula.satisfies, history_formula_l, Term.eval, Env.pushBound,
    η, Env.pushFree, Assignment.push] using h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHistoryFiniteSupport
