import BMSConstructibleBridge.PowerlessFiniteClosureSyntax
import BMSConstructibleBridge.PowerlessWeakSeparationSyntax
import BMSConstructibleBridge.SecondOrderWeakSetTheory
import BMSConstructibleBridge.PowerlessFiniteSupport

/-!
# 由闭合超集分离最小有限子集闭包

交取所有包含原集合的有限子集闭合类，但只在给定超集内实施分离。
量词遍历模型自身的所有集合，不要求候选闭合超集传递，不使用收集或幂集。
最后给出原弱集合论中的条件式对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteClosureMinimum

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax PowerlessFiniteClosureSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def member_m {Γ Δ : SortContext ℒ} (ω x z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp
    (.conj (subset_m (x.weakenBound SetTheory.SetSort.set) (.bvar .here))
      (closed_m (ω.weakenBound SetTheory.SetSort.set) (.bvar .here)))
    (SecondOrderObjectSyntax.member_m (z.weakenBound SetTheory.SetSort.set) (.bvar .here)))

theorem member_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω x z : Term ℒ Γ Δ .set) : (member_m ω x z).satisfies η ↔
      ∀ b, subset_l (x.eval η) b → closed_l (ω.eval η) b →
        ThirdOrderSemantics.member_l ℳ (z.eval η) b := by
  simp only [member_m, Formula.satisfies, PowerlessFiniteClosureSyntax.subset_formula_l, closed_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval, Term.eval_weakenBound, and_imp]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderWeakSetTheory.theory_m)
    (ω x b : carrier_l ℳ) (hxb : subset_l x b) (hb : closed_l ω b) :
    ∃ c, closure_l ω x c := by
  let φ : Formula ℒ [] [.set, .set, .set] :=
    member_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  let η : Env ℳ [] [.set, .set] := ((Env.empty (M := ℳ)).pushFree ω).pushFree x
  have hφ z : φ.satisfies (η.pushFree z) ↔
      ∀ d, subset_l x d → closed_l ω d → ThirdOrderSemantics.member_l ℳ z d :=
    member_formula_l _ _ _ _
  have hSep := hℳ _ (SecondOrderWeakSetTheory.axiom_m.separation φ)
  have hSep' := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp hSep η
  obtain ⟨c, hc⟩ := (PowerlessWeakSeparationSyntax.schema_formula_l φ η).mp hSep' b
  have hmem z : ThirdOrderSemantics.member_l ℳ z c ↔
      ThirdOrderSemantics.member_l ℳ z b ∧
        ∀ d, subset_l x d → closed_l ω d → ThirdOrderSemantics.member_l ℳ z d :=
    (hc z).trans (and_congr Iff.rfl (hφ z))
  refine ⟨c, ?_, ?_, ?_⟩
  · intro z hz
    exact (hmem z).mpr ⟨hxb z hz, fun d hxd _ => hxd z hz⟩
  · intro a ha hac
    refine (hmem a).mpr ⟨hb a ha (fun z hz => ((hmem z).mp (hac z hz)).1), ?_⟩
    intro d hxd hd
    exact hd a ha (fun z hz => ((hmem z).mp (hac z hz)).2 d hxd hd)
  · intro d hxd hd z hz
    exact ((hmem z).mp hz).2 d hxd hd

def sentence_m : Sentence ℒ :=
  .forallE .set (.forallE .set (.forallE .set (.imp
    (.conj (subset_m (.bvar (.there .here)) (.bvar .here))
      (closed_m (.bvar (.there (.there .here))) (.bvar .here)))
    (.existsE .set (closure_m (.bvar (.there (.there (.there .here))))
      (.bvar (.there (.there .here))) (.bvar .here))))))

theorem sentence_formula_l : sentence_m.TrueIn ℳ ↔
    ∀ ω x b : carrier_l ℳ, subset_l x b → closed_l ω b → ∃ c, closure_l ω x c := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, PowerlessFiniteClosureSyntax.subset_formula_l,
    closed_formula_l, closure_formula_l, Term.eval, and_imp]
  rfl

theorem derives_m : Derives SecondOrderWeakSetTheory.theory_m [] sentence_m :=
  PowerlessFiniteSupport.derives_m (fun _ hℳ => sentence_formula_l.mpr (exists_l hℳ))

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteClosureMinimum
