import BMSConstructibleBridge.PowerlessRelationalCollapseRestriction
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparation
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationWellOrder

/-! # 前驱优先序的实际封闭初段

纯隶属 ℒ，原 Z₂。在指定非零极限层中，用 I/J/p 三个实际参数
分离 E={x∈I : J(x,p)}。J 扩张 A 且传递、非自返时，E 对 A
前驱封闭、覆盖 p 的全部 A 前驱且不含 p。全坍缩 H/T 不参与分离。
本模块不假定或宣称任意良基关系的这种 J 已无条件构造出来。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseOrderedCut

open Logic FirstOrder StabilityFrame ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def extends_m {Γ Δ : SortContext ℒ} (I A J : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall I <| membershipLevyBound.boundedForall (up I) <|
    .imp (PowerlessValueBounded.formula_m (up (up A)) (.bvar (.there .here)) (.bvar .here))
      (PowerlessValueBounded.formula_m (up (up J)) (.bvar (.there .here)) (.bvar .here))

def cut_m {Γ Δ : SortContext ℒ} (I J p E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up E)) <|
    .conj (member_m (.bvar .here) (up I))
      (PowerlessValueBounded.formula_m (up J) (.bvar .here) (up p))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def extends_l (I A J : Raw) : Prop :=
  ∀ a, mem_l hℳ a I → ∀ b, mem_l hℳ b I →
    SecondOrderFunctionObjects.value_l hℳ A a b → SecondOrderFunctionObjects.value_l hℳ J a b

def cut_l (I J p E : Raw) : Prop :=
  ∀ x, mem_l hℳ x E ↔ mem_l hℳ x I ∧ SecondOrderFunctionObjects.value_l hℳ J x p

theorem extends_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (I A J : Term ℒ Γ Δ .set) : (extends_m I A J).satisfies η ↔
      extends_l (I.eval η) (A.eval η) (J.eval η) := by
  simp only [extends_m, extends_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem cut_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (I J p E : Term ℒ Γ Δ .set) : (cut_m I J p E).satisfies η ↔
      cut_l (I.eval η) (J.eval η) (p.eval η) (E.eval η) := by
  simp only [cut_m, cut_l, Formula.satisfies, PowerlessValueBounded.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def result_l (L A I J p : Raw) : Prop :=
  ∃ E, mem_l hℳ E L ∧ cut_l I J p E ∧
    (∀ a, mem_l hℳ a E → ∀ b, mem_l hℳ b I →
      SecondOrderFunctionObjects.value_l hℳ A b a → mem_l hℳ b E) ∧
    (∀ b, mem_l hℳ b I → SecondOrderFunctionObjects.value_l hℳ A b p → mem_l hℳ b E) ∧
    ¬mem_l hℳ p E

theorem exists_l {B β L A I J p : Raw}
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hL : PowerlessRelativeHierarchySemantics.level_l hℳ B β L)
    (hIL : mem_l hℳ I L) (hJL : mem_l hℳ J L) (hpL : mem_l hℳ p L)
    (hpI : mem_l hℳ p I)
    (hTrans : ∀ a b c, mem_l hℳ a I ∧ mem_l hℳ b I ∧ mem_l hℳ c I →
      SecondOrderFunctionObjects.value_l hℳ J a b →
      SecondOrderFunctionObjects.value_l hℳ J b c → SecondOrderFunctionObjects.value_l hℳ J a c)
    (hIrrefl : ∀ a, mem_l hℳ a I → ¬SecondOrderFunctionObjects.value_l hℳ J a a)
    (hExtends : extends_l I A J) : result_l L A I J p := by
  let η : Env 𝒱 [] [.set, .set] := Env.empty |>.pushFree J |>.pushFree p
  let φ : Formula ℒ [] [.set, .set, .set] :=
    PowerlessValueBounded.formula_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  have hφ : Formula.IsDelta0 membershipLevyBound φ := PowerlessValueBounded.delta_l _ _ _
  have hBody x : φ.satisfies (η.pushFree x) ↔ SecondOrderFunctionObjects.value_l hℳ J x p :=
    PowerlessValueBounded.formula_l (η.pushFree x) _ _ _
  obtain ⟨E, hEL, hE⟩ := PowerlessRelativeLimitDeltaSeparation.exists_l hBase hLimit hL hφ η hIL (by
    intro s v
    cases v with
    | here => exact hpL
    | there v => cases v with
      | here => exact hJL
      | there v => nomatch v)
  have hCut : cut_l I J p E := fun x => (hE x).trans (and_congr Iff.rfl (hBody x))
  refine ⟨E, hEL, hCut, ?_, ?_, ?_⟩
  · intro a ha b hb hba
    obtain ⟨haI, hap⟩ := (hCut a).mp ha
    exact (hCut b).mpr ⟨hb, hTrans b a p ⟨hb, haI, hpI⟩ (hExtends b hb a haI hba) hap⟩
  · intro b hb hbp
    exact (hCut b).mpr ⟨hb, hExtends b hb p hpI hbp⟩
  · intro hpE
    exact hIrrefl p hpI ((hCut p).mp hpE).2

def result_m {Γ Δ : SortContext ℒ} (L A I J p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (member_m (.bvar .here) (up L)) <|
    .conj (cut_m (up I) (up J) (up p) (.bvar .here)) <|
      .conj (PowerlessRelationalCollapsePartial.closed_m (up A) (up I) (.bvar .here)) <|
        .conj (PowerlessRelationalCollapseOutput.covered_m (up A) (up I) (.bvar .here) (up p))
          (.neg (member_m (up p) (.bvar .here)))

theorem result_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (L A I J p : Term ℒ Γ Δ .set) : (result_m L A I J p).satisfies η ↔
      result_l (L.eval η) (A.eval η) (I.eval η) (J.eval η) (p.eval η) := by
  simp only [result_m, result_l, Formula.satisfies, cut_formula_l,
    PowerlessRelationalCollapseRestriction.closed_formula_l,
    PowerlessRelationalCollapseOutput.covered_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (B β L A I J p : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β L) <|
        .imp (member_m I L) <| .imp (member_m J L) <| .imp (member_m p L) <| .imp (member_m p I) <|
          .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m I J) <|
            .imp (extends_m I A J) (result_m L A I J p)

def sentence_m {Δ : SortContext ℒ} (B β L A I J p : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β L A I J p)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β L A I J p : Term ℒ [] Δ .set) : (sentence_m B β L A I J p).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, result_formula_l,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    extends_formula_l, member_m, Arguments.eval]
  exact fun hBase hLimit hL hI hJ hp hpI hOrder hExtends =>
    exists_l (hℳ := hℳ) hBase hLimit hL hI hJ hp hpI hOrder.2.1 hOrder.1 hExtends

theorem derives_m {Δ : SortContext ℒ} (B β L A I J p : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B β L A I J p)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β L A I J p)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseOrderedCut
