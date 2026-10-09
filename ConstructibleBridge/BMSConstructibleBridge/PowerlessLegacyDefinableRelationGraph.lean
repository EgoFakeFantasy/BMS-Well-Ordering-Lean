import BMSConstructibleBridge.PowerlessLegacyDefinableRelationBounded
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 原 Def 有界行证书的实际 Class 统一图

一次实际关系构图收集全部给定指标及母集元素，不收集逐行的独立层界。
原商全部坐标都有精确规格；类外坐标与母集外坐标无边。纯 Δ₀ 构图模式
已有原 Z₂ Derives；该模式尚未精确认同原 Def，也不是最终 BMS 结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableRelationGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def matrix_m {Δ : SortContext ℒ} (ω e N P F A S I U R : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  let w (t : Term ℒ [] Δ .set) := (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
  PowerlessLegacyDefinableRelationBounded.formula_m
    (w ω) (w e) (w N) (w P) (w F) (w A) (w S) (w I) (w U) (w R)
    (.fvar .here) (.fvar (.there .here))

theorem matrix_delta_l {Δ : SortContext ℒ} (ω e N P F A S I U R : Term ℒ [] Δ .set) :
    Formula.IsDelta0 membershipLevyBound (matrix_m ω e N P F A S I U R) :=
  PowerlessLegacyDefinableRelationBounded.delta_l _ _ _ _ _ _ _ _ _ _ _ _

theorem matrix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 [] Δ) (ω e N P F A S I U R : Term ℒ [] Δ .set) (i x : carrier_l 𝒩) :
    (matrix_m ω e N P F A S I U R).satisfies ((η.pushFree x).pushFree i) ↔
      PowerlessLegacyDefinableRelationBounded.holds_l
        (ω.eval η) (e.eval η) (N.eval η) (P.eval η) (F.eval η) (A.eval η)
          (S.eval η) (I.eval η) (U.eval η) (R.eval η) i x := by
  simp only [matrix_m, PowerlessLegacyDefinableRelationBounded.formula_l,
    Term.eval_weakenFree, Term.eval, Env.pushFree_here, Env.pushFree_there]

private abbrev context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    (ω e N P F A S I U R J : type_l hℳ B) : ∃ Q : type_l hℳ B,
      ∀ i x : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) Q.val i x ↔
          mem_l hℳ i J.val ∧ mem_l hℳ x A.val ∧
            PowerlessLegacyDefinableRelationBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
              ω.val e.val N.val P.val F.val A.val S.val I.val U.val R.val i x := by
  let η : Env (structure_l hℳ B hBase) [] context_m :=
    ((((((((((Env.empty).pushFree R).pushFree U).pushFree I).pushFree S).pushFree A).pushFree F).pushFree P).pushFree N).pushFree e).pushFree ω
  let w : Term ℒ [] context_m .set := .fvar .here
  let z : Term ℒ [] context_m .set := .fvar (.there .here)
  let seq : Term ℒ [] context_m .set := .fvar (.there (.there .here))
  let power : Term ℒ [] context_m .set := .fvar (.there (.there (.there .here)))
  let translate : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there .here))))
  let domain : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let assignments : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let indices : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let enumeration : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let satisfaction : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l
    (matrix_delta_l w z seq power translate domain assignments indices enumeration satisfaction) η J A
  refine ⟨Q, fun i x => ?_⟩
  have h := (hQ i x).trans (and_congr Iff.rfl (and_congr Iff.rfl
    (matrix_formula_l (PowerlessRelativeClassRelativization.env_l η)
      w z seq power translate domain assignments indices enumeration satisfaction i x)))
  exact h

def sentence_m {Δ : SortContext ℒ} (ω e N P F A S I U R : Term ℒ [] Δ .set) : Sentence ℒ :=
  PowerlessRelativeClassRelativization.guarded_m
    (SecondOrderDefinableRelationImageDerives.sentence_m (matrix_m ω e N P F A S I U R))

theorem derives_m {Δ : SortContext ℒ} (ω e N P F A S I U R : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω e N P F A S I U R)) :=
  PowerlessRelativeClassRelation.derives_m (matrix_delta_l ω e N P F A S I U R)

#print axioms matrix_delta_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableRelationGraph
