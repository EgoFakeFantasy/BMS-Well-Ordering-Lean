import BMSConstructibleBridge.SecondOrderLegalFormulaIndex
import BMSConstructibleBridge.SecondOrderSelectedSubsetCollection
import BMSConstructibleBridge.SecondOrderMemberStructure
import BMSConstructibleBridge.SecondOrderSubsetExact
import BMSConstructibleBridge.SecondOrderDefinableRespect

/-!
# 非空成员结构的合法内部公式切片收集

同时保存合法性、内部求值器及精确索引筛选，实际集合只收集合法公式和有效
参数赋值的切片。全部源公式覆盖仍作为独立规格给出。这里是数码呈现接口，
尚未完成纯集合对象 Def 公式及其对象推导，不宣称相对 L* 或 BMS 终局成立。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegalMemberCollection

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

structure presentation_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) (V E D Q R T F : set_l ℳ)
    (H : SecondOrderGraph.code_l ℳ) : Prop where
  formula_codes : SecondOrderInternalFormulaSyntax.spec_l V
  powers : SecondOrderBinaryPowers.spec_l E
  domain : ∀ n, mem_l n D
  equality : ∀ n m, relation_l Q n m ↔
    SecondOrderMemberStructure.value_l hℳ A a ha n = SecondOrderMemberStructure.value_l hℳ A a ha m
  membership : ∀ n m, relation_l R n m ↔
    SecondOrderSourceSatisfaction.member_l (SecondOrderMemberStructure.structure_l hℳ A a ha)
      (SecondOrderMemberStructure.value_l hℳ A a ha n) (SecondOrderMemberStructure.value_l hℳ A a ha m)
  evaluation : SecondOrderEvaluationEquations.spec_l E D Q R T
  family : SecondOrderDefinableFamily.spec_l E D T F
  collection : ∀ B, SecondOrderGraph.mem_l B H ↔
    ∃ i, SecondOrderLegalFormulaIndex.spec_l V E i ∧ ∀ C, SecondOrderGraph.mem_l C B ↔
      ∃ n, relation_l A.real n A.root ∧ relation_l F i n ∧
        SecondOrderBisimulation.eq_l C.real A.real C.root n

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) :
    ∃ V E D Q R T F H, presentation_l hℳ A a ha V E D Q R T F H ∧
      ∀ (Γ Δ : SortContext ℒ) (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ)
        (φ : Formula ℒ (.set :: Γ) Δ), ∃ B, SecondOrderGraph.mem_l B H ∧
          ∀ n (hn : relation_l A.real n A.root),
            SecondOrderGraph.mem_l (SecondOrderGraph.child_l hℳ A n hn) B ↔
              φ.satisfies (η.pushBound (SecondOrderMemberStructure.value_l hℳ A a ha n)) := by
  let f := SecondOrderMemberStructure.value_l hℳ A a ha
  obtain ⟨D, Q, R, hD, hQ, hR⟩ := SecondOrderMemberStructure.graphs_l hℳ A a ha
  have hS y : ∃ n, mem_l n D ∧ f n = y := by
    obtain ⟨n, hn⟩ := SecondOrderMemberStructure.surjective_l hℳ A a ha y
    exact ⟨n, hD n, hn⟩
  obtain ⟨V, hV, _⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  obtain ⟨T, hT, _⟩ := SecondOrderEvaluationFixedPoint.exists_l hℳ E D Q R
  obtain ⟨F, hF, _⟩ := SecondOrderDefinableFamily.exists_l hℳ E D T
  let η₀ := ((Env.empty (M := ℳ)).pushFree E).pushFree V
  obtain ⟨H, hH⟩ := SecondOrderSelectedSubsetCollection.family_l hℳ
    SecondOrderLegalFormulaIndex.formula_m SecondOrderLegalFormulaIndex.pure_m η₀ A F
  have hCollection B : SecondOrderGraph.mem_l B H ↔
      ∃ i, SecondOrderLegalFormulaIndex.spec_l V E i ∧ ∀ C, SecondOrderGraph.mem_l C B ↔
        ∃ n, relation_l A.real n A.root ∧ relation_l F i n ∧
          SecondOrderBisimulation.eq_l C.real A.real C.root n := by
    refine (hH B).trans (exists_congr (fun i => and_congr ?_ Iff.rfl))
    exact SecondOrderLegalFormulaIndex.formula_l _
  refine ⟨V, E, D, Q, R, T, F, H, ⟨hV, hE, hD, hQ, hR, hT, hF, hCollection⟩, ?_⟩
  intro Γ Δ η φ
  obtain ⟨l, c, hc, hη⟩ := SecondOrderSourceAssignment.exists_l hℳ hE D f hS η
  let i := SecondOrderDefinableFamily.index_l (SecondOrderFormulaCompilation.formula_l ℳ φ) l c
  have hi : SecondOrderLegalFormulaIndex.spec_l V E i :=
    (SecondOrderLegalFormulaIndex.index_l hℳ V E _ l c).mpr
      ⟨hc, SecondOrderInternalFormulaCompilation.extension_l hℳ hV f η hc hη φ⟩
  have hRead n : relation_l F i n ↔
      φ.satisfies (η.pushBound (f n)) := by
    exact (SecondOrderDefinableCoverage.formula_l hℳ hE D Q R T F hT hF f hS
      (fun x y _ _ => hQ x y) (fun x y _ _ => hR x y) φ η l c hc hη n).trans
        (and_iff_right (hD n))
  obtain ⟨G, hG⟩ := SecondOrderSubsetLayer.exists_l hℳ A.real F A.root
  let B := SecondOrderSubsetLayer.code_l hℳ A F G hG i
  have hBH : SecondOrderGraph.mem_l B H := (hCollection B).mpr
    ⟨i, hi, SecondOrderSubsetLayer.mem_l hℳ A F G hG i⟩
  refine ⟨B, hBH, fun n hn => ?_⟩
  rw [SecondOrderSubsetLayer.mem_l hℳ A F G hG i]
  constructor
  · rintro ⟨m, hm, hFm, hnm⟩
    have hValue : f n = f m := by
      apply Subtype.ext
      change SecondOrderQuotient.mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha n) =
        SecondOrderQuotient.mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha m)
      rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha n hn,
        SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha m hm]
      exact (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr hnm
    have hφ := (hRead m).mp hFm
    change φ.satisfies (η.pushBound (f n))
    rw [hValue]
    exact hφ
  · intro hφ
    exact ⟨n, hn, (hRead n).mpr hφ, SecondOrderBisimulation.refl_l hℳ A.real n⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegalMemberCollection
