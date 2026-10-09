import BMSConstructibleBridge.SecondOrderStageIndexFunction
import BMSConstructibleBridge.SecondOrderFunctionGraphComposition
import BMSConstructibleBridge.SecondOrderUnion
import BMSConstructibleBridge.SecondOrderWellOrderCoherentUnion
import BMSConstructibleBridge.PowerlessRelativeHierarchySemantics

/-! # 规范阶段编号下的实际层次函数与共同成员载体

已有 F 的定义域是实际阶段集合，规范根指标函数 J 将其改写为 ω 子集上的
实际函数。r 的并集覆盖每个层的全部成员；不要求 r 是精确值域，也不构造
所有比较图的幂集。比较图历史随后以 C×C 为子集界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderStageLayerFunction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def predecessor_m {Γ Δ : SortContext ℒ} (δ J D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff
    (SecondOrderObjectSyntax.member_m (.bvar .here) (D.weakenBound SetTheory.SetSort.set)) <|
      .existsE .set <| .conj
        (SecondOrderObjectSyntax.value_m ((J.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)
          (.bvar (.there .here)) (.bvar .here))
        (SecondOrderObjectSyntax.member_m (.bvar .here) ((δ.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set))

def predecessor_l (δ J D : type_l hℳ) : Prop :=
  ∀ i, mem_l hℳ i D ↔ ∃ a, value_l (ℳ := 𝒱) J i a ∧ mem_l hℳ a δ

theorem predecessor_formula_l {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (δ J D : Term ℒ Γ Δ .set) :
    (predecessor_m δ J D).satisfies η ↔ predecessor_l (δ.eval η) (J.eval η) (D.eval η) := by
  simp only [predecessor_m, predecessor_l, Formula.satisfies, ThirdOrderSemantics.value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

/-- 前驱域由实际指标函数分离出来；其存在性不依赖任何比较历史。 -/
theorem predecessor_exists_l {δ J I A : type_l hℳ} (hJ : map_l (ℳ := 𝒱) J I A) :
    ∃ D : type_l hℳ, subset_l (ℳ := 𝒱) D I ∧ predecessor_l δ J D := by
  let φ : Formula ℒ [] [.set, .set, .set] :=
    .existsE .set <| .conj (SecondOrderObjectSyntax.value_m
      (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there .here)))
  let η : Env 𝒱 [] [.set, .set] := (Env.empty.pushFree J).pushFree δ
  obtain ⟨D, hD⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) I
  have hRead i : φ.satisfies (η.pushFree i) ↔ ∃ a, value_l (ℳ := 𝒱) J i a ∧ mem_l hℳ a δ := by
    simp only [φ, Formula.satisfies, ThirdOrderSemantics.value_formula_l,
      SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
    rfl
  refine ⟨D, fun i hi => ((hD i).mp hi).1, fun i => ?_⟩
  constructor
  · exact fun hi => (hRead i).mp ((hD i).mp hi).2
  · rintro ⟨a, hia, ha⟩
    exact (hD i).mpr ⟨(SecondOrderFunctionLaws.value_mem_l hℳ hJ hia).1, (hRead i).mpr ⟨a, hia, ha⟩⟩

/-- 原层次极限并式直接给比较极限行所需的精确成员覆盖。 -/
theorem limit_cover_l {δ J I A D T F C : type_l hℳ}
    (hJ : map_l (ℳ := 𝒱) J I A)
    (hOnto : ∀ a, mem_l hℳ a A → ∃ i, mem_l hℳ i I ∧ value_l (ℳ := 𝒱) J i a)
    (hδ : subset_l (ℳ := 𝒱) δ A) (hD : predecessor_l δ J D)
    (hT : ∀ i X, value_l (ℳ := 𝒱) T i X ↔ ∃ a, value_l (ℳ := 𝒱) J i a ∧ value_l (ℳ := 𝒱) F a X)
    (hUnion : PowerlessRelativeHierarchySemantics.union_l hℳ F δ C) :
    SecondOrderWellOrderCoherentUnion.cover_l (ℳ₀ := 𝒱) C D T := by
  intro x
  refine (hUnion x).trans ⟨?_, ?_⟩
  · rintro ⟨a, X, ha, haX, hx⟩
    obtain ⟨i, _, hia⟩ := hOnto a (hδ a ha)
    exact ⟨i, X, (hD i).mpr ⟨a, hia, ha⟩, (hT i X).mpr ⟨a, hia, haX⟩, hx⟩
  · rintro ⟨i, X, hi, hiX, hx⟩
    obtain ⟨a, hia, ha⟩ := (hD i).mp hi
    obtain ⟨b, hib, hbX⟩ := (hT i X).mp hiX
    have hab := SecondOrderFunctionLaws.value_unique_l hℳ hJ hia hib
    exact ⟨a, X, ha, hab.symm ▸ hbX, hx⟩

theorem exists_l (K : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    {Q D R : SecondOrderModel.set_l ℳ} (h : SecondOrderOrdinalHierarchy.presentation_l A Q D R)
    (I : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (hI : setRel_l K I D)
    {F r : type_l hℳ} (hF : map_l (ℳ := 𝒱) F (SecondOrderQuotient.mk_l hℳ A) r) :
    ∃ T C : type_l hℳ,
      map_l (ℳ := 𝒱) T I.val r ∧
      (∀ i X, value_l (ℳ := 𝒱) T i X ↔
        ∃ n, ∃ hn : SecondOrderModel.mem_l n D,
          i = (numberCode_l K n).val ∧
          value_l (ℳ := 𝒱) F
            (SecondOrderQuotient.mk_l hℳ (SecondOrderRootCorrespondence.member_code_l hℳ A h n hn)) X) ∧
      (∀ x, mem_l hℳ x C ↔ ∃ X, mem_l hℳ X r ∧ mem_l hℳ x X) ∧
      ∀ i X, value_l (ℳ := 𝒱) T i X → subset_l (ℳ := 𝒱) X C := by
  obtain ⟨J, hJ, _, _, hJRead⟩ := SecondOrderStageIndexFunction.exists_l K A h I hI
  obtain ⟨T, hT, hRead⟩ := SecondOrderFunctionGraphComposition.exists_l hJ hF
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ a : type_l hℳ, ∃ c : type_l hℳ, ∀ x : type_l hℳ,
    mem_l hℳ x c ↔ ∃ y : type_l hℳ, mem_l hℳ y a ∧ mem_l hℳ x y at hUnion
  obtain ⟨C, hC⟩ := hUnion r
  refine ⟨T, C, hT, ?_, hC, ?_⟩
  · intro i X
    refine (hRead i X).trans ⟨?_, ?_⟩
    · rintro ⟨a, hia, haX⟩
      obtain ⟨n, hn, hi, rfl⟩ := (hJRead i a).mp hia
      exact ⟨n, hn, hi, haX⟩
    · rintro ⟨n, hn, hi, hnX⟩
      exact ⟨SecondOrderQuotient.mk_l hℳ (SecondOrderRootCorrespondence.member_code_l hℳ A h n hn),
        (hJRead i _).mpr ⟨n, hn, hi, rfl⟩, hnX⟩
  · intro i X hiX x hx
    exact (hC x).mpr ⟨X, (SecondOrderFunctionLaws.value_mem_l hℳ hT hiX).2, hx⟩

#print axioms exists_l
#print axioms predecessor_formula_l
#print axioms predecessor_exists_l
#print axioms limit_cover_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderStageLayerFunction
