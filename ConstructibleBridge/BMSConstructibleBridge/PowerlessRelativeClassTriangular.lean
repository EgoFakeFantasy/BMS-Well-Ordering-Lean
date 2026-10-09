import BMSConstructibleBridge.PowerlessBoundedTriangular
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessRelativeClassBoundedArithmetic
import BMSConstructibleBridge.PowerlessTriangular

/-! # 相对类内的实际三角递推图

以纯 Δ₀ 多项式检查构图，再逐内部数根码验证原三角递推。
类内存在使用有界函数关系接口，不假定整类满足 PowerlessTheory 或 Collection。
序列参数必须在原商中具有全有限 ω 序列规格，而不只有类内规格。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassTriangular

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem absolute_l (ω e S n t : type_l hℳ B) :
    PowerlessBoundedTriangular.holds_l (𝒩 := structure_l hℳ B hBase) ω e S n t ↔
      PowerlessBoundedTriangular.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val e.val S.val n.val t.val := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set] :=
    ((((Env.empty.pushFree t).pushFree n).pushFree S).pushFree e).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let s : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let x : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let y : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  exact (PowerlessBoundedTriangular.formula_l η w z s x y).symm.trans
    ((PowerlessRelativeClassBounded.formula_l (hBase := hBase)
      (PowerlessBoundedTriangular.delta_l w z s x y) η).trans
      (PowerlessBoundedTriangular.formula_l (PowerlessRelativeClassRelativization.env_l η) w z s x y))

theorem exists_spec_l (K : source_coding_l hℳ) (ω e S : type_l hℳ B)
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S.val) :
    ∃ T : type_l hℳ B, PowerlessTriangular.triangular_l (ℳ := structure_l hℳ B hBase) ω e T ∧
      ∀ i j : SecondOrderModel.num_l ℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val (numberCode_l K i).val (numberCode_l K j).val ↔
          SecondOrderTriangularArithmetic.relation_l i j := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set] :=
    ((Env.empty.pushFree S).pushFree e).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := PowerlessBoundedTriangular.formula_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  have hRead (n t : type_l hℳ B) : φ.satisfies ((η.pushFree t).pushFree n) ↔
      PowerlessBoundedTriangular.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S.val n.val t.val := by
    have hφ := PowerlessBoundedTriangular.formula_l ((η.pushFree t).pushFree n)
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
    exact hφ.trans ((absolute_l ω e S n t).trans (by rw [hω, he]))
  have hTotal (n : type_l hℳ B) (hn : mem_l hℳ n.val ω.val) :
      ∃! t : type_l hℳ B, mem_l hℳ t.val ω.val ∧ φ.satisfies ((η.pushFree t).pushFree n) := by
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.val, hω ▸ hn⟩
    have hi' : (numberCode_l K i).val = n.val := congrArg Subtype.val hi
    obtain ⟨j, hj⟩ := SecondOrderTriangularArithmetic.exists_l hℳ i
    let t : type_l hℳ B := ⟨(numberCode_l K j).val,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property (hω.symm ▸ (numberCode_l K j).property)⟩
    refine ⟨t, ⟨hω.symm ▸ (numberCode_l K j).property, ?_⟩, ?_⟩
    · apply (hRead n t).mpr
      rw [← hi']
      exact (PowerlessBoundedTriangular.instance_l K hS i j).mpr hj
    · rintro v ⟨hvω, hv⟩
      obtain ⟨l, hl⟩ := numberCode_surjective_l K ⟨v.val, hω ▸ hvω⟩
      have hl' : (numberCode_l K l).val = v.val := congrArg Subtype.val hl
      have hv' := (hRead n v).mp hv
      rw [← hi', ← hl'] at hv'
      have hlj := SecondOrderTriangularArithmetic.unique_l hℳ
        ((PowerlessBoundedTriangular.instance_l K hS i l).mp hv') hj
      apply Subtype.ext
      exact hl'.symm.trans (congrArg (fun q => (numberCode_l K q).val) hlj)
  obtain ⟨T, hT, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (φ := φ) (PowerlessBoundedTriangular.delta_l _ _ _ _ _) η ω ω hTotal
  have hCodes (n t : type_l hℳ B) (i j : SecondOrderModel.num_l ℳ)
      (hi : n.val = (numberCode_l K i).val) (hj : t.val = (numberCode_l K j).val) :
      value_l (ℳ := structure_l hℳ B hBase) T n t ↔ SecondOrderTriangularArithmetic.relation_l i j := by
    rw [hValue n t, hRead n t, hω, hi, hj]
    exact (and_iff_right (numberCode_l K i).property).trans
      ((and_iff_right (numberCode_l K j).property).trans (PowerlessBoundedTriangular.instance_l K hS i j))
  have hCodesNative (i j : SecondOrderModel.num_l ℳ) :
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val (numberCode_l K i).val (numberCode_l K j).val ↔
        SecondOrderTriangularArithmetic.relation_l i j := by
    let n : type_l hℳ B := ⟨(numberCode_l K i).val,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property (hω.symm ▸ (numberCode_l K i).property)⟩
    let t : type_l hℳ B := ⟨(numberCode_l K j).val,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property (hω.symm ▸ (numberCode_l K j).property)⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) T n t).symm.trans
      (hCodes n t i j rfl rfl)
  refine ⟨T, ⟨hT, ?_, ?_⟩, hCodesNative⟩
  · apply (hCodes e e _ _ he he).mpr
    change SecondOrderModel.add_l (SecondOrderModel.zero_l ℳ) (SecondOrderModel.zero_l ℳ) =
      SecondOrderModel.mul_l (SecondOrderModel.zero_l ℳ) (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))
    rw [SecondOrderModel.add_zero_l hℳ, SecondOrderMultiplication.zero_mul_l hℳ]
  · intro n m x y hn hm hx hy
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.val, hω ▸ hn⟩
    have hi' : n.val = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
    have hm' := (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) n m).mp hm
    rw [hi'] at hm'
    have hmCode := PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ)
      (a := (numberCode_l K i).val) (b := m.val) (c := (numberCode_l K (SecondOrderModel.succ_l i)).val)
      hm' (PowerlessBMSQuotientSuccessor.successor_l K i)
    have hNativeMap := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) T ω ω).mp hT
    have hxNative := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) T n x).mp hx
    have hyNative := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) T m y).mp hy
    obtain ⟨j, hj⟩ := numberCode_surjective_l K
      ⟨x.val, hω ▸ (SecondOrderFunctionProperties.value_mem_l hℳ hNativeMap hxNative).2⟩
    obtain ⟨l, hl⟩ := numberCode_surjective_l K
      ⟨y.val, hω ▸ (SecondOrderFunctionProperties.value_mem_l hℳ hNativeMap hyNative).2⟩
    have hj' : x.val = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
    have hl' : y.val = (numberCode_l K l).val := (congrArg Subtype.val hl).symm
    apply (PowerlessRelativeClassAdditionAbsolute.instance_l K hω he hj' hmCode).mpr
    rw [hl']
    exact congrArg (fun q => (numberCode_l K q).val)
      (SecondOrderTriangularArithmetic.successor_l hℳ ((hCodes n x i j hi' hj').mp hx)
        ((hCodes m y (SecondOrderModel.succ_l i) l hmCode hl').mp hy))

theorem exists_l (K : source_coding_l hℳ) (ω e S : type_l hℳ B)
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S.val) :
    ∃ T : type_l hℳ B, PowerlessTriangular.triangular_l (ℳ := structure_l hℳ B hBase) ω e T := by
  obtain ⟨T, hT, _⟩ := exists_spec_l K ω e S hω he hS
  exact ⟨T, hT⟩

#print axioms absolute_l
#print axioms exists_spec_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassTriangular
