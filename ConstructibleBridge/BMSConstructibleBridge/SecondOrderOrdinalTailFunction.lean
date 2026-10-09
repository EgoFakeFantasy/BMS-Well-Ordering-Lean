import BMSConstructibleBridge.SecondOrderRootedNumericFunction
import BMSConstructibleBridge.SecondOrderOrdinalTailMembers
import BMSConstructibleBridge.PowerlessFunctionIteration
import BMSConstructibleBridge.PowerlessRelativeHierarchySemantics

/-! # 全部内部序数尾节点的实际 ω 值图

输入同一实际尾图和其集合包络，用原 Z₂ 理解与混合像构造无限函数。
随后逐步验证它确实迭代给定后继图；这里不预设函数图属于相对类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalTailFunction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {S G : SecondOrderModel.set_l ℳ} {r : SecondOrderModel.num_l ℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ)
    (hG : SecondOrderOrdinalTailGraph.spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a)
    (C : type_l hℳ) (hC : ∀ n, mem_l hℳ (mk_l hℳ (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n)) C) :
    ∃ F : type_l hℳ, map_l (ℳ := 𝒱) F K.omega C ∧
      ∀ n y, value_l (ℳ := 𝒱) F (numberCode_l K n).val y ↔
        y = mk_l hℳ (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n) := by
  let one : Term SecondOrderSyntax.signature_m [] [.num, .num] .num :=
    .app (σ := SecondOrderSyntax.signature_m) .succ
      (.cons (.app (σ := SecondOrderSyntax.signature_m) .zero .nil) .nil)
  let φ : Formula SecondOrderSyntax.signature_m [] [.num, .num] :=
    PrimitiveFormulas.pair_m one (.fvar .here) (.fvar (.there .here))
  obtain ⟨E, hE⟩ := SecondOrderRelations.comprehension_l hℳ φ
    (SecondOrderArithmetic.pure_language_m _ rfl) Env.empty
  have hRead (n m : SecondOrderModel.num_l ℳ) : SecondOrderPairing.relation_l E n m ↔
      SecondOrderPairing.value_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)) n = m := by
    have hnm := hE n m
    simp only [φ, SecondOrderPairing.formula_l] at hnm
    simpa only [one, Term.eval, Arguments.eval, Env.pushFree, Assignment.push,
      SecondOrderModel.zero_l, SecondOrderModel.succ_l] using hnm
  have hFunction : SecondOrderFunctions.function_l E := fun n =>
    ⟨_, (hRead n _).mpr rfl, fun m hm => ((hRead n m).mp hm).symm⟩
  obtain ⟨F, hF, hValue⟩ := SecondOrderRootedNumericFunction.exists_l K G
    (SecondOrderOrdinalTailGraph.wf_l hℳ hG hS) hFunction C (fun n m hnm => by
      obtain rfl := (hRead n m).mp hnm
      exact hC n)
  refine ⟨F, hF, fun n y => ?_⟩
  rw [hValue]
  constructor
  · rintro ⟨i, j, hij, hni, hyj⟩
    have hin : i = n := numberCode_injective_l K (Subtype.ext hni.symm)
    subst i
    obtain rfl := (hRead n j).mp hij
    exact hyj
  · intro hy
    exact ⟨n, _, (hRead n _).mpr rfl, rfl, hy⟩

theorem successor_l (hG : SecondOrderOrdinalTailGraph.spec_l S r G)
    (hS : ∀ a, SecondOrderDomain.wf_l S a) (n : SecondOrderModel.num_l ℳ) :
    PowerlessRelativeHierarchySemantics.successor_l hℳ
      (mk_l hℳ (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n))
      (mk_l hℳ (SecondOrderOrdinalTailGraph.code_l hℳ hG hS (SecondOrderModel.succ_l n))) := by
  intro x
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact (SecondOrderOrdinalTailMembers.successor_l hℳ hG hS n X).trans
    (or_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ _ _).symm)

theorem iteration_l (K : source_coding_l hℳ)
    (hG : SecondOrderOrdinalTailGraph.spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a)
    {C H F : type_l hℳ} (hF : map_l (ℳ := 𝒱) F K.omega C)
    (hRead : ∀ n y, value_l (ℳ := 𝒱) F (numberCode_l K n).val y ↔
      y = mk_l hℳ (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n))
    (hH : ∀ x y, mem_l hℳ x C → mem_l hℳ y C →
      PowerlessRelativeHierarchySemantics.successor_l hℳ x y → value_l (ℳ := 𝒱) H x y) :
    PowerlessFunctionIteration.iteration_l (ℳ := 𝒱) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val C H
      (mk_l hℳ (SecondOrderOrdinalTailGraph.code_l hℳ hG hS (SecondOrderModel.zero_l ℳ))) F := by
  refine ⟨hF, (hRead _ _).mpr rfl, ?_⟩
  intro n m x y hn hnm hx hy
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have hin : (numberCode_l K i).val = n := congrArg Subtype.val hi
  have hm : m = (numberCode_l K (SecondOrderModel.succ_l i)).val :=
    PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) (hin.symm ▸ hnm)
      (PowerlessBMSQuotientSuccessor.successor_l K i)
  have hx' := (hRead i x).mp (hin.symm ▸ hx)
  have hy' := (hRead (SecondOrderModel.succ_l i) y).mp (hm ▸ hy)
  exact hH x y (SecondOrderFunctionProperties.value_mem_l hℳ hF hx).2
    (SecondOrderFunctionProperties.value_mem_l hℳ hF hy).2
    (hx'.symm ▸ hy'.symm ▸ successor_l hG hS i)

#print axioms exists_l
#print axioms iteration_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalTailFunction
