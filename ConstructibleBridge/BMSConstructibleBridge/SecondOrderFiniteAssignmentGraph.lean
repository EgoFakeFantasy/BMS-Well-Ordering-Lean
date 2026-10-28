import BMSConstructibleBridge.SecondOrderLegacyAssignmentPadding
import BMSConstructibleBridge.SecondOrderMixedImage
import BMSConstructibleBridge.SecondOrderFunctionLaws
import BMSConstructibleBridge.PowerlessBMSQuotientCoding
import BMSConstructibleBridge.SecondOrderOmegaTransitive

/-! # 任意内部赋值数码的实际商函数图

原读取图先由实际二阶公式理解，再用两端自然数图的混合有序对像提升。
所得有限函数图是商对象，不是宿主函数；逐值规格也排除所有非数输出。
本模块是求值保持的中间构造，尚不单独声明原 Def 或 BMS 对象定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteAssignmentGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderQuotient (type_l mk_l)
open PowerlessBMSQuotientCoding
open SecondOrderSequenceSyntax (read_l)
open SecondOrderAssignmentSyntax (valid_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ theory_m}

theorem exists_l (K : source_coding_l hℳ) {E : set_l ℳ} {c l : num_l ℳ}
    (hc : valid_l E c l) :
    ∃ F : type_l hℳ,
      SecondOrderFunctionObjects.map_l hℳ F (numberCode_l K l).val K.omega ∧
      ∀ i : num_l ℳ, ∀ y : type_l hℳ,
        SecondOrderFunctionObjects.value_l hℳ F (numberCode_l K i).val y ↔
          ∃ j, read_l E c i j ∧ y = (numberCode_l K j).val := by
  let φ : Formula signature_m [] [.num, .num, .set, .num] :=
    SecondOrderSequenceSyntax.formula_m (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar .here) (.fvar (.there .here))
  obtain ⟨H, hH₀⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty.pushFree c).pushFree E)
  have hH (i j : num_l ℳ) : SecondOrderPairing.relation_l H i j ↔ read_l E c i j := by
    refine (hH₀ i j).trans ?_
    simp only [φ, SecondOrderSequenceSyntax.raw_l]
    rfl
  have hRoots (i j : num_l ℳ) (_ : SecondOrderPairing.relation_l H i j) :
      SecondOrderDomain.wf_l K.less i ∧ SecondOrderDomain.wf_l K.less j :=
    ⟨SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec i,
      SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec j⟩
  obtain ⟨F, hF⟩ := SecondOrderMixedImage.exists_l hℳ K.less K.less H hRoots
  have hRead (p : type_l hℳ) : SecondOrderQuotient.mem_l hℳ p F ↔
      ∃ i j, read_l E c i j ∧ SecondOrderPairObjects.ordered_l hℳ
        (numberCode_l K i).val (numberCode_l K j).val p := by
    refine (hF p).trans ?_
    constructor
    · rintro ⟨i, j, hij, hp⟩
      exact ⟨i, j, (hH i j).mp hij, hp⟩
    · rintro ⟨i, j, hij, hp⟩
      exact ⟨i, j, (hH i j).mpr hij, hp⟩
  have hValue (x y : type_l hℳ) : SecondOrderFunctionObjects.value_l hℳ F x y ↔
      ∃ i j, read_l E c i j ∧ x = (numberCode_l K i).val ∧ y = (numberCode_l K j).val := by
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨i, j, hij, hp'⟩ := (hRead p).mp hp
      exact ⟨i, j, hij, (SecondOrderPairObjects.ordered_eq_l hℳ hxy hp').mp rfl⟩
    · rintro ⟨i, j, hij, rfl, rfl⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (numberCode_l K i).val (numberCode_l K j).val
      exact ⟨p, (hRead p).mpr ⟨i, j, hij, hp⟩, hp⟩
  have hNumber (i : num_l ℳ) (y : type_l hℳ) :
      SecondOrderFunctionObjects.value_l hℳ F (numberCode_l K i).val y ↔
        ∃ j, read_l E c i j ∧ y = (numberCode_l K j).val := by
    refine (hValue _ y).trans ?_
    constructor
    · rintro ⟨i', j, hij, hi, hy⟩
      have hEq : i = i' := numberCode_injective_l K (Subtype.ext hi)
      subst i'
      exact ⟨j, hij, hy⟩
    · rintro ⟨j, hij, hy⟩
      exact ⟨i, j, hij, rfl, hy⟩
  refine ⟨F, ⟨?_, ?_⟩, hNumber⟩
  · intro p hp
    obtain ⟨i, j, hij, hp'⟩ := (hRead p).mp hp
    exact ⟨(numberCode_l K i).val, (numberCode_l K j).val,
      (numberCode_mem_iff_lt_l K i l).mpr (hc.2 i j hij), (numberCode_l K j).property, hp'⟩
  · intro x hx
    have hxω := SecondOrderOmegaTransitive.member_l hℳ (k := (numberCode_l K l).val)
      (x := x) K.omega_spec (numberCode_l K l).property hx
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨x, hxω⟩
    have hi' : (numberCode_l K i).val = x := congrArg Subtype.val hi
    have hiL : SecondOrderOrder.lt_l i l := (numberCode_mem_iff_lt_l K i l).mp (hi'.symm ▸ hx)
    obtain ⟨j, hij, hUnique⟩ := hc.1 i hiL
    refine ⟨(numberCode_l K j).val, ⟨(numberCode_l K j).property,
      hi' ▸ (hNumber i _).mpr ⟨j, hij, rfl⟩⟩, ?_⟩
    rintro y ⟨_, hy⟩
    obtain ⟨j', hij', hy'⟩ := (hNumber i y).mp (hi'.symm ▸ hy)
    exact hy'.trans (congrArg (fun j => (numberCode_l K j).val) (hUnique j' hij'))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteAssignmentGraph
