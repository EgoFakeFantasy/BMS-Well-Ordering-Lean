import BMSConstructibleBridge.PowerlessRelativeClassNumericGraph
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 类内实数与指定根的单张编码

第零行读取原实数，第一行只标记指定根。所有行下标都属于原模型的
内部自然数；两行的分离使用后继非零，而非外部标准性。构造仅消费
已证的类内 Δ₀ 关系图和数编码，不使用完整 Collection 或 Type 选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRootedReal

open Logic FirstOrder StabilityFrame ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def tag_m {Γ Δ : SortContext ℒ} (e o U r a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (.equal a e) (SecondOrderObjectSyntax.member_m b U))
    (.conj (.equal a o) (.equal b r))

theorem tag_delta_m {Γ Δ : SortContext ℒ} (e o U r a b : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (tag_m e o U r a b) :=
  .disj (.conj (.equal _ _) (.rel _ _)) (.conj (.equal _ _) (.equal _ _))

theorem tag_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (e o U r a b : Term ℒ Γ Δ .set) :
    (tag_m e o U r a b).satisfies η ↔
      (a.eval η = e.eval η ∧ member_l 𝒩 (b.eval η) (U.eval η)) ∨
      (a.eval η = o.eval η ∧ b.eval η = r.eval η) := by
  simp only [tag_m, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

include hBase in
/-- 指定根与原实数被实际类内实数 V 同时编码；输入 U 的类外自然数迹不被假定存在。 -/
theorem coded_l (K : source_coding_l hℳ) (U : type_l hℳ B) (r : SecondOrderModel.num_l ℳ) :
    ∃ V : type_l hℳ B, ∃ hV : ∀ c, mem_l hℳ c V.val → mem_l hℳ c K.omega,
      ∃ F : SecondOrderModel.set_l ℳ, setRel_l K ⟨V.val, hV⟩ F ∧ ∀ n m,
        SecondOrderPairing.relation_l F n m ↔
          (n = SecondOrderModel.zero_l ℳ ∧ mem_l hℳ (numberCode_l K m).val U.val) ∨
          (n = SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ) ∧ m = r) := by
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let N (n : SecondOrderModel.num_l ℳ) : type_l hℳ B := ⟨(numberCode_l K n).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property (numberCode_l K n).property⟩
  let e := N (SecondOrderModel.zero_l ℳ)
  let o := N (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))
  let η : Env 𝒩 [] [.set, .set, .set, .set] :=
    ((((Env.empty).pushFree (N r)).pushFree U).pushFree o).pushFree e
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] := tag_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar .here) (.fvar (.there .here))
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l
    (φ := φ) (tag_delta_m _ _ _ _ _ _) η O O
  obtain ⟨V, hV, F, hTrace, hRead⟩ := PowerlessRelativeClassNumericGraph.coded_l (hBase := hBase) K Q
  refine ⟨V, hV, F, hTrace, fun n m => ?_⟩
  have hTag := tag_formula_l
    (((PowerlessRelativeClassRelativization.env_l η).pushFree (numberCode_l K m).val).pushFree
      (numberCode_l K n).val)
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar .here) (.fvar (.there .here))
  have hCode (a b : SecondOrderModel.num_l ℳ) :
      (numberCode_l K a).val = (numberCode_l K b).val ↔ a = b :=
    ⟨fun h => numberCode_injective_l K (Subtype.ext h), fun h => congrArg (fun i => (numberCode_l K i).val) h⟩
  have h := (hRead n m).trans ((hQ _ _).trans
    (and_congr Iff.rfl (and_congr Iff.rfl hTag)))
  change SecondOrderPairing.relation_l F n m ↔
    mem_l hℳ (numberCode_l K n).val K.omega ∧ mem_l hℳ (numberCode_l K m).val K.omega ∧
      (((numberCode_l K n).val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val ∧
          mem_l hℳ (numberCode_l K m).val U.val) ∨
        ((numberCode_l K n).val = (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val ∧
          (numberCode_l K m).val = (numberCode_l K r).val)) at h
  have hn : mem_l hℳ (numberCode_l K n).val K.omega := (numberCode_l K n).property
  have hm : mem_l hℳ (numberCode_l K m).val K.omega := (numberCode_l K m).property
  simpa only [hCode, hn, hm, true_and] using h

include hBase in
/-- 行读取不需要配数函数满射；精确覆盖原模型中的全部内部根。 -/
theorem rows_l (K : source_coding_l hℳ) (U : type_l hℳ B) (r : SecondOrderModel.num_l ℳ) :
    ∃ V : type_l hℳ B, ∃ hV : ∀ c, mem_l hℳ c V.val → mem_l hℳ c K.omega,
      ∃ F : SecondOrderModel.set_l ℳ, setRel_l K ⟨V.val, hV⟩ F ∧
        (∀ m, SecondOrderPairing.relation_l F (SecondOrderModel.zero_l ℳ) m ↔
          mem_l hℳ (numberCode_l K m).val U.val) ∧
        (∀ m, SecondOrderPairing.relation_l F
          (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)) m ↔ m = r) := by
  obtain ⟨V, hV, F, hTrace, hRead⟩ := coded_l (hBase := hBase) K U r
  have hNe := SecondOrderModel.nonzero_l hℳ (SecondOrderModel.zero_l ℳ)
  refine ⟨V, hV, F, hTrace, ?_, ?_⟩
  · intro m
    simpa only [eq_self, hNe.symm, false_and, true_and, or_false] using hRead (SecondOrderModel.zero_l ℳ) m
  · intro m
    simpa only [eq_self, hNe, false_and, true_and, false_or] using
      hRead (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)) m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRootedReal
