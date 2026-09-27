import BMSConstructibleBridge.PowerlessBMSQuotientCoding
import BMSConstructibleBridge.SecondOrderRelationImage

/-!
# 任意 Z₂ 图商中自然数有序对的容器

用目标二阶模型中的全数域关系索引所有根码有序对，再调用已有关系像构造，得到
quotient 中一个真正包含全部 Kuratowski 数对的对象。这里只构造这一特定容器，不
推出商结构满足完整 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientPairContainer

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic

set_option autoImplicit false

universe u

variable {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

/-- 任意目标内部数的根码之间的全部有序对，都属于一个 quotient 集合。 -/
theorem exists_l
    (C : PowerlessBMSQuotientCoding.source_coding_l hM) :
    ∃ F : SecondOrderQuotient.type_l hM, ∀ p,
      SecondOrderQuotient.mem_l hM p F ↔
        ∃ a b : SecondOrderModel.num_l M,
          SecondOrderPairObjects.ordered_l hM
            (PowerlessBMSQuotientCoding.numberCode_l C a).val
            (PowerlessBMSQuotientCoding.numberCode_l C b).val p := by
  obtain ⟨S, hS⟩ := SecondOrderModel.comprehension_l hM .truth rfl
    (Env.empty (M := M))
  have hAll (a b : SecondOrderModel.num_l M) :
      SecondOrderPairing.relation_l S a b := by
    exact (hS (SecondOrderPairing.value_l a b)).mpr True.intro
  have hRoots (a b : SecondOrderModel.num_l M)
      (_ : SecondOrderPairing.relation_l S a b) :
      SecondOrderDomain.wf_l C.less a ∧ SecondOrderDomain.wf_l C.less b :=
    ⟨SecondOrderNaturalGraph.wf_l hM C.less C.less_spec a,
      SecondOrderNaturalGraph.wf_l hM C.less C.less_spec b⟩
  obtain ⟨F, hF⟩ := SecondOrderRelationImage.quotient_l hM C.less S hRoots
  have hCodeA (a b : SecondOrderModel.num_l M)
      (hab : SecondOrderPairing.relation_l S a b) :
      SecondOrderQuotient.mk_l hM ⟨C.less, a, (hRoots a b hab).1⟩ =
        (PowerlessBMSQuotientCoding.numberCode_l C a).val := by
    rfl
  have hCodeB (a b : SecondOrderModel.num_l M)
      (hab : SecondOrderPairing.relation_l S a b) :
      SecondOrderQuotient.mk_l hM ⟨C.less, b, (hRoots a b hab).2⟩ =
        (PowerlessBMSQuotientCoding.numberCode_l C b).val := by
    rfl
  refine ⟨F, fun p => ?_⟩
  rw [hF p]
  constructor
  · rintro ⟨a, b, hab, hp⟩
    rw [hCodeA a b hab, hCodeB a b hab] at hp
    exact ⟨a, b, hp⟩
  · rintro ⟨a, b, hp⟩
    refine ⟨a, b, hAll a b, ?_⟩
    rw [hCodeA a b (hAll a b), hCodeB a b (hAll a b)]
    exact hp

/-- 容器规格直接覆盖 quotient ω 的任意两数，而不仅是目标模型的根码写法。 -/
theorem omega_pairs_l
    (C : PowerlessBMSQuotientCoding.source_coding_l hM) :
    ∃ F : SecondOrderQuotient.type_l hM, ∀ p,
      SecondOrderQuotient.mem_l hM p F ↔
        ∃ a b : PowerlessArithmetic.num_l
          (ℳ := SecondOrderQuotient.structure_l hM) C.omega,
          SecondOrderPairObjects.ordered_l hM a.val b.val p := by
  obtain ⟨F, hF⟩ := exists_l C
  refine ⟨F, fun p => ?_⟩
  rw [hF p]
  constructor
  · rintro ⟨a, b, hab⟩
    exact ⟨PowerlessBMSQuotientCoding.numberCode_l C a,
      PowerlessBMSQuotientCoding.numberCode_l C b, hab⟩
  · rintro ⟨a, b, hab⟩
    obtain ⟨a₀, ha₀⟩ := PowerlessBMSQuotientCoding.numberCode_surjective_l C a
    obtain ⟨b₀, hb₀⟩ := PowerlessBMSQuotientCoding.numberCode_surjective_l C b
    have haVal := congrArg Subtype.val ha₀
    have hbVal := congrArg Subtype.val hb₀
    rw [← haVal, ← hbVal] at hab
    exact ⟨a₀, b₀, hab⟩

#print axioms exists_l
#print axioms omega_pairs_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientPairContainer
