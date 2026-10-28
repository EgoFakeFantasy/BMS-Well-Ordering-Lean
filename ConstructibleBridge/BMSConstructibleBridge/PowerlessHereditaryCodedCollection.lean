import BMSConstructibleBridge.PowerlessHereditaryCodedCollectionGraphs
import BMSConstructibleBridge.SecondOrderCodedFamilyCollection

/-! # 已编码良基族收集集的实际类内码图

背景是原 Z₂。输入族与索引有 Class 实数代表，输出整张集合码图 W
也有实际遗传实数代表；选中行的原内部良基证书保证新根良基。
所得商对象 C 的完整成员规格与原收集定义相同。

这里证明的是 C 的码图在 Class／Hereditary 内，不是 C 本身在其中。
将类内良基码解码为类内可数传递包络仍是独立义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryCodedCollection

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

theorem graft_spec_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {G P W : SecondOrderModel.set_l ℳ}
    (hW : ∀ c d, SecondOrderPairing.relation_l W c d ↔ PowerlessCodedCollectionReading.graft_l G P c d) :
    SecondOrderGraft.spec_l G P W := by
  refine ⟨?_, ?_, ?_⟩
  · intro d h
    obtain ⟨a, ha, _⟩ := (hW _ _).mp h
    exact SecondOrderModel.nonzero_l hℳ a ha.symm
  · intro a
    refine (hW _ _).trans ⟨?_, fun h => ⟨a, rfl, Or.inl ⟨rfl, h⟩⟩⟩
    rintro ⟨c, hc, hBody⟩
    have hac := SecondOrderModel.injective_l hℳ hc
    subst c
    rcases hBody with ⟨_, hP⟩ | ⟨d, hd, _⟩
    · exact hP
    · exact (SecondOrderModel.nonzero_l hℳ d hd.symm).elim
  · intro a b
    refine (hW _ _).trans ⟨?_, fun h => ⟨a, rfl, Or.inr ⟨b, rfl, h⟩⟩⟩
    rintro ⟨c, hc, hBody⟩
    have hac := SecondOrderModel.injective_l hℳ hc
    subst c
    rcases hBody with ⟨hb, _⟩ | ⟨d, hd, hG⟩
    · exact (SecondOrderModel.nonzero_l hℳ b hb).elim
    · have hbd := SecondOrderModel.injective_l hℳ hd
      subst d
      exact hG

private theorem index_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (I : SecondOrderModel.set_l ℳ) :
    ∃ R : SecondOrderModel.set_l ℳ, ∀ i n, SecondOrderPairing.relation_l R i n ↔ SecondOrderModel.mem_l i I := by
  let φ : Formula SecondOrderSyntax.signature_m [] [.num, .num, .set] :=
    .rel .mem (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) .nil))
  obtain ⟨R, hR⟩ := SecondOrderRelations.comprehension_l hℳ φ rfl (Env.empty.pushFree I)
  exact ⟨R, hR⟩

include hBase in
/-- 全部码边及全部跨图成员都精确；不把成员之并误当整行对象集合。 -/
theorem exists_l (K : source_coding_l hℳ) (U I₀ : M)
    (hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega)
    (hI : ∀ c, mem_l hℳ c I₀.val → mem_l hℳ c K.omega) {H I : SecondOrderModel.set_l ℳ}
    (hUTrace : setRel_l K ⟨U.val, hU⟩ H) (hITrace : setRel_l K ⟨I₀.val, hI⟩ I)
    (hRows : SecondOrderCodedFamilyCollection.rows_wf_l H I) :
    ∃ W₀ : M, PowerlessHereditaryClass.member_l hℳ B W₀.val ∧
      ∃ hW : ∀ c, mem_l hℳ c W₀.val → mem_l hℳ c K.omega,
        ∃ C : SecondOrderGraph.code_l ℳ, setRel_l K ⟨W₀.val, hW⟩ C.real ∧
          C.root = SecondOrderModel.zero_l ℳ ∧
            ∀ D, SecondOrderGraph.mem_l D C ↔ SecondOrderCodedFamilyCollection.member_l H I D := by
  let O : M := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  obtain ⟨S, hS, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (hBase := hBase)
    (X := O) ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr K.omega_spec)
  obtain ⟨P₀, _hPHC, hP, P, hPTrace, hPRead⟩ :=
    PowerlessHereditaryCodedCollectionGraphs.roots_l (hBase := hBase) K S I₀ hS hI hITrace
  obtain ⟨G₀, _hGHC, hG, G, hGTrace, hGRead⟩ :=
    PowerlessHereditaryCodedCollectionGraphs.tagged_l (hBase := hBase) K S U I₀ hS hU hI hUTrace hITrace
  obtain ⟨W₀, hWHC, hW, W, hWTrace, hWRead⟩ :=
    PowerlessHereditaryCodedCollectionGraphs.graft_l (hBase := hBase) K S G₀ P₀ hS hG hP hGTrace hPTrace
  obtain ⟨R, hR⟩ := index_l hℳ I
  have hTagged : SecondOrderPredecessorTaggedGraph.spec_l R H (SecondOrderModel.zero_l ℳ) G := by
    intro c d
    refine (hGRead c d).trans ⟨?_, ?_⟩
    · rintro ⟨i, a, b, hi, ha, hb, hRow⟩
      exact ⟨i, a, b, (hR i _).mpr hi, ha, hb, hRow⟩
    · rintro ⟨i, a, b, hi, ha, hb, hRow⟩
      exact ⟨i, a, b, (hR i _).mp hi, ha, hb, hRow⟩
  have hRoots c (hc : SecondOrderModel.mem_l c P) : SecondOrderDomain.wf_l G c := by
    obtain ⟨i, hi, rfl⟩ := (hPRead c).mp hc
    obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ H i
    exact SecondOrderPredecessorTaggedGraph.wf_l hℳ hTagged ((hR i _).mpr hi) hY (hRows i hi Y hY)
  have hGraft := graft_spec_l hℳ hWRead
  let C := SecondOrderGraftSemantics.code_l hℳ G P W hGraft hRoots
  have hC D := SecondOrderGraftSemantics.mem_l hℳ G P W hGraft hRoots D
  refine ⟨W₀, hWHC, hW, C, hWTrace, rfl, fun D => (hC D).trans ⟨?_, ?_⟩⟩
  · rintro ⟨c, hc, hDc⟩
    obtain ⟨i, hi, rfl⟩ := (hPRead c).mp hc
    obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ H i
    have hTag := SecondOrderPairSet.tag_eq_l hℳ i Y G
      (SecondOrderPredecessorTaggedGraph.fiber_l hℳ hTagged ((hR i _).mpr hi) hY) (SecondOrderModel.zero_l ℳ)
    exact ⟨i, ⟨Y, SecondOrderModel.zero_l ℳ, hRows i hi Y hY⟩, hi, hY, rfl,
      SecondOrderBisimulation.trans_l hℳ D.real G Y D.root _ (SecondOrderModel.zero_l ℳ) hDc
        (SecondOrderBisimulation.symm_l hℳ _ _ _ _ hTag)⟩
  · rintro ⟨i, Y, hi, hY, hZero, hDY⟩
    have hTag := SecondOrderPairSet.tag_eq_l hℳ i Y.real G
      (SecondOrderPredecessorTaggedGraph.fiber_l hℳ hTagged ((hR i _).mpr hi) hY) (SecondOrderModel.zero_l ℳ)
    exact ⟨SecondOrderPairing.value_l i (SecondOrderModel.zero_l ℳ), (hPRead _).mpr ⟨i, hi, rfl⟩,
      SecondOrderBisimulation.trans_l hℳ D.real Y.real G D.root (SecondOrderModel.zero_l ℳ) _
        (hZero ▸ hDY) hTag⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryCodedCollection
