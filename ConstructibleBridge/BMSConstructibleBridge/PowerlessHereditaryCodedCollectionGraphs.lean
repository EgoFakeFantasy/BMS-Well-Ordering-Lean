import BMSConstructibleBridge.PowerlessCodedCollectionReading
import BMSConstructibleBridge.PowerlessHereditaryNumericSlice

/-! # 原筛选根、带标签图及新根拼接的类内代表

原族和原索引实数均有实际 Class 代表时，三个完整算术图也有
实际遗传实数代表。根集按数迹分离，关系按整图分离；接口不要求
行良基，之后只在真正被选中的行上消费原内部良基证书。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryCodedCollectionGraphs

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

private def omega_l (K : source_coding_l hℳ) : M :=
  ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩

private def zero_l (K : source_coding_l hℳ) : M :=
  ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase (omega_l (hBase := hBase) K).property
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).property⟩

include hBase in
theorem roots_l (K : source_coding_l hℳ) (S I₀ : M)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S.val)
    (hI : ∀ c, mem_l hℳ c I₀.val → mem_l hℳ c K.omega) {I : SecondOrderModel.set_l ℳ}
    (hITrace : setRel_l K ⟨I₀.val, hI⟩ I) :
    ∃ P₀ : M, PowerlessHereditaryClass.member_l hℳ B P₀.val ∧
      ∃ hP : ∀ c, mem_l hℳ c P₀.val → mem_l hℳ c K.omega,
        ∃ P : SecondOrderModel.set_l ℳ, setRel_l K ⟨P₀.val, hP⟩ P ∧
          ∀ c, SecondOrderModel.mem_l c P ↔ PowerlessCodedCollectionReading.roots_l I c := by
  let η : Env 𝒩₀ [] [.set, .set, .set, .set] :=
    Env.empty |>.pushFree I₀ |>.pushFree S |>.pushFree (zero_l (hBase := hBase) K) |>.pushFree (omega_l (hBase := hBase) K)
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := PowerlessCodedCollectionSyntax.roots_m
    (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar .here)
  obtain ⟨P₀, hPHC, hP, P, hTrace, hRead⟩ := PowerlessHereditaryNumericSlice.coded_l K
    (φ := φ) (PowerlessCodedCollectionSyntax.roots_delta_m _ _ _ _ _) η
  refine ⟨P₀, hPHC, hP, P, hTrace, fun c => ?_⟩
  have hFormula := PowerlessCodedCollectionSyntax.roots_formula_l
    ((PowerlessRelativeClassRelativization.env_l η).pushFree (numberCode_l K c).val)
    (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar .here)
  exact (hRead c).trans (hFormula.trans (PowerlessCodedCollectionReading.roots_instance_l K hS hI hITrace c))

include hBase in
theorem tagged_l (K : source_coding_l hℳ) (S U I₀ : M)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S.val)
    (hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega)
    (hI : ∀ c, mem_l hℳ c I₀.val → mem_l hℳ c K.omega) {H I : SecondOrderModel.set_l ℳ}
    (hUTrace : setRel_l K ⟨U.val, hU⟩ H) (hITrace : setRel_l K ⟨I₀.val, hI⟩ I) :
    ∃ G₀ : M, PowerlessHereditaryClass.member_l hℳ B G₀.val ∧
      ∃ hG : ∀ c, mem_l hℳ c G₀.val → mem_l hℳ c K.omega,
        ∃ G : SecondOrderModel.set_l ℳ, setRel_l K ⟨G₀.val, hG⟩ G ∧
          ∀ c d, SecondOrderPairing.relation_l G c d ↔ PowerlessCodedCollectionReading.tagged_l H I c d := by
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set] := Env.empty |>.pushFree I₀ |>.pushFree U |>.pushFree S
    |>.pushFree (zero_l (hBase := hBase) K) |>.pushFree (omega_l (hBase := hBase) K)
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] := PowerlessCodedCollectionSyntax.tagged_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.fvar .here) (.fvar (.there .here))
  obtain ⟨G₀, hGHC, hG, G, hTrace, hRead⟩ := PowerlessHereditaryNumericRelation.coded_l K
    (φ := φ) (PowerlessCodedCollectionSyntax.tagged_delta_m _ _ _ _ _ _ _) η
  refine ⟨G₀, hGHC, hG, G, hTrace, fun c d => ?_⟩
  have hFormula := PowerlessCodedCollectionSyntax.tagged_formula_l
    (((PowerlessRelativeClassRelativization.env_l η).pushFree (numberCode_l K d).val).pushFree (numberCode_l K c).val)
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.fvar .here) (.fvar (.there .here))
  exact (hRead c d).trans (hFormula.trans
    (PowerlessCodedCollectionReading.tagged_instance_l K hS hU hI hUTrace hITrace c d))

include hBase in
theorem graft_l (K : source_coding_l hℳ) (S G₀ P₀ : M)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S.val)
    (hG : ∀ c, mem_l hℳ c G₀.val → mem_l hℳ c K.omega)
    (hP : ∀ c, mem_l hℳ c P₀.val → mem_l hℳ c K.omega) {G P : SecondOrderModel.set_l ℳ}
    (hGTrace : setRel_l K ⟨G₀.val, hG⟩ G) (hPTrace : setRel_l K ⟨P₀.val, hP⟩ P) :
    ∃ W₀ : M, PowerlessHereditaryClass.member_l hℳ B W₀.val ∧
      ∃ hW : ∀ c, mem_l hℳ c W₀.val → mem_l hℳ c K.omega,
        ∃ W : SecondOrderModel.set_l ℳ, setRel_l K ⟨W₀.val, hW⟩ W ∧
          ∀ c d, SecondOrderPairing.relation_l W c d ↔ PowerlessCodedCollectionReading.graft_l G P c d := by
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set] := Env.empty |>.pushFree P₀ |>.pushFree G₀ |>.pushFree S
    |>.pushFree (zero_l (hBase := hBase) K) |>.pushFree (omega_l (hBase := hBase) K)
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] := PowerlessCodedCollectionSyntax.graft_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.fvar .here) (.fvar (.there .here))
  obtain ⟨W₀, hWHC, hW, W, hTrace, hRead⟩ := PowerlessHereditaryNumericRelation.coded_l K
    (φ := φ) (PowerlessCodedCollectionSyntax.graft_delta_m _ _ _ _ _ _ _) η
  refine ⟨W₀, hWHC, hW, W, hTrace, fun c d => ?_⟩
  have hFormula := PowerlessCodedCollectionSyntax.graft_formula_l
    (((PowerlessRelativeClassRelativization.env_l η).pushFree (numberCode_l K d).val).pushFree (numberCode_l K c).val)
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.fvar .here) (.fvar (.there .here))
  exact (hRead c d).trans (hFormula.trans
    (PowerlessCodedCollectionReading.graft_instance_l K hS hG hP hGTrace hPTrace c d))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryCodedCollectionGraphs
