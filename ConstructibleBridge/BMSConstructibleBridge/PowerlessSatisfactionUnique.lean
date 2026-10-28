import BMSConstructibleBridge.PowerlessSatisfactionUniqueRow
import BMSConstructibleBridge.PowerlessRelationalCodeValidity
import BMSConstructibleBridge.PowerlessFormulaValidityReading
import BMSConstructibleBridge.SecondOrderFunctionLaws

/-! # 固定内部编码与合法性图的环境 Sat 读值唯一性

使用明确纯公式归纳行及全部内部构造子，不对宿主语法树归纳。存在分支
先由实际函数域唯一性对齐更新长度，再将任意更新赋值送入子码归纳。
前提是两张图均满足完整环境 Sat 规格；类内规格的环境传输须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionUnique

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessFormulaValidityReading (code_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem domain_unique_l {f L N A : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f L A) (hg : map_l (ℳ := 𝒱) f N A) : L = N := by
  apply SecondOrderQuotient.ext_l hℳ L N
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, _⟩ := hf.2 x hx
    exact (SecondOrderFunctionLaws.value_mem_l hℳ hg hy.2).1
  · intro hx
    obtain ⟨y, hy, _⟩ := hg.2 x hx
    exact (SecondOrderFunctionLaws.value_mem_l hℳ hf hy.2).1

theorem existential_congr_l {ω A R S f i b L : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f L A)
    (hAgree : ∀ g, map_l (ℳ := 𝒱) g L A → (value_l (ℳ := 𝒱) R b g ↔ value_l (ℳ := 𝒱) S b g)) :
    PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := 𝒱) ω A R f i b ↔
      PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := 𝒱) ω A S f i b := by
  have transfer {P Q : type_l hℳ}
      (h : ∀ g, map_l (ℳ := 𝒱) g L A → (value_l (ℳ := 𝒱) P b g ↔ value_l (ℳ := 𝒱) Q b g)) :
      PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := 𝒱) ω A P f i b →
        PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := 𝒱) ω A Q f i b := by
    rintro ⟨N, hN, hfN, hi, a, ha, g, hg, hUpdate, hValue⟩
    have hEq : N = L := domain_unique_l hfN hf
    exact ⟨N, hN, hfN, hi, a, ha, g, hg, hUpdate, (h g (hEq ▸ hg)).mp hValue⟩
  exact ⟨transfer hAgree, transfer (fun g hg => (hAgree g hg).symm)⟩

def fixed_spec_l (K : source_coding_l hℳ) (A T F R : type_l hℳ) : Prop :=
  PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒱) K.omega A
    (code_l K (numeral_l ℳ 0)) (code_l K (numeral_l ℳ 1))
    (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) T F R

theorem rows_l (K : source_coding_l hℳ) {A T F R S : type_l hℳ}
    (hT : map_l (ℳ := 𝒱) T K.omega K.omega) (hPair : PowerlessBMSQuotientPairingBounds.spec_l K T)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hF : ∀ c L, value_l (ℳ := 𝒱) F c L ↔ PowerlessRelationalCodeValidity.valid_l K V c L)
    (hR : fixed_spec_l K A T F R) (hS : fixed_spec_l K A T F S) :
    ∀ n, PowerlessSatisfactionUniqueRow.row_l (ℳ₀ := 𝒱) K.omega A F R S (code_l K n) := by
  apply PowerlessSatisfactionUniqueRow.induct_l K A F R S
  intro n ih L hL f hFc hf
  obtain ⟨l, hl⟩ := numberCode_surjective_l K ⟨L, hL⟩
  have hLEq : L = code_l K l := (congrArg Subtype.val hl).symm
  rw [hLEq] at hFc hf
  obtain ⟨n', l', hn, hl', hValid⟩ := (hF (code_l K n) (code_l K l)).mp hFc
  have hnEq : n = n' := numberCode_injective_l K (Subtype.ext hn)
  have hlEq : l = l' := numberCode_injective_l K (Subtype.ext hl')
  subst n'
  subst l'
  have hRBranches := hR.2.2 (code_l K n) (code_l K l) f
    (numberCode_l K n).property (numberCode_l K l).property hf
  have hSBranches := hS.2.2 (code_l K n) (code_l K l) f
    (numberCode_l K n).property (numberCode_l K l).property hf
  have hSub k (hk : SecondOrderPairing.relation_l V k l) : value_l (ℳ := 𝒱) F (code_l K k) (code_l K l) :=
    (hF _ _).mpr ⟨k, l, rfl, rfl, hk⟩
  have hConstructor t a b (h : SecondOrderTriangularConstructor.constructor_l t a b n) :=
    (PowerlessBMSQuotientTriangularSyntax.constructor_l K hT hPair t a b n).mpr h
  rcases (hV n l).mp hValid with hZero | ⟨a, b, hCase⟩
  · subst n
    exact ⟨fun h => (hR.2.1 f h).elim, fun h => (hS.2.1 f h).elim⟩
  · rcases hCase with ⟨hAtom, ha, hb⟩ | ⟨hNand, ha, hb⟩ | ⟨hExists, ha, hb⟩
    · have haL := (numberCode_mem_iff_lt_l K a l).mpr ha
      have hbL := (numberCode_mem_iff_lt_l K b l).mpr hb
      rcases hAtom with hMem | hEq
      · exact ((hRBranches (code_l K a) (code_l K b)).1 (hConstructor _ _ _ hMem) haL hbL).trans
          ((hSBranches (code_l K a) (code_l K b)).1 (hConstructor _ _ _ hMem) haL hbL).symm
      · exact ((hRBranches (code_l K a) (code_l K b)).2.1 (hConstructor _ _ _ hEq) haL hbL).trans
          ((hSBranches (code_l K a) (code_l K b)).2.1 (hConstructor _ _ _ hEq) haL hbL).symm
    · obtain ⟨haN, hbN⟩ := SecondOrderTriangularConstructor.bounds_l hℳ hNand
      have hA := ih a haN (code_l K l) (numberCode_l K l).property f (hSub a ha) hf
      have hB := ih b hbN (code_l K l) (numberCode_l K l).property f (hSub b hb) hf
      exact ((hRBranches (code_l K a) (code_l K b)).2.2.1 (hConstructor _ _ _ hNand) (hSub a ha) (hSub b hb)).trans
        ((not_congr (and_congr hA hB)).trans
          ((hSBranches (code_l K a) (code_l K b)).2.2.1 (hConstructor _ _ _ hNand) (hSub a ha) (hSub b hb)).symm)
    · have hbN := (SecondOrderTriangularConstructor.bounds_l hℳ hExists).2
      have haL := (numberCode_mem_iff_lt_l K a l).mpr ha
      have hQuant := existential_congr_l (ω := K.omega) (R := R) (S := S) (i := code_l K a) (b := code_l K b) hf
        (fun g hg => ih b hbN (code_l K l) (numberCode_l K l).property g (hSub b hb) hg)
      exact ((hRBranches (code_l K a) (code_l K b)).2.2.2 (hConstructor _ _ _ hExists) haL (hSub b hb)).trans
        (hQuant.trans ((hSBranches (code_l K a) (code_l K b)).2.2.2
          (hConstructor _ _ _ hExists) haL (hSub b hb)).symm)

theorem values_l (K : source_coding_l hℳ) {A T F R S : type_l hℳ}
    (hT : map_l (ℳ := 𝒱) T K.omega K.omega) (hPair : PowerlessBMSQuotientPairingBounds.spec_l K T)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hF : ∀ c L, value_l (ℳ := 𝒱) F c L ↔ PowerlessRelationalCodeValidity.valid_l K V c L)
    (hR : fixed_spec_l K A T F R) (hS : fixed_spec_l K A T F S) :
    ∀ c f, value_l (ℳ := 𝒱) R c f ↔ value_l (ℳ := 𝒱) S c f := by
  have hRows := rows_l K hT hPair hV hF hR hS
  intro c f
  constructor
  · intro h
    obtain ⟨hc, L, hL, hFc, hf⟩ := hR.1 c f h
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨c, hc⟩
    have hEq : c = code_l K n := (congrArg Subtype.val hn).symm
    rw [hEq] at hFc h ⊢
    exact (hRows n L hL f hFc hf).mp h
  · intro h
    obtain ⟨hc, L, hL, hFc, hf⟩ := hS.1 c f h
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨c, hc⟩
    have hEq : c = code_l K n := (congrArg Subtype.val hn).symm
    rw [hEq] at hFc h ⊢
    exact (hRows n L hL f hFc hf).mpr h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionUnique
