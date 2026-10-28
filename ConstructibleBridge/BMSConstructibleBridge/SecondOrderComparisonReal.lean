import BMSConstructibleBridge.SecondOrderGraphFormulaRelation
import BMSConstructibleBridge.SecondOrderFunctionLaws
import BMSConstructibleBridge.PowerlessBMSQuotientCoding

/-! # 固定实际枚举上的唯一比较实数

关系实数逐内部自然数坐标精确给出比较位，故由实数外延性唯一。
这不是从商对象唯一性选择一个图呈现实码。给定实际满射时可反向恢复
全部载体内比较值；仍须另证递归算子的总性、局部性及历史统一界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonReal

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def query_m {Γ Δ : SortContext ℒ} (f P i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    .conj (SecondOrderObjectSyntax.value_m (up (up f)) (up (up i)) (.bvar (.there .here))) <|
      .conj (SecondOrderObjectSyntax.value_m (up (up f)) (up (up j)) (.bvar .here))
        (SecondOrderObjectSyntax.value_m (up (up P)) (.bvar (.there .here)) (.bvar .here))

theorem query_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (f P i j : Term ℒ Γ Δ .set) :
    (query_m f P i j).satisfies η ↔ ∃ x y,
      value_l (f.eval η) (i.eval η) x ∧ value_l (f.eval η) (j.eval η) y ∧ value_l (P.eval η) x y := by
  simp only [query_m, Formula.satisfies, value_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def spec_l (K : source_coding_l hℳ) (f P : type_l hℳ) (R : SecondOrderModel.set_l ℳ) : Prop :=
  ∀ i j, SecondOrderPairing.relation_l R i j ↔ ∃ x y,
    value_l (ℳ := 𝒱) f (numberCode_l K i).val x ∧
    value_l (ℳ := 𝒱) f (numberCode_l K j).val y ∧ value_l (ℳ := 𝒱) P x y

theorem unique_l (K : source_coding_l hℳ) {f P : type_l hℳ} {R S : SecondOrderModel.set_l ℳ}
    (hR : spec_l K f P R) (hS : spec_l K f P S) : R = S :=
  SecondOrderRelations.ext_l hℳ R S (fun i j => (hR i j).trans (hS i j).symm)

theorem exists_unique_l (K : source_coding_l hℳ) (f P : type_l hℳ) :
    ∃! R : SecondOrderModel.set_l ℳ, spec_l K f P R := by
  let φ : Formula ℒ [] [.set, .set, .set, .set] := query_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒱 [] [.set, .set] := (Env.empty.pushFree P).pushFree f
  obtain ⟨R, hR⟩ := SecondOrderGraphFormulaRelation.exists_l hℳ φ η K.less K.less
  have hSpec : spec_l K f P R := by
    intro i j
    exact (hR i j (SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec i)
      (SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec j)).trans (query_formula_l _ _ _ _ _)
  exact ⟨R, hSpec, fun S hS => unique_l K hS hSpec⟩

/-- 满射的原像仅在 Prop 中逐点取得，不构造原像选择函数。 -/
theorem values_l (K : source_coding_l hℳ) {C f P Q : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f K.omega C)
    (hOnto : ∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x)
    {R : SecondOrderModel.set_l ℳ} (hP : spec_l K f P R) (hQ : spec_l K f Q R)
    {x y : type_l hℳ} (hx : mem_l hℳ x C) (hy : mem_l hℳ y C) :
    value_l (ℳ := 𝒱) P x y ↔ value_l (ℳ := 𝒱) Q x y := by
  obtain ⟨i, hi, hix⟩ := hOnto x hx
  obtain ⟨j, hj, hjy⟩ := hOnto y hy
  obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨i, hi⟩
  obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨j, hj⟩
  have hn' : (numberCode_l K n).val = i := congrArg Subtype.val hn
  have hm' : (numberCode_l K m).val = j := congrArg Subtype.val hm
  rw [← hn'] at hix
  rw [← hm'] at hjy
  have read (T : type_l hℳ) (hT : spec_l K f T R) :
      SecondOrderPairing.relation_l R n m ↔ value_l (ℳ := 𝒱) T x y := by
    refine (hT n m).trans ⟨?_, fun h => ⟨x, y, hix, hjy, h⟩⟩
    rintro ⟨a, b, ha, hb, hValue⟩
    have hA : a = x := SecondOrderFunctionLaws.value_unique_l hℳ hf ha hix
    have hB : b = y := SecondOrderFunctionLaws.value_unique_l hℳ hf hb hjy
    exact hA ▸ hB ▸ hValue
  exact (read P hP).symm.trans (read Q hQ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonReal
