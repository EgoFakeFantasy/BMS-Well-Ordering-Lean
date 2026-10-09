import BMSConstructibleBridge.SecondOrderComparisonEncodeSyntax
import BMSConstructibleBridge.SecondOrderCanonicalOrderComparison

/-! # 可供实际递归读取的纯规范后继行公式

图输出只作存在见证，行输出为唯一 ω 子集。原比较实数的唯一性与纯集合
代表唯一性分别核验；不借解码图唯一性推断任意实数相等。
下面总唯一性仍是模型接口，尚未装配全部阶段分支及最终 BMS Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderComparisonSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def output_m {Γ Δ : SortContext ℒ}
    (ω A P e t₁ t₂ t₃ Pair Valid D f W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj
    (SecondOrderCanonicalOrderUniform.step_m (up ω) (up A) (up P) (up e) (up t₁) (up t₂) (up t₃)
      (up Pair) (up Valid) (up D) (.bvar .here))
    (SecondOrderComparisonEncodeSyntax.formula_m (up ω) (up e) (up W) (up f) (.bvar .here))

def output_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A P e t₁ t₂ t₃ Pair Valid D f W : carrier_l 𝒩) : Prop :=
  ∃ E, SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒩) ω A P e t₁ t₂ t₃ Pair Valid D E ∧
    SecondOrderComparisonEncodeSyntax.encoded_l (𝒩 := 𝒩) ω e W f E

theorem output_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A P e t₁ t₂ t₃ Pair Valid D f W : Term ℒ Γ Δ .set) :
    (output_m ω A P e t₁ t₂ t₃ Pair Valid D f W).satisfies η ↔
      output_l (ω.eval η) (A.eval η) (P.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (Pair.eval η) (Valid.eval η) (D.eval η) (f.eval η) (W.eval η) := by
  simp only [output_m, output_l, Formula.satisfies, SecondOrderCanonicalOrderUniform.step_formula_l,
    SecondOrderComparisonEncodeSyntax.formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem reading_l (K : source_coding_l hℳ)
    (S : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (W : SecondOrderModel.set_l ℳ)
    (hS : setRel_l K S W) (A P t₁ t₂ t₃ Pair Valid D f : SecondOrderQuotient.type_l hℳ) :
    output_l (𝒩 := 𝒱) K.omega A P (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃ Pair Valid D f S.val ↔
      SecondOrderCanonicalOrderComparison.output_l K f K.omega A P
        (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃ Pair Valid D W := by
  unfold output_l SecondOrderCanonicalOrderComparison.output_l
  exact exists_congr (fun E => and_congr Iff.rfl
    (SecondOrderComparisonEncodeSyntax.reading_l K S W hS f E))

/-- 即使旧序非法，原部分步骤仍单值；存在性与单值性不能混作一项守卫。 -/
theorem unique_l (K : source_coding_l hℳ)
    {f A P t₁ t₂ t₃ Pair Valid D X Y : SecondOrderQuotient.type_l hℳ}
    (ht₁ : t₁ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 1))
    (ht₂ : t₂ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 2))
    (ht₃ : t₃ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 3))
    (hPairMap : map_l (ℳ := 𝒱) Pair K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N)
    (hX : output_l (𝒩 := 𝒱) K.omega A P (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃ Pair Valid D f X)
    (hY : output_l (𝒩 := 𝒱) K.omega A P (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃ Pair Valid D f Y) : X = Y := by
  obtain ⟨E, hE, hEncodedX⟩ := hX
  obtain ⟨E', hE', hEncodedY⟩ := hY
  have hEq := SecondOrderCanonicalOrderUniform.unique_l K rfl rfl ht₁ ht₂ ht₃ hPairMap hPair hV hValid hE' hE
  subst E'
  let X' : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega :=
    ⟨X, SecondOrderComparisonEncodeSyntax.guard_l hEncodedX⟩
  let Y' : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega :=
    ⟨Y, SecondOrderComparisonEncodeSyntax.guard_l hEncodedY⟩
  obtain ⟨U, hU⟩ := PowerlessBMSQuotientReals.trace_exists_l K X'
  obtain ⟨W, hW⟩ := PowerlessBMSQuotientReals.trace_exists_l K Y'
  have hUW : U = W := SecondOrderComparisonReal.unique_l K
    ((SecondOrderComparisonEncodeSyntax.reading_l K X' U hU f E).mp hEncodedX)
    ((SecondOrderComparisonEncodeSyntax.reading_l K Y' W hW f E).mp hEncodedY)
  exact congrArg Subtype.val (PowerlessBMSQuotientReals.representative_unique_l K (hUW ▸ hU) hW)

theorem exists_unique_l (K : source_coding_l hℳ)
    {f A P t₁ t₂ t₃ Pair Valid D : SecondOrderQuotient.type_l hℳ}
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒱) (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃)
    (ht₁ : t₁ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 1))
    (ht₂ : t₂ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 2))
    (ht₃ : t₃ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 3))
    (hPairMap : map_l (ℳ := 𝒱) Pair K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N)
    (hP : wellOrder_l (ℳ := 𝒱) A P)
    (hTrans : ∀ x y, SecondOrderQuotient.mem_l hℳ x A → SecondOrderQuotient.mem_l hℳ y x →
      SecondOrderQuotient.mem_l hℳ y A) (hDef : SecondOrderMemberDef.spec_l hℳ A D) :
    ∃! S : SecondOrderQuotient.type_l hℳ,
      output_l (𝒩 := 𝒱) K.omega A P (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃ Pair Valid D f S := by
  obtain ⟨W, hW, _⟩ := SecondOrderCanonicalOrderComparison.exists_unique_l
    K rfl rfl hTags ht₁ ht₂ ht₃ hPairMap hPair hV hValid hP hTrans hDef
  obtain ⟨S, hS⟩ := representative_exists_l K W
  have hOutput := (reading_l K S W hS A P t₁ t₂ t₃ Pair Valid D f).mpr hW
  exact ⟨S.val, hOutput, fun X hX => unique_l K ht₁ ht₂ ht₃ hPairMap hPair hV hValid hX hOutput⟩

#print axioms output_formula_l
#print axioms reading_l
#print axioms unique_l
#print axioms exists_unique_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderComparisonSyntax
