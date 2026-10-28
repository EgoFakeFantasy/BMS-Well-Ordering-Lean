import BMSConstructibleBridge.PowerlessFiniteSequencesBounded
import BMSConstructibleBridge.PowerlessSatisfactionSpecificationBounded
import BMSConstructibleBridge.PowerlessSatisfactionGraphClean

/-! # 统一 Sat 族的纯 Δ₀ 规范化矩阵

序列见证限制到显式层 D；覆盖合法赋值的母界 M 把序列规格化成有界检查，
原 Sat 方程使用同一有限序列见证，另加无垃圾成员证书。读数恢复原商
中全部对象上的完整 Seq 与 Sat 规格，不假定模型内部自然数外部标准。

这里只证明矩阵、原规格读数及规范图唯一性。共同层、层内见证总性与
历史存在必须另行构造；这些条件不能由 Δ₀ 分类或唯一性替代。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionNormalizedMatrix

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open PowerlessFormulaValidityReading (code_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ}
    (ω A e N T M D t₁ t₂ t₃ F R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists D <|
    .conj (PowerlessFiniteSequencesBounded.formula_m (up ω) (up A) (up M) (.bvar .here)) <|
      .conj (PowerlessSatisfactionSpecificationBounded.spec_m
        (up ω) (up A) (up e) (up N) (up T) (.bvar .here)
        (up t₁) (up t₂) (up t₃) (up F) (up R))
        (PowerlessSatisfactionGraphClean.formula_m (up ω) (.bvar .here) (up R))

theorem delta_l {Γ Δ : SortContext ℒ}
    (ω A e N T M D t₁ t₂ t₃ F R : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω A e N T M D t₁ t₂ t₃ F R) :=
  .bounded_exists _ <| .conj (PowerlessFiniteSequencesBounded.delta_l _ _ _ _) <|
    .conj (PowerlessSatisfactionSpecificationBounded.delta_l _ _ _ _ _ _ _ _ _ _ _)
      (PowerlessSatisfactionGraphClean.delta_l _ _ _)

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A e N T M D t₁ t₂ t₃ F R : carrier_l 𝒩) : Prop :=
  ∃ S, member_l 𝒩 S D ∧ PowerlessFiniteSequencesBounded.holds_l ω A M S ∧
    PowerlessSatisfactionSpecificationBounded.spec_l ω A e N T S t₁ t₂ t₃ F R ∧
    PowerlessSatisfactionGraphClean.holds_l ω S R

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A e N T M D t₁ t₂ t₃ F R : Term ℒ Γ Δ .set) :
    (formula_m ω A e N T M D t₁ t₂ t₃ F R).satisfies η ↔
      holds_l (ω.eval η) (A.eval η) (e.eval η) (N.eval η) (T.eval η)
        (M.eval η) (D.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (F.eval η) (R.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessFiniteSequencesBounded.formula_l,
    PowerlessSatisfactionSpecificationBounded.spec_formula_l,
    PowerlessSatisfactionGraphClean.formula_l, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 母界只须覆盖全部合法赋值，不必自身等于完整序列集。 -/
theorem spec_iff_of_coverage_l {ω A e N T M D t₁ t₂ t₃ F R : SecondOrderQuotient.type_l hℳ}
    (hω : omega_l (ℳ := RawModel) ω) (he : ∀ x, ¬SecondOrderQuotient.mem_l hℳ x e)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω ω N)
    (hT : map_l (ℳ := RawModel) T ω ω)
    (hCoverage : ∀ f, PowerlessFiniteSequencesSyntax.sequence_l (ℳ := RawModel) ω A f →
      SecondOrderQuotient.mem_l hℳ f M) :
    holds_l (𝒩 := RawModel) ω A e N T M D t₁ t₂ t₃ F R ↔
      ∃ S, SecondOrderQuotient.mem_l hℳ S D ∧
        PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω A S ∧
        PowerlessSatisfactionSpecification.spec_l (𝒩 := RawModel) ω A e t₁ t₂ t₃ T F R ∧
        PowerlessSatisfactionGraphClean.holds_l (𝒩 := RawModel) ω S R := by
  constructor
  · rintro ⟨S, hS, hSeq, hSat, hClean⟩
    have hSeq' := (PowerlessFiniteSequencesBounded.spec_iff_of_coverage_l hCoverage).mp hSeq
    exact ⟨S, hS, hSeq',
      (PowerlessSatisfactionSpecificationBounded.guarded_iff_l hω he hN hT hSeq').mp hSat, hClean⟩
  · rintro ⟨S, hS, hSeq, hSat, hClean⟩
    exact ⟨S, hS, (PowerlessFiniteSequencesBounded.spec_iff_of_coverage_l hCoverage).mpr hSeq,
      (PowerlessSatisfactionSpecificationBounded.guarded_iff_l hω he hN hT hSeq).mpr hSat, hClean⟩

/-- 完整母序列集是合法赋值覆盖条件的一个充分来源。 -/
theorem spec_iff_l {ω A X e N T M D t₁ t₂ t₃ F R : SecondOrderQuotient.type_l hℳ}
    (hω : omega_l (ℳ := RawModel) ω) (he : ∀ x, ¬SecondOrderQuotient.mem_l hℳ x e)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω ω N)
    (hT : map_l (ℳ := RawModel) T ω ω)
    (hM : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω X M)
    (hA : subset_l (ℳ := RawModel) A X) :
    holds_l (𝒩 := RawModel) ω A e N T M D t₁ t₂ t₃ F R ↔
      ∃ S, SecondOrderQuotient.mem_l hℳ S D ∧
        PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω A S ∧
        PowerlessSatisfactionSpecification.spec_l (𝒩 := RawModel) ω A e t₁ t₂ t₃ T F R ∧
        PowerlessSatisfactionGraphClean.holds_l (𝒩 := RawModel) ω S R :=
  spec_iff_of_coverage_l hω he hN hT (fun f ⟨n, hn, hf⟩ =>
    (hM f).mpr ⟨n, hn, PowerlessFiniteSequencesBounded.map_subset_l hA hf⟩)

/-- 合法赋值被共同母界覆盖时，固定编码包上的规范 Sat 图对象唯一。 -/
theorem unique_of_coverage_l (K : source_coding_l hℳ)
    {A N T M D F R R' : SecondOrderQuotient.type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) K.omega K.omega N)
    (hT : map_l (ℳ := RawModel) T K.omega K.omega)
    (hCoverage : ∀ f, PowerlessFiniteSequencesSyntax.sequence_l (ℳ := RawModel) K.omega A f →
      SecondOrderQuotient.mem_l hℳ f M)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K T)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hF : ∀ c L, value_l (ℳ := RawModel) F c L ↔ PowerlessRelationalCodeValidity.valid_l K V c L)
    (hR : holds_l (𝒩 := RawModel) K.omega A (code_l K (numeral_l ℳ 0)) N T M D
      (code_l K (numeral_l ℳ 1)) (code_l K (numeral_l ℳ 2))
      (code_l K (numeral_l ℳ 3)) F R)
    (hR' : holds_l (𝒩 := RawModel) K.omega A (code_l K (numeral_l ℳ 0)) N T M D
      (code_l K (numeral_l ℳ 1)) (code_l K (numeral_l ℳ 2))
      (code_l K (numeral_l ℳ 3)) F R') : R = R' := by
  have he := PowerlessBMSQuotientSuccessor.zero_l K
  have hω : omega_l (ℳ := RawModel) K.omega := K.omega_spec
  obtain ⟨S, _hS, hSeq, hSat, hClean⟩ :=
    (spec_iff_of_coverage_l hω he hN hT hCoverage).mp hR
  obtain ⟨S', _hS', hSeq', hSat', hClean'⟩ :=
    (spec_iff_of_coverage_l hω he hN hT hCoverage).mp hR'
  have hSS' : S = S' := SecondOrderQuotient.ext_l hℳ S S'
    (fun f => (hSeq f).trans (hSeq' f).symm)
  subst S'
  exact PowerlessSatisfactionGraphClean.unique_l K hT hPair hV hF hSat hSat' hClean hClean'

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionNormalizedMatrix
