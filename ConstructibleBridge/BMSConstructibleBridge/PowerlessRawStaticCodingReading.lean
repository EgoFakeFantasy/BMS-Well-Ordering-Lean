import BMSConstructibleBridge.SecondOrderQuotientNumericFunction
import BMSConstructibleBridge.PowerlessSatisfactionExistenceSyntax
import BMSConstructibleBridge.PowerlessFormulaValidityTrace
import BMSConstructibleBridge.PowerlessRelationalCodeValidity

/-! # 任意原商静态包的同编码读数

背景为原 num/set Z₂；实际归纳关系由纯公式的 GraphTranslation 归纳
实例提供。原商三角递推与规范数字图在全部内部自然数上相容，故
给定 P 的读数由原递推唯一确定；规范辅助图不替换给定图。
完整 Seq 与有限证书再识别给定 F 的全部 raw 坐标。不要求静态
参数属于 Class 或某个实际层，不假定母域满足完整源理论。
此语义接口服务于捕获包的原 Def 认同，不替代最终良序对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRawStaticCodingReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderEvaluationRule (numeral_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 规范辅助图由原理解公理产生，存在见证仅在 Prop 中消去。 -/
private theorem canonical_l (K : source_coding_l hℳ) :
    ∃ U : type_l hℳ,
      PowerlessTriangular.triangular_l (ℳ := 𝒱) K.omega (code_l K (numeral_l ℳ 0)) U ∧
      PowerlessBMSQuotientPairingBounds.spec_l K U := by
  let φ : Formula SecondOrderSyntax.signature_m [] [.num, .num] :=
    SecondOrderTriangularArithmetic.relation_m (.fvar .here) (.fvar (.there .here))
  obtain ⟨E, hE⟩ := SecondOrderRelations.comprehension_l hℳ φ
    (SecondOrderArithmetic.pure_language_m _ rfl) (Env.empty (M := ℳ))
  have hRead (i j : SecondOrderModel.num_l ℳ) :
      SecondOrderPairing.relation_l E i j ↔ SecondOrderTriangularArithmetic.relation_l i j := by
    simpa only [φ, SecondOrderTriangularArithmetic.relation_formula_l, Term.eval,
      Env.pushFree, Assignment.push] using hE i j
  have hFunction : SecondOrderFunctions.function_l E := by
    intro i
    obtain ⟨j, hj⟩ := SecondOrderTriangularArithmetic.exists_l hℳ i
    exact ⟨j, (hRead i j).mpr hj,
      fun k hk => SecondOrderTriangularArithmetic.unique_l hℳ ((hRead i k).mp hk) hj⟩
  obtain ⟨U, hMap, hValue⟩ := SecondOrderQuotientNumericFunction.exists_l K hFunction
  have hSpec : PowerlessBMSQuotientPairingBounds.spec_l K U := by
    intro i j
    rw [hValue i (code_l K j)]
    constructor
    · rintro ⟨v, hv, hEq⟩
      have h : j = v := numberCode_injective_l K (Subtype.ext hEq)
      subst v
      exact (hRead i j).mp hv
    · intro h
      exact ⟨j, (hRead i j).mpr h, rfl⟩
  refine ⟨U, ⟨hMap, ?_, ?_⟩, hSpec⟩
  · apply (hSpec (numeral_l ℳ 0) (numeral_l ℳ 0)).mpr
    change SecondOrderModel.add_l (SecondOrderModel.zero_l ℳ) (SecondOrderModel.zero_l ℳ) =
      SecondOrderModel.mul_l (SecondOrderModel.zero_l ℳ)
        (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))
    rw [SecondOrderModel.add_zero_l hℳ, SecondOrderMultiplication.zero_mul_l hℳ]
  · intro n m x y hn hm hx hy
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hn⟩
    have hnEq : n = code_l K i := (congrArg Subtype.val hi).symm
    rw [hnEq] at hm
    have hmEq : m = code_l K (SecondOrderModel.succ_l i) :=
      PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) hm
        (PowerlessBMSQuotientSuccessor.successor_l K i)
    obtain ⟨j, hj⟩ := numberCode_surjective_l K
      ⟨x, (SecondOrderFunctionProperties.value_mem_l hℳ hMap hx).2⟩
    obtain ⟨k, hk⟩ := numberCode_surjective_l K
      ⟨y, (SecondOrderFunctionProperties.value_mem_l hℳ hMap hy).2⟩
    have hxEq : x = code_l K j := (congrArg Subtype.val hj).symm
    have hyEq : y = code_l K k := (congrArg Subtype.val hk).symm
    rw [hnEq, hxEq] at hx
    rw [hmEq, hyEq] at hy
    have h := SecondOrderTriangularArithmetic.successor_l hℳ
      ((hSpec i j).mp hx) ((hSpec (SecondOrderModel.succ_l i) k).mp hy)
    rw [hxEq, hmEq]
    exact (PowerlessBMSQuotientRecursion.addition_iff_l K j (SecondOrderModel.succ_l i) y).mpr
      (hyEq.trans (congrArg (code_l K) h))

/-- 归纳对象是实际纯比较公式，不对任意宿主谓词或外部长度归纳。 -/
private theorem agreement_l (K : source_coding_l hℳ) {T U : type_l hℳ}
    (hT : PowerlessTriangular.triangular_l (ℳ := 𝒱) K.omega (code_l K (numeral_l ℳ 0)) T)
    (hU : PowerlessTriangular.triangular_l (ℳ := 𝒱) K.omega (code_l K (numeral_l ℳ 0)) U)
    (n : SecondOrderModel.num_l ℳ) (x y : type_l hℳ)
    (hx : value_l (ℳ := 𝒱) T (code_l K n) x)
    (hy : value_l (ℳ := 𝒱) U (code_l K n) y) : x = y := by
  have h := PowerlessBMSQuotientInduction.induction_l K
    PowerlessBMSQuotientRecursion.agreement_m
    (((Env.empty (M := 𝒱)).pushFree U).pushFree T) ?_ ?_ n
  · exact (PowerlessBMSQuotientRecursion.agreement_formula_l T U (code_l K n)).mp h x y hx hy
  · apply (PowerlessBMSQuotientRecursion.agreement_formula_l T U _).mpr
    intro x y hx hy
    exact (PowerlessBMSQuotientRecursion.value_unique_l hT.1 hx hT.2.1).trans
      (PowerlessBMSQuotientRecursion.value_unique_l hU.1 hy hU.2.1).symm
  · intro k hk
    apply (PowerlessBMSQuotientRecursion.agreement_formula_l T U _).mpr
    intro x y hx hy
    obtain ⟨v, hv, _⟩ := hT.1.2 (code_l K k) (numberCode_l K k).property
    obtain ⟨w, hw, _⟩ := hU.1.2 (code_l K k) (numberCode_l K k).property
    have hvw := (PowerlessBMSQuotientRecursion.agreement_formula_l T U (code_l K k)).mp hk
      v w hv.2 hw.2
    subst w
    exact PowerlessBMSQuotientRecursion.addition_unique_l K
      (numberCode_l K (SecondOrderModel.succ_l k)).property
      (hT.2.2 _ _ v x (numberCode_l K k).property
        (PowerlessBMSQuotientSuccessor.successor_l K k) hv.2 hx)
      (hU.2.2 _ _ v y (numberCode_l K k).property
        (PowerlessBMSQuotientSuccessor.successor_l K k) hw.2 hy)

/-- 给定图的完整三角递推确定原内部数字规格，不替换该图。 -/
theorem triangular_l (K : source_coding_l hℳ) {ω e T : type_l hℳ}
    (hω : ω = K.omega) (he : e = code_l K (numeral_l ℳ 0))
    (hT : PowerlessTriangular.triangular_l (ℳ := 𝒱) ω e T) :
    PowerlessBMSQuotientPairingBounds.spec_l K T := by
  subst ω
  subst e
  obtain ⟨U, hU, hSpec⟩ := canonical_l K
  intro i j
  have hRead : value_l (ℳ := 𝒱) T (code_l K i) (code_l K j) ↔
      value_l (ℳ := 𝒱) U (code_l K i) (code_l K j) := by
    constructor
    · intro h
      obtain ⟨y, hy, _⟩ := hU.1.2 (code_l K i) (numberCode_l K i).property
      have hEq := agreement_l K hT hU i (code_l K j) y h hy.2
      exact hEq.symm ▸ hy.2
    · intro h
      obtain ⟨x, hx, _⟩ := hT.1.2 (code_l K i) (numberCode_l K i).property
      have hEq := agreement_l K hT hU i x (code_l K j) hx.2 h
      exact hEq ▸ hx.2
  exact hRead.trans (hSpec i j)

/-- 空集与真实后继在全部 raw 候选上识别零码和三个标签。 -/
theorem tags_l (K : source_coding_l hℳ) {e t₁ t₂ t₃ : type_l hℳ}
    (h : PowerlessEvaluationTags.tags_l (ℳ := 𝒱) e t₁ t₂ t₃) :
    e = code_l K (numeral_l ℳ 0) ∧ t₁ = code_l K (numeral_l ℳ 1) ∧
      t₂ = code_l K (numeral_l ℳ 2) ∧ t₃ = code_l K (numeral_l ℳ 3) := by
  have he : e = code_l K (numeral_l ℳ 0) :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false (h.1 x)
      (PowerlessBMSQuotientSuccessor.zero_l K x))
  have h₁ := h.2.1
  rw [he] at h₁
  have ht₁ : t₁ = code_l K (numeral_l ℳ 1) :=
    PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) h₁
      (PowerlessBMSQuotientSuccessor.successor_l K (numeral_l ℳ 0))
  have h₂ := h.2.2.1
  rw [ht₁] at h₂
  have ht₂ : t₂ = code_l K (numeral_l ℳ 2) :=
    PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) h₂
      (PowerlessBMSQuotientSuccessor.successor_l K (numeral_l ℳ 1))
  have h₃ := h.2.2.2
  rw [ht₂] at h₃
  exact ⟨he, ht₁, ht₂, PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) h₃
    (PowerlessBMSQuotientSuccessor.successor_l K (numeral_l ℳ 2))⟩

/-- 完整数字序列覆盖使给定合法性图的全 raw 规格等于原内部关系。 -/
private theorem validity_l (K : source_coding_l hℳ) {N T : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N)
    (hT : map_l (ℳ := 𝒱) T K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (c l : type_l hℳ) :
    PowerlessFormulaValidityBounded.query_l (𝒩 := 𝒱) K.omega (code_l K (numeral_l ℳ 0))
      N T (code_l K (numeral_l ℳ 1)) (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) c l ↔
      PowerlessRelationalCodeValidity.valid_l K V c l := by
  let B := code_l K (numeral_l ℳ 0)
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B :=
    fun x hx _ _ => (PowerlessBMSQuotientSuccessor.zero_l K x hx).elim
  have hClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
  let ω₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨K.omega, hClass⟩
  have hΩ : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) ω₀ :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω₀).mpr K.omega_spec
  have hRead (n m : SecondOrderModel.num_l ℳ) :=
    PowerlessFormulaValidityTrace.query_iff_l K hΩ rfl hN hT hSpec hV n m
  constructor
  · intro h
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨c, h.1⟩
    obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨l, h.2.1⟩
    have hc : c = code_l K n := (congrArg Subtype.val hn).symm
    have hl : l = code_l K m := (congrArg Subtype.val hm).symm
    rw [hc, hl] at h
    exact ⟨n, m, hc, hl, (hRead n m).mp h⟩
  · rintro ⟨n, m, rfl, rfl, h⟩
    exact (hRead n m).mpr h

/-- 原静态包提供同一 e、标签、N、P、F 的完整读数。 -/
theorem reading_l (K : source_coding_l hℳ) {ω e t₁ t₂ t₃ P N F : type_l hℳ}
    (hω : ω = K.omega)
    (h : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒱) ω e t₁ t₂ t₃ P N F) :
    e = code_l K (numeral_l ℳ 0) ∧ t₁ = code_l K (numeral_l ℳ 1) ∧
      t₂ = code_l K (numeral_l ℳ 2) ∧ t₃ = code_l K (numeral_l ℳ 3) ∧
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N ∧
      map_l (ℳ := 𝒱) P K.omega K.omega ∧ PowerlessBMSQuotientPairingBounds.spec_l K P ∧
      ∀ V : SecondOrderModel.set_l ℳ, SecondOrderTriangularFormulaSyntax.spec_l V →
        ∀ c l, value_l (ℳ := 𝒱) F c l ↔ PowerlessRelationalCodeValidity.valid_l K V c l := by
  obtain ⟨he, ht₁, ht₂, ht₃⟩ := tags_l K h.1
  have hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N := by
    simpa only [hω] using h.2.2.2.1
  have hP : map_l (ℳ := 𝒱) P K.omega K.omega := by
    simpa only [hω] using h.2.1.1
  have hSpec := triangular_l K hω he h.2.1
  refine ⟨he, ht₁, ht₂, ht₃, hN, hP, hSpec, ?_⟩
  intro V hV c l
  have hF := h.2.2.2.2 c l
  rw [hω, he, ht₁, ht₂, ht₃] at hF
  exact hF.trans (validity_l K hN hP hSpec hV c l)

#print axioms triangular_l
#print axioms tags_l
#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRawStaticCodingReading
