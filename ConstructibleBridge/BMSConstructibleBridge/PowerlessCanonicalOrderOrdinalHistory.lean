import BMSConstructibleBridge.SecondOrderCanonicalLevel
import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.PowerlessValueBounded

/-! # 原规范良序历史的实际序数重索引

对象语言为纯隶属 ℒ，背景是原 num/set 的二阶算术模型及其实际商。
消费同一原规范历史的 I、J、T、G、q，实际构造定义域为原序数 A 的
函数图 Pord。旧数字索引仅用于这次 raw 图像构造及正确性证明；没有
把 J、q 或 Pord 当作 Class，没有构造枚举族，也没有使用 Collection。

两种读数覆盖全部内部 raw 坐标：一是固定原历史的数字图像，二是同一
实际层载体上的原规范良序。后者通过原规范历史唯一性认同，不重新选择
编码包或 Sat。这里是后续有界历史检查器的语义中间接口，不是 Class
规范历史的存在性或 BMS 终局对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderOrdinalHistory

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 固定旧编号图的图像正文；并不要求这些参数属于 Class。 -/
def body_m {Γ Δ : SortContext ℒ} (I J G a P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists I <|
    .conj (PowerlessValueBounded.formula_m (up J) (.bvar .here) (up a))
      (PowerlessValueBounded.formula_m (up G) (.bvar .here) (up P))

theorem body_delta_l {Γ Δ : SortContext ℒ} (I J G a P : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m I J G a P) :=
  .bounded_exists _ (.conj (PowerlessValueBounded.delta_l _ _ _)
    (PowerlessValueBounded.delta_l _ _ _))

def body_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I J G a P : carrier_l 𝒩) : Prop :=
  ∃ i, member_l 𝒩 i I ∧ value_l (ℳ := 𝒩) J i a ∧ value_l (ℳ := 𝒩) G i P

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (I J G a P : Term ℒ Γ Δ .set) :
    (body_m I J G a P).satisfies η ↔
      body_l (I.eval η) (J.eval η) (G.eval η) (a.eval η) (P.eval η) := by
  simp only [body_m, body_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private abbrev zero_l (K : source_coding_l hℳ) :=
  (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

/-- 完整 raw 值读数；图的干净成员另由原 map 规格保留。 -/
def spec_l (A I J G Pord : type_l hℳ) : Prop :=
  ∀ a P, value_l (ℳ := 𝒱) Pord a P ↔ mem_l hℳ a A ∧ body_l (𝒩 := 𝒱) I J G a P

variable {t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q : type_l hℳ}

/-- 每个实际层坐标都有一个旧图像输出，仍留在原 raw 陪域 q 内。 -/
theorem body_total_l (K : source_coding_l hℳ)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    {a : type_l hℳ} (ha : mem_l hℳ a A) :
    ∃ P, mem_l hℳ P q ∧ body_l (𝒩 := 𝒱) I J G a P := by
  obtain ⟨i, hi, hia⟩ := h.configuration.indexOnto a ha
  obtain ⟨P, ⟨hPq, hiP⟩, _⟩ := h.comparisonMap.2 i (h.configuration.indexSubset i hi)
  exact ⟨P, hPq, i, hi, hia, hiP⟩

/-- 用同一原历史及其实际 F 读数，直接建立原规范层证书。 -/
theorem body_level_l (K : source_coding_l hℳ)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    {a X P : type_l hℳ} (hFX : value_l (ℳ := 𝒱) F a X)
    (hBody : body_l (𝒩 := 𝒱) I J G a P) :
    SecondOrderCanonicalLevelSyntax.level_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid B P₀ a X P := by
  obtain ⟨i, _, hia, hiP⟩ := hBody
  exact ⟨A, F, r, I, J, T, G, q, h, i, hia,
    (h.configuration.layerRead i X).mpr ⟨a, hia, hFX⟩, hiP⟩

theorem body_unique_l (K : source_coding_l hℳ)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    {a P Q : type_l hℳ} (hP : body_l (𝒩 := 𝒱) I J G a P)
    (hQ : body_l (𝒩 := 𝒱) I J G a Q) : P = Q := by
  have hPCopy := hP
  obtain ⟨i, _, hia, _⟩ := hPCopy
  have ha := (SecondOrderFunctionLaws.value_mem_l hℳ h.configuration.indexMap hia).2
  obtain ⟨X, ⟨_, hFX⟩, _⟩ := h.configuration.hierarchy.1.2 a ha
  exact (SecondOrderCanonicalLevel.unique_l K hCoding
    (body_level_l K h hFX hP) (body_level_l K h hFX hQ)).2

/-- 与任意原规范证书比较，不要求其采用同一数字编号。 -/
theorem level_body_l (K : source_coding_l hℳ)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    {a X P : type_l hℳ} (hFX : value_l (ℳ := 𝒱) F a X)
    (hLevel : SecondOrderCanonicalLevelSyntax.level_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid B P₀ a X P) :
    body_l (𝒩 := 𝒱) I J G a P := by
  have ha := (SecondOrderFunctionLaws.value_mem_l hℳ h.configuration.hierarchy.1 hFX).1
  obtain ⟨Q, _, hQ⟩ := body_total_l K h ha
  have hPQ := (SecondOrderCanonicalLevel.unique_l K hCoding hLevel
    (body_level_l K h hFX hQ)).2
  exact hPQ.symm ▸ hQ

theorem level_read_l (K : source_coding_l hℳ)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    {Pord a X P : type_l hℳ} (hRead : spec_l A I J G Pord)
    (hFX : value_l (ℳ := 𝒱) F a X) :
    value_l (ℳ := 𝒱) Pord a P ↔
      SecondOrderCanonicalLevelSyntax.level_l K.omega (zero_l K)
        t₁ t₂ t₃ Pair Valid B P₀ a X P := by
  constructor
  · intro hP
    exact body_level_l K h hFX ((hRead a P).mp hP).2
  · intro hP
    exact (hRead a P).mpr
      ⟨(SecondOrderFunctionLaws.value_mem_l hℳ h.configuration.hierarchy.1 hFX).1,
        level_body_l K hCoding h hFX hP⟩

/-- 即使不预先给出 F 的某个输出，也保留明确的原序数域守卫。 -/
theorem canonical_read_l (K : source_coding_l hℳ)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    {Pord : type_l hℳ} (hRead : spec_l A I J G Pord) (a P : type_l hℳ) :
    value_l (ℳ := 𝒱) Pord a P ↔ mem_l hℳ a A ∧ ∃ X,
      value_l (ℳ := 𝒱) F a X ∧ SecondOrderCanonicalLevelSyntax.level_l
        K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P := by
  constructor
  · intro hP
    have ha := ((hRead a P).mp hP).1
    obtain ⟨X, ⟨_, hFX⟩, _⟩ := h.configuration.hierarchy.1.2 a ha
    exact ⟨ha, X, hFX, (level_read_l K hCoding h hRead hFX).mp hP⟩
  · rintro ⟨_, X, hFX, hP⟩
    exact (level_read_l K hCoding h hRead hFX).mpr hP

/-- 原图像存在构造产生一张实际集合函数图；不选择 Type 层输出函数。 -/
theorem exists_l (K : source_coding_l hℳ)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q) :
    ∃ Pord : type_l hℳ, map_l (ℳ := 𝒱) Pord A q ∧ spec_l A I J G Pord ∧
      (∀ a X P, value_l (ℳ := 𝒱) F a X →
        (value_l (ℳ := 𝒱) Pord a P ↔ SecondOrderCanonicalLevelSyntax.level_l
          K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P)) ∧
      ∀ a P, value_l (ℳ := 𝒱) Pord a P ↔ mem_l hℳ a A ∧ ∃ X,
        value_l (ℳ := 𝒱) F a X ∧ SecondOrderCanonicalLevelSyntax.level_l
          K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := body_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree G).pushFree J).pushFree I
  have hφ (a P : type_l hℳ) : φ.satisfies ((η.pushFree P).pushFree a) ↔
      body_l (𝒩 := 𝒱) I J G a P := body_formula_l _ _ _ _ _ _
  obtain ⟨Pord, hImage⟩ := SecondOrderDefinableRelationImage.exists_l hℳ φ η A q
  have hMembers (p : type_l hℳ) : mem_l hℳ p Pord ↔ ∃ a P,
      mem_l hℳ a A ∧ mem_l hℳ P q ∧ body_l (𝒩 := 𝒱) I J G a P ∧
        SecondOrderPairObjects.ordered_l hℳ a P p := by
    constructor
    · intro hp
      obtain ⟨a, P, ha, hPq, hBody, hPair⟩ := (hImage p).mp hp
      exact ⟨a, P, ha, hPq, (hφ a P).mp hBody, hPair⟩
    · rintro ⟨a, P, ha, hPq, hBody, hPair⟩
      exact (hImage p).mpr ⟨a, P, ha, hPq, (hφ a P).mpr hBody, hPair⟩
  have hRead : spec_l A I J G Pord := by
    intro a P
    constructor
    · rintro ⟨p, hp, haP⟩
      obtain ⟨b, Q, hb, _, hBody, hbQ⟩ := (hMembers p).mp hp
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ haP hbQ).mp rfl
      exact ⟨hb, hBody⟩
    · rintro ⟨ha, hBody⟩
      have hBodyCopy := hBody
      obtain ⟨i, _, _, hiP⟩ := hBodyCopy
      have hPq := (SecondOrderFunctionLaws.value_mem_l hℳ h.comparisonMap hiP).2
      obtain ⟨p, hPair⟩ := SecondOrderPairObjects.ordered_exists_l hℳ a P
      exact ⟨p, (hMembers p).mpr ⟨a, P, ha, hPq, hBody, hPair⟩, hPair⟩
  have hMap : map_l (ℳ := 𝒱) Pord A q := by
    constructor
    · intro p hp
      obtain ⟨a, P, ha, hPq, _, hPair⟩ := (hMembers p).mp hp
      exact ⟨a, P, ha, hPq, hPair⟩
    · intro a ha
      obtain ⟨P, hPq, hBody⟩ := body_total_l K h ha
      refine ⟨P, ⟨hPq, (hRead a P).mpr ⟨ha, hBody⟩⟩, ?_⟩
      intro Q hQ
      exact body_unique_l K hCoding h ((hRead a Q).mp hQ.2).2 hBody
  exact ⟨Pord, hMap, hRead,
    fun _ _ _ hFX => level_read_l K hCoding h hRead hFX,
    canonical_read_l K hCoding h hRead⟩

/-- 相同全 raw 读数及干净 map 规格决定同一实际函数图。 -/
theorem unique_l {Pord Qord : type_l hℳ}
    (hP : map_l (ℳ := 𝒱) Pord A q) (hQ : map_l (ℳ := 𝒱) Qord A q)
    (hReadP : spec_l A I J G Pord) (hReadQ : spec_l A I J G Qord) : Pord = Qord := by
  have hForward {S R : type_l hℳ} (hS : map_l (ℳ := 𝒱) S A q)
      (hReadS : spec_l A I J G S) (hReadR : spec_l A I J G R)
      (p : type_l hℳ) (hp : mem_l hℳ p S) : mem_l hℳ p R := by
    obtain ⟨a, P, _, _, hPair⟩ := hS.1 p hp
    have hValue : value_l (ℳ := 𝒱) R a P := (hReadR a P).mpr
      ((hReadS a P).mp ⟨p, hp, hPair⟩)
    obtain ⟨s, hs, hsPair⟩ := hValue
    exact (SecondOrderPairObjects.ordered_unique_l hℳ hsPair hPair) ▸ hs
  apply SecondOrderQuotient.ext_l hℳ
  intro p
  exact ⟨hForward hP hReadP hReadQ p, hForward hQ hReadQ hReadP p⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderOrdinalHistory
