import BMSConstructibleBridge.SecondOrderCanonicalOrderUniform
import BMSConstructibleBridge.PowerlessRelativeClassFixedCoding

/-! # 同一规范后继证书的原 Class 公式读出

纯隶属 ℒ、原 Z₂。已有候选的部分字段是 raw 规格，部分是 Class
规格；本模块逐项读为同一个原对象公式在真实 Class 子模型中的真值。
只把查询、行比较和扩张正文认作 Δ₀，完整候选及良序并非 Δ₀。
不借用完整 Class 理论，不宣称原计数式层次的全局绝对性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalStepReading

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem query_l (ω A S I R t x : M) :
    PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒩₀) ω A S I R t x ↔
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱)
        ω.val A.val S.val I.val R.val t.val x.val := by
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree x |>.pushFree t |>.pushFree R |>.pushFree I
      |>.pushFree S |>.pushFree A |>.pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    PowerlessRelativeClassSatisfactionAllSlots.query_m
      (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
  have h := PowerlessRelativeClassBounded.formula_l (hBase := hBase) (φ := φ)
    (PowerlessRelativeClassSatisfactionAllSlots.query_delta_l _ _ _ _ _ _ _) η
  simpa only [φ, PowerlessRelativeClassSatisfactionAllSlots.query_formula_l,
    PowerlessRelativeClassRelativization.env_l, η, Term.eval,
    Env.pushFree_here, Env.pushFree_there] using h

theorem comparison_l (I U A Q x y : M) :
    PowerlessRelativeClassRowOrderCanonical.comparison_l (ℳ₀ := 𝒩₀) I U A Q x y ↔
      PowerlessRelativeClassRowOrderCanonical.comparison_l (ℳ₀ := 𝒱)
        I.val U.val A.val Q.val x.val y.val := by
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree y |>.pushFree x |>.pushFree Q
      |>.pushFree A |>.pushFree U |>.pushFree I
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
    PowerlessRelativeClassRowOrderCanonical.comparison_m
      (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
  have h := PowerlessRelativeClassBounded.formula_l (hBase := hBase) (φ := φ)
    (PowerlessRelativeClassRowOrderCanonical.comparison_delta_l _ _ _ _ _ _) η
  simpa only [φ, PowerlessRelativeClassRowOrderCanonical.comparison_formula_l,
    PowerlessRelativeClassRelativization.env_l, η, Term.eval,
    Env.pushFree_here, Env.pushFree_there] using h

theorem queryRead_l {ω A S I R J Q : M}
    (h : SecondOrderCanonicalOrderSyntax.queryRead_l (ℳ₀ := 𝒱)
      ω.val A.val S.val I.val R.val J.val Q.val) :
    SecondOrderCanonicalOrderSyntax.queryRead_l (ℳ₀ := 𝒩₀) ω A S I R J Q := by
  intro t x
  exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Q t x).trans
    ((h t.val x.val).trans (and_congr Iff.rfl (and_congr Iff.rfl
      (query_l ω A S I R t x).symm)))

/-- 完整图的 raw 见证由其已有坐标成员守卫提升，不另选表示。 -/
theorem graph_l {I U A Q Y L : M}
    (h : PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱)
      I.val U.val A.val Q.val Y.val L.val) :
    PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒩₀) I U A Q Y L := by
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, hx, hy, hxy, hBody⟩ := (h p.val).mp hp
    let x₀ : M := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hx⟩
    let y₀ : M := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩
    exact ⟨x₀, y₀, hx, hy,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x₀ y₀ p).mpr hxy,
      (comparison_l I U A Q x₀ y₀).mpr hBody⟩
  · rintro ⟨x, y, hx, hy, hxy, hBody⟩
    exact (h p.val).mpr ⟨x.val, y.val, hx, hy,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p).mp hxy,
      (comparison_l I U A Q x y).mp hBody⟩

theorem extension_l {A D P L E : M}
    (h : SecondOrderWellOrderEndExtensionUnique.graph_l (ℳ₀ := 𝒱)
      A.val D.val P.val L.val E.val) :
    SecondOrderWellOrderEndExtensionUnique.graph_l (ℳ₀ := 𝒩₀) A D P L E := by
  have hBody (x y : M) : SecondOrderWellOrderEndExtension.body_l (ℳ₀ := 𝒩₀) A P L x y ↔
      SecondOrderWellOrderEndExtension.body_l (ℳ₀ := 𝒱) A.val P.val L.val x.val y.val :=
    or_congr
      (and_congr Iff.rfl (and_congr Iff.rfl
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) P x y)))
      (or_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) L x y))))
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, hx, hy, hStep, hxy⟩ := (h p.val).mp hp
    let x₀ : M := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase D.property hx⟩
    let y₀ : M := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase D.property hy⟩
    exact ⟨x₀, y₀, hx, hy, (hBody x₀ y₀).mpr hStep,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x₀ y₀ p).mpr hxy⟩
  · rintro ⟨x, y, hx, hy, hStep, hxy⟩
    exact (h p.val).mpr ⟨x.val, y.val, hx, hy, (hBody x y).mp hStep,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p).mp hxy⟩

/-- 混合证书的每个字段读为真实 Class 结构中的原候选关系。 -/
theorem candidate_l {ω A P R D L : M}
    (h : PowerlessRelativeClassCanonicalOrderStep.candidate_l (hBase := hBase) ω A P R D L) :
    SecondOrderCanonicalOrderSyntax.candidate_l (ℳ₀ := 𝒩₀) ω A P R D L := by
  obtain ⟨S, I, J, U, Q, Y, hIndex, hRead, hRows, hGraph, hSubset, hOrder⟩ := h
  exact ⟨S, I, J, U, Q, Y, hIndex, queryRead_l hRead, hRows, graph_l hGraph,
    (fun x hx => hSubset x.val hx), PowerlessRelativeClassAmbientWellOrder.restrict_l hOrder⟩

theorem step_l {ω A P R D E : M}
    (h : PowerlessRelativeClassCanonicalOrderStep.step_l (hBase := hBase) ω A P R D E) :
    SecondOrderCanonicalOrderSyntax.step_l (ℳ₀ := 𝒩₀) ω A P R D E := by
  obtain ⟨L, hL, hGraph⟩ := h
  exact ⟨L, candidate_l hL, extension_l hGraph⟩

theorem uniform_l {ω A P e t₁ t₂ t₃ Pair Valid D E : M}
    (h : PowerlessRelativeClassCanonicalOrderUniform.step_l (hBase := hBase)
      ω A P e t₁ t₂ t₃ Pair Valid D E) :
    SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒩₀) ω A P e t₁ t₂ t₃ Pair Valid D E := by
  obtain ⟨R, hR, hStep⟩ := h
  exact ⟨R, hR, step_l hStep⟩

#print axioms query_l
#print axioms comparison_l
#print axioms candidate_l
#print axioms step_l
#print axioms uniform_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalStepReading
