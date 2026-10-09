import BMSConstructibleBridge.PowerlessRelativeFiniteHullSatisfaction
import BMSConstructibleBridge.PowerlessRelativeCofinalDefCoding

/-! # 同一闭包域内的原完整 Sat 编码见证

原十二参数矩阵和正文在同一 I/W 上反射。规范 Sat 的真实读值来自
同一个共尾层 U 的原编码包，U 的合法有限赋值覆盖也由此包提供。
捕获 I 内的同一个 S 后，在原模型恢复完整无界 Seq、Sat 和无垃圾
规格；不增加 I 传递性、外部标准性、源 Collection 或 Type 选择。
这里尚不声称非传递 MemberI 中完整无界 Seq/Sat 已对应原规格。
实际 SourceHistory 保留这个双式元素性族并提供调用接口；最终源存在
仍需 Def 精确截迹及弱凝聚，不以本语义中间定理冒充最终 Z₂ 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullSatCoding

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 直接保留全部原绑定参数；同一个 U 同时充当 M 与 D。 -/
def env_l {Δ : SortContext ℒ} (ν : Env RawModel [] Δ)
    (ω A e N T U t₁ t₂ t₃ F R : SecondOrderQuotient.type_l hℳ) :
    Env RawModel PowerlessRelativeFiniteHullSatisfaction.context_m Δ :=
  let η₀ := ((ν.pushBound ω).pushBound A).pushBound e
  let η₁ := ((η₀.pushBound N).pushBound T).pushBound U
  let η₂ := ((η₁.pushBound U).pushBound t₁).pushBound t₂
  ((η₂.pushBound t₃).pushBound F).pushBound R

/-- 消费实际共尾编码包和同 I 元素性，不预供 I 内 Seq 见证。 -/
theorem capture_l {B U I₀ W₀ : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (K : source_coding_l hℳ)
    {ω e t₁ t₂ t₃ T N F Q G : type_l hℳ B} {C : SecondOrderModel.set_l ℳ}
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l (W := U) hBase K ω e t₁ t₂ t₃ T N F Q G C)
    {Δ Ε : SortContext ℒ} (ζ : Env RawModel [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env RawModel [] Δ) (hτ : ∀ v, (τ v).eval ζ = ν.freeVal v)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, SecondOrderQuotient.mem_l hℳ x W₀ → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y W₀)
    (hIW : subset_l (ℳ := RawModel) I₀ W₀)
    (hFree : ∀ v : Variable Δ .set, SecondOrderQuotient.mem_l hℳ (ν.freeVal v) I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeFiniteHullSatisfaction.family_m Δ) I W τ).satisfies ζ)
    {A R : SecondOrderQuotient.type_l hℳ}
    (hBound : ∀ v : Variable PowerlessRelativeFiniteHullSatisfaction.context_m .set,
      SecondOrderQuotient.mem_l hℳ
        ((env_l ν ω.val A e.val N.val T.val U t₁.val t₂.val t₃.val F.val R).boundVal v) I₀)
    (hValue : value_l (ℳ := RawModel) G.val A R) :
    ∃ S, SecondOrderQuotient.mem_l hℳ S I₀ ∧ SecondOrderQuotient.mem_l hℳ S U ∧
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val A S ∧
      PowerlessSatisfactionSpecification.spec_l (𝒩 := RawModel)
        ω.val A e.val t₁.val t₂.val t₃.val T.val F.val R ∧
      PowerlessSatisfactionGraphClean.holds_l (𝒩 := RawModel) ω.val S R := by
  let η := env_l ν ω.val A e.val N.val T.val U t₁.val t₂.val t₃.val F.val R
  obtain ⟨hAU, _hRU, hNorm⟩ := (hCoding.sat_read A R).mp hValue
  have hMatrix : (PowerlessRelativeFiniteHullSatisfaction.matrix_m Δ).satisfies η := by
    apply (PowerlessRelativeFiniteHullSatisfaction.matrix_formula_l η).mpr
    exact hNorm
  have hNonempty : ∃ x, member_l RawModel x W₀ :=
    ⟨R, hIW R (hBound .here)⟩
  obtain ⟨S, hSI, hBody⟩ := PowerlessRelativeFiniteHullSatisfaction.capture_l
    ζ I W τ ν hτ hI₀ hW₀ hW hNonempty hIW hFree h η (fun _ _ => rfl) hBound hMatrix
  obtain ⟨hSU, hSeq, hSat, hClean⟩ :=
    (PowerlessRelativeFiniteHullSatisfaction.body_formula_l η S).mp hBody
  have hSeq' : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val A S :=
    (PowerlessFiniteSequencesBounded.spec_iff_of_coverage_l (hCoding.coverage A hAU)).mp hSeq
  obtain ⟨_he, _ht₁, _ht₂, _ht₃, hN, hT, _hPair, _hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l (hBase := hBase) K hCoding.omega_eq hCoding.static
  have he : ∀ x, ¬SecondOrderQuotient.mem_l hℳ x e.val :=
    (PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp hCoding.static.1.1
  have hNω : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val ω.val N.val := by
    simpa only [hCoding.omega_eq] using hN
  have hTω : map_l (ℳ := RawModel) T.val ω.val ω.val := by
    simpa only [hCoding.omega_eq] using hT
  have hωRaw : SecondOrderOmega.omega_l hℳ ω.val := hCoding.omega_eq.symm ▸ K.omega_spec
  let ηω : Env RawModel [] [.set] := Env.empty.pushFree ω.val
  have hω : omega_l (ℳ := RawModel) ω.val :=
    (omega_formula_l ηω (.fvar .here)).mp
      ((SecondOrderOmegaSyntax.omega_l hℳ ηω (.fvar .here)).mpr hωRaw)
  exact ⟨S, hSI, hSU, hSeq',
    (PowerlessSatisfactionSpecificationBounded.guarded_iff_l hω he hNω hTω hSeq').mp hSat, hClean⟩

#print axioms capture_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullSatCoding
