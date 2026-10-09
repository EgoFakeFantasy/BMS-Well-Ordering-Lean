import BMSConstructibleBridge.PowerlessFiniteProgramStepSyntax
import BMSConstructibleBridge.PowerlessRelativeClassProgramStoreReading

/-! # 原总状态转移与类内同一程序的双向读数

纯隶属 ℒ，背景原 Z₂。记录中的坐标、当前指令、存储输出均先由实际
raw 方程取得 Class 资格，再限制存在量词。比较无有效后继时的缺省
分支也覆盖所有 raw 候选；不以另一段简化程序替换原程序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramStepReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassRequestFamilyReading (coordinates_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem record_l (i D f s : M) :
    PowerlessFiniteProgramStepSyntax.record_l (𝒩 := 𝒩₀) i D f s ↔
      PowerlessRelativeFiniteProgramStep.record_l i.val D.val f.val s.val := by
  constructor
  · rintro ⟨p, hp, hs⟩
    exact ⟨p.val, (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) D f p).mp hp,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) i p s).mp hs⟩
  · rintro ⟨p, hp, hs⟩
    let p₀ : M := ⟨p, (coordinates_l (hBase := hBase) s hs).2⟩
    exact ⟨p₀, (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) D f p₀).mpr hp,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) i p₀ s).mpr hs⟩

include hBase in
theorem current_class_l (w e : M) {i q : SecondOrderQuotient.type_l hℳ}
    (h : PowerlessRelativeFiniteProgramStep.current_l w.val e.val i q) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B q := by
  rcases h with h | ⟨_, rfl⟩
  · exact (PowerlessRelativeClassValueCoordinates.value_l hBase w h).2
  · exact e.property

theorem current_l (w e i q : M) :
    PowerlessFiniteProgramStepSyntax.current_l (𝒩 := 𝒩₀) w e i q ↔
      PowerlessRelativeFiniteProgramStep.current_l w.val e.val i.val q.val := by
  have hSome : (∃ z, value_l (ℳ := 𝒱) w.val i.val z) ↔
      ∃ z : M, value_l (ℳ := 𝒩₀) w i z := by
    constructor
    · rintro ⟨z, hz⟩
      let z₀ : M := ⟨z, (PowerlessRelativeClassValueCoordinates.value_l hBase w hz).2⟩
      exact ⟨z₀, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) w i z₀).mpr hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z.val, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) w i z).mp hz⟩
  exact or_congr (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) w i q)
    (and_congr (not_congr hSome.symm) ⟨congrArg Subtype.val, Subtype.ext⟩)

theorem valid_l (ω i D f s : M) :
    PowerlessFiniteProgramStepSyntax.valid_l (𝒩 := 𝒩₀) ω i D f s ↔
      PowerlessRelativeFiniteProgramStep.valid_l B ω.val i.val D.val f.val s.val := by
  constructor
  · rintro ⟨hs, hi, hf⟩
    exact ⟨(record_l i D f s).mp hs, hi, i.property, D.property, f.property,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f i D).mp hf⟩
  · rintro ⟨hs, hi, _hiClass, _hDClass, _hfClass, hf⟩
    exact ⟨(record_l i D f s).mpr hs, hi,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f i D).mpr hf⟩

theorem good_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (C ω w e t₀ t₁ t₂ s t : M) :
    PowerlessFiniteProgramStepSyntax.good_l φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C ω w e t₀ t₁ t₂ s t ↔
    PowerlessRelativeFiniteProgramStep.good_l ψ ξ B C.val ω.val w.val e.val
      t₀.val t₁.val t₂.val s.val t.val := by
  constructor
  · rintro ⟨i, D, f, q, S, E, g, hv, hq, hg, ht⟩
    exact ⟨i.val, D.val, f.val, q.val, S.val, E.val, g.val,
      (valid_l ω i D f s).mp hv, (current_l w e i q).mp hq,
      (PowerlessRelativeClassProgramStoreReading.store_l φ ψ η ξ hOperator
        C i D f i t₀ t₁ t₂ q S E g hv.2.2).mp hg, (record_l S E g t).mp ht⟩
  · rintro ⟨i, D, f, q, S, E, g, hv, hq, hg, ht⟩
    let i₀ : M := ⟨i, hv.2.2.1⟩
    let D₀ : M := ⟨D, hv.2.2.2.1⟩
    let f₀ : M := ⟨f, hv.2.2.2.2.1⟩
    let q₀ : M := ⟨q, current_class_l (hBase := hBase) w e hq⟩
    have hStore := hg
    obtain ⟨_y, _hy, hSC, hEC, hgC, _⟩ := hg
    let S₀ : M := ⟨S, hSC⟩
    let E₀ : M := ⟨E, hEC⟩
    let g₀ : M := ⟨g, hgC⟩
    have hv₀ := (valid_l (hBase := hBase) ω i₀ D₀ f₀ s).mpr hv
    exact ⟨i₀, D₀, f₀, q₀, S₀, E₀, g₀, hv₀, (current_l w e i₀ q₀).mpr hq,
      (PowerlessRelativeClassProgramStoreReading.store_l φ ψ η ξ hOperator
        C i₀ D₀ f₀ i₀ t₀ t₁ t₂ q₀ S₀ E₀ g₀ hv₀.2.2).mpr hStore,
      (record_l S₀ E₀ g₀ t).mpr ht⟩

theorem step_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (C ω w e t₀ t₁ t₂ s t : M) :
    PowerlessFiniteProgramStepSyntax.step_l φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C ω w e t₀ t₁ t₂ s t ↔
    PowerlessRelativeFiniteProgramStep.step_l ψ ξ B C.val ω.val w.val e.val
      t₀.val t₁.val t₂.val s.val t.val := by
  have hSome : (∃ z, PowerlessRelativeFiniteProgramStep.good_l ψ ξ B C.val ω.val w.val e.val
      t₀.val t₁.val t₂.val s.val z) ↔
    ∃ z : M, PowerlessFiniteProgramStepSyntax.good_l φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C ω w e t₀ t₁ t₂ s z := by
    constructor
    · rintro ⟨z, hz⟩
      let z₀ : M := ⟨z, PowerlessRelativeFiniteProgramStep.good_class_l (hℳ := hℳ) ψ ξ hBase hz⟩
      exact ⟨z₀, (good_l φ ψ η ξ hOperator C ω w e t₀ t₁ t₂ s z₀).mpr hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z.val, (good_l φ ψ η ξ hOperator C ω w e t₀ t₁ t₂ s z).mp hz⟩
  have hEqual : t = ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ↔ t.val = B :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hDisj := or_congr (good_l φ ψ η ξ hOperator C ω w e t₀ t₁ t₂ s t)
    (and_congr (not_congr hSome.symm) hEqual)
  exact ⟨fun h => ⟨t.property, hDisj.mp h⟩, fun h => hDisj.mpr h.2⟩

#print axioms record_l
#print axioms current_class_l
#print axioms current_l
#print axioms valid_l
#print axioms good_l
#print axioms step_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramStepReading
