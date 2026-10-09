import BMSConstructibleBridge.PowerlessFiniteEvaluationRelationEquations

/-! # 集合求值图的类内语义传输

类内关系图的坐标闭包给出原子及全域赋值更新的双向绝对性。
量词分支额外使用原商全有限赋值规格，把任意更新见证送回类；
据此把原商四分支方程传给实际相对类，不假定类满足完整源理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEvaluationAbsolute

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem equal_l (f i j : type_l hℳ B) :
    PowerlessEvaluationClause.equal_l (ℳ := structure_l hℳ B hBase) f i j ↔
      PowerlessEvaluationClause.equal_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val i.val j.val := by
  constructor
  · rintro ⟨a, hi, hj⟩
    exact ⟨a.val, (PowerlessRelativeClassFunctionAbsolute.value_l f i a).mp hi,
      (PowerlessRelativeClassFunctionAbsolute.value_l f j a).mp hj⟩
  · rintro ⟨a, hi, hj⟩
    let a' : type_l hℳ B := ⟨a, (PowerlessRelativeClassValueCoordinates.value_l hBase f hi).2⟩
    exact ⟨a', (PowerlessRelativeClassFunctionAbsolute.value_l f i a').mpr hi,
      (PowerlessRelativeClassFunctionAbsolute.value_l f j a').mpr hj⟩

theorem member_l (f i j : type_l hℳ B) :
    PowerlessEvaluationClause.member_l (ℳ := structure_l hℳ B hBase) f i j ↔
      PowerlessEvaluationClause.member_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val i.val j.val := by
  constructor
  · rintro ⟨a, b, hi, hj, hab⟩
    exact ⟨a.val, b.val, (PowerlessRelativeClassFunctionAbsolute.value_l f i a).mp hi,
      (PowerlessRelativeClassFunctionAbsolute.value_l f j b).mp hj, hab⟩
  · rintro ⟨a, b, hi, hj, hab⟩
    let a' : type_l hℳ B := ⟨a, (PowerlessRelativeClassValueCoordinates.value_l hBase f hi).2⟩
    let b' : type_l hℳ B := ⟨b, (PowerlessRelativeClassValueCoordinates.value_l hBase f hj).2⟩
    exact ⟨a', b', (PowerlessRelativeClassFunctionAbsolute.value_l f i a').mpr hi,
      (PowerlessRelativeClassFunctionAbsolute.value_l f j b').mpr hj, hab⟩

theorem update_l (f i a g : type_l hℳ B) :
    PowerlessAssignmentUpdate.update_l (ℳ := structure_l hℳ B hBase) f i a g ↔
      PowerlessAssignmentUpdate.update_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val i.val a.val g.val := by
  constructor
  · intro h x y
    constructor
    · intro hValue
      obtain ⟨hx, hy⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase g hValue
      rcases (h ⟨x, hx⟩ ⟨y, hy⟩).mp
          ((PowerlessRelativeClassFunctionAbsolute.value_l g ⟨x, hx⟩ ⟨y, hy⟩).mpr hValue) with hNew | hOld
      · exact Or.inl ⟨congrArg Subtype.val hNew.1, congrArg Subtype.val hNew.2⟩
      · exact Or.inr ⟨fun he => hOld.1 (Subtype.ext he),
          (PowerlessRelativeClassFunctionAbsolute.value_l f ⟨x, hx⟩ ⟨y, hy⟩).mp hOld.2⟩
    · rintro (⟨rfl, rfl⟩ | ⟨hi, hValue⟩)
      · exact (PowerlessRelativeClassFunctionAbsolute.value_l g i a).mp
          ((h i a).mpr (Or.inl ⟨rfl, rfl⟩))
      · obtain ⟨hx, hy⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase f hValue
        exact (PowerlessRelativeClassFunctionAbsolute.value_l g ⟨x, hx⟩ ⟨y, hy⟩).mp
          ((h ⟨x, hx⟩ ⟨y, hy⟩).mpr (Or.inr ⟨fun he => hi (congrArg Subtype.val he),
            (PowerlessRelativeClassFunctionAbsolute.value_l f ⟨x, hx⟩ ⟨y, hy⟩).mpr hValue⟩))
  · intro h x y
    constructor
    · intro hValue
      rcases (h x.val y.val).mp ((PowerlessRelativeClassFunctionAbsolute.value_l g x y).mp hValue) with hNew | hOld
      · exact Or.inl ⟨Subtype.ext hNew.1, Subtype.ext hNew.2⟩
      · exact Or.inr ⟨fun he => hOld.1 (congrArg Subtype.val he),
          (PowerlessRelativeClassFunctionAbsolute.value_l f x y).mpr hOld.2⟩
    · intro hValue
      apply (PowerlessRelativeClassFunctionAbsolute.value_l g x y).mpr
      apply (h x.val y.val).mpr
      rcases hValue with hNew | hOld
      · exact Or.inl ⟨congrArg Subtype.val hNew.1, congrArg Subtype.val hNew.2⟩
      · exact Or.inr ⟨fun he => hOld.1 (Subtype.ext he),
          (PowerlessRelativeClassFunctionAbsolute.value_l f x y).mp hOld.2⟩

theorem exists_l (ω A S G f i b : type_l hℳ B)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val A.val S.val) :
    PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := structure_l hℳ B hBase) ω A G f i b ↔
      PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val A.val G.val f.val i.val b.val := by
  constructor
  · rintro ⟨m, hm, hf, hi, a, ha, g, hg, hUpdate, hValue⟩
    exact ⟨m.val, hm, (PowerlessRelativeClassFunctionAbsolute.map_l f m A).mp hf, hi,
      a.val, ha, g.val, (PowerlessRelativeClassFunctionAbsolute.map_l g m A).mp hg,
      (update_l f i a g).mp hUpdate, (PowerlessRelativeClassFunctionAbsolute.value_l G b g).mp hValue⟩
  · rintro ⟨m, hm, hf, hi, a, ha, g, hg, hUpdate, hValue⟩
    let m' : type_l hℳ B := ⟨m, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hm⟩
    let a' : type_l hℳ B := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property ha⟩
    let g' : type_l hℳ B := ⟨g, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase S.property
      ((hS g).mpr ⟨m, hm, hg⟩)⟩
    exact ⟨m', hm, (PowerlessRelativeClassFunctionAbsolute.map_l f m' A).mpr hf, hi,
      a', ha, g', (PowerlessRelativeClassFunctionAbsolute.map_l g' m' A).mpr hg,
      (update_l f i a' g').mpr hUpdate, (PowerlessRelativeClassFunctionAbsolute.value_l G b g').mpr hValue⟩

theorem equations_l (ω e T A S t₁ t₂ t₃ G : type_l hℳ B)
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val A.val S.val)
    (hEquation : PowerlessFiniteEvaluationRelationEquations.equations_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      ω.val e.val T.val A.val S.val t₁.val t₂.val t₃.val G.val) :
    PowerlessFiniteEvaluationRelationEquations.equations_l (𝒩 := structure_l hℳ B hBase) ω e T A S t₁ t₂ t₃ G := by
  intro n hn f a b
  have hFour := hEquation n.val hn f.val a.val b.val
  have hValue := PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G n f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact hValue.trans ((hFour.1 (PowerlessRelativeClassConstructorBounds.constructor_to_ambient_l hω h)).trans
      (and_congr Iff.rfl (member_l (hBase := hBase) f a b).symm))
  · intro h
    exact hValue.trans ((hFour.2.1 (PowerlessRelativeClassConstructorBounds.constructor_to_ambient_l hω h)).trans
      (and_congr Iff.rfl (equal_l (hBase := hBase) f a b).symm))
  · intro h
    exact hValue.trans ((hFour.2.2.1 (PowerlessRelativeClassConstructorBounds.constructor_to_ambient_l hω h)).trans
      (and_congr Iff.rfl (not_congr (and_congr
        (PowerlessRelativeClassFunctionAbsolute.value_l G a f).symm
        (PowerlessRelativeClassFunctionAbsolute.value_l G b f).symm))))
  · intro h
    exact hValue.trans ((hFour.2.2.2 (PowerlessRelativeClassConstructorBounds.constructor_to_ambient_l hω h)).trans
      (and_congr Iff.rfl (exists_l ω A S G f a b hS).symm))

#print axioms update_l
#print axioms exists_l
#print axioms equations_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEvaluationAbsolute
