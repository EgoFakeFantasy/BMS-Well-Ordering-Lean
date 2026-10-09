import BMSConstructibleBridge.PowerlessRelativeClassFunctionSpecifications
import BMSConstructibleBridge.PowerlessRelativeClassBasicClosure
import BMSConstructibleBridge.PowerlessCodedHistoryCoverageSyntax

/-! # 实际 Class 中原局部覆盖包的逐项读入

序数的最小元条款显式限制原良序证书，不用 Δ₀ 冒充完整序数资格。
原旧数字矩阵和轻量历史已是 Δ₀；操作闭包仍量化全部类内候选，先用
传递性把二元并的成员方程读回 raw 再消费原闭包。没有预供元素性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCoverageAbsolute

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

/-- 原良序的最小元证书保持在同一 Class，不能只检查线序。 -/
theorem ordinal_l (α : M)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α.val) :
    SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩₀) α := by
  have hSame {a b : M} (h : SetTheory.Structure.SameMembers
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a.val b.val) :
      SetTheory.Structure.SameMembers
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩₀) a b := fun z => h z.val
  refine ⟨(fun a ha b hb => hα.transitive a.val ha b.val hb), ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact fun a ha => hα.wellOrder.linear.irrefl a.val ha
    · exact fun a ha b hb c hc => hα.wellOrder.linear.trans a.val ha b.val hb c.val hc
    · intro a ha b hb
      exact (hα.wellOrder.linear.compare a.val ha b.val hb).imp hSame id
  · intro S hSub hNonempty
    obtain ⟨z, hz⟩ := hNonempty
    obtain ⟨a, ha, hLeast⟩ := hα.wellOrder.least S.val
      (fun b hb => hSub ⟨b, PowerlessRelativeClassCorrespondence.transitive_l
        hℳ hBase S.property hb⟩ hb) ⟨z.val, hz⟩
    let a₀ : M := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase S.property ha⟩
    exact ⟨a₀, ha, fun b hb => (hLeast b.val hb).imp hSame id⟩

theorem numeric_l
    (ω e t₁ t₂ t₃ t₄ P N V Q : M) :
    PowerlessLegacyNumericSyntax.spec_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ t₄ P N V Q ↔
      PowerlessLegacyNumericSyntax.spec_l (𝒩 := 𝒱)
        ω.val e.val t₁.val t₂.val t₃.val t₄.val P.val N.val V.val Q.val := by
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree Q |>.pushFree V |>.pushFree N |>.pushFree P
      |>.pushFree t₄ |>.pushFree t₃ |>.pushFree t₂ |>.pushFree t₁
      |>.pushFree e |>.pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    PowerlessLegacyNumericSyntax.formula_m
      (.fvar .here)
      (.fvar (.there .here))
      (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
  have hφ : Formula.IsDelta0 StabilityFrame.membershipLevyBound φ :=
    PowerlessLegacyNumericSyntax.delta_l _ _ _ _ _ _ _ _ _ _
  have h := PowerlessRelativeClassBounded.formula_l (hBase := hBase) hφ η
  simpa only [φ, PowerlessLegacyNumericSyntax.formula_l, Term.eval,
    Env.pushFree_here, Env.pushFree_there, PowerlessRelativeClassRelativization.env_l, η] using h

/-- 同一个完整轻量历史，不改变图或原参数。 -/
theorem history_l (B₀ D A U f : M) :
    PowerlessHierarchyLightHistory.holds_l (𝒩 := 𝒩₀) B₀ D A U f ↔
      PowerlessHierarchyLightHistory.holds_l (𝒩 := 𝒱) B₀.val D.val A.val U.val f.val := by
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree f |>.pushFree U |>.pushFree A |>.pushFree D |>.pushFree B₀
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    PowerlessHierarchyLightHistory.formula_m (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
  have h := PowerlessRelativeClassBounded.formula_l (hBase := hBase) (φ := φ)
    (PowerlessHierarchyLightHistory.delta_l _ _ _ _ _) η
  simpa only [φ, PowerlessHierarchyLightHistory.formula_l, Term.eval,
    Env.pushFree_here, Env.pushFree_there, PowerlessRelativeClassRelativization.env_l, η] using h

/-- 对全部类内候选的两项原操作闭包，而非选定操作见证的闭包。 -/
theorem closed_l (U : M)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) U.val) :
    PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒩₀) U := by
  constructor
  · intro a b p ha hb hp
    exact hClosed.1 a.val b.val p.val ha hb
      ((PowerlessRelativeClassFunctionAbsolute.pair_l (hBase := hBase) a b p).mp hp)
  · intro a b c ha hb hc
    apply hClosed.2 a.val b.val c.val ha hb
    intro z
    constructor
    · intro hz
      exact (hc ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase c.property hz⟩).mp hz
    · rintro (hz | hz)
      · exact (hc ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase a.property hz⟩).mpr
          (Or.inl hz)
      · exact (hc ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase b.property hz⟩).mpr
          (Or.inr hz)

#print axioms ordinal_l
#print axioms numeric_l
#print axioms history_l
#print axioms closed_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCoverageAbsolute
