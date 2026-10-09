import BMSConstructibleBridge.PowerlessRelativeCofinalNormalizedSatisfaction
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionFunction
import BMSConstructibleBridge.PowerlessRelativeLimitFunctionGraphBounded

/-! # 共尾极限层的整张规范 Sat 函数及两次 Def 界

固定同一完整编码包后，所有域 A∈W 的规范 Sat 对象实际属于 W，形成
一张 Class 函数 W→W。其全部 raw 读数由同一个纯 Δ₀ 矩阵表示，整张图
进入 Def(Def(W))；矩阵的 W 参数属于 Def(W)，绝不假定 W∈W。

原共尾条件、实际层关系和两次原 Def 规格明确保留。此处没有假设
Collection，也没有把所得图认作 W 的成员或把前史界、BMS 终局认作已证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalSatisfactionFunction

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev parameters_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set]

private abbrev entry_m (v : Variable parameters_m .set) : Term ℒ [] parameters_m .set := .fvar v

private abbrev lift_m (v : Variable parameters_m .set) : Term ℒ [] (.set :: .set :: parameters_m) .set :=
  .fvar (.there (.there v))

def matrix_m : Formula ℒ [] (.set :: .set :: parameters_m) :=
  PowerlessSatisfactionNormalizedMatrix.formula_m (lift_m .here) (.fvar .here)
    (lift_m (.there .here)) (lift_m (.there (.there .here)))
    (lift_m (.there (.there (.there .here))))
    (lift_m (.there (.there (.there (.there .here)))))
    (lift_m (.there (.there (.there (.there .here)))))
    (lift_m (.there (.there (.there (.there (.there .here))))))
    (lift_m (.there (.there (.there (.there (.there (.there .here)))))))
    (lift_m (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (lift_m (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there .here))

theorem delta_l : Formula.IsDelta0 membershipLevyBound matrix_m :=
  PowerlessSatisfactionNormalizedMatrix.delta_l _ _ _ _ _ _ _ _ _ _ _ _

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β W D E : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => structure_l hℳ B hBase

/-- 逐域同层总性实际装配为函数，并证明整张图的明确两次 Def 成员界。 -/
theorem exists_l (K : source_coding_l hℳ) (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    (hWD : SecondOrderMemberDef.spec_l hℳ W D) (hDE : SecondOrderMemberDef.spec_l hℳ D E)
    (ω : type_l hℳ B) (hωW : mem_l hℳ ω.val W) (hωEq : ω.val = K.omega) :
    ∃ e t₁ t₂ t₃ T N F G : type_l hℳ B,
      PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := ClassModel) ω e t₁ t₂ t₃ T N F ∧
        mem_l hℳ G.val E ∧ map_l (ℳ := RawModel) G.val W W ∧
          ∀ a r : SecondOrderQuotient.type_l hℳ,
            value_l (ℳ := RawModel) G.val a r ↔ mem_l hℳ a W ∧ mem_l hℳ r W ∧
              PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := RawModel)
                ω.val a e.val N.val T.val W W t₁.val t₂.val t₃.val F.val r := by
  obtain ⟨e, t₁, t₂, t₃, T, N, F, heW, ht₁W, ht₂W, ht₃W, hTW, hNW, hFW, hStatic, hTotal⟩ :=
    PowerlessRelativeCofinalNormalizedSatisfaction.exists_l
      (hBase := hBase) K hLimit hW hCofinal ω hωW hωEq
  obtain ⟨he, ht₁, ht₂, ht₃, hN, hT, hPair, hF⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hωEq hStatic
  obtain ⟨V, hV, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  let WC : type_l hℳ B := ⟨W, PowerlessRelativeLevelClosure.class_l hℳ hBase hW⟩
  let ηTail : Env ClassModel [] [.set, .set, .set] :=
    (((Env.empty).pushFree F).pushFree t₃).pushFree t₂
  let η : Env ClassModel [] parameters_m :=
    (((((ηTail.pushFree t₁).pushFree WC).pushFree T).pushFree N).pushFree e).pushFree ω
  let w := entry_m .here
  let z := entry_m (.there .here)
  let n := entry_m (.there (.there .here))
  let t := entry_m (.there (.there (.there .here)))
  let c := entry_m (.there (.there (.there (.there .here))))
  let x := entry_m (.there (.there (.there (.there (.there .here)))))
  let y := entry_m (.there (.there (.there (.there (.there (.there .here))))))
  let d := entry_m (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let f := entry_m (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  have hCoverage (A : type_l hℳ B) (hA : mem_l hℳ A.val W)
      (g : SecondOrderQuotient.type_l hℳ)
      (hg : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := RawModel) K.omega A.val g) :
      mem_l hℳ g W := by
    obtain ⟨L, hL, hMap⟩ := hg
    exact PowerlessRelativeLimitFiniteMaps.subset_member_l hℳ hBase hLimit hW K
      (hωEq ▸ hωW) (fun a ha => hTrans A.val hA a ha) hL hMap
  obtain ⟨G, hG, hRead⟩ := PowerlessRelativeClassSatisfactionFunction.exists_l K
    η w z n t c c x y d f WC hωEq he ht₁ ht₂ ht₃ hN hT hCoverage hPair hV (hF V hV) hTotal
  let ρTail : Env RawModel [] [.set, .set, .set] :=
    (((Env.empty).pushFree F.val).pushFree t₃.val).pushFree t₂.val
  let ρ : Env RawModel [] parameters_m :=
    (((((ρTail.pushFree t₁.val).pushFree W).pushFree T.val).pushFree N.val).pushFree e.val).pushFree ω.val
  have hMatrix (a r : SecondOrderQuotient.type_l hℳ) :
      matrix_m.satisfies ((ρ.pushFree r).pushFree a) ↔
        PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := RawModel)
          ω.val a e.val N.val T.val W W t₁.val t₂.val t₃.val F.val r := by
    simpa only [matrix_m, ρ, ρTail, lift_m, Term.eval, Env.pushFree_here, Env.pushFree_there] using
      PowerlessSatisfactionNormalizedMatrix.formula_l ((ρ.pushFree r).pushFree a)
        (lift_m .here) (.fvar .here) (lift_m (.there .here)) (lift_m (.there (.there .here)))
        (lift_m (.there (.there (.there .here))))
        (lift_m (.there (.there (.there (.there .here)))))
        (lift_m (.there (.there (.there (.there .here)))))
        (lift_m (.there (.there (.there (.there (.there .here))))))
        (lift_m (.there (.there (.there (.there (.there (.there .here)))))))
        (lift_m (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (lift_m (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.fvar (.there .here))
  have hSub := SecondOrderMemberDefProperties.contains_l hℳ hWD
    (fun a b ha hb => hTrans a ha b hb)
  have hWDMember := SecondOrderMemberDefProperties.mother_member_l hℳ hWD
  have hParamsD : ∀ s (v : Variable parameters_m s), mem_l hℳ (ρ.freeVal v) D := by
    intro s v
    cases s
    match v with
    | .here => exact hSub ω.val hωW
    | .there .here => exact hSub e.val heW
    | .there (.there .here) => exact hSub N.val hNW
    | .there (.there (.there .here)) => exact hSub T.val hTW
    | .there (.there (.there (.there .here))) => exact hWDMember
    | .there (.there (.there (.there (.there .here)))) => exact hSub t₁.val ht₁W
    | .there (.there (.there (.there (.there (.there .here))))) => exact hSub t₂.val ht₂W
    | .there (.there (.there (.there (.there (.there (.there .here)))))) => exact hSub t₃.val ht₃W
    | .there (.there (.there (.there (.there (.there (.there (.there .here))))))) => exact hSub F.val hFW
  have hGE := PowerlessRelativeLimitFunctionGraphBounded.member_l hℳ hBase hW hLimit hWD hDE
    delta_l ρ hParamsD hWDMember hWDMember (fun _ h => h) (fun _ h => h) hG
    (fun a r => (hRead a r).trans (and_congr Iff.rfl (and_congr Iff.rfl (hMatrix a r).symm)))
  exact ⟨e, t₁, t₂, t₃, T, N, F, G, hStatic, hGE, hG, hRead⟩

#print axioms delta_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalSatisfactionFunction
