import BMSConstructibleBridge.PowerlessMemberDefImageBounded
import BMSConstructibleBridge.PowerlessMemberDefImageBoundedReading
import BMSConstructibleBridge.PowerlessRelativeClassRawFunction
import BMSConstructibleBridge.PowerlessRelativeCofinalMemberDefClosure

/-! # 共尾极限层的实际原 Def 函数

背景为原 SecondOrderArithmetic.theory_m，矩阵为纯隶属 ℒ 的有界 AST。
给定同一层的实际编码和已验证的矩阵读数，原 Def 的全域唯一性与
共尾层 Def 闭包给固定 W→W 的总性；原 Δ₀ 构图输出实际 Class 函数。
读数覆盖全部原商坐标，不把 Type 选择或逐点见证族当作实际集合图。

exists_for_reading_l 是装配辅助，精确读数前提须由真实编码包消去。
其本身不宣称已完成无前提编码包装配，也不宣称函数图属于 W、已有
长超限前史或最终 BMS 对象推导；最终对象出口由实际装配端提供。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalDefFunction

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β W : SecondOrderQuotient.type_l hℳ}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 实际统一读数是明确辅助前提，不假称编码包已经存在。 -/
theorem exists_for_reading_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    (hKωW : mem_l hℳ K.omega W) (ω e N F G : type_l hℳ B)
    (hReading : ∀ A : SecondOrderQuotient.type_l hℳ, mem_l hℳ A W →
      ∀ H : SecondOrderQuotient.type_l hℳ,
        PowerlessMemberDefImageBounded.holds_l (𝒩 := RawModel)
          ω.val e.val N.val F.val W G.val A H ↔ SecondOrderMemberDef.spec_l hℳ A H) :
    ∃ D : type_l hℳ B, map_l (ℳ := RawModel) D.val W W ∧
      ∀ A H : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := RawModel) D.val A H ↔ mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A H := by
  let WClass : type_l hℳ B := ⟨W, PowerlessRelativeLevelClosure.class_l hℳ hBase hW⟩
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set, .set] :=
    (((((Env.empty.pushFree G).pushFree WClass).pushFree F).pushFree N).pushFree e).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    PowerlessMemberDefImageBounded.formula_m
      (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar .here) (.fvar (.there .here))
  have hφ : Formula.IsDelta0 membershipLevyBound φ :=
    PowerlessMemberDefImageBounded.delta_l _ _ _ _ _ _ _ _
  have hMatrix (A H : SecondOrderQuotient.type_l hℳ) :
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree H).pushFree A) ↔
        PowerlessMemberDefImageBounded.holds_l (𝒩 := RawModel)
          ω.val e.val N.val F.val W G.val A H := by
    simpa only [φ, η, PowerlessRelativeClassRawFunction.env_pushFree_l,
      PowerlessRelativeClassRelativization.env_l, Term.eval, Env.pushFree, Assignment.push] using
      PowerlessMemberDefImageBounded.formula_l
        (((PowerlessRelativeClassRelativization.env_l η).pushFree H).pushFree A)
        (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there (.there (.there (.there .here))))))
        (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (.fvar .here) (.fvar (.there .here))
  have hTotal (A : SecondOrderQuotient.type_l hℳ) (hAW : mem_l hℳ A W) :
      ∃! H : SecondOrderQuotient.type_l hℳ, mem_l hℳ H W ∧
        φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree H).pushFree A) := by
    obtain ⟨H, hDef, _⟩ := SecondOrderMemberDef.exists_l hℳ A
    have hHW := PowerlessRelativeCofinalMemberDefClosure.member_l
      hBase K hLimit hW hCofinal hKωW hAW hDef
    refine ⟨H, ⟨hHW, (hMatrix A H).mpr ((hReading A hAW H).mpr hDef)⟩, ?_⟩
    intro H' hH'
    exact SecondOrderMemberDef.unique_l hℳ
      ((hReading A hAW H').mp ((hMatrix A H').mp hH'.2)) hDef
  obtain ⟨D, hD, hValue⟩ := PowerlessRelativeClassRawFunction.exists_l hφ η WClass WClass hTotal
  refine ⟨D, hD, fun A H => ?_⟩
  constructor
  · intro hDH
    obtain ⟨hAW, _hHW, hCheck⟩ := (hValue A H).mp hDH
    exact ⟨hAW, (hReading A hAW H).mp ((hMatrix A H).mp hCheck)⟩
  · rintro ⟨hAW, hDef⟩
    exact (hValue A H).mpr
      ⟨hAW, PowerlessRelativeCofinalMemberDefClosure.member_l
        hBase K hLimit hW hCofinal hKωW hAW hDef,
        (hMatrix A H).mpr ((hReading A hAW H).mpr hDef)⟩

/-- 全部编码与精确读数在证明内取得，没有最终 checker 读数前提。 -/
theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    (hKωW : mem_l hℳ K.omega W) :
    ∃ D : type_l hℳ B, map_l (ℳ := RawModel) D.val W W ∧
      ∀ A H : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := RawModel) D.val A H ↔ mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A H := by
  let ω : type_l hℳ B := ⟨K.omega, ⟨β, W, hW, hKωW⟩⟩
  obtain ⟨e, t₁, t₂, t₃, Pair, N, Valid, Translation, G, C, hCoding⟩ :=
    PowerlessRelativeCofinalDefCoding.exists_l hBase K hLimit hW hCofinal ω hKωW rfl
  apply exists_for_reading_l hBase K hLimit hW hCofinal hKωW ω e N Translation G
  intro A hAW H
  exact PowerlessMemberDefImageBoundedReading.checkeriff_l
    hBase K hLimit hW hKωW hCoding hAW

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalDefFunction
