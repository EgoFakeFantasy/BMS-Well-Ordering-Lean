import BMSConstructibleBridge.PowerlessRelativeClassRowFamilyAmbient
import BMSConstructibleBridge.SecondOrderMemberDefBoundedSlice
import BMSConstructibleBridge.PowerlessRelativeLevelClosure

/-! # 实际 Class 行族进入两次原 Def 的有限界

给定同一传递母集 W 中的实际 Class 参数 I、A、Q，每行先由 row_bound_l
进入 D=Def(W)。整个精确行族再以纯 Δ₀ 矩阵 ∃i∈I row_m A Q i Z 在 D
上定义，进入 E=Def(D)。不要求各行原已属于 W，也不使用一般 Collection。

核心 member_l 只需 W 传递；指定实际层的 exists_l 从既有层传递性取得
这一条件，因此不额外保留无用的极限假设。两步原 Def 见证都显式保留。
原 Boundedslice 接口内部构造切片并用全部 raw 外延性识别给定 Y，不由
任意子集推断 Class。所有指标、行对象和行元素都保留全部 raw 读数。

这里只给明确的有限后继成员界和实际 Class 见证，不构造共同历史、枚举
族或最终对象 Derives，也不把这一语义辅助模块称为 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitRowFamilyBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 只有实际 I 作存在母界；行的两个方向由原 row_m 保留。 -/
def body_m {Γ Δ : SortContext ℒ} (I A Q Z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists I <|
    PowerlessRelativeClassRowFamily.row_m (up A) (up Q) (.bvar .here) (up Z)

theorem body_delta_l {Γ Δ : SortContext ℒ} (I A Q Z : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m I A Q Z) :=
  .bounded_exists I (PowerlessRelativeClassRowFamily.row_delta_l _ _ _ _)

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (I A Q Z : Term ℒ Γ Δ .set) :
    (body_m I A Q Z).satisfies η ↔
      ∃ i, member_l 𝒩 i (I.eval η) ∧ PowerlessRelativeClassRowFamily.row_l
        (ℳ₀ := 𝒩) (A.eval η) (Q.eval η) i (Z.eval η) := by
  simp only [body_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessRelativeClassRowFamily.row_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

include hBase in
/-- 任意具有全 raw 精确行规格的 Y 都进入第二次 Def；不先假设 Y 是 Class。 -/
theorem member_l {W D E Y : SecondOrderQuotient.type_l hℳ} {I A Q : type_l hℳ B}
    (hTransW : ∀ x, mem_l hℳ x W → ∀ y, mem_l hℳ y x → mem_l hℳ y W)
    (hCD : SecondOrderMemberDef.spec_l hℳ W D) (hDE : SecondOrderMemberDef.spec_l hℳ D E)
    (hIW : mem_l hℳ I.val W) (hAW : mem_l hℳ A.val W) (hQW : mem_l hℳ Q.val W)
    (hY : ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z Y ↔
      ∃ i : SecondOrderQuotient.type_l hℳ, mem_l hℳ i I.val ∧
        PowerlessRelativeClassRowFamily.row_l (ℳ₀ := RawModel) A.val Q.val i Z) :
    mem_l hℳ Y E := by
  have hRowsD (Z : SecondOrderQuotient.type_l hℳ)
      (hBody : ∃ i : SecondOrderQuotient.type_l hℳ, mem_l hℳ i I.val ∧
        PowerlessRelativeClassRowFamily.row_l (ℳ₀ := RawModel) A.val Q.val i Z) :
      mem_l hℳ Z D := by
    obtain ⟨i, hi, hRow⟩ := hBody
    let i' : type_l hℳ B := ⟨i,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase I.property hi⟩
    let Z' : type_l hℳ B := ⟨Z,
      PowerlessRelativeClassRowFamilyAmbient.row_class_l (hBase := hBase)
        (A := A) (Q := Q) (i := i') hRow⟩
    have hClassRow :=
      (PowerlessRelativeClassRowFamilyAmbient.row_absolute_l (hBase := hBase) A Q i' Z').mpr hRow
    exact PowerlessRelativeClassRowFamily.row_bound_l hCD hTransW hAW hQW
      (hTransW I.val hIW i hi) hClassRow
  have hSub := SecondOrderMemberDefProperties.contains_l hℳ hCD
    (fun x y hx hy => hTransW x hx y hy)
  have hTransD := SecondOrderMemberDefProperties.transitive_l hℳ hCD
    (fun x y hx hy => hTransW x hx y hy)
  let η : Env RawModel [] [.set, .set, .set] :=
    (((Env.empty).pushFree Q.val).pushFree A.val).pushFree I.val
  let φ : Formula ℒ [] [.set, .set, .set, .set] :=
    body_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar .here)
  have hRead (Z : SecondOrderQuotient.type_l hℳ) : φ.satisfies (η.pushFree Z) ↔
      ∃ i : SecondOrderQuotient.type_l hℳ, mem_l hℳ i I.val ∧
        PowerlessRelativeClassRowFamily.row_l (ℳ₀ := RawModel) A.val Q.val i Z :=
    body_formula_l (η.pushFree Z) _ _ _ _
  apply SecondOrderMemberDefBoundedSlice.member_l (φ := φ) hℳ hDE
    (fun x hx y hy => hTransD x y hx hy) (body_delta_l _ _ _ _) η
  · intro s v
    cases s
    cases v with
    | here => exact hSub I.val hIW
    | there v => cases v with
      | here => exact hSub A.val hAW
      | there v => cases v with
        | here => exact hSub Q.val hQW
        | there v => nomatch v
  · intro Z
    exact (hY Z).trans
      ⟨fun h => ⟨hRowsD Z h, (hRead Z).mpr h⟩, fun h => (hRead Z).mp h.2⟩

/-- 指定真实相对层及两步原 Def 后，实际 Class 行族具有全部 raw 规格和成员界。 -/
theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {γ W D E : SecondOrderQuotient.type_l hℳ}
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B γ W)
    (hCD : SecondOrderMemberDef.spec_l hℳ W D) (hDE : SecondOrderMemberDef.spec_l hℳ D E)
    (I A Q : type_l hℳ B)
    (hIW : mem_l hℳ I.val W) (hAW : mem_l hℳ A.val W) (hQW : mem_l hℳ Q.val W) :
    ∃ Y : type_l hℳ B, mem_l hℳ Y.val E ∧
      ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z Y.val ↔
        ∃ i : SecondOrderQuotient.type_l hℳ, mem_l hℳ i I.val ∧
          PowerlessRelativeClassRowFamily.row_l (ℳ₀ := RawModel) A.val Q.val i Z := by
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassRowFamilyAmbient.exists_l (hBase := hBase) I A Q
  exact ⟨Y, member_l (hBase := hBase) (Y := Y.val)
    (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW) hCD hDE hIW hAW hQW hY, hY⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitRowFamilyBounded
