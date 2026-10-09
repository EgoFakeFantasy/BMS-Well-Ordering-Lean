import BMSConstructibleBridge.PowerlessRelativeClassInjectionEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassValueCoordinates
import BMSConstructibleBridge.PowerlessRelativeLimitFunctionGraphBounded

/-! # 已有层内计数注射的有限两次 Def 枚举界

对象语言是纯隶属 ℒ，背景为原二阶算术模型的实际商结构。给定实际 Class
注射 R:X→ω 和默认值 d∈X，且 ω、X、R、d 均已属于同一个非零极限层 C，
原带默认值逆枚举构造给出实际 Class 满射 U:ω→X。其矩阵参数只来自 C，
完整 raw 坐标读数和原两次 Def 图界证明 U∈E=Def(Def(C))。

计数注射的层内界 R∈C 是真实输入，不能由 R∈Class 自动获得。本文件
不假定 HC 等于某个截断层，不给长前史共同界、凝聚、完整 Collection 或
最终 BMS 推导。K 保留主线编码接口；反转注射本身不需新增数码读数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitInjectionEnumeration

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 所有输入对象的实际层界均保留；输出同时给出全部 raw 坐标的完整读数。 -/
theorem exists_l (_K : source_coding_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {γ C D E : SecondOrderQuotient.type_l hℳ}
    (hLimit : limit_l hℳ γ) (hC : level_l hℳ B γ C)
    (hCD : SecondOrderMemberDef.spec_l hℳ C D) (hDE : SecondOrderMemberDef.spec_l hℳ D E)
    {ω X R d : type_l hℳ B}
    (hωC : mem_l hℳ ω.val C) (hXC : mem_l hℳ X.val C)
    (hRC : mem_l hℳ R.val C) (hdC : mem_l hℳ d.val C)
    (hR : map_l (ℳ := RawModel) R.val X.val ω.val)
    (hInjective : ∀ x y i : SecondOrderQuotient.type_l hℳ,
      value_l (ℳ := RawModel) R.val x i → value_l (ℳ := RawModel) R.val y i → x = y)
    (hd : mem_l hℳ d.val X.val) :
    ∃ U : type_l hℳ B, mem_l hℳ U.val E ∧
      map_l (ℳ := RawModel) U.val ω.val X.val ∧
      (∀ y, mem_l hℳ y X.val → ∃ i,
        mem_l hℳ i ω.val ∧ value_l (ℳ := RawModel) U.val i y) ∧
      ∀ i y : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := RawModel) U.val i y ↔ mem_l hℳ i ω.val ∧ mem_l hℳ y X.val ∧
          PowerlessRelativeClassInjectionEnumeration.holds_l (𝒩 := RawModel)
            R.val X.val d.val i y := by
  have hRClass := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) R X ω).mpr hR
  have hInjectiveClass : ∀ x y i : type_l hℳ B,
      value_l (ℳ := structure_l hℳ B hBase) R x i →
      value_l (ℳ := structure_l hℳ B hBase) R y i → x = y := by
    intro x y i hxi hyi
    exact Subtype.ext (hInjective x.val y.val i.val
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R x i).mp hxi)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R y i).mp hyi))
  obtain ⟨U, hU, hOnto, hRead⟩ := PowerlessRelativeClassInjectionEnumeration.exists_l
    (hBase := hBase) hRClass hInjectiveClass hd
  have hURaw : map_l (ℳ := RawModel) U.val ω.val X.val := by
    simpa only [ThirdOrderSemantics.map_l, ThirdOrderSemantics.member_l,
      ThirdOrderSemantics.value_l, ThirdOrderSemantics.ordered_l, ThirdOrderSemantics.pair_l,
      SecondOrderQuotient.structure_l, SecondOrderFunctionObjects.map_l,
      SecondOrderFunctionObjects.value_l, SecondOrderPairObjects.ordered_l,
      SecondOrderPairObjects.pair_l]
      using (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) U ω X).mp hU
  -- 默认分支量化的对象受 X 守卫；Class 传递性取回全部 raw 原像。
  have hHolds (i y : type_l hℳ B) :
      PowerlessRelativeClassInjectionEnumeration.holds_l (𝒩 := structure_l hℳ B hBase) R X d i y ↔
        PowerlessRelativeClassInjectionEnumeration.holds_l (𝒩 := RawModel)
          R.val X.val d.val i.val y.val := by
    unfold PowerlessRelativeClassInjectionEnumeration.holds_l
    refine or_congr (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R y i)
      (and_congr ?_ ?_)
    · constructor
      · intro h g hg hgi
        let g' : type_l hℳ B := ⟨g,
          PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hg⟩
        exact h g' hg ((PowerlessRelativeClassFunctionAbsolute.value_l
          (hBase := hBase) R g' i).mpr hgi)
      · intro h g hg hgi
        exact h g.val hg ((PowerlessRelativeClassFunctionAbsolute.value_l
          (hBase := hBase) R g i).mp hgi)
    · exact ⟨congrArg Subtype.val, Subtype.ext⟩
  have hClassRead (i y : type_l hℳ B) :
      value_l (ℳ := RawModel) U.val i.val y.val ↔
        mem_l hℳ i.val ω.val ∧ mem_l hℳ y.val X.val ∧
          PowerlessRelativeClassInjectionEnumeration.holds_l (𝒩 := RawModel)
            R.val X.val d.val i.val y.val :=
    (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) U i y).symm.trans
      ((hRead i y).trans (and_congr Iff.rfl (and_congr Iff.rfl (hHolds i y))))
  have hRawRead (i y : SecondOrderQuotient.type_l hℳ) :
      value_l (ℳ := RawModel) U.val i y ↔ mem_l hℳ i ω.val ∧ mem_l hℳ y X.val ∧
        PowerlessRelativeClassInjectionEnumeration.holds_l (𝒩 := RawModel) R.val X.val d.val i y := by
    constructor
    · intro hValue
      obtain ⟨hi, hy⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase U hValue
      exact (hClassRead ⟨i, hi⟩ ⟨y, hy⟩).mp hValue
    · rintro ⟨hi, hy, hValue⟩
      let i' : type_l hℳ B := ⟨i,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hi⟩
      let y' : type_l hℳ B := ⟨y,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hy⟩
      exact (hClassRead i' y').mpr ⟨hi, hy, hValue⟩
  -- 三个旧参数依次为 R、X、d；前面两个新自由槽是输入 i 和输出 y。
  let ρ : Env RawModel [] [.set, .set, .set] :=
    ((Env.empty.pushFree d.val).pushFree X.val).pushFree R.val
  let r : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let x : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let a : Term ℒ [] [.set, .set, .set, .set, .set] .set :=
    .fvar (.there (.there (.there (.there .here))))
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    PowerlessRelativeClassInjectionEnumeration.formula_m r x a (.fvar .here) (.fvar (.there .here))
  have hφ : Formula.IsDelta0 membershipLevyBound φ :=
    PowerlessRelativeClassInjectionEnumeration.delta_l r x a (.fvar .here) (.fvar (.there .here))
  have hFormula (i y : SecondOrderQuotient.type_l hℳ) :
      φ.satisfies ((ρ.pushFree y).pushFree i) ↔
        PowerlessRelativeClassInjectionEnumeration.holds_l (𝒩 := RawModel) R.val X.val d.val i y := by
    simpa only [φ, ρ, r, x, a, Term.eval, Env.pushFree_here, Env.pushFree_there] using
      PowerlessRelativeClassInjectionEnumeration.formula_l ((ρ.pushFree y).pushFree i)
        r x a (.fvar .here) (.fvar (.there .here))
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hSub := SecondOrderMemberDefProperties.contains_l hℳ hCD
    (fun x y hx hy => hTrans x hx y hy)
  have hParamsD : ∀ (s : SetTheory.SetSort)
      (v : Variable [SetTheory.SetSort.set, SetTheory.SetSort.set, SetTheory.SetSort.set] s),
      mem_l hℳ (ρ.freeVal v) D := by
    intro s v
    cases s
    match v with
    | .here => exact hSub R.val hRC
    | .there .here => exact hSub X.val hXC
    | .there (.there .here) => exact hSub d.val hdC
  have hUE := PowerlessRelativeLimitFunctionGraphBounded.member_l hℳ (G := U.val)
    hBase hC hLimit hCD hDE
    hφ ρ hParamsD (hSub ω.val hωC) (hSub X.val hXC)
    (fun i hi => hTrans ω.val hωC i hi) (fun y hy => hTrans X.val hXC y hy) hURaw
    (fun i y => (hRawRead i y).trans
      (and_congr Iff.rfl (and_congr Iff.rfl (hFormula i y).symm)))
  refine ⟨U, hUE, hURaw, ?_, hRawRead⟩
  intro y hy
  let y' : type_l hℳ B := ⟨y,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hy⟩
  obtain ⟨i, hi, hiy⟩ := hOnto y' hy
  exact ⟨i.val, hi, (PowerlessRelativeClassFunctionAbsolute.value_l
    (hBase := hBase) U i y').mp hiy⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitInjectionEnumeration
