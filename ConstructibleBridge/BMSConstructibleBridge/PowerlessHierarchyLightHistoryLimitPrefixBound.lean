import BMSConstructibleBridge.PowerlessHierarchyLightHistoryUnique
import BMSConstructibleBridge.SecondOrderMemberDefBoundedSlice
import BMSConstructibleBridge.SecondOrderSeparationAxiom
import BMSConstructibleBridge.PowerlessRelativeClassStructure

/-! # 轻量历史的极限前缀切片及两次原 Def 界

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m 的实际图商。
给定完整 raw 轻量历史 f:α→W，在非零内部极限 α 上，局部预算归纳已经
把每个严格较早的完整前缀放入同一个具体传递母集 C。以纯 Δ₀ 矩阵
∃β∈α light_history(B,D,β,W,g) 精确切片 C，所得前缀集合 H 属于原 Def(C)。
原内部历史相容性排除候选垃圾，全部 raw 有序对成员读数证明 ∪H=f，
因此原 f 属于 Def²(C)。C 只作分离母集，不作为要求 C∈C 的自由参数。

hCover 是显式增长层预算归纳的局部归纳假设，不是最终长前史存在定理
的新前提。本文件不生成这一预算，不宣称任意长前史已经属于 Class 或 W，
不调用 Collection、外部良基性、可数选择或 Type 层见证抽取。Class 包装
只从 H 属于实际 Class 的 Def 母对象提升身份，不从任意子集推断 Class。
本模块是语义中间成果，不代替原推导核中的最终 Derives 或 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryLimitPrefixBound

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 前缀候选的唯一存在母界是实际内部序数 α；C 不出现在矩阵中。 -/
def body_m {Γ Δ : SortContext ℒ} (B D α W g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists α <|
    PowerlessHierarchyLightHistory.formula_m (up B) (up D) (.bvar .here) (up W) (up g)

theorem body_delta_l {Γ Δ : SortContext ℒ} (B D α W g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m B D α W g) :=
  .bounded_exists α (PowerlessHierarchyLightHistory.delta_l _ _ _ _ _)

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (B D α W g : Term ℒ Γ Δ .set) :
    (body_m B D α W g).satisfies η ↔
      ∃ β, member_l 𝒩 β (α.eval η) ∧ PowerlessHierarchyLightHistory.holds_l
        (B.eval η) (D.eval η) β (W.eval η) (g.eval η) := by
  simp only [body_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessHierarchyLightHistory.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct RawModel)

theorem body_reading_l {Γ Δ : SortContext ℒ} (η : Env RawModel Γ Δ)
    (B D α W g : Term ℒ Γ Δ .set) :
    (body_m B D α W g).satisfies η ↔
      ∃ β, mem_l hℳ β (α.eval η) ∧ PowerlessHierarchyLightHistory.history_l
        hℳ (B.eval η) (D.eval η) β (W.eval η) (g.eval η) := by
  refine (body_formula_l η B D α W g).trans ?_
  exact exists_congr (fun β => and_congr Iff.rfl (PowerlessHierarchyLightHistory.reading_l hℳ))

/-- 局部覆盖与完整图唯一性消去最终全 raw 规格中的母集守卫。 -/
theorem exact_l {B D W α C H : type_l hℳ}
    (hRead : ∀ A Y : type_l hℳ, value_l (ℳ := RawModel) D A Y ↔
      mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A Y)
    (hα : Ordinal α)
    (hH : ∀ g : type_l hℳ, mem_l hℳ g H ↔ mem_l hℳ g C ∧
      ∃ β, mem_l hℳ β α ∧ PowerlessHierarchyLightHistory.history_l hℳ B D β W g)
    (hCover : ∀ β, mem_l hℳ β α → ∃ g, mem_l hℳ g C ∧
      PowerlessHierarchyLightHistory.history_l hℳ B D β W g) :
    ∀ g : type_l hℳ, mem_l hℳ g H ↔
      ∃ β, mem_l hℳ β α ∧ PowerlessHierarchyLightHistory.history_l hℳ B D β W g := by
  intro g
  constructor
  · intro hg
    exact ((hH g).mp hg).2
  · rintro ⟨β, hβ, hg⟩
    obtain ⟨g', hg'C, hg'⟩ := hCover β hβ
    have hβOrd : Ordinal β := SetTheory.Structure.IsOrdinal.mem hα hβ
    have hgg' : g = g' := PowerlessHierarchyLightHistoryUnique.unique_l hℳ hRead hβOrd hg hg'
    exact (hH g).mpr ⟨hgg'.symm ▸ hg'C, β, hβ, hg⟩

/-- 极限序数的全部 raw 图成员正好来自某个严格较早的完整前缀。 -/
theorem union_l {B D W α C f H : type_l hℳ}
    (hRead : ∀ A Y : type_l hℳ, value_l (ℳ := RawModel) D A Y ↔
      mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A Y)
    (hα : Ordinal α) (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ α)
    (hf : PowerlessHierarchyLightHistory.history_l hℳ B D α W f)
    (hH : ∀ g : type_l hℳ, mem_l hℳ g H ↔ mem_l hℳ g C ∧
      ∃ β, mem_l hℳ β α ∧ PowerlessHierarchyLightHistory.history_l hℳ B D β W g)
    (hCover : ∀ β, mem_l hℳ β α → ∃ g, mem_l hℳ g C ∧
      PowerlessHierarchyLightHistory.history_l hℳ B D β W g) :
    ∀ p : type_l hℳ, mem_l hℳ p f ↔ ∃ g, mem_l hℳ g H ∧ mem_l hℳ p g := by
  intro p
  constructor
  · intro hp
    obtain ⟨i, y, hi, _hy, hPair⟩ := hf.1.1 p hp
    obtain ⟨β, hβ, hiβ⟩ := hLimit.2 i hi
    obtain ⟨g, hgC, hg⟩ := hCover β hβ
    have hβOrd : Ordinal β := SetTheory.Structure.IsOrdinal.mem hα hβ
    obtain ⟨z, ⟨_hzW, hValue⟩, _hUnique⟩ := hg.1.2 i hiβ
    have hyz : y = z := PowerlessHierarchyLightHistoryUnique.agreement_l hℳ hRead hα hβOrd
      hf hg i ⟨hi, hiβ⟩ y z ⟨⟨p, hp, hPair⟩, hValue⟩
    subst z
    obtain ⟨q, hq, hPair'⟩ := hValue
    have hqp : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair
    exact ⟨g, (hH g).mpr ⟨hgC, β, hβ, hg⟩, hqp ▸ hq⟩
  · rintro ⟨g, hgH, hpg⟩
    obtain ⟨_hgC, β, hβ, hg⟩ := (hH g).mp hgH
    obtain ⟨i, y, hiβ, _hy, hPair⟩ := hg.1.1 p hpg
    have hi : mem_l hℳ i α := hα.transitive β hβ i hiβ
    have hβOrd : Ordinal β := SetTheory.Structure.IsOrdinal.mem hα hβ
    obtain ⟨z, ⟨_hzW, hValue⟩, _hUnique⟩ := hf.1.2 i hi
    have hzy : z = y := PowerlessHierarchyLightHistoryUnique.agreement_l hℳ hRead hα hβOrd
      hf hg i ⟨hi, hiβ⟩ z y ⟨hValue, ⟨p, hpg, hPair⟩⟩
    subst z
    obtain ⟨q, hq, hPair'⟩ := hValue
    have hqp : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair
    exact hqp ▸ hq

/-- 局部共同母界生成精确前缀集合；两次原 Def 见证保留为实际对象。 -/
theorem exists_l {B D W α C C₁ C₂ f : type_l hℳ}
    (hRead : ∀ A Y : type_l hℳ, value_l (ℳ := RawModel) D A Y ↔
      mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A Y)
    (hα : Ordinal α) (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ α)
    (hf : PowerlessHierarchyLightHistory.history_l hℳ B D α W f)
    (hTransC : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C)
    (hCD : SecondOrderMemberDef.spec_l hℳ C C₁)
    (hDE : SecondOrderMemberDef.spec_l hℳ C₁ C₂)
    (hBC : mem_l hℳ B C) (hDC : mem_l hℳ D C)
    (hWC : mem_l hℳ W C) (hαC : mem_l hℳ α C)
    (hCover : ∀ β, mem_l hℳ β α → ∃ g, mem_l hℳ g C ∧
      PowerlessHierarchyLightHistory.history_l hℳ B D β W g) :
    ∃ H : type_l hℳ, mem_l hℳ H C₁ ∧
      (∀ g : type_l hℳ, mem_l hℳ g H ↔
        ∃ β, mem_l hℳ β α ∧ PowerlessHierarchyLightHistory.history_l hℳ B D β W g) ∧
      (∀ p : type_l hℳ, mem_l hℳ p f ↔ ∃ g, mem_l hℳ g H ∧ mem_l hℳ p g) ∧
      mem_l hℳ f C₂ := by
  let η : Env RawModel [] [.set, .set, .set, .set] :=
    Env.empty |>.pushFree B |>.pushFree D |>.pushFree W |>.pushFree α
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    body_m (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar .here)
  have hFormula (g : type_l hℳ) : φ.satisfies (η.pushFree g) ↔
      ∃ β, mem_l hℳ β α ∧ PowerlessHierarchyLightHistory.history_l hℳ B D β W g :=
    body_reading_l hℳ (η.pushFree g) _ _ _ _ _
  obtain ⟨H, hH⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) C
  have hHRead (g : type_l hℳ) : mem_l hℳ g H ↔ mem_l hℳ g C ∧
      ∃ β, mem_l hℳ β α ∧ PowerlessHierarchyLightHistory.history_l hℳ B D β W g :=
    (hH g).trans (and_congr Iff.rfl (hFormula g))
  have hHC₁ : mem_l hℳ H C₁ := by
    apply SecondOrderMemberDefBoundedSlice.member_l (φ := φ) hℳ hCD hTransC
      (body_delta_l _ _ _ _ _) η
    · intro s v
      cases s
      cases v with
      | here => exact hαC
      | there v => cases v with
        | here => exact hWC
        | there v => cases v with
          | here => exact hDC
          | there v => cases v with
            | here => exact hBC
            | there v => nomatch v
    · exact hH
  have hUnion := union_l hℳ hRead hα hLimit hf hHRead hCover
  have hTransC₁ := SecondOrderMemberDefProperties.transitive_l hℳ hCD
    (fun x y hx hy => hTransC x hx y hy)
  exact ⟨H, hHC₁, exact_l hℳ hRead hα hHRead hCover, hUnion,
    SecondOrderMemberDefBasicClosure.union_l hℳ hDE hHC₁
    (fun x hx y hy => hTransC₁ x y hx hy) hUnion⟩

/-- 若第一个 Def 是实际 Class 对象，成员界给出实际 Class 的前缀族。 -/
theorem class_exists_l {B D W α C C₂ f : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (C₁ : PowerlessRelativeClassStructure.type_l hℳ B)
    (hRead : ∀ A Y : type_l hℳ, value_l (ℳ := RawModel) D A Y ↔
      mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A Y)
    (hα : Ordinal α) (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ α)
    (hf : PowerlessHierarchyLightHistory.history_l hℳ B D α W f)
    (hTransC : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C)
    (hCD : SecondOrderMemberDef.spec_l hℳ C C₁.val)
    (hDE : SecondOrderMemberDef.spec_l hℳ C₁.val C₂)
    (hBC : mem_l hℳ B C) (hDC : mem_l hℳ D C)
    (hWC : mem_l hℳ W C) (hαC : mem_l hℳ α C)
    (hCover : ∀ β, mem_l hℳ β α → ∃ g, mem_l hℳ g C ∧
      PowerlessHierarchyLightHistory.history_l hℳ B D β W g) :
    ∃ H : PowerlessRelativeClassStructure.type_l hℳ B, mem_l hℳ H.val C₁.val ∧
      (∀ g : type_l hℳ, mem_l hℳ g H.val ↔
        ∃ β, mem_l hℳ β α ∧ PowerlessHierarchyLightHistory.history_l hℳ B D β W g) ∧
      (∀ p : type_l hℳ, mem_l hℳ p f ↔ ∃ g, mem_l hℳ g H.val ∧ mem_l hℳ p g) ∧
      mem_l hℳ f C₂ := by
  obtain ⟨H, hHC₁, hH, hUnion, hfC₂⟩ := exists_l hℳ hRead hα hLimit hf hTransC
    hCD hDE hBC hDC hWC hαC hCover
  exact ⟨⟨H, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase C₁.property hHC₁⟩,
    hHC₁, hH, hUnion, hfC₂⟩

#print axioms body_delta_l
#print axioms body_reading_l
#print axioms exact_l
#print axioms union_l
#print axioms exists_l
#print axioms class_exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryLimitPrefixBound
