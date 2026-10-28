import BMSConstructibleBridge.PowerlessHierarchyLightHistoryLimitPrefixBound
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryRestriction
import BMSConstructibleBridge.PowerlessWeakSetInduction
import BMSConstructibleBridge.PowerlessRelativeOrdinalCoverage
import BMSConstructibleBridge.SecondOrderOrdinalCases

/-! # 轻量历史的原内部集合归纳预算核

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m 的实际图商。
固定 raw 预算图 Q，纯公式 point(a) 对全部实际预算值、实际层和 raw 完整
轻量历史断言成员界。归纳使用原弱集合论的公式集合归纳，不对模型序数
作宿主良基归纳，也不要求 Q 或待核验历史事先属于 Class。

预算证书全部留在 Prop。它只有真实内部序数域、预算图的源界及总性、
序数输出和统一的原两次 Def 层包：每个目标有严格较早的非零极限母层，
四个固定参数及当前阶段属于该母层，全部前驱预算层对象也属于该母层。
证书不含 hCover、历史 Class 身份或历史见证选择。实际限制图、预算总性、
原层存在性及归纳假设共同生成前缀覆盖；极限切片随后取得精确成员界。

本文件只给条件式预算归纳与 Class 身份。预算图及其证书的实际存在仍须
由后续内部序数编码模块构造，不能把本接口当作长前史存在或 BMS 终局。
原 Derives 的封装也不由这一语义中间核替代；没有新增 Collection 或选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryBudgetInduction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 全 raw 候选的纯模板；预算域外由实际 Q 的源界保证蕴含前件为空。 -/
def point_m {Γ Δ : SortContext ℒ} (B D W Q a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let w (t : Term ℒ Γ Δ .set) := up (up (up t))
    let δ : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let C : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let f : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .imp (PowerlessValueBounded.formula_m (w Q) (w a) δ) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m (w B) δ C) <|
        .imp (PowerlessHierarchyLightHistory.formula_m (w B) (w D) (w a) (w W) f)
          (SecondOrderObjectSyntax.member_m f C)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct RawModel)

def point_l (B D W Q a : type_l hℳ) : Prop :=
  ∀ δ C f, value_l (ℳ := RawModel) Q a δ →
    PowerlessRelativeHierarchySemantics.level_l hℳ B δ C →
      PowerlessHierarchyLightHistory.history_l hℳ B D a W f → mem_l hℳ f C

theorem point_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env RawModel Γ Δ) (B D W Q a : Term ℒ Γ Δ .set) :
    (point_m B D W Q a).satisfies η ↔
      point_l hℳ (B.eval η) (D.eval η) (W.eval η) (Q.eval η) (a.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, PowerlessValueBounded.formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessHierarchyLightHistory.reading_formula_l hℳ, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 所有字段只有预算图、真实序数及实际层关系；没有历史覆盖字段。 -/
structure budget_l (B D W A Q : type_l hℳ) : Prop where
  domain_ordinal : Ordinal A
  source : ∀ a δ, value_l (ℳ := RawModel) Q a δ → mem_l hℳ a A
  total : ∀ a, mem_l hℳ a A → ∃ δ, value_l (ℳ := RawModel) Q a δ
  output_ordinal : ∀ a δ, value_l (ℳ := RawModel) Q a δ → Ordinal δ
  layers : ∀ a δ C, value_l (ℳ := RawModel) Q a δ →
    PowerlessRelativeHierarchySemantics.level_l hℳ B δ C →
      ∃ ξ C₀ C₁, PowerlessRelativeHierarchySemantics.limit_l hℳ ξ ∧
        PowerlessRelativeHierarchySemantics.level_l hℳ B ξ C₀ ∧
        SecondOrderMemberDef.spec_l hℳ C₀ C₁ ∧ SecondOrderMemberDef.spec_l hℳ C₁ C ∧
        mem_l hℳ B C₀ ∧ mem_l hℳ D C₀ ∧ mem_l hℳ W C₀ ∧ mem_l hℳ a C₀ ∧
        ∀ b, mem_l hℳ b a → ∀ θ E, value_l (ℳ := RawModel) Q b θ →
          PowerlessRelativeHierarchySemantics.level_l hℳ B θ E → mem_l hℳ E C₀

/-- 原商序数的三分支读数，不引入宿主递归或额外良基假设。 -/
theorem cases_l {a : type_l hℳ} (ha : Ordinal a) :
    PowerlessRelativeHierarchySemantics.empty_l hℳ a ∨
      (∃ b, PowerlessRelativeHierarchySemantics.successor_l hℳ b a) ∨
      PowerlessRelativeHierarchySemantics.limit_l hℳ a := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  rcases SecondOrderOrdinalCases.cases_l hℳ A ha with hZero | ⟨P, hSucc⟩ | ⟨hNonempty, hNoMax⟩
  · refine Or.inl ?_
    intro x hx
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact hZero X hx
  · refine Or.inr (Or.inl ⟨SecondOrderQuotient.mk_l hℳ P, ?_⟩)
    intro x
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (hSucc X).trans (or_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ X P).symm)
  · refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · obtain ⟨P, hP⟩ := hNonempty
      exact ⟨SecondOrderQuotient.mk_l hℳ P, hP⟩
    · intro x hx
      obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
      obtain ⟨P, hP, hXP⟩ := hNoMax X hx
      exact ⟨SecondOrderQuotient.mk_l hℳ P, hP, hXP⟩

/-- 单个原集合归纳步；全部前缀由实际限制构造，不由证书预设。 -/
theorem step_l {B D W A Q a : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hRead : ∀ X Y : type_l hℳ, value_l (ℳ := RawModel) D X Y ↔
      mem_l hℳ X W ∧ SecondOrderMemberDef.spec_l hℳ X Y)
    (hBudget : budget_l hℳ B D W A Q)
    (hPast : ∀ b, mem_l hℳ b a → point_l hℳ B D W Q b) :
    point_l hℳ B D W Q a := by
  intro δ C f hQ hC hf
  have haA : mem_l hℳ a A := hBudget.source a δ hQ
  have ha : Ordinal a := SetTheory.Structure.IsOrdinal.mem hBudget.domain_ordinal haA
  obtain ⟨ξ, C₀, C₁, hLimit, hC₀, hDef₀₁, hDef₁C, hBC₀, hDC₀, hWC₀, haC₀, hEarlier⟩ :=
    hBudget.layers a δ C hQ hC
  have hTransC₀ := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC₀
  have hTransC₁ := SecondOrderMemberDefProperties.transitive_l hℳ hDef₀₁
    (fun x y hx hy => hTransC₀ x hx y hy)
  have hSub₀₁ := SecondOrderMemberDefProperties.contains_l hℳ hDef₀₁
    (fun x y hx hy => hTransC₀ x hx y hy)
  have hSub₁C := SecondOrderMemberDefProperties.contains_l hℳ hDef₁C hTransC₁
  have hIntoC (x : type_l hℳ) (hx : mem_l hℳ x C₀) : mem_l hℳ x C :=
    hSub₁C x (hSub₀₁ x hx)
  have hPrefix (b : type_l hℳ) (hb : mem_l hℳ b a) :
      ∃ g, PowerlessHierarchyLightHistory.history_l hℳ B D b W g ∧ mem_l hℳ g C₀ ∧
        ∀ x y, SecondOrderFunctionObjects.value_l hℳ g x y ↔
          mem_l hℳ x b ∧ SecondOrderFunctionObjects.value_l hℳ f x y := by
    have hbA : mem_l hℳ b A := hBudget.domain_ordinal.transitive a haA b hb
    have hbOrd : Ordinal b := SetTheory.Structure.IsOrdinal.mem ha hb
    obtain ⟨θ, hQb⟩ := hBudget.total b hbA
    obtain ⟨E, hE⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase
      (hBudget.output_ordinal b θ hQb)
    obtain ⟨g, hg, hValue⟩ := PowerlessHierarchyLightHistoryRestriction.exists_l hℳ hbOrd
      (fun x hx => ha.transitive b hb x hx) hf
    have hgE : mem_l hℳ g E := hPast b hb θ E g hQb hE hg
    exact ⟨g, hg, hTransC₀ E (hEarlier b hb θ E hQb hE) g hgE, hValue⟩
  rcases cases_l hℳ ha with hZero | ⟨b, hSucc⟩ | hLimitA
  · have hfa : f = a := by
      apply SecondOrderQuotient.ext_l hℳ
      intro x
      constructor
      · intro hx
        obtain ⟨i, _y, hi, _hy, _hPair⟩ := hf.1.1 x hx
        exact False.elim (hZero i hi)
      · intro hx
        exact False.elim (hZero x hx)
    exact hIntoC f (hfa.symm ▸ haC₀)
  · have hb : mem_l hℳ b a := (hSucc b).mpr (Or.inr rfl)
    have hbOrd : Ordinal b := SetTheory.Structure.IsOrdinal.mem ha hb
    obtain ⟨g, hg, hgC₀, hValue⟩ := hPrefix b hb
    have hbC₀ : mem_l hℳ b C₀ := hTransC₀ a haC₀ b hb
    exact hIntoC f (PowerlessHierarchyLightHistoryRestriction.successor_member_l hℳ
      hBase hLimit hC₀ hWC₀ hbC₀ hgC₀ hbOrd hSucc hf.1 hg.1 hValue)
  · have hCover (b : type_l hℳ) (hb : mem_l hℳ b a) :
        ∃ g, mem_l hℳ g C₀ ∧ PowerlessHierarchyLightHistory.history_l hℳ B D b W g := by
      obtain ⟨g, hg, hgC₀, _hValue⟩ := hPrefix b hb
      exact ⟨g, hgC₀, hg⟩
    obtain ⟨_H, _hHC₁, _hH, _hUnion, hfC⟩ :=
      PowerlessHierarchyLightHistoryLimitPrefixBound.exists_l hℳ hRead ha hLimitA hf hTransC₀
        hDef₀₁ hDef₁C hBC₀ hDC₀ hWC₀ haC₀ hCover
    exact hfC

/-- 对实际纯 point 模板施行原内部集合归纳，覆盖全部 raw 阶段。 -/
theorem bounded_l (K : source_coding_l hℳ) {B D W A Q : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hRead : ∀ X Y : type_l hℳ, value_l (ℳ := RawModel) D X Y ↔
      mem_l hℳ X W ∧ SecondOrderMemberDef.spec_l hℳ X Y)
    (hBudget : budget_l hℳ B D W A Q) : ∀ a, point_l hℳ B D W Q a := by
  let η : Env RawModel [] [.set, .set, .set, .set] :=
    Env.empty |>.pushFree B |>.pushFree D |>.pushFree W |>.pushFree Q
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    point_m (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  have hFormula (a : type_l hℳ) : φ.satisfies (η.pushFree a) ↔ point_l hℳ B D W Q a :=
    point_formula_l hℳ K (η.pushFree a) _ _ _ _ _
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ) φ η
    (fun a ih => (hFormula a).mpr (step_l hℳ hBase hRead hBudget
      (fun b hb => (hFormula b).mp (ih b hb))))
  exact fun a => (hFormula a).mp (hAll a)

/-- 同一个原 raw 图进入实际预算层；该成员证书给出 Class 身份。 -/
theorem class_l (K : source_coding_l hℳ) {B D W A Q a δ C f : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hRead : ∀ X Y : type_l hℳ, value_l (ℳ := RawModel) D X Y ↔
      mem_l hℳ X W ∧ SecondOrderMemberDef.spec_l hℳ X Y)
    (hBudget : budget_l hℳ B D W A Q)
    (hQ : value_l (ℳ := RawModel) Q a δ)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B δ C)
    (hf : PowerlessHierarchyLightHistory.history_l hℳ B D a W f) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B f :=
  ⟨δ, C, hC, bounded_l hℳ K hBase hRead hBudget a δ C f hQ hC hf⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryBudgetInduction
