import BMSConstructibleBridge.SecondOrderCanonicalLevel
import BMSConstructibleBridge.SecondOrderCanonicalLevelDerives
import BMSConstructibleBridge.SecondOrderOrdinalComparison
import BMSConstructibleBridge.PowerlessRelativeLevelClosure

/-! # 全局规范比较与任意可定义子类的唯一最小元

对象语言为纯隶属 ℒ，背景为原 Z₂ 的图商弱集合论。全局关系由原规范
阶段证书定义，最小元通过 raw 分离及一个实际阶段的环境良序取得。
不假定 Class 完整分离，不构造 Type 选择函数或假定类值域是集合。
本模块给 AST 读数及语义辅助；对象句的正式推导出口另行装配。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeGlobalCanonicalOrder

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderCanonicalLevelSyntax (level_l)
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))

def edge_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let a := .bvar (.there (.there .here))
    let X := .bvar (.there .here)
    let P := .bvar .here
    .conj (SecondOrderCanonicalLevelSyntax.level_m (up₃ ω) (up₃ e) (up₃ t₁) (up₃ t₂)
      (up₃ t₃) (up₃ Pair) (up₃ Valid) (up₃ B) (up₃ P₀) a X P) <|
      .conj (member_m (up₃ x) X) <| .conj (member_m (up₃ y) X) (value_m P (up₃ x) (up₃ y))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => type_l hℳ

def edge_l (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Raw) : Prop :=
  ∃ a X P, level_l ω e t₁ t₂ t₃ Pair Valid B P₀ a X P ∧
    mem_l hℳ x X ∧ mem_l hℳ y X ∧ value_l (ℳ := 𝒱) P x y

theorem edge_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Term ℒ Γ Δ .set) :
    (edge_m ω e t₁ t₂ t₃ Pair Valid B P₀ x y).satisfies η ↔
      edge_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) (x.eval η) (y.eval η) := by
  simp only [edge_m, edge_l, Formula.satisfies, SecondOrderCanonicalLevelSyntax.level_formula_l K,
    value_formula_l, member_m, Arguments.eval, up₃, up, Term.eval_weakenBound, Term.eval]
  rfl

private abbrev zero_l (K : source_coding_l hℳ) :=
  (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

variable (K : source_coding_l hℳ)
  {t₁ t₂ t₃ Pair Valid B P₀ : SecondOrderQuotient.type_l hℳ}
  (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)

local notation "Edge" => edge_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀

include hCoding

theorem restrict_l {a X P x y : Raw}
    (hP : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P)
    (hx : mem_l hℳ x X) (hy : mem_l hℳ y X) :
    Edge x y ↔ value_l (ℳ := 𝒱) P x y := by
  constructor
  · rintro ⟨b, Y, Q, hQ, hxY, hyY, hxy⟩
    have ha := PowerlessRelativeLevelClosure.ordinal_l hℳ (SecondOrderCanonicalLevel.hierarchy_l hP)
    have hb := PowerlessRelativeLevelClosure.ordinal_l hℳ (SecondOrderCanonicalLevel.hierarchy_l hQ)
    rcases SecondOrderOrdinalComparison.compare_l hℳ ha hb with hab | hab | hba
    · subst b
      have hEq := (SecondOrderCanonicalLevel.unique_l K hCoding hP hQ).2
      exact hEq.symm ▸ hxy
    · exact ((SecondOrderCanonicalLevel.extension_l K hCoding hab hP hQ).2.1 x y hx hy).mp hxy
    · exact ((SecondOrderCanonicalLevel.extension_l K hCoding hba hQ hP).2.1 x y hxY hyY).mpr hxy
  · intro hxy
    exact ⟨a, X, P, hP, hx, hy, hxy⟩

theorem initial_l {a X P x y : Raw}
    (hP : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P)
    (hx : mem_l hℳ x X) (hyx : Edge y x) : mem_l hℳ y X := by
  obtain ⟨b, Y, Q, hQ, hyY, _hxY, hyx⟩ := hyx
  have ha := PowerlessRelativeLevelClosure.ordinal_l hℳ (SecondOrderCanonicalLevel.hierarchy_l hP)
  have hb := PowerlessRelativeLevelClosure.ordinal_l hℳ (SecondOrderCanonicalLevel.hierarchy_l hQ)
  rcases SecondOrderOrdinalComparison.compare_l hℳ ha hb with hab | hab | hba
  · subst b
    have hEq := (SecondOrderCanonicalLevel.unique_l K hCoding hP hQ).1
    exact hEq.symm ▸ hyY
  · exact (SecondOrderCanonicalLevel.extension_l K hCoding hab hP hQ).2.2 x y hx hyY hyx
  · exact (SecondOrderCanonicalLevel.extension_l K hCoding hba hQ hP).1 y hyY

theorem trichotomy_l (hSeed : SecondOrderCanonicalLevelDerives.guard_l B P₀)
    {x y : Raw} (hx : PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (hy : PowerlessRelativeClassCorrespondence.member_l hℳ B y) :
    Edge x y ∨ x = y ∨ Edge y x := by
  obtain ⟨a, X, hX, hxX⟩ := hx
  obtain ⟨b, Y, hY, hyY⟩ := hy
  obtain ⟨P, hP, _⟩ := SecondOrderCanonicalLevel.exists_unique_l K hCoding
    hSeed.1 (fun x hx y hy => hSeed.2.1 x y hx hy) hSeed.2.2.1 hSeed.2.2.2 hX
  obtain ⟨Q, hQ, _⟩ := SecondOrderCanonicalLevel.exists_unique_l K hCoding
    hSeed.1 (fun x hx y hy => hSeed.2.1 x y hx hy) hSeed.2.2.1 hSeed.2.2.2 hY
  have compare {c Z R : Raw}
      (hR : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ c Z R)
      (hxZ : mem_l hℳ x Z) (hyZ : mem_l hℳ y Z) : Edge x y ∨ x = y ∨ Edge y x := by
    rcases (SecondOrderCanonicalLevel.order_l hR).2.2.1 x y ⟨hxZ, hyZ⟩ with h | h | h
    · exact Or.inl ⟨c, Z, R, hR, hxZ, hyZ, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨c, Z, R, hR, hyZ, hxZ, h⟩)
  have ha := PowerlessRelativeLevelClosure.ordinal_l hℳ hX
  have hb := PowerlessRelativeLevelClosure.ordinal_l hℳ hY
  rcases SecondOrderOrdinalComparison.compare_l hℳ ha hb with hab | hab | hba
  · subst b
    have hEq := (SecondOrderCanonicalLevel.unique_l K hCoding hP hQ).1
    exact compare hP hxX (hEq.symm ▸ hyY)
  · exact compare hQ ((SecondOrderCanonicalLevel.extension_l K hCoding hab hP hQ).1 x hxX) hyY
  · exact compare hP hxX ((SecondOrderCanonicalLevel.extension_l K hCoding hba hQ hP).1 y hyY)

/-- 原矩阵可任意复杂；分离发生在原 raw 弱背景，而非尚未验证的 Class 理论中。 -/
theorem least_l (hSeed : SecondOrderCanonicalLevelDerives.guard_l B P₀)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 [] Δ)
    (hSome : ∃ y : Raw, PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
      φ.satisfies (η.pushFree y)) :
    ∃! y : Raw, PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
      φ.satisfies (η.pushFree y) ∧
      ∀ z : Raw, PowerlessRelativeClassCorrespondence.member_l hℳ B z →
        φ.satisfies (η.pushFree z) → ¬Edge z y := by
  obtain ⟨y₀, ⟨a, X, hX, hy₀X⟩, hy₀⟩ := hSome
  obtain ⟨P, hP, _⟩ := SecondOrderCanonicalLevel.exists_unique_l K hCoding
    hSeed.1 (fun x hx y hy => hSeed.2.1 x y hx hy) hSeed.2.2.1 hSeed.2.2.2 hX
  obtain ⟨U, hU⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) X
  obtain ⟨y, hyU, hMin⟩ := (SecondOrderCanonicalLevel.order_l hP).2.2.2 U
    ⟨fun z hz => ((hU z).mp hz).1, y₀, (hU y₀).mpr ⟨hy₀X, hy₀⟩⟩
  obtain ⟨hyX, hyφ⟩ := (hU y).mp hyU
  have hyClass : PowerlessRelativeClassCorrespondence.member_l hℳ B y := ⟨a, X, hX, hyX⟩
  have hyMin : ∀ z : Raw, PowerlessRelativeClassCorrespondence.member_l hℳ B z →
      φ.satisfies (η.pushFree z) → ¬Edge z y := by
    intro z _hzClass hzφ hzy
    have hzX := initial_l K hCoding hP hyX hzy
    exact hMin z ((hU z).mpr ⟨hzX, hzφ⟩) ((restrict_l K hCoding hP hzX hyX).mp hzy)
  refine ⟨y, ⟨hyClass, hyφ, hyMin⟩, ?_⟩
  intro z hz
  rcases trichotomy_l K hCoding hSeed hyClass hz.1 with hyz | hyz | hzy
  · exact False.elim (hz.2.2 y hyClass hyφ hyz)
  · exact hyz.symm
  · exact False.elim (hyMin z hz.1 hz.2.1 hzy)

#print axioms edge_formula_l
#print axioms restrict_l
#print axioms initial_l
#print axioms trichotomy_l
#print axioms least_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeGlobalCanonicalOrder
