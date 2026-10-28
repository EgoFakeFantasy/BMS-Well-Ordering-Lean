import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph
import BMSConstructibleBridge.PowerlessHereditaryClassInternals
import BMSConstructibleBridge.PowerlessBMSClassCollapse
import BMSConstructibleBridge.PowerlessValueBounded
import BMSConstructibleBridge.SecondOrderFunctionProperties
import BMSConstructibleBridge.PowerlessRelativeClassNumericGraph

/-! # 类内可数包络的良基成员图表示

将实际类内枚举的成员关系拉回到 ω，关系集合本身由类内 Δ₀ 分离构造。
原 Z₂ 理解再给同一关系的实数图；内部良基性和各根的坍缩值复用已证
类映射工具。枚举允许重复，不作 Type 选择，也不假定完整 Collection。
先得到 ω 上的有序对关系集合，再由实际 Δ₀ 数编码取得类内 ω 子集，
同时保留原模型实数和坍缩根。任意见证族的统一内域编码及完整源公理
仍是最终候选源装配的独立义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryGraphPresentation

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l mk_l)
open PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def edge_m {Γ Δ : SortContext ℒ} (T f a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists T <| membershipLevyBound.boundedExists (up T) <|
    .conj (PowerlessValueBounded.formula_m (up (up f)) (up (up a)) (.bvar (.there .here))) <|
      .conj (PowerlessValueBounded.formula_m (up (up f)) (up (up b)) (.bvar .here))
        (member_m (.bvar (.there .here)) (.bvar .here))

theorem edge_delta_m {Γ Δ : SortContext ℒ} (T f a b : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (edge_m T f a b) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessValueBounded.delta_l _ _ _)
    (.conj (PowerlessValueBounded.delta_l _ _ _) (.rel _ _))))

def edge_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (T f a b : carrier_l ℳ₀) : Prop :=
  ∃ x y, member_l ℳ₀ x T ∧ member_l ℳ₀ y T ∧
    ThirdOrderSemantics.value_l f a x ∧ ThirdOrderSemantics.value_l f b y ∧ member_l ℳ₀ x y

theorem edge_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (T f a b : Term ℒ Γ Δ .set) :
    (edge_m T f a b).satisfies η ↔ edge_l (T.eval η) (f.eval η) (a.eval η) (b.eval η) := by
  simp only [edge_m, edge_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨x, hx, y, hy, hax, hby, hxy⟩ => ⟨x, y, hx, hy, hax, hby, hxy⟩,
    fun ⟨x, y, hx, hy, hax, hby, hxy⟩ => ⟨x, hx, y, hy, hax, hby, hxy⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

include hBase in
/-- 图规格覆盖环境中的全部坐标，类外坐标不偷偷留作垃圾成员。 -/
theorem class_graph_l (ω T f : type_l hℳ B) : ∃ Q : type_l hℳ B,
    ∀ a b : SecondOrderQuotient.type_l hℳ,
      ThirdOrderSemantics.value_l (ℳ := 𝒱) Q.val a b ↔
        mem_l hℳ a ω.val ∧ mem_l hℳ b ω.val ∧ edge_l (ℳ₀ := 𝒱) T.val f.val a b := by
  let φ : Formula ℒ [] [.set, .set, .set, .set] := edge_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒩 [] [.set, .set] := ((Env.empty).pushFree f).pushFree T
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l
    (φ := φ) (edge_delta_m _ _ _ _) η ω ω
  refine ⟨Q, fun a b => (hQ a b).trans ?_⟩
  exact and_congr Iff.rfl (and_congr Iff.rfl (edge_formula_l
    (((PowerlessRelativeClassRelativization.env_l η).pushFree b).pushFree a)
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar .here) (.fvar (.there .here))))

include hBase in
/-- 每个已有遗传对象有类内关系表示及原模型内部良基实数图。

全部根都良基，且指定根准确坍缩为 X；没有固定全局代码代表。
-/
theorem presentation_l (K : source_coding_l hℳ) {X : SecondOrderQuotient.type_l hℳ}
    (hX : PowerlessHereditaryClass.member_l hℳ B X) :
    ∃ Q : type_l hℳ B, ∃ R : SecondOrderModel.set_l ℳ, ∃ r : SecondOrderModel.num_l ℳ,
      ∃ hWf : ∀ n, SecondOrderDomain.wf_l R n,
        (∀ n m, SecondOrderPairing.relation_l R n m ↔
          ThirdOrderSemantics.value_l (ℳ := 𝒱) Q.val
            (numberCode_l K n).val (numberCode_l K m).val) ∧ mk_l hℳ ⟨R, r, hWf r⟩ = X := by
  obtain ⟨T, f, w, hT, hf, hXT, hTrans, hω, hMap, hOnto⟩ := hX
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  rw [hωEq] at hMap hOnto
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  obtain ⟨Q, hQ⟩ := class_graph_l (hBase := hBase) O ⟨T, hT⟩ ⟨f, hf⟩
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessValueBounded.formula_m
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  let η : Env 𝒱 [] [.set] := Env.empty.pushFree f
  have hRead (a y : SecondOrderQuotient.type_l hℳ) :
      φ.satisfies ((η.pushFree a).pushFree y) ↔ ThirdOrderSemantics.value_l (ℳ := 𝒱) f a y :=
    PowerlessValueBounded.formula_l ((η.pushFree a).pushFree y)
      (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  have hTotal n : ∃ y, φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y) := by
    obtain ⟨y, ⟨_, hy⟩, _⟩ := hMap.2 (numberCode_l K n).val (numberCode_l K n).property
    exact ⟨y, (hRead _ y).mpr hy⟩
  have hUnique n y z (hy : φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y))
      (hz : φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree z)) : y = z :=
    SecondOrderFunctionProperties.value_unique_l hℳ hMap ((hRead _ y).mp hy) ((hRead _ z).mp hz)
  obtain ⟨R, hEdge, hWf⟩ := PowerlessBMSClassRelation.exists_l K φ η hTotal hUnique
  have hTrans' n y (hy : φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree y))
      z (hzy : mem_l hℳ z y) : ∃ m,
        φ.satisfies ((η.pushFree (numberCode_l K m).val).pushFree z) := by
    have hyT := (SecondOrderFunctionProperties.value_mem_l hℳ hMap ((hRead _ y).mp hy)).2
    obtain ⟨a, ha, haz⟩ := hOnto z (hTrans y hyT z hzy)
    obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨a, ha⟩
    have hm' : (numberCode_l K m).val = a := congrArg Subtype.val hm
    exact ⟨m, (hRead _ z).mpr (hm'.symm ▸ haz)⟩
  obtain ⟨a, ha, haX⟩ := hOnto X hXT
  obtain ⟨r, hr⟩ := numberCode_surjective_l K ⟨a, ha⟩
  have hr' : (numberCode_l K r).val = a := congrArg Subtype.val hr
  refine ⟨Q, R, r, hWf, ?_, PowerlessBMSClassCollapse.agrees_l K φ η R hWf hUnique hEdge
    hTrans' r X ((hRead _ X).mpr (hr'.symm ▸ haX))⟩
  intro n m
  refine (hEdge n m).trans ?_
  constructor
  · rintro ⟨y, z, hy, hz, hyz⟩
    have hny := (hRead _ y).mp hy
    have hmz := (hRead _ z).mp hz
    exact (hQ _ _).mpr ⟨(numberCode_l K n).property, (numberCode_l K m).property,
      y, z, (SecondOrderFunctionProperties.value_mem_l hℳ hMap hny).2,
      (SecondOrderFunctionProperties.value_mem_l hℳ hMap hmz).2, hny, hmz, hyz⟩
  · intro h
    obtain ⟨_, _, y, z, _, _, hny, hmz, hyz⟩ := (hQ _ _).mp h
    exact ⟨y, z, (hRead _ y).mpr hny, (hRead _ z).mpr hmz, hyz⟩

include hBase in
/-- 遗传对象具有类内实数代表的内部良基图码，且指定根仍精确代表该对象。 -/
theorem real_presentation_l (K : source_coding_l hℳ) {X : SecondOrderQuotient.type_l hℳ}
    (hX : PowerlessHereditaryClass.member_l hℳ B X) :
    ∃ U : type_l hℳ B, ∃ hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega,
      ∃ R : SecondOrderModel.set_l ℳ, ∃ r : SecondOrderModel.num_l ℳ,
        ∃ hWf : ∀ n, SecondOrderDomain.wf_l R n,
          setRel_l K ⟨U.val, hU⟩ R ∧ mk_l hℳ ⟨R, r, hWf r⟩ = X := by
  obtain ⟨Q, R₀, r, hWf₀, hEdges₀, hRoot⟩ := presentation_l (hBase := hBase) K hX
  obtain ⟨U, hU, R, hTrace, hEdges⟩ := PowerlessRelativeClassNumericGraph.coded_l (hBase := hBase) K Q
  have hRel n m : SecondOrderPairing.relation_l R n m ↔ SecondOrderPairing.relation_l R₀ n m :=
    (hEdges n m).trans (hEdges₀ n m).symm
  have hWf n : SecondOrderDomain.wf_l R n :=
    SecondOrderDomain.mono_l R₀ R n (fun a b hab => (hRel a b).mp hab) (hWf₀ n)
  have hEq : SecondOrderGraph.eq_l ⟨R, r, hWf r⟩ ⟨R₀, r, hWf₀ r⟩ := by
    obtain ⟨D, hD⟩ := SecondOrderRelationOps.diagonal_l hℳ
    refine ⟨D, ?_, (hD r r).mpr rfl⟩
    intro a b hab
    obtain rfl := (hD a b).mp hab
    exact ⟨fun c hc => ⟨c, (hRel c a).mp hc, (hD c c).mpr rfl⟩,
      fun c hc => ⟨c, (hRel c a).mpr hc, (hD c c).mpr rfl⟩⟩
  exact ⟨U, hU, R, r, hWf, hTrace,
    ((SecondOrderQuotient.eq_iff_l hℳ _ _).mpr hEq).trans hRoot⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryGraphPresentation
