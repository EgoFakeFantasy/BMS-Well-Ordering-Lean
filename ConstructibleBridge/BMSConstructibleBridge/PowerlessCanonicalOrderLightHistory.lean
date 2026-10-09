import BMSConstructibleBridge.PowerlessHierarchyLightHistory
import BMSConstructibleBridge.PowerlessCanonicalOrderCandidateBounded

/-! # 固定层图及满足图的有界规范序前史

对象语言为纯隶属 ℒ；后续应用背景为原 Z₂ 图商。F 是实际层对象图，G
是实际规范 Sat 图；W 只界定层和 Sat 输出，C 界定比较图及有限辅助证书。
不要求 W∈W、C∈C，不将原数字指标图或原陪域升级为 Class。

检查器保留干净总函数、真实前驱、相同 F/G 查询及完整极限成员并。
此处只有 Δ₀ AST 与全部 raw 语义等价；存在性、内部唯一性、实际 Class
预算界及最终原 Derives 必须由后续证明完成，不能视为新增公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderLightHistory

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  up (up (up (up (up t))))

def successor_data_m {Γ Δ : SortContext ℒ}
    (C ω F G g a E b A D Sat Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessHierarchyLightHistory.successor_m b a) <|
    .conj (PowerlessValueBounded.formula_m F b A) <|
      .conj (PowerlessValueBounded.formula_m F a D) <|
        .conj (PowerlessValueBounded.formula_m G A Sat) <|
          .conj (PowerlessValueBounded.formula_m g b Q)
            (PowerlessCanonicalOrderCandidateBounded.formula_m C ω A Q Sat D E)

theorem successor_data_delta_l {Γ Δ : SortContext ℒ}
    (C ω F G g a E b A D Sat Q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound
      (successor_data_m C ω F G g a E b A D Sat Q) :=
  .conj (PowerlessHierarchyLightHistory.successor_delta_l _ _)
    (.conj (PowerlessValueBounded.delta_l _ _ _)
      (.conj (PowerlessValueBounded.delta_l _ _ _)
        (.conj (PowerlessValueBounded.delta_l _ _ _)
          (.conj (PowerlessValueBounded.delta_l _ _ _)
            (PowerlessCanonicalOrderCandidateBounded.delta_l _ _ _ _ _ _ _)))))

def successor_data_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C ω F G g a E b A D Sat Q : carrier_l 𝒩) : Prop :=
  PowerlessHierarchyLightHistory.successor_holds_l b a ∧
    value_l (ℳ := 𝒩) F b A ∧ value_l (ℳ := 𝒩) F a D ∧
      value_l (ℳ := 𝒩) G A Sat ∧ value_l (ℳ := 𝒩) g b Q ∧
        PowerlessCanonicalOrderCandidateBounded.holds_l (𝒩 := 𝒩) C ω A Q Sat D E

theorem successor_data_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (C ω F G g a E b A D Sat Q : Term ℒ Γ Δ .set) :
    (successor_data_m C ω F G g a E b A D Sat Q).satisfies η ↔
      successor_data_l (C.eval η) (ω.eval η) (F.eval η) (G.eval η)
        (g.eval η) (a.eval η) (E.eval η) (b.eval η) (A.eval η)
        (D.eval η) (Sat.eval η) (Q.eval η) := by
  simp only [successor_data_m, successor_data_l, Formula.satisfies,
    PowerlessHierarchyLightHistory.successor_formula_l,
    PowerlessValueBounded.formula_l, PowerlessCanonicalOrderCandidateBounded.formula_l]

def successor_m {Γ Δ : SortContext ℒ}
    (C W ω F G g a E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists a <|
    membershipLevyBound.boundedExists (up W) <|
      membershipLevyBound.boundedExists (up (up W)) <|
        membershipLevyBound.boundedExists (up (up (up W))) <|
          membershipLevyBound.boundedExists (up (up (up (up C)))) <|
            successor_data_m (up₅ C) (up₅ ω) (up₅ F) (up₅ G) (up₅ g) (up₅ a) (up₅ E)
              (.bvar (.there (.there (.there (.there .here)))))
              (.bvar (.there (.there (.there .here))))
              (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem successor_delta_l {Γ Δ : SortContext ℒ}
    (C W ω F G g a E : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (successor_m C W ω F G g a E) :=
  .bounded_exists _ (.bounded_exists _ (.bounded_exists _ (.bounded_exists _
    (.bounded_exists _ (successor_data_delta_l _ _ _ _ _ _ _ _ _ _ _ _)))))

def successor_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C W ω F G g a E : carrier_l 𝒩) : Prop :=
  ∃ b, member_l 𝒩 b a ∧ ∃ A, member_l 𝒩 A W ∧ ∃ D, member_l 𝒩 D W ∧
    ∃ Sat, member_l 𝒩 Sat W ∧ ∃ Q, member_l 𝒩 Q C ∧
      successor_data_l C ω F G g a E b A D Sat Q

theorem successor_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (C W ω F G g a E : Term ℒ Γ Δ .set) :
    (successor_m C W ω F G g a E).satisfies η ↔ successor_holds_l
      (C.eval η) (W.eval η) (ω.eval η) (F.eval η) (G.eval η)
      (g.eval η) (a.eval η) (E.eval η) := by
  simp only [successor_m, successor_holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    successor_data_formula_l, Arguments.eval, up₅, up, Term.eval_weakenBound, Term.eval]
  rfl

def step_m {Γ Δ : SortContext ℒ}
    (C W ω F G P₀ g a E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (PowerlessHierarchyLightHistory.empty_m a) (.equal E P₀)) <|
    .disj (successor_m C W ω F G g a E)
      (.conj (PowerlessHierarchyLightHistory.limit_m a)
        (PowerlessHierarchyLightHistory.union_m C g a E))

theorem step_delta_l {Γ Δ : SortContext ℒ}
    (C W ω F G P₀ g a E : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (step_m C W ω F G P₀ g a E) :=
  .disj (.conj (PowerlessHierarchyLightHistory.empty_delta_l _) (.equal _ _))
    (.disj (successor_delta_l _ _ _ _ _ _ _ _)
      (.conj (PowerlessHierarchyLightHistory.limit_delta_l _)
        (PowerlessHierarchyLightHistory.union_delta_l _ _ _ _)))

def step_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C W ω F G P₀ g a E : carrier_l 𝒩) : Prop :=
  (PowerlessHierarchyLightHistory.empty_holds_l a ∧ E = P₀) ∨
    successor_holds_l C W ω F G g a E ∨
      (PowerlessHierarchyLightHistory.limit_holds_l a ∧
        PowerlessHierarchyLightHistory.union_holds_l C g a E)

theorem step_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (C W ω F G P₀ g a E : Term ℒ Γ Δ .set) :
    (step_m C W ω F G P₀ g a E).satisfies η ↔ step_holds_l
      (C.eval η) (W.eval η) (ω.eval η) (F.eval η) (G.eval η)
      (P₀.eval η) (g.eval η) (a.eval η) (E.eval η) := by
  simp only [step_m, step_holds_l, Formula.satisfies,
    PowerlessHierarchyLightHistory.empty_formula_l, successor_formula_l,
    PowerlessHierarchyLightHistory.limit_formula_l, PowerlessHierarchyLightHistory.union_formula_l]

def formula_m {Γ Δ : SortContext ℒ}
    (C W ω F G P₀ α g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessMapBounded.formula_m g α C) <|
    membershipLevyBound.boundedForall α <|
      membershipLevyBound.boundedForall (up C) <| .imp
        (PowerlessValueBounded.formula_m (up (up g)) (.bvar (.there .here)) (.bvar .here))
        (step_m (up (up C)) (up (up W)) (up (up ω)) (up (up F))
          (up (up G)) (up (up P₀)) (up (up g)) (.bvar (.there .here)) (.bvar .here))

theorem delta_l {Γ Δ : SortContext ℒ}
    (C W ω F G P₀ α g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m C W ω F G P₀ α g) :=
  .conj (PowerlessMapBounded.delta_l _ _ _) (.bounded_forall _ (.bounded_forall _
    (.imp (PowerlessValueBounded.delta_l _ _ _) (step_delta_l _ _ _ _ _ _ _ _ _))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C W ω F G P₀ α g : carrier_l 𝒩) : Prop :=
  map_l (ℳ := 𝒩) g α C ∧ ∀ a, member_l 𝒩 a α → ∀ E, member_l 𝒩 E C →
    value_l (ℳ := 𝒩) g a E → step_holds_l C W ω F G P₀ g a E

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (C W ω F G P₀ α g : Term ℒ Γ Δ .set) :
    (formula_m C W ω F G P₀ α g).satisfies η ↔ holds_l
      (C.eval η) (W.eval η) (ω.eval η) (F.eval η) (G.eval η)
      (P₀.eval η) (α.eval η) (g.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessMapBounded.formula_l, PowerlessValueBounded.formula_l, step_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 陪域界由完整函数图证明，所以结论覆盖所有 raw 输出。 -/
theorem full_reading_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {C W ω F G P₀ α g : SecondOrderQuotient.type_l hℳ} :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) C W ω F G P₀ α g ↔
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) g α C ∧
        ∀ a E, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g a E →
          step_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) C W ω F G P₀ g a E := by
  constructor
  · rintro ⟨hMap, hSteps⟩
    refine ⟨hMap, fun a E hValue => ?_⟩
    have hMem := SecondOrderFunctionProperties.value_mem_l hℳ hMap hValue
    exact hSteps a hMem.1 E hMem.2 hValue
  · rintro ⟨hMap, hSteps⟩
    exact ⟨hMap, fun a _ha E _hE hValue => hSteps a E hValue⟩

#print axioms delta_l
#print axioms formula_l
#print axioms full_reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderLightHistory
