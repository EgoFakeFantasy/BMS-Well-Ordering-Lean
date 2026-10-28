import BMSConstructibleBridge.PowerlessMemberBounded
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity
import BMSConstructibleBridge.PowerlessRelativeCofinalDefGraph
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryUnique
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives

/-! # 有限初等子结构捕获同一真实层次前史

原公式族同时保留轻量历史的存在式与完整 Δ₀ 矩阵。存在式回收 I 中
见证，矩阵反射回传递 W，再由 W 的绝对性读成环境真实历史。I 不须
传递，也不须 I∈W；单独反射存在式不足以保证回收的图在环境中有效。

在同一实际完整 Def 图下，内部历史唯一性认出回收图就是原前史 f，
故取得 f∈I，而不另选一张相似历史。原 Z₂ Derives 保留可由已有局部
历史与有限元素性构造提供的守卫；本模块不声称已经运输 Def 截迹、
证明弱凝聚、完整 Collection 或最终候选源存在性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullHistory

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

/-- 绑定槽依次为 f、U、A、D、B；原自由上下文完全不变。 -/
def matrix_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set, .set, .set, .set] Δ :=
  PowerlessHierarchyLightHistory.formula_m
    (.bvar (.there (.there (.there (.there .here)))))
    (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
    (.bvar (.there .here)) (.bvar .here)

def exists_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set, .set, .set] Δ :=
  .existsE .set (matrix_m Δ)

def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m Δ :=
  [Sigma.mk ([.set, .set, .set, .set] : SortContext ℒ) (exists_m Δ),
    Sigma.mk ([.set, .set, .set, .set, .set] : SortContext ℒ) (matrix_m Δ)]

theorem matrix_delta_l (Δ : SortContext ℒ) :
    Formula.IsDelta0 membershipLevyBound (matrix_m Δ) :=
  PowerlessHierarchyLightHistory.delta_l _ _ _ _ _

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 回收完整真实轻量图；W 的传递性不传播给 I。 -/
theorem capture_l {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env 𝒩 [] Δ) (hτ : ∀ v, (τ v).eval ζ = ν.freeVal v)
    {I₀ W₀ B D A U : carrier_l 𝒩}
    (hFree : ∀ v : Variable Δ .set, member_l 𝒩 (ν.freeVal v) I₀)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, member_l 𝒩 x W₀ → ∀ y, member_l 𝒩 y x → member_l 𝒩 y W₀)
    (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (hB : member_l 𝒩 B I₀) (hD : member_l 𝒩 D I₀)
    (hA : member_l 𝒩 A I₀) (hU : member_l 𝒩 U I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hf : ∃ f, member_l 𝒩 f W₀ ∧ PowerlessHierarchyLightHistory.holds_l B D A U f) :
    ∃ f, member_l 𝒩 f I₀ ∧ PowerlessHierarchyLightHistory.holds_l B D A U f := by
  have hNonempty : ∃ x, member_l 𝒩 x W₀ := ⟨B, hIW B hB⟩
  change (PowerlessRelativeFiniteElementarity.entry_m (exists_m Δ) I W τ).satisfies ζ ∧
    (PowerlessRelativeFiniteElementarity.entry_m (matrix_m Δ) I W τ).satisfies ζ ∧ True at h
  have hExists := (PowerlessRelativeFiniteElementarity.entry_formula_l
    (exists_m Δ) ζ I W τ ν hτ).mp h.1
  have hMatrix := (PowerlessRelativeFiniteElementarity.entry_formula_l
    (matrix_m Δ) ζ I W τ ν hτ).mp h.2.1
  let η : Env 𝒩 [.set, .set, .set, .set] Δ :=
    ν |>.pushBound B |>.pushBound D |>.pushBound A |>.pushBound U
  have hParams : ∀ v : Variable ([.set, .set, .set, .set] : SortContext ℒ) .set,
      member_l 𝒩 (η.boundVal v) I₀ := by
    intro v
    match v with
    | .here => exact hU
    | .there .here => exact hA
    | .there (.there .here) => exact hD
    | .there (.there (.there .here)) => exact hB
  have hPush (C f : carrier_l 𝒩) :
      (η.pushFree C).pushBound f = (η.pushBound f).pushFree C := by
    apply Env.ext
    · intro s v; cases s; cases v <;> rfl
    · intro s v; cases s; cases v with
      | here => rfl
      | there v => rfl
  have hRead (f : carrier_l 𝒩) :
      (matrix_m Δ).satisfies (η.pushBound f) ↔
        PowerlessHierarchyLightHistory.holds_l B D A U f := by
    rw [matrix_m, PowerlessHierarchyLightHistory.formula_l]
    rfl
  have hAbsolute (f : carrier_l 𝒩) (hfW : member_l 𝒩 f W₀) :=
    PowerlessMemberBounded.relativized_l hW hNonempty (matrix_delta_l Δ)
      (η.pushBound f) (fun v => by
        cases v with
        | here => exact hfW
        | there v => exact hIW (η.boundVal v) (hParams v)) (fun v => hIW _ (hFree v))
  obtain ⟨f, hfW, hf⟩ := hf
  have hWitness : (PowerlessRelativization.formula_m (exists_m Δ)).satisfies
      (η.pushFree W₀) := by
    change ∃ g, member_l 𝒩 g W₀ ∧
      (PowerlessRelativization.formula_m (matrix_m Δ)).satisfies
        ((η.pushFree W₀).pushBound g)
    refine ⟨f, hfW, ?_⟩
    rw [hPush]
    exact (hAbsolute f hfW).mpr ((hRead f).mpr hf)
  have hReflect := hExists η (fun _ _ => rfl)
    (fun v => hI₀.symm ▸ hParams v)
  rw [hW₀, hI₀] at hReflect
  have hInside := hReflect.mp hWitness
  change ∃ g, member_l 𝒩 g I₀ ∧
    (PowerlessRelativization.formula_m (matrix_m Δ)).satisfies
      ((η.pushFree I₀).pushBound g) at hInside
  obtain ⟨g, hgI, hg⟩ := hInside
  rw [hPush] at hg
  have hRecover := hMatrix (η.pushBound g) (fun _ _ => rfl)
    (fun v => by
      rw [hI₀]
      cases v with
      | here => exact hgI
      | there v => exact hParams v)
  rw [hW₀, hI₀] at hRecover
  exact ⟨g, hgI, (hRead g).mp ((hAbsolute g (hIW g hgI)).mp (hRecover.mpr hg))⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 用真实 Def 读数与内部唯一性认出同一原历史；不是仅另造 I 内历史。 -/
theorem member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = ν.freeVal v)
    {I₀ W₀ B D A U f : SecondOrderQuotient.type_l hℳ}
    (hFree : ∀ v : Variable Δ .set, SecondOrderQuotient.mem_l hℳ (ν.freeVal v) I₀)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, SecondOrderQuotient.mem_l hℳ x W₀ → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (hB : SecondOrderQuotient.mem_l hℳ B I₀) (hD : SecondOrderQuotient.mem_l hℳ D I₀)
    (hA : SecondOrderQuotient.mem_l hℳ A I₀) (hU : SecondOrderQuotient.mem_l hℳ U I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hGraph : PowerlessRelativeCofinalDefGraph.graph_l U D)
    (hOrdinal : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
        (SecondOrderQuotient.structure_l hℳ)) A)
    (hf : PowerlessRelativeHierarchySemantics.history_l hℳ B A f U)
    (hfW : SecondOrderQuotient.mem_l hℳ f W₀) : SecondOrderQuotient.mem_l hℳ f I₀ := by
  have hLight : PowerlessHierarchyLightHistory.history_l hℳ B D A U f :=
    PowerlessHierarchyLightHistoryUnique.from_original_l hℳ (D := D) (W := U) hGraph.2
    (fun _ hx => hx) hf
  obtain ⟨g, hgI, hg⟩ := capture_l (I₀ := I₀) (W₀ := W₀)
    (B := B) (D := D) (A := A) (U := U) ζ I W τ ν hτ
    (fun v => by simpa only [ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l]
      using hFree v) hI₀ hW₀ hW hIW hB hD hA hU h
    ⟨f, hfW, (PowerlessHierarchyLightHistory.reading_l hℳ).mpr hLight⟩
  have hEq : f = g := PowerlessHierarchyLightHistoryUnique.original_unique_l hℳ (D := D) (W := U)
    hGraph.2 hOrdinal hf ((PowerlessHierarchyLightHistory.reading_l hℳ).mp hg)
  exact hEq.symm ▸ hgI

def schema_m {Θ Δ : SortContext ℒ} (B D A U I W f : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessNaturalOrder.transitive_m W) <|
    .imp (ThirdOrderTheory.subset_m I W) <|
      .imp (SecondOrderObjectSyntax.member_m B I) <|
        .imp (SecondOrderObjectSyntax.member_m D I) <|
          .imp (SecondOrderObjectSyntax.member_m A I) <|
            .imp (SecondOrderObjectSyntax.member_m U I) <|
              .imp (parameters_m Δ I τ) <|
                .imp (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ) <|
                  .imp (PowerlessRelativeCofinalDefGraph.graph_m U D) <|
                    .imp (PowerlessRelativeHierarchySyntax.ordinal_m A) <|
                      .imp (PowerlessRelativeHierarchySyntax.history_m B A f U) <|
                        .imp (SecondOrderObjectSyntax.member_m f W)
                          (SecondOrderObjectSyntax.member_m f I)

def sentence_m {Θ Δ : SortContext ℒ} (B D A U I W f : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B D A U I W f τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (B D A U I W f : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    (sentence_m B D A U I W f τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessNaturalOrder.transitive_formula_l,
    ThirdOrderSemantics.subset_formula_l, PowerlessRelativeCofinalDefGraph.graph_formula_l K,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeHierarchySemantics.history_formula_l K,
    parameters_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro hW hIW hB hD hA hU hParams h hGraph hOrdinal hf hfW
  let ν : Env (SecondOrderQuotient.structure_l hℳ) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (τ v).eval η }
  exact member_l hℳ η I W τ ν (fun _ => rfl) (fun v => hParams _ v)
    rfl rfl (fun x hx y hy => hW x y hx hy) hIW hB hD hA hU h hGraph hOrdinal hf hfW

theorem derives_m {Θ Δ : SortContext ℒ} (B D A U I W f : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B D A U I W f τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B D A U I W f τ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullHistory
