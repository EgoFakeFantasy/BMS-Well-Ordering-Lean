import BMSConstructibleBridge.PowerlessRelativeCofinalDefFunction
import BMSConstructibleBridge.PowerlessRelativeLimitFunctionGraphBounded
import BMSConstructibleBridge.PowerlessRelativeLimitRelationalGraph
import BMSConstructibleBridge.PowerlessMemberDefDerives

/-! # 严格较早共尾层的原 Def 图属于指定外极限层

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m。
给定真实 U=Lβ[B]、W=LΩ[B]，其中 β<Ω、β 是非零共尾极限且 ω∈U，
把同一编码包的完整规范 Sat 函数先放入 Def²(U)，再在 W 中以原有界
Def 检查器构造 U→U 的完整成员图。所有 raw 坐标的读数最终回到原
MemberDef.global_m，而不是仅保留 checker 或 Class 身份。

本文件不证明这样的 β 在 Ω 以下存在，不把普通极限性冒充共尾性，
也不证明长超限前史、完整 Collection 或 BMS 终局。原 Z₂ 闭句明确
保留实际层与共尾守卫；所有中间编码见证在证明内取得，无 Type 选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalDefGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 原 Def 图的全部 raw 读数；候选输出不额外受 Class 或 W 限制。 -/
def graph_m {Γ Δ : SortContext ℒ} (U D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.map_m D U U) <|
    .forallE .set <| .forallE .set <|
      .iff (SecondOrderObjectSyntax.value_m (up (up D))
        (.bvar (.there .here)) (.bvar .here))
        (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up (up U)))
          (PowerlessMemberDefSyntax.global_m (.bvar (.there .here)) (.bvar .here)))

def graph_l (U D : Raw) : Prop :=
  SecondOrderFunctionObjects.map_l hℳ D U U ∧
    ∀ A H : Raw, SecondOrderFunctionObjects.value_l hℳ D A H ↔
      mem_l hℳ A U ∧ SecondOrderMemberDef.spec_l hℳ A H

theorem graph_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (U D : Term ℒ Γ Δ .set) :
    (graph_m U D).satisfies η ↔ graph_l (U.eval η) (D.eval η) := by
  simp only [graph_m, graph_l, Formula.satisfies, SecondOrderObjectSyntax.map_l,
    SecondOrderObjectSyntax.value_l, PowerlessMemberDefDerives.formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

private abbrev coding_m : SortContext ℒ :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .set]

private abbrev lift_m (v : Variable coding_m .set) :
    Term ℒ [] (.set :: .set :: coding_m) .set := .fvar (.there (.there v))

private def satisfaction_m : Formula ℒ [] (.set :: .set :: coding_m) :=
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

/-- 同一整包的整张 Sat 图进入外层，不重新选取或替换 Sat 函数。 -/
theorem satisfaction_member_l (K : source_coding_l hℳ) {B β U Ω W : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hInner : limit_l hℳ β) (hU : level_l hℳ B β U)
    (hOuter : limit_l hℳ Ω) (hW : level_l hℳ B Ω W) (hBelow : mem_l hℳ β Ω)
    {ω e t₁ t₂ t₃ Pair N Valid Translation G : PowerlessRelativeClassStructure.type_l hℳ B}
    {C : SecondOrderModel.set_l ℳ} (hωU : mem_l hℳ ω.val U)
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l (W := U)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G C) : mem_l hℳ G.val W := by
  obtain ⟨γ, U₁, hγ, hU₁, hDef₁⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hOuter hW hBelow hU
  obtain ⟨δ, U₂, hδ, hU₂, hDef₂⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hOuter hW hγ hU₁
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hU
  have hSub := SecondOrderMemberDefProperties.contains_l hℳ hDef₁
    (fun x y hx hy => hTrans x hx y hy)
  have hUU₁ := SecondOrderMemberDefProperties.mother_member_l hℳ hDef₁
  let ρTail : Env 𝒱 [] [.set, .set, .set] :=
    ((Env.empty.pushFree Valid.val).pushFree t₃.val).pushFree t₂.val
  let ρ : Env 𝒱 [] coding_m :=
    (((((ρTail.pushFree t₁.val).pushFree U).pushFree Pair.val).pushFree N.val).pushFree e.val).pushFree ω.val
  have hParams : ∀ s (v : Variable coding_m s), mem_l hℳ (ρ.freeVal v) U₁ := by
    intro s v
    cases s
    match v with
    | .here => exact hSub ω.val hωU
    | .there .here => exact hSub e.val hCoding.e_mem
    | .there (.there .here) => exact hSub N.val hCoding.numbers_mem
    | .there (.there (.there .here)) => exact hSub Pair.val hCoding.pair_mem
    | .there (.there (.there (.there .here))) => exact hUU₁
    | .there (.there (.there (.there (.there .here)))) => exact hSub t₁.val hCoding.tag₁_mem
    | .there (.there (.there (.there (.there (.there .here))))) => exact hSub t₂.val hCoding.tag₂_mem
    | .there (.there (.there (.there (.there (.there (.there .here)))))) => exact hSub t₃.val hCoding.tag₃_mem
    | .there (.there (.there (.there (.there (.there (.there (.there .here))))))) =>
        exact hSub Valid.val hCoding.validity_mem
  have hMatrix (A H : Raw) : satisfaction_m.satisfies ((ρ.pushFree H).pushFree A) ↔
      PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒱)
        ω.val A e.val N.val Pair.val U U t₁.val t₂.val t₃.val Valid.val H := by
    simpa only [satisfaction_m, ρ, ρTail, lift_m, Term.eval, Env.pushFree_here, Env.pushFree_there] using
      PowerlessSatisfactionNormalizedMatrix.formula_l ((ρ.pushFree H).pushFree A)
        (lift_m .here) (.fvar .here) (lift_m (.there .here)) (lift_m (.there (.there .here)))
        (lift_m (.there (.there (.there .here))))
        (lift_m (.there (.there (.there (.there .here)))))
        (lift_m (.there (.there (.there (.there .here)))))
        (lift_m (.there (.there (.there (.there (.there .here))))))
        (lift_m (.there (.there (.there (.there (.there (.there .here)))))))
        (lift_m (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (lift_m (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.fvar (.there .here))
  have hφ : Formula.IsDelta0 membershipLevyBound satisfaction_m :=
    PowerlessSatisfactionNormalizedMatrix.delta_l _ _ _ _ _ _ _ _ _ _ _ _
  have hGU₂ := PowerlessRelativeLimitFunctionGraphBounded.member_l hℳ hBase hU hInner hDef₁ hDef₂
    hφ ρ hParams
    hUU₁ hUU₁ (fun _ h => h) (fun _ h => h) hCoding.sat_map
    (fun A H => (hCoding.sat_read A H).trans
      (and_congr Iff.rfl (and_congr Iff.rfl (hMatrix A H).symm)))
  exact (PowerlessRelativeLimitClosure.value_l hℳ hBase hOuter hW G.val).mpr
    ⟨δ, U₂, hδ, hU₂, hGU₂⟩

/-- 所有编码及完整 Sat 见证均在证明内产生；不要求它们预先属于外层。 -/
theorem exists_l (K : source_coding_l hℳ) {B β U Ω W : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hInner : limit_l hℳ β) (hU : level_l hℳ B β U)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β) (hωU : mem_l hℳ K.omega U)
    (hOuter : limit_l hℳ Ω) (hW : level_l hℳ B Ω W) (hBelow : mem_l hℳ β Ω) :
    ∃ D : Raw, mem_l hℳ D W ∧ graph_l U D := by
  let ω : PowerlessRelativeClassStructure.type_l hℳ B := ⟨K.omega, ⟨β, U, hU, hωU⟩⟩
  obtain ⟨e, t₁, t₂, t₃, Pair, N, Valid, Translation, G, C, hCoding⟩ :=
    PowerlessRelativeCofinalDefCoding.exists_l hBase K hInner hU hCofinal ω hωU rfl
  have hGUW := satisfaction_member_l K hBase hInner hU hOuter hW hBelow hωU hCoding
  have hUW := PowerlessRelativeLevelClosure.members_l hℳ hBase hBelow hU hW
  have hSub := PowerlessRelativeLevelClosure.subset_l hℳ hBase hBelow hU hW
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set, .set] :=
    (((((Env.empty.pushFree G.val).pushFree U).pushFree Translation.val).pushFree N.val).pushFree e.val).pushFree ω.val
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    PowerlessMemberDefImageBounded.formula_m
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar .here) (.fvar (.there .here))
  have hφ : Formula.IsDelta0 membershipLevyBound φ :=
    PowerlessMemberDefImageBounded.delta_l _ _ _ _ _ _ _ _
  have hMatrix (A H : Raw) : φ.satisfies ((η.pushFree H).pushFree A) ↔
      PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒱)
        ω.val e.val N.val Translation.val U G.val A H := by
    simpa only [φ, η, Term.eval, Env.pushFree_here, Env.pushFree_there] using
      PowerlessMemberDefImageBounded.formula_l ((η.pushFree H).pushFree A)
        (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there (.there (.there (.there .here))))))
        (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (.fvar .here) (.fvar (.there .here))
  have hParams : ∀ s (v : Variable
      ([.set, .set, .set, .set, .set, .set] : SortContext ℒ) s),
      mem_l hℳ (η.freeVal v) W := by
    intro s v
    cases s
    match v with
    | .here => exact hSub ω.val hωU
    | .there .here => exact hSub e.val hCoding.e_mem
    | .there (.there .here) => exact hSub N.val hCoding.numbers_mem
    | .there (.there (.there .here)) => exact hSub Translation.val hCoding.translation_mem
    | .there (.there (.there (.there .here))) => exact hUW
    | .there (.there (.there (.there (.there .here)))) => exact hGUW
  obtain ⟨D, hDW, hMembers⟩ := PowerlessRelativeLimitRelationalGraph.exists_member_l
    hBase hOuter hW hφ η hUW hUW hParams
  have hValues := PowerlessRelativeLimitRelationalGraph.values_of_members_l hMembers
  have hRead (A H : Raw) : SecondOrderFunctionObjects.value_l hℳ D A H ↔
      mem_l hℳ A U ∧ SecondOrderMemberDef.spec_l hℳ A H := by
    constructor
    · intro hDH
      obtain ⟨hAU, _hHU, hCheck⟩ := (hValues A H).mp hDH
      exact ⟨hAU, (PowerlessMemberDefImageBoundedReading.checkeriff_l
        hBase K hInner hU hωU hCoding hAU).mp ((hMatrix A H).mp hCheck)⟩
    · rintro ⟨hAU, hDef⟩
      have hHU := PowerlessRelativeCofinalMemberDefClosure.member_l
        hBase K hInner hU hCofinal hωU hAU hDef
      exact (hValues A H).mpr ⟨hAU, hHU, (hMatrix A H).mpr
        ((PowerlessMemberDefImageBoundedReading.checkeriff_l
          hBase K hInner hU hωU hCoding hAU).mpr hDef)⟩
  refine ⟨D, hDW, ⟨?_, ?_⟩, hRead⟩
  · intro p hp
    obtain ⟨A, H, hAU, hHU, hPair, _hCheck⟩ := (hMembers p).mp hp
    exact ⟨A, H, hAU, hHU, hPair⟩
  · intro A hAU
    obtain ⟨H, hDef, _hUnique⟩ := SecondOrderMemberDef.exists_l hℳ A
    have hHU := PowerlessRelativeCofinalMemberDefClosure.member_l
      hBase K hInner hU hCofinal hωU hAU hDef
    refine ⟨H, ⟨hHU, (hRead A H).mpr ⟨hAU, hDef⟩⟩, ?_⟩
    intro H' hH'
    exact SecondOrderMemberDef.unique_l hℳ ((hRead A H').mp hH'.2).2 hDef

/-- 六个自由槽依次为 W、Ω、U、β、ω、B；较早共尾性明确留在原守卫。 -/
def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  let W : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let Ω := .fvar (.there .here)
  let U := .fvar (.there (.there .here))
  let β := .fvar (.there (.there (.there .here)))
  let ω := .fvar (.there (.there (.there (.there .here))))
  let B := .fvar (.there (.there (.there (.there (.there .here)))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (PowerlessRelativeCofinalLimitBounds.cofinal_m β) <|
          .imp (PowerlessRelativeHierarchySyntax.level_m B β U) <|
            .imp (SecondOrderObjectSyntax.member_m ω U) <|
              .imp (PowerlessRelativeHierarchySyntax.limit_m Ω) <|
                .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
                  .imp (SecondOrderObjectSyntax.member_m β Ω) <|
                    .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up W))
                      (graph_m (up U) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeCofinalLimitBounds.cofinal_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K, graph_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hω hInner hCofinal hU hωU hOuter hW hBelow
  have hKωU : mem_l hℳ K.omega ((.fvar (.there (.there .here)) :
      Term ℒ [] [.set, .set, .set, .set, .set, .set] .set).eval η) :=
    (SecondOrderOmega.unique_l hℳ hω K.omega_spec) ▸ hωU
  exact exists_l K hBase hInner hU hCofinal hKωU hOuter hW hBelow

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalDefGraph
