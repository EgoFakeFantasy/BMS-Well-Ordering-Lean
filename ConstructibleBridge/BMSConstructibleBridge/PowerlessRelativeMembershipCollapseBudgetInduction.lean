import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseBudgetSlice
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseBoundedGraph
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryBudgetExists

/-! # 同一成员坍缩的实际源层预算归纳

纯 point 公式量化全部实际局部域和图，结论同时给出二者的预算层成员界。
源层 U 明确属于实际传递层 W，故更早的源层仍在 W 中。原预算的共同
极限母层包含 W 及全部前驱预算层；零、后继、极限步分别由恒等图、旧
局部解和真实前驱覆盖给出。归纳调用原公式集合归纳，不使用宿主良基性。
预算证书不含局部解覆盖字段，原 H 也不作为 Δ₀ 切片参数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseBudgetInduction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def point_m {Γ Δ : SortContext ℒ} (B I T W Q a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let w (t : Term ℒ Γ Δ .set) := up (up (up (up (up t))))
    let δ : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
      .bvar (.there (.there (.there (.there .here))))
    let C : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
    let U : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let E : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let G : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .imp (PowerlessValueBounded.formula_m (w Q) (w a) δ) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m (w B) δ C) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m (w B) (w a) U) <|
          .imp (member_m U (w W)) <|
            .imp (PowerlessRelativeMembershipCollapseRestriction.domain_m (w I) U E) <|
              .imp (PowerlessRelativeMembershipCollapsePartial.partial_m (w I) E (w T) G)
                (.conj (member_m E C) (member_m G C))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def point_l (B I T W Q a : Raw) : Prop :=
  ∀ δ C U E G, value_l (ℳ := 𝒱) Q a δ →
    PowerlessRelativeHierarchySemantics.level_l hℳ B δ C →
      PowerlessRelativeHierarchySemantics.level_l hℳ B a U → mem_l hℳ U W →
        PowerlessRelativeMembershipCollapseRestriction.domain_l I U E →
          PowerlessRelativeMembershipCollapsePartial.partial_l I E T G →
            mem_l hℳ E C ∧ mem_l hℳ G C

theorem point_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B I T W Q a : Term ℒ Γ Δ .set) :
    (point_m B I T W Q a).satisfies η ↔
      point_l (B.eval η) (I.eval η) (T.eval η) (W.eval η) (Q.eval η) (a.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, PowerlessValueBounded.formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeMembershipCollapseRestriction.domain_formula_l,
    PowerlessRelativeMembershipCollapsePartial.formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 前驱预算层由真实 Q 总性取得，局部解由同一 H 的限制构造。 -/
theorem step_l {B Ω I T W A Q H a : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hBI : ∀ x, mem_l hℳ x B → mem_l hℳ x I)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hTW : mem_l hℳ T W)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hBudget : PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ B I W A Q)
    (hPast : ∀ b, mem_l hℳ b a → point_l B I T W Q b) : point_l B I T W Q a := by
  intro δ C U E G hQ hC hU hUW hE hG
  have haA := hBudget.source a δ hQ
  obtain ⟨ξ, C₀, C₁, hLimit, hC₀, hCD, hDC, hBC₀, hIC₀, hWC₀, _haC₀, hEarlier⟩ :=
    hBudget.layers a δ C hQ hC
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC₀
  have hTransW := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  have hTransD := SecondOrderMemberDefProperties.transitive_l hℳ hCD
    (fun x y hx hy => hTrans x hx y hy)
  have hSubCD := SecondOrderMemberDefProperties.contains_l hℳ hCD
    (fun x y hx hy => hTrans x hx y hy)
  have hSubDC := SecondOrderMemberDefProperties.contains_l hℳ hDC hTransD
  have hInto (x : Raw) (hx : mem_l hℳ x C₀) : mem_l hℳ x C :=
    hSubDC x (hSubCD x hx)
  have hUC₀ := hTrans W hWC₀ U hUW
  have hTC₀ := hTrans W hWC₀ T hTW
  have hED : mem_l hℳ E C₁ :=
    PowerlessRelativeMembershipCollapseBudgetSlice.domain_member_l hCD hTrans hIC₀ hUC₀ hE
  have hPrefix (b V : Raw) (hb : mem_l hℳ b a)
      (hV : PowerlessRelativeHierarchySemantics.level_l hℳ B b V) (hVW : mem_l hℳ V W) :
      ∃ E₀ G₀, PowerlessRelativeMembershipCollapseRestriction.domain_l I V E₀ ∧
        PowerlessRelativeMembershipCollapsePartial.partial_l I E₀ T G₀ ∧
          mem_l hℳ E₀ C₀ ∧ mem_l hℳ G₀ C₀ := by
    have hbA := hBudget.domain_ordinal.transitive a haA b hb
    obtain ⟨θ, hQb⟩ := hBudget.total b hbA
    obtain ⟨D, hD⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase
      (hBudget.output_ordinal b θ hQb)
    obtain ⟨E₀, G₀, hE₀, hG₀, _hRead⟩ :=
      PowerlessRelativeMembershipCollapseRestriction.level_l hBase hV hH
    obtain ⟨hE₀D, hG₀D⟩ := hPast b hb θ D V E₀ G₀ hQb hD hV hVW hE₀ hG₀
    exact ⟨E₀, G₀, hE₀, hG₀, hTrans D (hEarlier b hb θ D hQb hD) E₀ hE₀D,
      hTrans D (hEarlier b hb θ D hQb hD) G₀ hG₀D⟩
  obtain ⟨A₀, f, r, hA₀, haA₀, hHist, hf⟩ := hU
  have hSource (b V : Raw) (hb : mem_l hℳ b a)
      (hfb : SecondOrderFunctionObjects.value_l hℳ f b V) :
      PowerlessRelativeHierarchySemantics.level_l hℳ B b V :=
    ⟨A₀, f, r, hA₀, hA₀.transitive a haA₀ b hb, hHist, hfb⟩
  rcases hHist.2 a U ⟨haA₀, hf⟩ with ⟨_hZero, hUB⟩ | ⟨b, V, hSucc, hfb, hVU⟩ | ⟨_hLimitA, hUnion⟩
  · subst U
    have hEB : E = B := by
      apply SecondOrderQuotient.ext_l hℳ
      intro x
      exact (hE x).trans ⟨fun h => h.2, fun hx => ⟨hBI x hx, hx⟩⟩
    subst E
    exact ⟨hInto B hBC₀, hSubDC G
      (PowerlessRelativeMembershipCollapseBudgetSlice.base_member_l
        hBase hBI hC₀ hLimit hCD hBC₀ hH hG)⟩
  · have hb := PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc
    have hV := hSource b V hb hfb
    have hVUmem := SecondOrderMemberDefProperties.mother_member_l hℳ hVU
    have hVW := hTransW U hUW V hVUmem
    obtain ⟨E₀, G₀, hE₀, hG₀, _hE₀C₀, hG₀C₀⟩ := hPrefix b V hb hV hVW
    obtain ⟨E₁, G₁, hE₁, hG₁, hG₁D, _hRead⟩ :=
      PowerlessRelativeMembershipCollapseSuccessor.member_l hBase hC₀ hLimit hCD
        (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hV) hVU hIC₀
        (hTrans W hWC₀ V hVW) hUC₀ hTC₀ hG₀C₀ hH hE₀ hG₀
    have hEqE : E₁ = E := by
      apply SecondOrderQuotient.ext_l hℳ
      intro x
      exact (hE₁ x).trans (hE x).symm
    subst E₁
    have hEqG : G = G₁ := PowerlessRelativeMembershipCollapseBudgetSlice.ext_l hH hG hG₁
    exact ⟨hSubDC E hED, hEqG.symm ▸ hSubDC G₁ hG₁D⟩
  · have hCover (x : Raw) (hx : mem_l hℳ x E) :
        ∃ E₀, mem_l hℳ E₀ C₀ ∧ ∃ G₀, mem_l hℳ G₀ C₀ ∧
          mem_l hℳ x E₀ ∧ PowerlessRelativeMembershipCollapsePartial.partial_l I E₀ T G₀ := by
      obtain ⟨hxI, hxU⟩ := (hE x).mp hx
      obtain ⟨b, V, hb, hfb, hxV⟩ := (hUnion x).mp hxU
      have hV := hSource b V hb hfb
      have hVU := PowerlessRelativeLevelClosure.members_l hℳ hBase hb hV
        ⟨A₀, f, r, hA₀, haA₀, hHist, hf⟩
      obtain ⟨E₀, G₀, hE₀, hG₀, hE₀C₀, hG₀C₀⟩ :=
        hPrefix b V hb hV (hTransW U hUW V hVU)
      exact ⟨E₀, hE₀C₀, G₀, hG₀C₀, (hE₀ x).mpr ⟨hxI, hxV⟩, hG₀⟩
    exact ⟨hSubDC E hED, PowerlessRelativeMembershipCollapseBoundedGraph.slice_member_l
      hBase hC₀ hLimit hCD hDC hIC₀ hTC₀ hED hG.1 hH hG.2.2.1
        (PowerlessRelativeMembershipCollapseBudgetSlice.value_l hH hG) hCover⟩

/-- 原纯公式集合归纳同时取得全部实际局部域和图的真实预算成员界。 -/
theorem bounded_l (K : source_coding_l hℳ) {B Ω I T W A Q H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hBI : ∀ x, mem_l hℳ x B → mem_l hℳ x I)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hTW : mem_l hℳ T W)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hBudget : PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ B I W A Q) :
    ∀ a, point_l B I T W Q a := by
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree B |>.pushFree I |>.pushFree T |>.pushFree W |>.pushFree Q
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] := point_m
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  have hFormula (a : Raw) : φ.satisfies (η.pushFree a) ↔ point_l B I T W Q a :=
    point_formula_l K (η.pushFree a) _ _ _ _ _ _
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ) φ η
    (fun a ih => (hFormula a).mpr (step_l hBase hBI hW hTW hH hBudget
      (fun b hb => (hFormula b).mp (ih b hb))))
  exact fun a => (hFormula a).mp (hAll a)

#print axioms point_formula_l
#print axioms step_l
#print axioms bounded_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseBudgetInduction
