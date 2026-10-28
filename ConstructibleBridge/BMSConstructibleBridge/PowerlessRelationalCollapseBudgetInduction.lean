import BMSConstructibleBridge.PowerlessRelationalCollapseOrdinalCut
import BMSConstructibleBridge.PowerlessRelationalCollapseBoundedSlice
import BMSConstructibleBridge.PowerlessRelationalCollapseLimitExtension
import BMSConstructibleBridge.PowerlessRelationalCollapseTransport
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryBudgetExists

/-! # 前驱优先初段的原内部预算归纳

纯隶属 ℒ，原 Z₂。point(a) 量化同一 P 所刻画的全部原初段和局部图；
零、后继、极限三步实际产生前缀覆盖，不把覆盖字段加入预算证书。
P/Q/H/T 均允许 raw，只有 I/J 和关系 A 通过固定母层 W 获得分离参数界。
本模块是条件式预算归纳核；后续还须实际构造预算并给出原 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseBudgetInduction

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def point_m {Γ Δ : SortContext ℒ} (B A I T P Q a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
    let δ : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
    let C : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let E : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let G : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .imp (PowerlessValueBounded.formula_m (w Q) (w a) δ) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m (w B) δ C) <|
        .imp (PowerlessRelationalCollapseOrdinalCut.cut_m (w I) (w P) (w a) E) <|
          .imp (PowerlessRelationalCollapsePartial.partial_m (w A) (w I) E (w T) G)
            (.conj (SecondOrderObjectSyntax.member_m E C) (SecondOrderObjectSyntax.member_m G C))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def point_l (B A I T P Q a : Raw) : Prop :=
  ∀ δ C E G, value_l (ℳ := 𝒱) Q a δ →
    PowerlessRelativeHierarchySemantics.level_l hℳ B δ C →
      PowerlessRelationalCollapseOrdinalCut.cut_l I P a E →
        PowerlessRelationalCollapsePartial.partial_l A I E T G →
          mem_l hℳ E C ∧ mem_l hℳ G C

theorem point_formula_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B A I T P Q a : Term ℒ Γ Δ .set) :
    (point_m B A I T P Q a).satisfies η ↔
      point_l (B.eval η) (A.eval η) (I.eval η) (T.eval η) (P.eval η) (Q.eval η) (a.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, PowerlessValueBounded.formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K, PowerlessRelationalCollapseOrdinalCut.cut_formula_l,
    PowerlessRelationalCollapsePartial.formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem step_l {B γ W A I J T H α P Q a : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hAW : mem_l hℳ A W) (hJW : mem_l hℳ J W)
    (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hP : SecondOrderCollapseFunction.spec_l hℳ J I α P)
    (hExtends : PowerlessRelationalCollapseOrderedCut.extends_l I A J)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hγ : PowerlessRelativeHierarchySemantics.successor_l hℳ α γ)
    (hBudget : PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ B I W γ Q)
    (hPast : ∀ b, mem_l hℳ b a → point_l B A I T P Q b) : point_l B A I T P Q a := by
  intro δ C E G hQ hC hE hG
  have haγ := hBudget.source a δ hQ
  have hStage : mem_l hℳ a α ∨ a = α := (hγ a).mp haγ
  have hα := PowerlessRelationalCollapseOrderReading.ordinal_l hJ hP
  have ha : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a :=
    SetTheory.Structure.IsOrdinal.mem hBudget.domain_ordinal haγ
  obtain ⟨ξ, C₀, C₁, hLimit, hC₀, hCD, hDC, _hBC₀, hIC₀, hWC₀, _haC₀, hEarlier⟩ :=
    hBudget.layers a δ C hQ hC
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC₀
  have hTransT := fun x hx y hy => hH.1 x y hx hy
  have hTransD := SecondOrderMemberDefProperties.transitive_l hℳ hCD
    (fun x y hx hy => hTrans x hx y hy)
  have hSubCD := SecondOrderMemberDefProperties.contains_l hℳ hCD
    (fun x y hx hy => hTrans x hx y hy)
  have hSubDC := SecondOrderMemberDefProperties.contains_l hℳ hDC hTransD
  have hInto (x : Raw) (hx : mem_l hℳ x C₀) : mem_l hℳ x C := hSubDC x (hSubCD x hx)
  have hAC₀ := hTrans W hWC₀ A hAW
  have hJC₀ := hTrans W hWC₀ J hJW
  have hEC₀ := PowerlessRelationalCollapseOrdinalCut.member_l hBase hLimit hC₀ hIC₀ hJC₀
    hJ hP hExtends hStage hE
  have hPrefix (b : Raw) (hb : mem_l hℳ b a) :
      ∃ q E₀ G₀, mem_l hℳ q I ∧ SecondOrderFunctionObjects.value_l hℳ P q b ∧
        mem_l hℳ E₀ C₀ ∧ mem_l hℳ G₀ C₀ ∧ PowerlessRelationalCollapseOrdinalCut.cut_l I P b E₀ ∧
          PowerlessRelationalCollapsePartial.partial_l A I E₀ T G₀ ∧
          (∀ z, mem_l hℳ z I → SecondOrderFunctionObjects.value_l hℳ A z q → mem_l hℳ z E₀) ∧
            ¬mem_l hℳ q E₀ := by
    have hbα : mem_l hℳ b α := hStage.elim
      (fun haα => hα.transitive a haα b hb) (fun heq => heq ▸ hb)
    obtain ⟨q, hqI, hqb⟩ := hP.2.2.1 b hbα
    have hqC₀ := hTrans I hIC₀ q hqI
    obtain ⟨E₀, _hE₀C₀, hCut, hClosed, hCover, hNew⟩ := PowerlessRelationalCollapseOrderedCut.exists_l
      hBase hLimit hC₀ hIC₀ hJC₀ hqC₀ hqI hJ.2.1 hJ.1 hExtends
    have hRank := PowerlessRelationalCollapseOrdinalCut.of_point_l hJ hP hqb hCut
    obtain ⟨G₀, hG₀, _hRead⟩ := PowerlessRelationalCollapseRestriction.exists_l hH
      (fun x hx => ((hCut x).mp hx).1) hClosed
    obtain ⟨θ, hQb⟩ := hBudget.total b (hBudget.domain_ordinal.transitive a haγ b hb)
    obtain ⟨D, hD⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase
      (hBudget.output_ordinal b θ hQb)
    obtain ⟨hE₀D, hG₀D⟩ := hPast b hb θ D E₀ G₀ hQb hD hRank hG₀
    have hDC₀ := hEarlier b hb θ D hQb hD
    exact ⟨q, E₀, G₀, hqI, hqb, hTrans D hDC₀ E₀ hE₀D,
      hTrans D hDC₀ G₀ hG₀D, hRank, hG₀, hCover, hNew⟩
  rcases PowerlessHierarchyLightHistoryBudgetInduction.cases_l hℳ ha with hZero | ⟨b, hSucc⟩ | hLimitA
  · have hEmpty (x : Raw) (hx : mem_l hℳ x E) : False := by
      obtain ⟨_, b, hb, _⟩ := (hE x).mp hx
      exact hZero b hb
    have hEq : G = E := by
      apply SecondOrderQuotient.ext_l hℳ
      intro p
      constructor
      · intro hp
        obtain ⟨x, _y, hx, _, _⟩ := hG.2.2.1.1 p hp
        exact (hEmpty x hx).elim
      · exact fun hp => (hEmpty p hp).elim
    exact ⟨hInto E hEC₀, hInto G (hEq.symm ▸ hEC₀)⟩
  · have hb := PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc
    obtain ⟨q, E₀, G₀, hqI, hqb, hE₀C₀, hG₀C₀, hRank, hG₀, hCover, hNew⟩ := hPrefix b hb
    obtain ⟨y, hy, _⟩ := hH.2.1.2 q hqI
    obtain ⟨S, F, _hSC₀, hFC₀, hF, hAdjoin⟩ := PowerlessRelationalCollapseLimitExtension.exists_l
      hBase hLimit hC₀ hAC₀ hE₀C₀ hG₀C₀ (hTrans I hIC₀ q hqI)
        hTransT hH hG₀ hCover hqI hy.2 hNew
    have hEAdjoin := PowerlessRelationalCollapseOrdinalCut.successor_l hJ hP hSucc hqb hE hRank
    have hEqS : S = E := SecondOrderQuotient.ext_l hℳ S E
      (fun x => (hAdjoin x).trans (hEAdjoin x).symm)
    subst S
    have hEqG := PowerlessRelationalCollapseTransport.graph_eq_l hH hTrans hTransT hF hG
    exact ⟨hInto E hEC₀, hInto G (hEqG ▸ hFC₀)⟩
  · have hCover : PowerlessRelationalCollapseBoundedSlice.witness_l A I E C₀ := by
      intro x hx
      obtain ⟨_hxI, b, hb, hxb⟩ := (hE x).mp hx
      obtain ⟨c, hc, hbc⟩ := hLimitA.2 b hb
      obtain ⟨_q, E₀, G₀, _hqI, _hqc, hE₀C₀, hG₀C₀, hRank, hG₀, _hCover, _hNew⟩ := hPrefix c hc
      have hxE₀ := (hRank x).mpr ⟨hG.1 x hx, b, hbc, hxb⟩
      exact ⟨E₀, hE₀C₀, G₀, hG₀C₀, hxE₀,
        PowerlessRelationalCollapseTransport.limit_l hBase hLimit hC₀ hE₀C₀ hG₀C₀ hTransT hG₀⟩
    exact ⟨hInto E hEC₀, PowerlessRelationalCollapseBoundedSlice.member_l
      hBase hC₀ hLimit hCD hDC hAC₀ hIC₀ (hSubCD E hEC₀) hH hG hCover⟩

theorem bounded_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ) {B γ W A I J T H α P Q : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hAW : mem_l hℳ A W) (hJW : mem_l hℳ J W)
    (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hP : SecondOrderCollapseFunction.spec_l hℳ J I α P)
    (hExtends : PowerlessRelationalCollapseOrderedCut.extends_l I A J)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hγ : PowerlessRelativeHierarchySemantics.successor_l hℳ α γ)
    (hBudget : PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ B I W γ Q) :
    ∀ a, point_l B A I T P Q a := by
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree B |>.pushFree A |>.pushFree I |>.pushFree T |>.pushFree P |>.pushFree Q
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] := point_m
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
    (.fvar (.there .here)) (.fvar .here)
  have hFormula (a : Raw) : φ.satisfies (η.pushFree a) ↔ point_l B A I T P Q a :=
    point_formula_l K (η.pushFree a) _ _ _ _ _ _ _
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ) φ η
    (fun a ih => (hFormula a).mpr (step_l hBase hAW hJW hJ hP hExtends hH hγ hBudget
      (fun b hb => (hFormula b).mp (ih b hb))))
  exact fun a => (hFormula a).mp (hAll a)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseBudgetInduction
