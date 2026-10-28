import BMSConstructibleBridge.PowerlessKleeneBrouwerPredecessorOrder

/-! # 根覆盖数码域上的实际前驱优先索引

纯隶属 ℒ，原 Z₂。调用端给定同根路径覆盖原 I；证明内构造 Class 路径集、
可达域、末节点满射和 KB 环境良序。覆盖方程识别可达域为原 I，再得到
无垃圾的前驱优先 Class J。没有预供 J、枚举或 Class H/T。
根覆盖与原坍缩 H 存在仍是明确条件，不能冒充任意根码的无条件结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerNumericIndex

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerPath (path_l path_m path_formula_l)
open PowerlessKleeneBrouwerEndpoint (endpoint_l endpoint_m endpoint_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def cover_m {Γ Δ : SortContext ℒ} (ω I A z r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall I <| .existsE .set <|
    .conj (path_m (up (up ω)) (up (up I)) (up (up A)) (up (up z)) (up (up r)) (.bvar .here))
      (endpoint_m (up (up ω)) (up (up I)) (.bvar .here) (.bvar (.there .here)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def cover_l (ω I A z r : Raw) : Prop :=
  ∀ a, mem_l hℳ a I → ∃ f, path_l (𝒩 := 𝒱) ω I A z r f ∧ endpoint_l ω I f a

theorem cover_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (ω I A z r : Term ℒ Γ Δ .set) :
    (cover_m ω I A z r).satisfies η ↔ cover_l (ω.eval η) (I.eval η) (A.eval η) (z.eval η) (r.eval η) := by
  simp only [cover_m, cover_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, path_formula_l, endpoint_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_l {B ω I A z r T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ b, mem_l hℳ b I → mem_l hℳ b ω)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z) (hz : mem_l hℳ z ω) (hr : mem_l hℳ r I)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H) (hCover : cover_l ω I A z r) :
    ∃ J, PowerlessRelativeClassCorrespondence.member_l hℳ B J ∧
      SecondOrderRegularRelation.relation_l hℳ J I ∧ wellOrder_l (ℳ := 𝒱) I J ∧
        PowerlessRelationalCollapseOrderedCut.extends_l I A J := by
  obtain ⟨S, R, hSClass, hRClass, hS, hReadR, hR⟩ :=
    PowerlessKleeneBrouwerPathWellOrder.exists_l hBase hω hI hA hSub hZero hz hr hH
  obtain ⟨D, hDClass, hD, _hClosed⟩ := PowerlessKleeneBrouwerReachable.exists_l hBase hω hI hSClass hS
  have hSame : D = I := by
    apply SecondOrderQuotient.ext_l hℳ
    intro a
    constructor
    · exact fun ha => ((hD a).mp ha).1
    · intro ha
      obtain ⟨f, hPath, hEnd⟩ := hCover a ha
      exact (hD a).mpr ⟨ha, f, (hS f).mpr hPath, hEnd⟩
  subst D
  obtain ⟨F, hFClass, hMapF, hOntoF, hReadF⟩ :=
    PowerlessKleeneBrouwerEndpointMap.exists_l hBase hω hI hSClass hDClass hS hD
  exact PowerlessKleeneBrouwerPredecessorOrder.exists_l hBase hω hSub hSClass hDClass hFClass hRClass
    hS hD hMapF hOntoF hReadF hR hReadR

def schema_m {Δ : SortContext ℒ} (B ω I A z r T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (ThirdOrderTheory.subset_m I ω) <| .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
        .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up z)))) <|
          .imp (SecondOrderObjectSyntax.member_m z ω) <| .imp (SecondOrderObjectSyntax.member_m r I) <|
            .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
              .imp (cover_m ω I A z r) (PowerlessKleeneBrouwerPredecessorOrder.result_m B I A)

def sentence_m {Δ : SortContext ℒ} (B ω I A z r T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω I A z r T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω I A z r T H : Term ℒ [] Δ .set) : (sentence_m B ω I A z r T H).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, PowerlessKleeneBrouwerPredecessorOrder.result_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, subset_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, SecondOrderCollapseSyntax.formula_l, cover_formula_l,
    SecondOrderRelationSyntax.relation_l, PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessRelationalCollapseOrderedCut.extends_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact exists_l (hℳ := hℳ)

theorem derives_m {Δ : SortContext ℒ} (B ω I A z r T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω I A z r T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω I A z r T H)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerNumericIndex
