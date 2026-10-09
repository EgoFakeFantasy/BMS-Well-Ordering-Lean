import BMSConstructibleBridge.PowerlessRelationalCollapseRestriction
import BMSConstructibleBridge.PowerlessRelationalCollapseBoundedGraph
import BMSConstructibleBridge.PowerlessMemberDefDerives

/-! # 有界较早局部解的精确合并切片

纯隶属 ℒ，原 Z₂。共同极限母层 C 中的较早局部解覆盖封闭源 E，
则原 H↾E 的实际限制图 F 属于 Def(Def(C))。F 先由原二阶理解
构造，再由内部一致性认同有界切片，不预供 ClassF 或 ClassT。
覆盖的共同界仍须由实际预算取得，不能把本接口误记为无限界已构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseBoundedSlice

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def slice_m {Γ Δ : SortContext ℒ} (A I E C p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists E <| membershipLevyBound.boundedExists (up C) <|
    .conj (PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (up (up p)))
      (PowerlessRelationalCollapseBoundedGraph.value_m (up (up A)) (up (up I))
        (up (up C)) (.bvar (.there .here)) (.bvar .here))

theorem delta_m {Γ Δ : SortContext ℒ} (A I E C p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (slice_m A I E C p) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
    (.bounded_exists _ (.bounded_exists _ (.conj (.rel _ _)
      (.conj (PowerlessRelationalCollapsePartial.delta_m _ _ _ _ _) (PowerlessValueBounded.delta_l _ _ _)))))))

def witness_m {Γ Δ : SortContext ℒ} (A I E C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall E <| membershipLevyBound.boundedExists (up C) <|
    membershipLevyBound.boundedExists (up (up C)) <|
      .conj (member_m (.bvar (.there (.there .here))) (.bvar (.there .here)))
        (PowerlessRelationalCollapsePartial.partial_m (up (up (up A))) (up (up (up I)))
          (.bvar (.there .here)) (up (up (up C))) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def witness_l (A I E C : Raw) : Prop :=
  ∀ x, mem_l hℳ x E → ∃ E₀, mem_l hℳ E₀ C ∧ ∃ G, mem_l hℳ G C ∧
    mem_l hℳ x E₀ ∧ PowerlessRelationalCollapsePartial.partial_l A I E₀ C G

theorem witness_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (A I E C : Term ℒ Γ Δ .set) : (witness_m A I E C).satisfies η ↔
      witness_l (A.eval η) (I.eval η) (E.eval η) (C.eval η) := by
  simp only [witness_m, witness_l, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessRelationalCollapsePartial.formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem slice_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (A I E C p : Term ℒ Γ Δ .set) : (slice_m A I E C p).satisfies η ↔
      ∃ x, mem_l hℳ x (E.eval η) ∧ ∃ y, mem_l hℳ y (C.eval η) ∧
        SecondOrderPairObjects.ordered_l hℳ x y (p.eval η) ∧
        ∃ E₀, mem_l hℳ E₀ (C.eval η) ∧ ∃ G, mem_l hℳ G (C.eval η) ∧
          mem_l hℳ x E₀ ∧ PowerlessRelationalCollapsePartial.partial_l (A.eval η) (I.eval η) E₀ (C.eval η) G ∧
            SecondOrderFunctionObjects.value_l hℳ G x y := by
  simp only [slice_m, PowerlessRelationalCollapseBoundedGraph.value_m, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, PowerlessRelationalCollapsePartial.formula_l,
    PowerlessValueBounded.formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem member_l {B β C D Z A I E T H F : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hCD : SecondOrderMemberDef.spec_l hℳ C D) (hDZ : SecondOrderMemberDef.spec_l hℳ D Z)
    (hAC : mem_l hℳ A C) (hIC : mem_l hℳ I C) (hED : mem_l hℳ E D)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hF : PowerlessRelationalCollapsePartial.partial_l A I E T F)
    (hCover : witness_l A I E C) : mem_l hℳ F Z := by
  let η : Env 𝒱 [] [.set, .set, .set, .set] := Env.empty |>.pushFree A |>.pushFree I |>.pushFree E |>.pushFree C
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := slice_m
    (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hTransT := fun a ha b hb => hH.1 a b ha hb
  have hSub := SecondOrderMemberDefProperties.contains_l hℳ hCD (fun x y hx hy => hTrans x hx y hy)
  apply SecondOrderMemberDefBoundedSlice.member_l hℳ hDZ (φ := φ)
    (fun x hx y hy => SecondOrderMemberDefProperties.transitive_l hℳ hCD
      (fun a b ha hb => hTrans a ha b hb) x y hx hy) (delta_m _ _ _ _ _) η
  · intro s v
    cases s
    match v with
    | .here => exact SecondOrderMemberDefProperties.mother_member_l hℳ hCD
    | .there .here => exact hED
    | .there (.there .here) => exact hSub I hIC
    | .there (.there (.there .here)) => exact hSub A hAC
  · intro p
    rw [slice_formula_l (η.pushFree p) _ _ _ _ _]
    constructor
    · intro hp
      obtain ⟨x, y, hx, _, hPair⟩ := hF.2.2.1.1 p hp
      obtain ⟨E₀, hE₀C, G, hGC, hxE₀, hG⟩ := hCover x hx
      have hFxy : SecondOrderFunctionObjects.value_l hℳ F x y := ⟨p, hp, hPair⟩
      have hHxy := (PowerlessRelationalCollapsePartial.value_l hH hTransT hF hx).mp hFxy
      have hGxy := (PowerlessRelationalCollapsePartial.value_l hH hTrans hG hxE₀).mpr hHxy
      have hyC := (SecondOrderFunctionProperties.value_mem_l hℳ hG.2.2.1 hGxy).2
      have hpC := PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hC
        (hTrans I hIC x (hF.1 x hx)) hyC hPair
      exact ⟨hSub p hpC, x, hx, y, hyC, hPair, E₀, hE₀C, G, hGC, hxE₀, hG, hGxy⟩
    · rintro ⟨_, x, hx, y, _, hPair, E₀, _, G, _, hxE₀, hG, hGxy⟩
      have hHxy := (PowerlessRelationalCollapsePartial.value_l hH hTrans hG hxE₀).mp hGxy
      obtain ⟨q, hq, hPair'⟩ := (PowerlessRelationalCollapsePartial.value_l hH hTransT hF hx).mpr hHxy
      have hEq : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair
      exact hEq ▸ hq

/-- 限制图先真正存在，再送入指定两次 Def；不要求调用端预供 F。 -/
theorem exists_l {B β C D Z A I E T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hCD : SecondOrderMemberDef.spec_l hℳ C D) (hDZ : SecondOrderMemberDef.spec_l hℳ D Z)
    (hAC : mem_l hℳ A C) (hIC : mem_l hℳ I C) (hED : mem_l hℳ E D)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hSub : ∀ x, mem_l hℳ x E → mem_l hℳ x I)
    (hClosed : ∀ x, mem_l hℳ x E → ∀ a, mem_l hℳ a I →
      SecondOrderFunctionObjects.value_l hℳ A a x → mem_l hℳ a E)
    (hCover : witness_l A I E C) :
    ∃ F, mem_l hℳ F Z ∧ PowerlessRelationalCollapsePartial.partial_l A I E T F := by
  obtain ⟨F, hF, _⟩ := PowerlessRelationalCollapseRestriction.exists_l hH hSub hClosed
  exact ⟨F, member_l hBase hC hLimit hCD hDZ hAC hIC hED hH hF hCover, hF⟩

def result_m {Γ Δ : SortContext ℒ} (A I E T Z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (member_m (.bvar .here) (up Z))
    (PowerlessRelationalCollapsePartial.partial_m (up A) (up I) (up E) (up T) (.bvar .here))

theorem result_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (A I E T Z : Term ℒ Γ Δ .set) : (result_m A I E T Z).satisfies η ↔
      ∃ F, mem_l hℳ F (Z.eval η) ∧
        PowerlessRelationalCollapsePartial.partial_l (A.eval η) (I.eval η) (E.eval η) (T.eval η) F := by
  simp only [result_m, Formula.satisfies, PowerlessRelationalCollapsePartial.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (B β C D Z A I E T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (PowerlessMemberDefSyntax.global_m C D) <| .imp (PowerlessMemberDefSyntax.global_m D Z) <|
          .imp (member_m A C) <| .imp (member_m I C) <| .imp (member_m E D) <|
            .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
              .imp (PowerlessRelativeMembershipCollapsePartial.subset_m E I) <|
                .imp (PowerlessRelationalCollapsePartial.closed_m A I E) <|
                  .imp (witness_m A I E C) (result_m A I E T Z)

def sentence_m {Δ : SortContext ℒ} (B β C D Z A I E T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β C D Z A I E T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β C D Z A I E T H : Term ℒ [] Δ .set) : (sentence_m B β C D Z A I E T H).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, result_formula_l,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K, PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessMemberDefDerives.formula_l K, SecondOrderCollapseSyntax.formula_l,
    PowerlessRelativeMembershipCollapsePartial.subset_m, PowerlessRelationalCollapseRestriction.closed_formula_l,
    witness_formula_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership, membershipLevyBound,
    member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  exact fun hBase hC hLimit hCD hDZ hAC hIC hED hH hSub hClosed hCover =>
    exists_l hBase hC hLimit hCD hDZ hAC hIC hED hH hSub hClosed hCover

theorem derives_m {Δ : SortContext ℒ} (B β C D Z A I E T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B β C D Z A I E T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β C D Z A I E T H)

#print axioms delta_m
#print axioms member_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseBoundedSlice
