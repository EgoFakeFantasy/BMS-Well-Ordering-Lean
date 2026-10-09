import BMSConstructibleBridge.PowerlessRelativeMembershipCollapsePartial
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseRestriction
import BMSConstructibleBridge.SecondOrderMemberDefBoundedSlice
import BMSConstructibleBridge.PowerlessRelativeLimitClosure

/-! # 有界局部解把同一实际坍缩图送入两次 Def

检查式只使用 I/T/C；原 H 不作为 Def 的自由参数。共同极限层 C 中每个
源点有一个前驱封闭的局部解时，内部一致性定理把精确图读回 H，故 H
属于 Def(Def(C))。原 Z₂ 正式推出此条件规则，不新增 ClassH 公理。
共同局部解界仍须由实际候选的预算构造；本文件不把该义务视为已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseBoundedGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def value_m {Γ Δ : SortContext ℒ} (I T C x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists C <| membershipLevyBound.boundedExists (up C) <|
    .conj (member_m (up (up x)) (.bvar (.there .here))) <| .conj
      (PowerlessRelativeMembershipCollapsePartial.partial_m (up (up I))
        (.bvar (.there .here)) (up (up T)) (.bvar .here))
      (PowerlessValueBounded.formula_m (.bvar .here) (up (up x)) (up (up y)))

def graph_m {Γ Δ : SortContext ℒ} (I T C p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists I <| membershipLevyBound.boundedExists (up T) <|
    .conj (PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (up (up p)))
      (value_m (up (up I)) (up (up T)) (up (up C)) (.bvar (.there .here)) (.bvar .here))

theorem value_delta_m {Γ Δ : SortContext ℒ} (I T C x y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (value_m I T C x y) :=
  .bounded_exists _ (.bounded_exists _ (.conj (.rel _ _)
    (.conj (PowerlessRelativeMembershipCollapsePartial.delta_m _ _ _ _)
      (PowerlessValueBounded.delta_l _ _ _))))

theorem graph_delta_m {Γ Δ : SortContext ℒ} (I T C p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (graph_m I T C p) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
    (value_delta_m _ _ _ _ _)))

/-- 极限预算步的域 E 可在 Def(C) 中；旧局部解仍检查原源 I。 -/
def slice_m {Γ Δ : SortContext ℒ} (I E T C p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists E <| membershipLevyBound.boundedExists (up T) <|
    .conj (PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (up (up p)))
      (value_m (up (up I)) (up (up T)) (up (up C)) (.bvar (.there .here)) (.bvar .here))

theorem slice_delta_m {Γ Δ : SortContext ℒ} (I E T C p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (slice_m I E T C p) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
    (value_delta_m _ _ _ _ _)))

def witness_m {Γ Δ : SortContext ℒ} (I T C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall I <| membershipLevyBound.boundedExists (up C) <|
    membershipLevyBound.boundedExists (up (up C)) <|
      .conj (member_m (.bvar (.there (.there .here))) (.bvar (.there .here)))
        (PowerlessRelativeMembershipCollapsePartial.partial_m (up (up (up I)))
          (.bvar (.there .here)) (up (up (up T))) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def witness_l (I T C : Raw) : Prop :=
  ∀ x, mem_l hℳ x I → ∃ A, mem_l hℳ A C ∧ ∃ G, mem_l hℳ G C ∧
    mem_l hℳ x A ∧ PowerlessRelativeMembershipCollapsePartial.partial_l I A T G

theorem witness_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (I T C : Term ℒ Γ Δ .set) : (witness_m I T C).satisfies η ↔
      witness_l (I.eval η) (T.eval η) (C.eval η) := by
  simp only [witness_m, witness_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, PowerlessRelativeMembershipCollapsePartial.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem graph_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (I T C p : Term ℒ Γ Δ .set) : (graph_m I T C p).satisfies η ↔
      ∃ x, mem_l hℳ x (I.eval η) ∧ ∃ y, mem_l hℳ y (T.eval η) ∧
        SecondOrderPairObjects.ordered_l hℳ x y (p.eval η) ∧
        ∃ A, mem_l hℳ A (C.eval η) ∧ ∃ G, mem_l hℳ G (C.eval η) ∧
          mem_l hℳ x A ∧ PowerlessRelativeMembershipCollapsePartial.partial_l
            (I.eval η) A (T.eval η) G ∧ SecondOrderFunctionObjects.value_l hℳ G x y := by
  simp only [graph_m, value_m, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, PowerlessRelativeMembershipCollapsePartial.formula_l,
    PowerlessValueBounded.formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem slice_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (I E T C p : Term ℒ Γ Δ .set) : (slice_m I E T C p).satisfies η ↔
      ∃ x, mem_l hℳ x (E.eval η) ∧ ∃ y, mem_l hℳ y (T.eval η) ∧
        SecondOrderPairObjects.ordered_l hℳ x y (p.eval η) ∧
        ∃ A, mem_l hℳ A (C.eval η) ∧ ∃ G, mem_l hℳ G (C.eval η) ∧
          mem_l hℳ x A ∧ PowerlessRelativeMembershipCollapsePartial.partial_l
            (I.eval η) A (T.eval η) G ∧ SecondOrderFunctionObjects.value_l hℳ G x y := by
  simp only [slice_m, value_m, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, PowerlessRelativeMembershipCollapsePartial.formula_l,
    PowerlessValueBounded.formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 有界较早局部解覆盖任意子域时，同一实际限制图进入两次 Def。 -/
theorem slice_member_l {B β C D Z I E T H F : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hCD : SecondOrderMemberDef.spec_l hℳ C D) (hDZ : SecondOrderMemberDef.spec_l hℳ D Z)
    (hIC : mem_l hℳ I C) (hTC : mem_l hℳ T C) (hED : mem_l hℳ E D)
    (hSub : ∀ x, mem_l hℳ x E → mem_l hℳ x I)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hF : SecondOrderFunctionObjects.map_l hℳ F E T)
    (hRead : ∀ x y, SecondOrderFunctionObjects.value_l hℳ F x y ↔
      mem_l hℳ x E ∧ SecondOrderFunctionObjects.value_l hℳ H x y)
    (hCover : ∀ x, mem_l hℳ x E → ∃ A, mem_l hℳ A C ∧ ∃ G, mem_l hℳ G C ∧
      mem_l hℳ x A ∧ PowerlessRelativeMembershipCollapsePartial.partial_l I A T G) :
    mem_l hℳ F Z := by
  let η : Env 𝒱 [] [.set, .set, .set, .set] :=
    Env.empty |>.pushFree T |>.pushFree I |>.pushFree E |>.pushFree C
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := slice_m
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here)) (.fvar .here)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hInto := SecondOrderMemberDefProperties.contains_l hℳ hCD
    (fun x y hx hy => hTrans x hx y hy)
  apply SecondOrderMemberDefBoundedSlice.member_l hℳ hDZ (φ := φ)
    (fun x hx y hy => SecondOrderMemberDefProperties.transitive_l hℳ hCD
      (fun a b ha hb => hTrans a ha b hb) x y hx hy) (slice_delta_m _ _ _ _ _) η
  · intro s v
    cases s
    match v with
    | .here => exact SecondOrderMemberDefProperties.mother_member_l hℳ hCD
    | .there .here => exact hED
    | .there (.there .here) => exact hInto I hIC
    | .there (.there (.there .here)) => exact hInto T hTC
  · intro p
    rw [slice_formula_l (η.pushFree p) _ _ _ _ _]
    constructor
    · intro hp
      obtain ⟨x, y, hx, hy, hPair⟩ := hF.1 p hp
      obtain ⟨A, hAC, G, hGC, hxA, hG⟩ := hCover x hx
      have hHxy := ((hRead x y).mp ⟨p, hp, hPair⟩).2
      have hGxy := (PowerlessRelativeMembershipCollapsePartial.value_l
        hH.2.1 hH.2.2.2.1 hH.1 hG hxA).mpr hHxy
      have hpC := PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hC
        (hTrans I hIC x (hSub x hx)) (hTrans T hTC y hy) hPair
      exact ⟨hInto p hpC, x, hx, y, hy, hPair, A, hAC, G, hGC, hxA, hG, hGxy⟩
    · rintro ⟨_, x, hx, y, _, hPair, A, _, G, _, hxA, hG, hGxy⟩
      obtain ⟨q, hq, hPair'⟩ := (hRead x y).mpr ⟨hx,
        (PowerlessRelativeMembershipCollapsePartial.value_l hH.2.1 hH.2.2.2.1 hH.1 hG hxA).mp hGxy⟩
      have hEq : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair
      exact hEq ▸ hq

/-- 精确切片的所有自由参数都在 Def(C) 中，H 不在参数环境中。 -/
theorem member_l {B β C D E I T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hCD : SecondOrderMemberDef.spec_l hℳ C D) (hDE : SecondOrderMemberDef.spec_l hℳ D E)
    (hIC : mem_l hℳ I C) (hTC : mem_l hℳ T C)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H) (hWitness : witness_l I T C) :
    mem_l hℳ H E := by
  let η : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree T).pushFree I).pushFree C
  let φ : Formula ℒ [] [.set, .set, .set, .set] := graph_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there .here)) (.fvar .here)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hSub := SecondOrderMemberDefProperties.contains_l hℳ hCD (fun x y hx hy => hTrans x hx y hy)
  apply SecondOrderMemberDefBoundedSlice.member_l hℳ hDE (φ := φ)
    (fun x hx y hy => SecondOrderMemberDefProperties.transitive_l hℳ hCD
      (fun a b ha hb => hTrans a ha b hb) x y hx hy) (graph_delta_m _ _ _ _) η
  · intro s v
    cases s
    match v with
    | .here => exact SecondOrderMemberDefProperties.mother_member_l hℳ hCD
    | .there .here => exact hSub I hIC
    | .there (.there .here) => exact hSub T hTC
  · intro p
    rw [graph_formula_l (η.pushFree p) _ _ _ _]
    constructor
    · intro hp
      obtain ⟨x, y, hx, hy, hPair⟩ := hH.2.1.1 p hp
      have hpC := PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hC
        (hTrans I hIC x hx) (hTrans T hTC y hy) hPair
      obtain ⟨A, hAC, G, hGC, hxA, hG⟩ := hWitness x hx
      have hxy : SecondOrderFunctionObjects.value_l hℳ H x y := ⟨p, hp, hPair⟩
      have hGxy := (PowerlessRelativeMembershipCollapsePartial.value_l hH.2.1
        hH.2.2.2.1 hH.1 hG hxA).mpr hxy
      exact ⟨hSub p hpC, x, hx, y, hy, hPair, A, hAC, G, hGC, hxA, hG, hGxy⟩
    · rintro ⟨_, x, _, y, _, hPair, A, _, G, _, hxA, hG, hGxy⟩
      obtain ⟨q, hq, hPair'⟩ := (PowerlessRelativeMembershipCollapsePartial.value_l
        hH.2.1 hH.2.2.2.1 hH.1 hG hxA).mp hGxy
      have hEq : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair
      exact hEq ▸ hq

/-- 后继层真实存在性消去两次 Def 见证，不把 ClassH 当作前提。 -/
theorem class_l {B β C I T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hIC : mem_l hℳ I C) (hTC : mem_l hℳ T C)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H) (hWitness : witness_l I T C) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B H := by
  obtain ⟨δ, D, _, hD, hCD⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hC
  obtain ⟨ε, E, _, hE, hDE⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hD
  exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hE)
    (member_l hBase hC hLimit hCD hDE hIC hTC hH hWitness)

def schema_m {Δ : SortContext ℒ} (B β C I T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <| .imp (member_m I C) <|
        .imp (member_m T C) <| .imp (PowerlessRelativeMembershipCollapse.spec_m I T H) <|
          .imp (witness_m I T C) (PowerlessRelativeHierarchySyntax.class_m B H)

def sentence_m {Δ : SortContext ℒ} (B β C I T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β C I T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β C I T H : Term ℒ [] Δ .set) : (sentence_m B β C I T H).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeMembershipCollapse.spec_formula_l, witness_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, member_m, Arguments.eval]
  exact fun hBase hC hLimit hIC hTC hH hWitness => class_l hBase hC hLimit hIC hTC hH hWitness

theorem derives_m {Δ : SortContext ℒ} (B β C I T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B β C I T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β C I T H)

#print axioms graph_delta_m
#print axioms slice_delta_m
#print axioms slice_member_l
#print axioms member_l
#print axioms class_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseBoundedGraph
