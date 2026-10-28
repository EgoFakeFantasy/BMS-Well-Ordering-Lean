import BMSConstructibleBridge.PowerlessRelationalCollapsePartial
import BMSConstructibleBridge.SecondOrderMemberDefBoundedSlice
import BMSConstructibleBridge.PowerlessRelativeLimitClosure

/-! # 不预设全值域资格的有界关系坍缩图

纯隶属 ℒ，原 Z₂。检查器仅以源关系 A、源 I、共同传递母界 C 为参数，
不把原全值域 T 或全图 H 放进 Def 环境。局部解的内部一致性使同一 H
成为 Def(Def(C)) 的实际成员。共同局部解界仍须构造，不是新增公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseBoundedGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def value_m {Γ Δ : SortContext ℒ} (A I C x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists C <| membershipLevyBound.boundedExists (up C) <|
    .conj (member_m (up (up x)) (.bvar (.there .here))) <| .conj
      (PowerlessRelationalCollapsePartial.partial_m (up (up A)) (up (up I))
        (.bvar (.there .here)) (up (up C)) (.bvar .here))
      (PowerlessValueBounded.formula_m (.bvar .here) (up (up x)) (up (up y)))

def graph_m {Γ Δ : SortContext ℒ} (A I C p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists I <| membershipLevyBound.boundedExists (up C) <|
    .conj (PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (up (up p)))
      (value_m (up (up A)) (up (up I)) (up (up C)) (.bvar (.there .here)) (.bvar .here))

theorem graph_delta_m {Γ Δ : SortContext ℒ} (A I C p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (graph_m A I C p) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
    (.bounded_exists _ (.bounded_exists _ (.conj (.rel _ _)
      (.conj (PowerlessRelationalCollapsePartial.delta_m _ _ _ _ _)
        (PowerlessValueBounded.delta_l _ _ _)))))))

def witness_m {Γ Δ : SortContext ℒ} (A I C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall I <| membershipLevyBound.boundedExists (up C) <|
    membershipLevyBound.boundedExists (up (up C)) <|
      .conj (member_m (.bvar (.there (.there .here))) (.bvar (.there .here)))
        (PowerlessRelationalCollapsePartial.partial_m (up (up (up A))) (up (up (up I)))
          (.bvar (.there .here)) (up (up (up C))) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def witness_l (A I C : Raw) : Prop :=
  ∀ x, mem_l hℳ x I → ∃ E, mem_l hℳ E C ∧ ∃ G, mem_l hℳ G C ∧
    mem_l hℳ x E ∧ PowerlessRelationalCollapsePartial.partial_l A I E C G

theorem witness_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (A I C : Term ℒ Γ Δ .set) : (witness_m A I C).satisfies η ↔
      witness_l (A.eval η) (I.eval η) (C.eval η) := by
  simp only [witness_m, witness_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, PowerlessRelationalCollapsePartial.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem graph_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (A I C p : Term ℒ Γ Δ .set) : (graph_m A I C p).satisfies η ↔
      ∃ x, mem_l hℳ x (I.eval η) ∧ ∃ y, mem_l hℳ y (C.eval η) ∧
        SecondOrderPairObjects.ordered_l hℳ x y (p.eval η) ∧
        ∃ E, mem_l hℳ E (C.eval η) ∧ ∃ G, mem_l hℳ G (C.eval η) ∧
          mem_l hℳ x E ∧ PowerlessRelationalCollapsePartial.partial_l
            (A.eval η) (I.eval η) E (C.eval η) G ∧ SecondOrderFunctionObjects.value_l hℳ G x y := by
  simp only [graph_m, value_m, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, PowerlessRelationalCollapsePartial.formula_l,
    PowerlessValueBounded.formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 局部解的总定义与一致性给出全图的逐值界，无需 T 已在母界中。 -/
theorem value_bound_l {A I T H C : Raw}
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hC : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C)
    (hWitness : witness_l A I C) {x y : Raw}
    (hx : mem_l hℳ x I) (hxy : SecondOrderFunctionObjects.value_l hℳ H x y) :
    mem_l hℳ y C := by
  obtain ⟨E, _, G, _, hxE, hG⟩ := hWitness x hx
  exact (SecondOrderFunctionProperties.value_mem_l hℳ hG.2.2.1
    ((PowerlessRelationalCollapsePartial.value_l hH hC hG hxE).mpr hxy)).2

theorem member_l {B β C D Z A I T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hCD : SecondOrderMemberDef.spec_l hℳ C D) (hDZ : SecondOrderMemberDef.spec_l hℳ D Z)
    (hAC : mem_l hℳ A C) (hIC : mem_l hℳ I C)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H) (hWitness : witness_l A I C) :
    mem_l hℳ H Z := by
  let η : Env 𝒱 [] [.set, .set, .set] := Env.empty |>.pushFree A |>.pushFree I |>.pushFree C
  let φ : Formula ℒ [] [.set, .set, .set, .set] := graph_m
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
    (.fvar (.there .here)) (.fvar .here)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hSub := SecondOrderMemberDefProperties.contains_l hℳ hCD (fun x y hx hy => hTrans x hx y hy)
  apply SecondOrderMemberDefBoundedSlice.member_l hℳ hDZ (φ := φ)
    (fun x hx y hy => SecondOrderMemberDefProperties.transitive_l hℳ hCD
      (fun a b ha hb => hTrans a ha b hb) x y hx hy) (graph_delta_m _ _ _ _) η
  · intro s v
    cases s
    match v with
    | .here => exact SecondOrderMemberDefProperties.mother_member_l hℳ hCD
    | .there .here => exact hSub I hIC
    | .there (.there .here) => exact hSub A hAC
  · intro p
    rw [graph_formula_l (η.pushFree p) _ _ _ _]
    constructor
    · intro hp
      obtain ⟨x, y, hx, _, hPair⟩ := hH.2.1.1 p hp
      have hxy : SecondOrderFunctionObjects.value_l hℳ H x y := ⟨p, hp, hPair⟩
      have hyC := value_bound_l hH hTrans hWitness hx hxy
      have hpC := PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hC
        (hTrans I hIC x hx) hyC hPair
      obtain ⟨E, hEC, G, hGC, hxE, hG⟩ := hWitness x hx
      exact ⟨hSub p hpC, x, hx, y, hyC, hPair, E, hEC, G, hGC, hxE, hG,
        (PowerlessRelationalCollapsePartial.value_l hH hTrans hG hxE).mpr hxy⟩
    · rintro ⟨_, x, _, y, _, hPair, E, _, G, _, hxE, hG, hGxy⟩
      obtain ⟨q, hq, hPair'⟩ := (PowerlessRelationalCollapsePartial.value_l hH hTrans hG hxE).mp hGxy
      have hEq : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair
      exact hEq ▸ hq

/-- 两次后继层均实际存在；结论保持原 H，不另选一个等价图。 -/
theorem class_l {B β C A I T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hAC : mem_l hℳ A C) (hIC : mem_l hℳ I C)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H) (hWitness : witness_l A I C) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B H := by
  obtain ⟨δ, D, _, hD, hCD⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hC
  obtain ⟨ε, Z, _, hZ, hDZ⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hD
  exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hZ)
    (member_l hBase hC hLimit hCD hDZ hAC hIC hH hWitness)

def schema_m {Δ : SortContext ℒ} (B β C A I T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <| .imp (member_m A C) <|
        .imp (member_m I C) <| .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
          .imp (witness_m A I C) (PowerlessRelativeHierarchySyntax.class_m B H)

def sentence_m {Δ : SortContext ℒ} (B β C A I T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β C A I T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β C A I T H : Term ℒ [] Δ .set) : (sentence_m B β C A I T H).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.limit_formula_l, SecondOrderCollapseSyntax.formula_l,
    witness_formula_l, PowerlessRelativeHierarchySemantics.class_formula_l K, member_m, Arguments.eval]
  exact fun hBase hC hLimit hAC hIC hH hWitness => class_l hBase hC hLimit hAC hIC hH hWitness

theorem derives_m {Δ : SortContext ℒ} (B β C A I T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B β C A I T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β C A I T H)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseBoundedGraph
