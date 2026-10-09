import BMSConstructibleBridge.PowerlessRelativeFiniteProgramSeedClosedImage
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramTaggedClosure
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramLevelDomain
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramInitialFrame
import BMSConstructibleBridge.PowerlessRelativeFiniteNumeralTags

/-! # 四张实际图生成同一个真实可数闭包

原 Z₂、纯隶属语言。原种子满射和四张 Class 的 W→W 图保持不变；
证明内构造数码标签、字母表、全程序域及空初始帧，消费原对象程序像规则。
所得同一个 I 属于 Class、类内可数、包含 C，且对四图的全部实际值闭合。
不预供 I 或操作闭包，不要求任一图属于 W，不把 Class 可数性升级成层内图界。
这是候选装配的语义中间接口；所消费的程序像规则已有原 Z₂ Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramFourGraphImage

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_empty_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev context_m : SortContext ℒ := List.replicate 19 .set
private def term_m (i : Fin 19) : Term ℒ [] context_m .set :=
  .fvar (SetTheory.Definitional.Project.fo_bound_variable i)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem image_l {Δ : SortContext ℒ}
    (K : source_coding_l hℳ) {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env 𝒱 [] Δ)
    (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set)
    (hParams : (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Δ B
      (fun v => .fvar v)).satisfies η)
    (hGuard : PowerlessRelativeFiniteProgramEvaluationBounded.guard_l φ η
      (B.eval η) (β.eval η) (C.eval η) (W.eval η) (ω.eval η) (Q.eval η)
      (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η))
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l
      (B.eval η) (ω.eval η) (Q.eval η) (S.eval η) (P.eval η))
    (hMap : map_l (ℳ := 𝒱) (G.eval η) (ω.eval η) (C.eval η))
    (hOnto : ∀ x, mem_l hℳ x (C.eval η) →
      ∃ i, mem_l hℳ i (ω.eval η) ∧ value_l (ℳ := 𝒱) (G.eval η) i x)
    (hAlphabet : ∀ q, mem_l hℳ q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l
        (C.eval η) (ω.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hBC : mem_l hℳ (B.eval η) (C.eval η)) :
    ∃ I : type_l hℳ (B.eval η),
      PowerlessRelativeOrdinalCutoff.countable_l (B.eval η) (ω.eval η) I.val ∧
      (∀ x, mem_l hℳ x I.val → mem_l hℳ x (W.eval η)) ∧
      (∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x I.val) ∧
      (∀ x y, mem_l hℳ x I.val → mem_l hℳ y I.val →
        ∃ s, mem_l hℳ s I.val ∧ ordered_l (ℳ := 𝒱) x y s) ∧
      (∀ x y, mem_l hℳ x I.val →
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y →
          φ.satisfies ((η.pushFree x).pushFree y) → mem_l hℳ y I.val) := by
  have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeFiniteProgramSeedClosedImage.models_l hℳ hφ
      B β C W ω Q G e t₀ t₁ t₂ a S P) η
  simp only [PowerlessRelativeFiniteProgramSeedClosedImage.schema_m, Formula.satisfies] at h
  have hI := h hParams
    ((PowerlessRelativeFiniteProgramEvaluationBounded.guard_formula_l K φ η
      B β C W ω Q e t₀ t₁ t₂ a).mpr (by simpa only [parameters_empty_l] using hGuard))
    ((PowerlessRelativeFiniteProgramDomain.domain_formula_l K η B ω Q S P).mpr hDomain)
    ((map_formula_l η G ω C).mpr hMap)
    ((PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l η G ω C).mpr hOnto)
    ((PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l η C ω t₀ t₁ t₂ Q).mpr hAlphabet) hBC
  simp only [PowerlessRelativeFiniteProgramSeedClosedImage.conclusion_m,
    PowerlessRelativeFiniteProgramImageRealization.conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, subset_formula_l,
    PowerlessRelativeFiniteProgramEvaluationGraph.image_formula_l K,
    PowerlessRelativeFiniteProgramImageRealization.image_formula_l K,
    PowerlessRelativeFiniteProgramImageClosure.closure_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, parameters_pushBound_l, parameters_empty_l,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] at hI
  obtain ⟨I, hIC, hCount, hBound, _hImage, ⟨hSeed, _hActual⟩, hPair, hCall⟩ := hI
  exact ⟨⟨I, hIC⟩, hCount, hBound, hSeed, hPair, hCall⟩

theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {β W : Raw}
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (hBW : mem_l hℳ B W) (C G ω P U J F : type_l hℳ B)
    (hω : SecondOrderOmega.omega_l hℳ ω.val) (hωW : mem_l hℳ ω.val W)
    (hCW : ∀ x, mem_l hℳ x C.val → mem_l hℳ x W)
    (hωC : ∀ x, mem_l hℳ x ω.val → mem_l hℳ x C.val) (hBC : mem_l hℳ B C.val)
    (hG : map_l (ℳ := 𝒱) G.val ω.val C.val)
    (hOnto : ∀ x, mem_l hℳ x C.val → ∃ i, mem_l hℳ i ω.val ∧ value_l (ℳ := 𝒱) G.val i x)
    (hP : map_l (ℳ := 𝒱) P.val W W) (hU : map_l (ℳ := 𝒱) U.val W W)
    (hJ : map_l (ℳ := 𝒱) J.val W W) (hF : map_l (ℳ := 𝒱) F.val W W) :
    ∃ I : type_l hℳ B, PowerlessRelativeOrdinalCutoff.countable_l B ω.val I.val ∧
      (∀ x, mem_l hℳ x I.val → mem_l hℳ x W) ∧
      (∀ x, mem_l hℳ x C.val → mem_l hℳ x I.val) ∧
      (∀ x y, mem_l hℳ x I.val → mem_l hℳ y I.val →
        ∃ s, mem_l hℳ s I.val ∧ ordered_l (ℳ := 𝒱) x y s) ∧
      (∀ x y, mem_l hℳ x I.val → value_l (ℳ := 𝒱) P.val x y → mem_l hℳ y I.val) ∧
      (∀ x y, mem_l hℳ x I.val → value_l (ℳ := 𝒱) U.val x y → mem_l hℳ y I.val) ∧
      (∀ x y, mem_l hℳ x I.val → value_l (ℳ := 𝒱) J.val x y → mem_l hℳ y I.val) ∧
      (∀ x y, mem_l hℳ x I.val → value_l (ℳ := 𝒱) F.val x y → mem_l hℳ y I.val) := by
  have hClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hW
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  let b : type_l hℳ B := ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let α : type_l hℳ B := ⟨β, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hW)⟩
  let V : type_l hℳ B := ⟨W, hClass⟩
  let t (i : Nat) : type_l hℳ B := ⟨PowerlessRelativeFiniteNumeralTags.value_l K i,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
      (PowerlessRelativeFiniteNumeralTags.member_l K hω i)⟩
  have htW (i : Nat) : mem_l hℳ (t i).val W :=
    hTrans ω.val hωW (t i).val (PowerlessRelativeFiniteNumeralTags.member_l K hω i)
  obtain ⟨Q, S, D, hQ, hAlphabet, hQW, hDomain⟩ :=
    PowerlessRelativeFiniteProgramLevelDomain.exists_l hBase hLimit hW C.property hω ω.property
      hCW (hTrans ω.val hωW) (htW 0) (htW 1) (htW 2)
  obtain ⟨e, a, he, ha, heC, haC, _heW, _haW⟩ :=
    PowerlessRelativeFiniteProgramInitialFrame.exists_l hBase hLimit hW hω hωW
  let η : Env (structure_l hℳ B hBase) [] context_m :=
    Env.empty (M := structure_l hℳ B hBase) |>.pushFree b |>.pushFree α |>.pushFree C
      |>.pushFree V |>.pushFree ω |>.pushFree G |>.pushFree ⟨Q, hQ⟩
      |>.pushFree ⟨S, hDomain.1⟩ |>.pushFree ⟨D, hDomain.2.2.1⟩
      |>.pushFree ⟨e, heC⟩ |>.pushFree ⟨a, haC⟩
      |>.pushFree (t 0) |>.pushFree (t 1) |>.pushFree (t 2) |>.pushFree (t 3)
      |>.pushFree P |>.pushFree U |>.pushFree J |>.pushFree F
  let ξ := PowerlessRelativeClassRelativization.env_l η
  let E := [(term_m 7, term_m 3), (term_m 6, term_m 2),
    (term_m 5, term_m 1), (term_m 4, term_m 0)]
  let φ := PowerlessRelativeFiniteProgramTaggedOperator.relation_m (term_m 15) E
  have hMaps : ∀ p ∈ E, map_l (ℳ := 𝒱) (p.2.eval ξ) W W := by
    intro p hp
    simp only [E, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact hP
    · exact hU
    · exact hJ
    · exact hF
  have hCoherent : ∀ p ∈ E, ∀ q ∈ E, p.1.eval ξ = q.1.eval ξ → p.2.eval ξ = q.2.eval ξ := by
    intro p hp q hq hEq
    simp only [E, List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
    all_goals first | rfl | (have h := PowerlessRelativeFiniteNumeralTags.injective_l K hEq; cases h)
  have ht : (t 0).val ≠ (t 1).val ∧ (t 0).val ≠ (t 2).val ∧ (t 1).val ≠ (t 2).val := by
    refine ⟨?_, ?_, ?_⟩ <;> intro hEq
    all_goals have h := PowerlessRelativeFiniteNumeralTags.injective_l K hEq; cases h
  have hFunctional := PowerlessRelativeFiniteProgramTaggedOperator.functional_l
    (term_m 15) E ξ B hMaps hCoherent
  have hClosed := PowerlessRelativeFiniteProgramTaggedOperator.closed_l (term_m 15) E ξ B hMaps
  have hParams := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l
    K context_m ξ (term_m 18) (fun v => .fvar v)).mpr (fun _ v => (η.freeVal v).property)
  have hGuard : PowerlessRelativeFiniteProgramEvaluationBounded.guard_l φ ξ B β C.val W ω.val
      Q e (t 0).val (t 1).val (t 2).val a :=
    ⟨hBase, hLimit, hW, hBW, C.property, hCW, hω, hωW, hQW, he, ha, ht, hFunctional, hClosed⟩
  obtain ⟨I, hCount, hBound, hSeed, hPair, hCall⟩ := image_l K
    (PowerlessRelativeFiniteProgramTaggedOperator.delta_l (term_m 15) E) ξ
    (term_m 18) (term_m 17) (term_m 16) (term_m 15) (term_m 14) (term_m 12) (term_m 13)
    (term_m 9) (term_m 7) (term_m 6) (term_m 5) (term_m 8) (term_m 11) (term_m 10)
    hParams hGuard hDomain hG hOnto hAlphabet hBC
  have hGraph (p : Term ℒ [] context_m .set × Term ℒ [] context_m .set) (hp : p ∈ E)
      (hTag : mem_l hℳ (p.1.eval ξ) C.val) :
      ∀ x y : Raw, mem_l hℳ x I.val → value_l (ℳ := 𝒱) (p.2.eval ξ) x y → mem_l hℳ y I.val := by
    intro x y hx hxy
    exact PowerlessRelativeFiniteProgramTaggedClosure.call_l (term_m 15) E ξ p
      hBase hClass hBound hPair hCall hp (hMaps p hp) (hSeed _ hTag) hx hxy
  refine ⟨I, hCount, hBound, hSeed, hPair, ?_, ?_, ?_, ?_⟩
  · exact hGraph (term_m 7, term_m 3) (by simp [E])
      (hωC _ (PowerlessRelativeFiniteNumeralTags.member_l K hω 0))
  · exact hGraph (term_m 6, term_m 2) (by simp [E])
      (hωC _ (PowerlessRelativeFiniteNumeralTags.member_l K hω 1))
  · exact hGraph (term_m 5, term_m 1) (by simp [E])
      (hωC _ (PowerlessRelativeFiniteNumeralTags.member_l K hω 2))
  · exact hGraph (term_m 4, term_m 0) (by simp [E])
      (hωC _ (PowerlessRelativeFiniteNumeralTags.member_l K hω 3))

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramFourGraphImage
