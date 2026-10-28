import BMSConstructibleBridge.SecondOrderFiniteFunctionAgreement
import BMSConstructibleBridge.SecondOrderFiniteFunctionRestriction
import BMSConstructibleBridge.SecondOrderMemberDefBoundedSlice

/-! # 通用无限迭代图由共同有限见证界进入两次 Def

检查式的层参数 C 属于 Def(C)，不假定 C∈C。每个实际无限图成员用有限
限制作见证，反向由原 Z₂ 内部归纳比较有限轨迹与给定无限图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionIterationBoundedGraph

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySyntax (up)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
  let C : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let ω : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let e : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let A : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let H : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let a : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let p : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let n : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set, .set] .set := .bvar (.there .here)
  let x : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set, .set] .set := .bvar .here
  membershipLevyBound.boundedExists (.fvar (.there (.there .here))) <|
    membershipLevyBound.boundedExists (.fvar (.there (.there (.there (.there .here))))) <| .conj
      (PowerlessPairBounded.ordered_m n x p) <| membershipLevyBound.boundedExists C <| .conj
        (PowerlessFunctionTraceBounded.formula_m (up ω) (up e) (up A) (up H) (up a) (up n) (.bvar .here))
        (PowerlessValueBounded.formula_m (.bvar .here) (up n) (up x))

theorem delta_l : Formula.IsDelta0 membershipLevyBound formula_m :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
    (.bounded_exists _ (.conj (PowerlessFunctionTraceBounded.delta_l _ _ _ _ _ _ _)
      (PowerlessValueBounded.delta_l _ _ _)))))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (C ω e A H a p : 𝒩.Carrier .set) : formula_m.satisfies
    (((((((Env.empty (M := 𝒩)).pushFree a).pushFree H).pushFree A).pushFree e).pushFree ω).pushFree C |>.pushFree p) ↔
      ∃ n, member_l 𝒩 n ω ∧ ∃ x, member_l 𝒩 x A ∧ ordered_l (ℳ := 𝒩) n x p ∧
        ∃ g, member_l 𝒩 g C ∧ PowerlessFunctionTraceBounded.trace_l (𝒩 := 𝒩) ω e A H a n g ∧
          value_l (ℳ := 𝒩) g n x := by
  simp only [formula_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, PowerlessPairBounded.ordered_formula_l, PowerlessFunctionTraceBounded.formula_l,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem member_l (K : source_coding_l hℳ) {B β C D E A H a F : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hCD : SecondOrderMemberDef.spec_l hℳ C D) (hDE : SecondOrderMemberDef.spec_l hℳ D E)
    (hωC : mem_l hℳ K.omega C) (hAC : mem_l hℳ A C) (hHC : mem_l hℳ H C) (ha : mem_l hℳ a A)
    (hH : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) H A A)
    (hF : PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A H a F) : mem_l hℳ F E := by
  let e := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set, .set, .set, .set] :=
    ((((((Env.empty.pushFree a).pushFree H).pushFree A).pushFree e).pushFree K.omega).pushFree C)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hSub := SecondOrderMemberDefProperties.contains_l hℳ hCD (fun x y hx hy => hTrans x hx y hy)
  apply SecondOrderMemberDefBoundedSlice.member_l hℳ hDE
    (fun x hx y hy => SecondOrderMemberDefProperties.transitive_l hℳ hCD
      (fun v w hv hw => hTrans v hv w hw) x y hx hy) delta_l η
  · intro s v
    cases s
    match v with
    | .here => exact SecondOrderMemberDefProperties.mother_member_l hℳ hCD
    | .there .here => exact hSub K.omega hωC
    | .there (.there .here) => exact hSub e (hTrans K.omega hωC e (numberCode_l K (SecondOrderModel.zero_l ℳ)).property)
    | .there (.there (.there .here)) => exact hSub A hAC
    | .there (.there (.there (.there .here))) => exact hSub H hHC
    | .there (.there (.there (.there (.there .here)))) => exact hSub a (hTrans A hAC a ha)
  · intro p
    rw [formula_l (𝒩 := SecondOrderQuotient.structure_l hℳ) C K.omega e A H a p]
    constructor
    · intro hp
      obtain ⟨n, x, hn, hx, hPair⟩ := hF.1.1 p hp
      have hpC := PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hC
        (hTrans K.omega hωC n hn) (hTrans A hAC x hx) hPair
      obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hn⟩
      have hi' : (numberCode_l K i).val = n := congrArg Subtype.val hi
      obtain ⟨g, hgC, hg⟩ := SecondOrderFiniteFunctionRestriction.exists_l K hBase hLimit hC hωC hAC hF i
      rw [hi'] at hg
      have hTrace := hg
      obtain ⟨T, _, hT, hG, _, _⟩ := hg
      obtain ⟨y, hy, _⟩ := hG.2 n ((hT n).mpr (Or.inr rfl))
      have hFy := SecondOrderFiniteFunctionAgreement.value_l K hH hF hn hTrace hy.2
      have hFx : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F n x := ⟨p, hp, hPair⟩
      have hyx := PowerlessBMSQuotientRecursion.value_unique_l (hM := hℳ) hF.1 hFy hFx
      exact ⟨hSub p hpC, n, hn, x, hx, hPair, g, hgC, hTrace, hyx ▸ hy.2⟩
    · rintro ⟨_, n, hn, x, _, hPair, g, _, hg, hValue⟩
      obtain ⟨q, hq, hPair'⟩ := SecondOrderFiniteFunctionAgreement.value_l K hH hF hn hg hValue
      exact (SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair) ▸ hq

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionIterationBoundedGraph
