import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBoundAppend

/-! # 同一程序的两个读数来自同一实际末态

两个 run 可给不同历史陪域，但确定性保证历史图相同，末态三字段
随之相同。因此可在同一存储图读取两个坐标，不能重新选择各自的
末态后直接拼成配对指令。本辅助结果由后续原 Z₂ 配对出口消费。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramJointRead

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramExecution (relation_m relation_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l)
open PowerlessRelativeFiniteProgramBoundOutput (run_l)
open PowerlessRelativeFiniteProgramBoundAppend (history_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem joint_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w n Q e t₀ t₁ t₂ a k x l z : Term ℒ [] Δ .set)
    (hBase : ∀ y, mem_l hℳ y (B.eval η) → ∀ u, mem_l hℳ u y → mem_l hℳ u (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (he : ∀ y, ¬mem_l hℳ y (e.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (n.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ η (B.eval η)) (hn : mem_l hℳ (n.eval η) K.omega)
    (hRunX : run_l φ η (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (x.eval η))
    (hRunZ : run_l φ η (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (l.eval η) (z.eval η)) :
    ∃ S D F s E f, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) D ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) F ∧
        history_l φ η (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (n.eval η) (e.eval η)
          (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) S D F ∧
        value_l (ℳ := 𝒱) F (n.eval η) s ∧
        PowerlessRelativeFiniteProgramStep.valid_l (B.eval η) (ω.eval η) (n.eval η) E f s ∧
        value_l (ℳ := 𝒱) f (k.eval η) (x.eval η) ∧ value_l (ℳ := 𝒱) f (l.eval η) (z.eval η) := by
  let ψ := relation_m φ B C ω w e t₀ t₁ t₂
  have hX := (PowerlessRelativeFiniteProgramBoundRun.native_l K φ η
    B C ω w e t₀ t₁ t₂ a n k (x.eval η)).mpr hRunX
  have hZ := (PowerlessRelativeFiniteProgramBoundRun.native_l K φ η
    B C ω w e t₀ t₁ t₂ a n l (z.eval η)).mpr hRunZ
  obtain ⟨S, D, F, s, E, f, hDC, hFC, hF, hs, hValid, hx⟩ := hX
  obtain ⟨T, A, H, t, A', g, _, _, hH, ht, hValid', hz⟩ := hZ
  have heEq : e.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun y =>
      iff_of_false (he y) (PowerlessBMSQuotientSuccessor.zero_l K y))
  have hUnique : ∀ s t u, ψ.satisfies ((η.pushFree s).pushFree t) →
      ψ.satisfies ((η.pushFree s).pushFree u) → t = u := by
    intro s t u ht hu
    obtain ⟨v, _, hv⟩ := PowerlessRelativeFiniteProgramStep.exists_unique_l
      φ η (ω := ω.eval η) (e := e.eval η) hBase hC hw hTags hFunctional s
    exact (hv t ((relation_formula_l K φ η B C ω w e t₀ t₁ t₂ s t).mp ht)).trans
      (hv u ((relation_formula_l K φ η B C ω w e t₀ t₁ t₂ s u).mp hu)).symm
  have hFH := PowerlessDefinableFiniteTraceUnique.unique_l K ψ η hn heEq hF hH hUnique
  subst H
  have hst := SecondOrderFunctionProperties.value_unique_l hℳ hF.2.1 hs ht
  subst t
  obtain ⟨_, hEA, hfg⟩ := PowerlessRelativeFiniteProgramStep.record_coordinates_l hValid.1 hValid'.1
  subst A'; subst g
  refine ⟨S, D, F, s, E, f, hDC, hFC, ?_, hs, hValid, hx, hz⟩
  simpa only [PowerlessDefinableFiniteTrace.trace_l, history_l, relation_formula_l K,
    ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using hF

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramJointRead
