import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessRelativeClassOmegaAbsolute
import BMSConstructibleBridge.PowerlessSuccessorBounded
import BMSConstructibleBridge.SecondOrderOrdinalSuccessor
import BMSConstructibleBridge.SecondOrderOrdinalComparison

/-! # 非零极限序数上的实际类内后继图

每个后继仍低于给定极限，由原商的序数比较证明，不调用 Collection。
图由有界后继检查式取得；环境序数性质与类内函数性质分开标明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLimitSuccessorGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => structure_l hℳ B hBase
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

private theorem irrefl_l (x : SecondOrderQuotient.type_l hℳ) : ¬mem_l hℳ x x := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact SecondOrderFoundation.irrefl_l hℳ X

theorem successor_below_l {C x : SecondOrderQuotient.type_l hℳ} (hC : Ordinal C)
    (hNoMax : ∀ a, mem_l hℳ a C → ∃ b, mem_l hℳ b C ∧ mem_l hℳ a b)
    (hx : mem_l hℳ x C) : ∃ y, mem_l hℳ y C ∧
      PowerlessRelativeHierarchySemantics.successor_l hℳ x y := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  obtain ⟨Y, hY, _, hSucc⟩ := SecondOrderOrdinalSuccessor.exists_l hℳ X
    (SetTheory.Structure.IsOrdinal.mem hC hx)
  have hRaw (z : SecondOrderQuotient.type_l hℳ) :
      mem_l hℳ z (SecondOrderQuotient.mk_l hℳ Y) ↔
        mem_l hℳ z (SecondOrderQuotient.mk_l hℳ X) ∨ z = SecondOrderQuotient.mk_l hℳ X := by
    obtain ⟨Z, rfl⟩ := SecondOrderQuotient.surj_l hℳ z
    exact (hSucc Z).trans (or_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ _ _).symm)
  obtain ⟨z, hzC, hxz⟩ := hNoMax _ hx
  have hzOrd : Ordinal z := by
    apply SetTheory.Structure.IsOrdinal.mem (α := C) hC
    exact hzC
  have hYC : mem_l hℳ (SecondOrderQuotient.mk_l hℳ Y) C := by
    rcases SecondOrderOrdinalComparison.compare_l hℳ hY
      hzOrd with h | h | h
    · exact h.symm ▸ hzC
    · exact hC.transitive z hzC (SecondOrderQuotient.mk_l hℳ Y) h
    · rcases (hRaw z).mp h with hzx | hzx
      · exact (irrefl_l z (hzOrd.transitive (SecondOrderQuotient.mk_l hℳ X) hxz z hzx)).elim
      · exact (irrefl_l z (hzx.symm ▸ hxz)).elim
  exact ⟨_, hYC, hRaw⟩

theorem exists_l (C : type_l hℳ B) (hC : Ordinal C.val)
    (hNoMax : ∀ a, mem_l hℳ a C.val → ∃ b, mem_l hℳ b C.val ∧ mem_l hℳ a b) :
    ∃ H : type_l hℳ B, map_l (ℳ := 𝒩) H C C ∧
      ∀ x y : type_l hℳ B, value_l (ℳ := 𝒩) H x y ↔
        mem_l hℳ x.val C.val ∧ mem_l hℳ y.val C.val ∧
          PowerlessRelativeHierarchySemantics.successor_l hℳ x.val y.val := by
  let φ : Formula ℒ [] [.set, .set] :=
    PowerlessSuccessorBounded.formula_m (.fvar .here) (.fvar (.there .here))
  have hRead (x y : type_l hℳ B) : φ.satisfies (((Env.empty (M := 𝒩)).pushFree y).pushFree x) ↔
      PowerlessRelativeHierarchySemantics.successor_l hℳ x.val y.val :=
    (PowerlessSuccessorBounded.formula_l _ _ _).trans
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) x y)
  obtain ⟨H, hH, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (PowerlessSuccessorBounded.delta_l _ _) Env.empty C C (fun x hx => by
      obtain ⟨y, hy, hxy⟩ := successor_below_l hC hNoMax hx
      let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase C.property hy⟩
      refine ⟨y', ⟨hy, (hRead x y').mpr hxy⟩, ?_⟩
      rintro z ⟨_, hz⟩
      exact Subtype.ext (SecondOrderQuotient.ext_l hℳ z.val y
        (fun a => (((hRead x z).mp hz) a).trans (hxy a).symm)))
  exact ⟨H, hH, fun x y => (hValue x y).trans
    (and_congr Iff.rfl (and_congr Iff.rfl (hRead x y)))⟩

#print axioms successor_below_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLimitSuccessorGraph
