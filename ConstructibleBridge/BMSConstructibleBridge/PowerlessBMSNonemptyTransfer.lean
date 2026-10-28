import BMSConstructibleBridge.PowerlessBMSDerives

/-! # 逐候选源模型的 Prop 存在接口

保留旧的显式源族接口。本模块逐个消去 Nonempty，不在 Type 中从所有
候选同时抽取源模型函数。目标仍是原 fixed-height 闭句及原推导核；
源存在性本身不由这一适配层证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSNonemptyTransfer

open Logic FirstOrder SecondOrderSyntax
open SecondOrderProgramArithmetic (numeral_val_l)

set_option autoImplicit false

universe u v

variable {M : FirstOrder.Structure.{0, 0, 0, v} signature_m}

theorem closed_l (H : Nat)
    (hSources : ∀ X : M.Carrier .set,
      Nonempty (PowerlessBMSMatrixTransfer.candidate_source_l.{u, v} (M := M) X)) :
    (SecondOrderConcreteFormula.closed_m H).TrueIn M := by
  change Formula.satisfies Env.empty
    (PureSecondOrder.closed_m SecondOrderConcreteFormula.matrix_m H)
  rw [PureSecondOrder.closed_eq_m SecondOrderConcreteFormula.matrix_m H]
  change ∀ X : M.Carrier .set, Formula.satisfies (Env.empty.pushBound X)
    (SecondOrderConcreteFormula.matrix_m.instantiateFreeTop (numeral_m H))
  intro X
  obtain ⟨S⟩ := hSources X
  let ρ : Env M [.set] [] := Env.empty.pushBound X
  have hNumeral : (numeral_m (Γ := [.set]) (Δ := []) H).eval ρ =
      numeral_val_l (ℳ := M) H := by
    rw [← SecondOrderSyntax.numeral_weaken_m sort_m.set H, Term.eval_weakenBound]
    rfl
  apply (Formula.satisfies_instantiateFreeTop ρ (numeral_m H)
    SecondOrderConcreteFormula.matrix_m).mpr
  simpa only [ρ, hNumeral] using
    PowerlessBMSMatrixTransfer.matrix_at_l (ℳ := S.source) (ω := S.sourceOmega)
      (e := S.sourceZero) (he := S.sourceZeroSpec) (h₀ := S.sourceZeroMem)
      (F := S.sourceOperations) S.sourceModels S.sourceOmegaSpec
      S.arithmeticCorrespondence H X S.representative S.representativeRelated

/-- 任意 Type 0 模型中的逐候选 Prop 存在性足以取得原对象推导。 -/
theorem derives_m (H : Nat)
    (hSources : ∀ {M : FirstOrder.Structure.{0, 0, 0, 0} signature_m},
      Theory.Models M SecondOrderArithmetic.theory_m → ∀ X : M.Carrier .set,
        Nonempty (PowerlessBMSMatrixTransfer.candidate_source_l.{0, 0} (M := M) X)) :
    Derives SecondOrderArithmetic.theory_m [] (SecondOrderConcreteFormula.closed_m H) := by
  apply SecondOrderCompleteness.derives_m
  intro M hM
  exact closed_l H (hSources hM)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSNonemptyTransfer
