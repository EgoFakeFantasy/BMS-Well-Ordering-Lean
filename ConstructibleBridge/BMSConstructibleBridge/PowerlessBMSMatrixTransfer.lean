import BMSConstructibleBridge.PowerlessBMSWellOrder
import BMSConstructibleBridge.SecondOrderPureTransfer

/-!
# 无幂集背景 BMS 终局到外部算术模型的条件式迁移

将已完成的 PowerlessTheory 背景矩阵定理与纯算术跨模型真值保持连接。唯一新增输入
是两个算术环境逐项对应；其集合分量明确包含候选实数的成员对应。这一步不构造
PowerlessTheory 模型；本文件的闭句迁移接口保留源模型覆盖条件。原 Z₂ 下的实际
逐候选源构造见 `SecondOrderHereditaryCandidateSource`，无额外源假设的固定外部
高度对象推导见 `SecondOrderHereditaryBMSWellOrder.derives_m`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSMatrixTransfer

open Logic FirstOrder SecondOrderSyntax ThirdOrderSemantics
open SecondOrderProgramArithmetic (numeral_val_l)

set_option autoImplicit false

universe u v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

variable {M : FirstOrder.Structure.{0, 0, 0, v} signature_m}

/-- 对一个目标集合候选单独提供的 Powerless 源模型及成员代表。

源模型允许依赖目标候选 `X`；这比要求一个源模型覆盖目标结构中的所有集合更贴近
逐反例迁移所需的接口。它在本模块中作为条件数据；任意 Z₂ 模型中每个候选的
`Nonempty` 源证书已由 `SecondOrderHereditaryCandidateSource.exists_l` 给出。
-/
structure candidate_source_l (X : M.Carrier .set) where
  source : FirstOrder.Structure.{0, 0, 0, u} ℒ
  sourceOmega : carrier_l source
  sourceZero : carrier_l source
  sourceZeroSpec : PowerlessNatural.zero_l sourceZero
  sourceZeroMem : member_l source sourceZero sourceOmega
  sourceOperations : PowerlessArithmetic.operations_l sourceOmega sourceZero
  sourceModels : Theory.Models source PowerlessTheory.theory_m
  sourceOmegaSpec : omega_l sourceOmega
  arithmeticCorrespondence : SecondOrderPureTransfer.correspondence_l
    (M := PowerlessArithmetic.structure_l sourceZeroSpec sourceZeroMem sourceOperations)
    (N := M)
  representative : PowerlessArithmetic.set_l sourceOmega
  representativeRelated : arithmeticCorrespondence.setRel_l representative X

/-- 在给定算术同构及候选集合成员对应时，将 Powerless 背景的实际矩阵证明迁往目标结构。 -/
theorem matrix_l
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (C : SecondOrderPureTransfer.correspondence_l (M := 𝒩) (N := M))
    {H : Nat} (η : Env 𝒩 [.set] [.num])
    (hη : η.freeVal .here = numeral_val_l (ℳ := 𝒩) H)
    (ξ : Env M [.set] [.num])
    (hEnv : SecondOrderPureTransfer.environments_related_l C η ξ) :
    Formula.satisfies ξ SecondOrderConcreteFormula.matrix_m := by
  have hSource := PowerlessBMSWellOrder.matrix_l hℳ hω H η hη
  exact (SecondOrderPureTransfer.formula_l C SecondOrderConcreteFormula.matrix_m
    SecondOrderConcreteFormula.matrix_pure_m η ξ hEnv).mp hSource

/-- 将单个目标集合候选的矩阵实例迁移到其源模型中对应的成员代表。 -/
theorem matrix_at_l
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (C : SecondOrderPureTransfer.correspondence_l (M := 𝒩) (N := M))
    (H : Nat) (X : M.Carrier .set) (A : PowerlessArithmetic.set_l ω)
    (hA : C.setRel_l A X) :
    Formula.satisfies
      (((Env.empty (M := M)).pushBound X).pushFree (numeral_val_l (ℳ := M) H))
      SecondOrderConcreteFormula.matrix_m := by
  let ρ : Env M [.set] [] := (Env.empty (M := M)).pushBound X
  let A' : FirstOrder.Structure.Carrier 𝒩 sort_m.set := A
  let η : Env 𝒩 [.set] [.num] :=
    ((Env.empty (σ := signature_m) (M := 𝒩)).pushBound (sort := sort_m.set) A').pushFree
      (sort := sort_m.num) (numeral_val_l (ℳ := 𝒩) H)
  let ξ : Env M [.set] [.num] :=
    ρ.pushFree (numeral_val_l (ℳ := M) H)
  have hNumeral :
      C.numberEquiv_l (numeral_val_l (ℳ := 𝒩) H) = numeral_val_l (ℳ := M) H := by
    induction H with
    | zero =>
        change C.numberEquiv_l (SecondOrderModel.zero_l 𝒩) = SecondOrderModel.zero_l M
        exact C.zero_l
    | succ n ih =>
        rw [SecondOrderProgramArithmetic.numeral_val_succ_l,
          SecondOrderProgramArithmetic.numeral_val_succ_l]
        calc
          C.numberEquiv_l (SecondOrderModel.succ_l (numeral_val_l (ℳ := 𝒩) n)) =
            SecondOrderModel.succ_l (C.numberEquiv_l (numeral_val_l (ℳ := 𝒩) n)) :=
              C.succ_l _
          _ = SecondOrderModel.succ_l (numeral_val_l (ℳ := M) n) :=
              congrArg (fun x : M.Carrier .num => SecondOrderModel.succ_l x) ih
  have hηFree : η.freeVal (.here : Variable [sort_m.num] sort_m.num) =
      numeral_val_l (ℳ := 𝒩) H := by
    rfl
  have hEnv : SecondOrderPureTransfer.environments_related_l C η ξ := by
    constructor
    · intro s entry
      cases s with
      | num => nomatch entry
      | set =>
          cases entry with
          | here =>
              change C.setRel_l (η.boundVal .here) (ξ.boundVal .here)
              have hη : η.boundVal (.here : Variable [sort_m.set] sort_m.set) = A' := by
                change ((Env.empty (σ := signature_m) (M := 𝒩)).pushBound
                  (sort := sort_m.set) A').boundVal
                  (.here : Variable [sort_m.set] sort_m.set) = A'
                rfl
              have hξ : ξ.boundVal (.here : Variable [sort_m.set] sort_m.set) = X := by
                change ((Env.empty (M := M)).pushBound X).boundVal
                  (.here : Variable [sort_m.set] sort_m.set) = X
                rfl
              rw [hη, hξ]
              simpa [A'] using hA
          | there rest => nomatch rest
    · intro s entry
      cases s with
      | num =>
          cases entry with
          | here =>
              change C.numberEquiv_l (η.freeVal .here) = ξ.freeVal .here
              have hξ : ξ.freeVal (.here : Variable [sort_m.num] sort_m.num) =
                  numeral_val_l (ℳ := M) H := by
                rfl
              rw [hηFree, hξ]
              exact hNumeral
          | there rest => nomatch rest
      | set => nomatch entry
  have hMatrix := matrix_l (H := H) hℳ hω C η hηFree ξ hEnv
  simpa [ρ, ξ] using hMatrix

/-- 若源模型覆盖目标中的每个集合候选，则整条原固定高度闭句迁移到目标结构。

本接口显式要求 `hCover`：每个目标集合都有一个源集合，其成员关系经 `C` 对应。
本定理不构造一个统一的源模型或该覆盖；最终 Z₂ 证明使用逐候选遗传源，不要求
单个源覆盖全部候选。允许源模型依赖目标候选的条件式接口见
`closed_from_candidate_sources_l`。
-/
theorem closed_l
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (C : SecondOrderPureTransfer.correspondence_l (M := 𝒩) (N := M))
    (H : Nat)
    (hCover : ∀ X : M.Carrier .set,
      ∃ A : PowerlessArithmetic.set_l ω, C.setRel_l A X) :
    (SecondOrderConcreteFormula.closed_m H).TrueIn M := by
  change Formula.satisfies (Env.empty (M := M))
    (PureSecondOrder.closed_m SecondOrderConcreteFormula.matrix_m H)
  rw [PureSecondOrder.closed_eq_m SecondOrderConcreteFormula.matrix_m H]
  change ∀ X : M.Carrier .set,
    Formula.satisfies ((Env.empty (M := M)).pushBound X)
      (SecondOrderConcreteFormula.matrix_m.instantiateFreeTop (numeral_m H))
  intro X
  obtain ⟨A, hA⟩ := hCover X
  let ρ : Env M [.set] [] := (Env.empty (M := M)).pushBound X
  have hNumeralEval : (numeral_m (Γ := [.set]) (Δ := []) H).eval ρ =
      numeral_val_l (ℳ := M) H := by
    rw [← SecondOrderSyntax.numeral_weaken_m sort_m.set H]
    rw [Term.eval_weakenBound]
    rfl
  have hTarget : Formula.satisfies (ρ.pushFree ((numeral_m H).eval ρ))
      SecondOrderConcreteFormula.matrix_m := by
    simpa [ρ, hNumeralEval] using matrix_at_l hℳ hω C H X A hA
  exact (Formula.satisfies_instantiateFreeTop ρ (numeral_m H)
    SecondOrderConcreteFormula.matrix_m).mpr hTarget

/-- 若每个目标候选各自拥有一个可迁移的源模型，则整条固定高度闭句成立。

源模型可随目标集合候选变化；假设仅要求在该源模型中找到此候选的集合代表，不要求
某一个源模型同时覆盖目标结构的全部二阶对象。源模型的 `Nonempty` 证书已由
`SecondOrderHereditaryCandidateSource.exists_l` 构造，最终出口经
`PowerlessBMSNonemptyTransfer` 逐候选消去该证书，不抽取 Type 层源族。
-/
theorem closed_from_candidate_sources_l
    (H : Nat)
    (hSources : ∀ X : M.Carrier .set, candidate_source_l (M := M) X) :
    (SecondOrderConcreteFormula.closed_m H).TrueIn M := by
  change Formula.satisfies (Env.empty (M := M))
    (PureSecondOrder.closed_m SecondOrderConcreteFormula.matrix_m H)
  rw [PureSecondOrder.closed_eq_m SecondOrderConcreteFormula.matrix_m H]
  change ∀ X : M.Carrier .set,
    Formula.satisfies ((Env.empty (M := M)).pushBound X)
      (SecondOrderConcreteFormula.matrix_m.instantiateFreeTop (numeral_m H))
  intro X
  let S : candidate_source_l (M := M) X := hSources X
  let ρ : Env M [.set] [] := (Env.empty (M := M)).pushBound X
  have hNumeralEval : (numeral_m (Γ := [.set]) (Δ := []) H).eval ρ =
      numeral_val_l (ℳ := M) H := by
    rw [← SecondOrderSyntax.numeral_weaken_m sort_m.set H]
    rw [Term.eval_weakenBound]
    rfl
  have hTarget : Formula.satisfies (ρ.pushFree ((numeral_m H).eval ρ))
      SecondOrderConcreteFormula.matrix_m := by
    simpa [S, ρ, hNumeralEval] using
      matrix_at_l (ℳ := S.source) (ω := S.sourceOmega) (e := S.sourceZero)
        (he := S.sourceZeroSpec) (h₀ := S.sourceZeroMem) (F := S.sourceOperations)
        (M := M) S.sourceModels S.sourceOmegaSpec S.arithmeticCorrespondence H X
        S.representative S.representativeRelated
  exact (Formula.satisfies_instantiateFreeTop ρ (numeral_m H)
    SecondOrderConcreteFormula.matrix_m).mpr hTarget

#print axioms matrix_l
#print axioms matrix_at_l
#print axioms closed_l
#print axioms closed_from_candidate_sources_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSMatrixTransfer
