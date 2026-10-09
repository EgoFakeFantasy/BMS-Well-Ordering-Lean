import BMSConstructibleBridge.SecondOrderWellFoundedHistoryExtension

/-! # 每个内部良基初段有递归历史

用原 Z₂ 公式归纳遍历全部内部节点。前驱历史只以存在命题提供，实际历史
并由统一理解构造；一行延长把它变为当前节点的历史。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedHistoryExistence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderWellFoundedAgreement

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def insert_m {Δ : SortContext signature_m} :
    VariableSubstitution signature_m (.num :: .set :: .set :: Δ) [.set] (.num :: .set :: Δ)
  | _, .here => .fvar .here
  | _, .there .here => .fvar (.there .here)
  | _, .there (.there .here) => .bvar .here
  | _, .there (.there (.there v)) => .fvar (.there (.there v))

def formula_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Formula signature_m [] (.num :: .set :: Δ) :=
  .existsE .set <| (SecondOrderWellFoundedHistorySyntax.formula_m φ).substitute
    (show Substitution signature_m [] (.num :: .set :: .set :: Δ) [.set] (.num :: .set :: Δ)
      from .map (fun v => nomatch v) insert_m)

theorem pure_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : language_m (formula_m φ) = true := by
  refine (SecondOrderSubstitution.form_subst_m _ _ _ ?_ ?_).trans
    (SecondOrderWellFoundedHistorySyntax.pure_m φ hφ)
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases s <;> rfl

theorem formula_l {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (η : Env ℳ [] Δ) (R : set_l ℳ) (n : num_l ℳ) :
    (formula_m φ).satisfies ((η.pushFree R).pushFree n) ↔
      ∃ H, good_l (SecondOrderSetOperator.relation_l φ η) R H n := by
  rw [formula_m, Formula.satisfies]
  apply exists_congr
  intro H
  refine (Formula.satisfies_substitute _ _ _).trans ?_
  have hEnv :
      (((η.pushFree R).pushFree n).pushBound H).pullback
        (show Substitution signature_m [] (.num :: .set :: .set :: Δ) [.set] (.num :: .set :: Δ)
          from .map (fun v => nomatch v) insert_m) = (((η.pushFree H).pushFree R).pushFree n) := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => cases s <;> rfl
  rw [hEnv]
  exact SecondOrderWellFoundedHistorySyntax.formula_l φ η R H n

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [.set, .set] Δ) (hφ : language_m φ = true) (η : Env ℳ [] Δ) (R : set_l ℳ)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n)
    (hTrans : ∀ a b c, relation_l R a b → relation_l R b c → relation_l R a c)
    (hIrrefl : ∀ n, ¬relation_l R n n)
    (hLocal : local_l (SecondOrderSetOperator.relation_l φ η) R)
    (hTotal : ∀ H, ∃ U, SecondOrderSetOperator.relation_l φ η H U) :
    ∀ n, ∃ H, good_l (SecondOrderSetOperator.relation_l φ η) R H n := by
  intro n
  apply (formula_l φ η R n).mp
  apply SecondOrderWellFoundedInduction.induction_l hℳ (formula_m φ) (pure_m φ hφ)
    (η.pushFree R) R ?_ n (hWf n)
  intro k _ ih
  have hExist : ∀ m, relation_l R m k → ∃ H, good_l (SecondOrderSetOperator.relation_l φ η) R H m :=
    fun m hm => (formula_l φ η R m).mp (ih m hm)
  obtain ⟨S, hS⟩ := SecondOrderWellFoundedHistoryUnion.exists_l hℳ φ hφ η R k
  obtain ⟨H, hH⟩ := SecondOrderWellFoundedHistoryExtension.exists_l hℳ
    (SecondOrderSetOperator.relation_l φ η) R hWf hTrans hIrrefl hLocal hTotal k S hExist hS
  exact (formula_l φ η R k).mpr ⟨H, hH⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedHistoryExistence
