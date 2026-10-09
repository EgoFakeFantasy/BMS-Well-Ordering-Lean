import BMSConstructibleBridge.SecondOrderWellFoundedHistoryExistence

/-! # 原 Z₂ 中可定义局部算子的内部良基递归

全局解由所有有限或超限初段历史的相容行并取得。这里的“初段”是模型内
前驱关系的初段，不是外部有限长度；没有抽取实数值历史选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedRecursion

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderWellFoundedAgreement

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def insert_m {Δ : SortContext signature_m} :
    VariableSubstitution signature_m (.num :: .set :: .set :: Δ) [.set] (.num :: .num :: .set :: Δ)
  | _, .here => .fvar .here
  | _, .there .here => .fvar (.there (.there .here))
  | _, .there (.there .here) => .bvar .here
  | _, .there (.there (.there v)) => .fvar (.there (.there (.there v)))

private def history_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Formula signature_m [.set] (.num :: .num :: .set :: Δ) :=
  (SecondOrderWellFoundedHistorySyntax.formula_m φ).substitute
    (show Substitution signature_m [] (.num :: .set :: .set :: Δ) [.set] (.num :: .num :: .set :: Δ)
      from .map (fun v => nomatch v) insert_m)

def union_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Formula signature_m [] (.num :: .num :: .set :: Δ) :=
  .existsE .set <| .conj (history_m φ)
    (GraphSyntax.edge_m (.bvar .here) (.fvar .here) (.fvar (.there .here)))

theorem union_pure_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : language_m (union_m φ) = true := by
  have hHistory : language_m (history_m φ) = true := by
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
  change (language_m (history_m φ) && _) = true
  rw [hHistory]
  rfl

theorem union_formula_l {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (η : Env ℳ [] Δ) (R : set_l ℳ) (n a : num_l ℳ) :
    (union_m φ).satisfies ((((η.pushFree R).pushFree a).pushFree n)) ↔
      ∃ H, good_l (SecondOrderSetOperator.relation_l φ η) R H n ∧ relation_l H n a := by
  simp only [union_m, Formula.satisfies, SecondOrderPairing.edge_l, Term.eval]
  apply exists_congr
  intro H
  apply and_congr _ Iff.rfl
  refine (Formula.satisfies_substitute _ _ _).trans ?_
  have hEnv :
      ((((η.pushFree R).pushFree a).pushFree n).pushBound H).pullback
        (show Substitution signature_m [] (.num :: .set :: .set :: Δ) [.set] (.num :: .num :: .set :: Δ)
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

theorem union_exists_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [.set, .set] Δ) (hφ : language_m φ = true) (η : Env ℳ [] Δ) (R : set_l ℳ) :
    ∃ S, ∀ n a, relation_l S n a ↔
      ∃ H, good_l (SecondOrderSetOperator.relation_l φ η) R H n ∧ relation_l H n a := by
  obtain ⟨S, hS⟩ := SecondOrderRelations.comprehension_l hℳ (union_m φ) (union_pure_m φ hφ) (η.pushFree R)
  exact ⟨S, fun n a => (hS n a).trans (union_formula_l φ η R n a)⟩

theorem agrees_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop) (R S : set_l ℳ)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n)
    (hTrans : ∀ a b c, relation_l R a b → relation_l R b c → relation_l R a c)
    (hLocal : local_l P R) (hExist : ∀ n, ∃ H, good_l P R H n)
    (hS : ∀ n a, relation_l S n a ↔ ∃ H, good_l P R H n ∧ relation_l H n a)
    (k : num_l ℳ) (K : set_l ℳ) (hK : good_l P R K k) :
    ∀ m, prefix_l R m k → ∀ a, relation_l S m a ↔ relation_l K m a := by
  intro m hm a
  constructor
  · intro h
    obtain ⟨H, hH, ha⟩ := (hS m a).mp h
    exact (coherence_l hℳ P R hWf hTrans hLocal H K m k hH hK m (Or.inl rfl) hm a).mp ha
  · intro ha
    obtain ⟨H, hH⟩ := hExist m
    exact (hS m a).mpr ⟨H, hH,
      (coherence_l hℳ P R hWf hTrans hLocal H K m k hH hK m (Or.inl rfl) hm a).mpr ha⟩

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [.set, .set] Δ) (hφ : language_m φ = true) (η : Env ℳ [] Δ) (R : set_l ℳ)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n)
    (hTrans : ∀ a b c, relation_l R a b → relation_l R b c → relation_l R a c)
    (hIrrefl : ∀ n, ¬relation_l R n n)
    (hLocal : local_l (SecondOrderSetOperator.relation_l φ η) R)
    (hTotal : ∀ H, ∃ U, SecondOrderSetOperator.relation_l φ η H U) :
    ∃! S, SecondOrderSetOperator.relation_l φ η S S := by
  let P := SecondOrderSetOperator.relation_l φ η
  have hExist := SecondOrderWellFoundedHistoryExistence.exists_l hℳ φ hφ η R
    hWf hTrans hIrrefl hLocal hTotal
  obtain ⟨S, hS⟩ := union_exists_l hℳ φ hφ η R
  obtain ⟨U, hU⟩ := hTotal S
  have hUS : U = S := by
    apply SecondOrderRelations.ext_l hℳ
    intro n a
    obtain ⟨K, hK⟩ := hExist n
    have hAgree := agrees_l hℳ P R S hWf hTrans hLocal hExist hS n K hK
    obtain ⟨V, hV, hKV⟩ := hK
    exact (hLocal S K U V hU hV n (fun m hm => hAgree m (Or.inr hm)) a).trans
      ((hKV n (Or.inl rfl) a).symm.trans (hAgree n (Or.inl rfl) a).symm)
  subst U
  exact ⟨S, hU, fun T hT => SecondOrderWellFoundedAgreement.unique_l hℳ P R hWf hTrans hLocal T S hT hU⟩

#print axioms union_exists_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedRecursion
