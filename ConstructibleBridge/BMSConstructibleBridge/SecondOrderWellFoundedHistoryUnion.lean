import BMSConstructibleBridge.SecondOrderWellFoundedHistorySyntax

/-! # 内部前驱历史的相容并

对每个前驱只使用“有历史”的命题见证；统一理解直接收集所有历史的行。
共同初段一致性保证这张实际实数图与每个已有前驱历史一致，不选择历史族。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedHistoryUnion

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderWellFoundedAgreement

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def insert_m {Δ : SortContext signature_m} :
    VariableSubstitution signature_m (.num :: .set :: .set :: Δ) [.set] (.num :: .num :: .num :: .set :: Δ)
  | _, .here => .fvar .here
  | _, .there .here => .fvar (.there (.there (.there .here)))
  | _, .there (.there .here) => .bvar .here
  | _, .there (.there (.there v)) => .fvar (.there (.there (.there (.there v))))

private def history_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Formula signature_m [.set] (.num :: .num :: .num :: .set :: Δ) :=
  (SecondOrderWellFoundedHistorySyntax.formula_m φ).substitute
    (show Substitution signature_m [] (.num :: .set :: .set :: Δ) [.set]
      (.num :: .num :: .num :: .set :: Δ) from .map (fun v => nomatch v) insert_m)

def formula_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ) :
    Formula signature_m [] (.num :: .num :: .num :: .set :: Δ) :=
  .conj (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar .here)
    (.fvar (.there (.there .here)))) <| .existsE .set <| .conj (history_m φ)
      (GraphSyntax.edge_m (.bvar .here) (.fvar .here) (.fvar (.there .here)))

theorem pure_m {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (hφ : language_m φ = true) : language_m (formula_m φ) = true := by
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
  change (language_m (GraphSyntax.edge_m (Γ := []) (Δ := .num :: .num :: .num :: .set :: Δ)
    (.fvar (.there (.there (.there .here)))) (.fvar .here) (.fvar (.there (.there .here)))) &&
    (language_m (history_m φ) && _)) = true
  rw [hHistory]
  rfl

theorem formula_l {Δ : SortContext signature_m} (φ : Formula signature_m [.set, .set] Δ)
    (η : Env ℳ [] Δ) (R : set_l ℳ) (n m a : num_l ℳ) :
    (formula_m φ).satisfies (((((η.pushFree R).pushFree n).pushFree a).pushFree m)) ↔
      relation_l R m n ∧ ∃ H, good_l (SecondOrderSetOperator.relation_l φ η) R H m ∧ relation_l H m a := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.edge_l, Term.eval]
  apply and_congr Iff.rfl
  apply exists_congr
  intro H
  apply and_congr _ Iff.rfl
  refine (Formula.satisfies_substitute _ _ _).trans ?_
  have hEnv :
      (((((η.pushFree R).pushFree n).pushFree a).pushFree m).pushBound H).pullback
        (show Substitution signature_m [] (.num :: .set :: .set :: Δ) [.set]
          (.num :: .num :: .num :: .set :: Δ) from .map (fun v => nomatch v) insert_m) =
      (((η.pushFree H).pushFree R).pushFree m) := by
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
  exact SecondOrderWellFoundedHistorySyntax.formula_l φ η R H m

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [.set, .set] Δ) (hφ : language_m φ = true) (η : Env ℳ [] Δ)
    (R : set_l ℳ) (n : num_l ℳ) : ∃ S, ∀ m a,
      relation_l S m a ↔ relation_l R m n ∧
        ∃ H, good_l (SecondOrderSetOperator.relation_l φ η) R H m ∧ relation_l H m a := by
  obtain ⟨S, hS⟩ := SecondOrderRelations.comprehension_l hℳ (formula_m φ) (pure_m φ hφ)
    ((η.pushFree R).pushFree n)
  exact ⟨S, fun m a => (hS m a).trans (formula_l φ η R n m a)⟩

theorem agrees_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop) (R S : set_l ℳ)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n)
    (hTrans : ∀ a b c, relation_l R a b → relation_l R b c → relation_l R a c)
    (hLocal : local_l P R) (n : num_l ℳ)
    (hExist : ∀ m, relation_l R m n → ∃ H, good_l P R H m)
    (hS : ∀ m a, relation_l S m a ↔ relation_l R m n ∧ ∃ H, good_l P R H m ∧ relation_l H m a)
    (k : num_l ℳ) (hk : relation_l R k n) (K : set_l ℳ) (hK : good_l P R K k) :
    ∀ m, prefix_l R m k → ∀ a, relation_l S m a ↔ relation_l K m a := by
  intro m hm a
  have hmn : relation_l R m n := by
    rcases hm with rfl | hm
    · exact hk
    · exact hTrans m k n hm hk
  constructor
  · intro h
    obtain ⟨_, H, hH, ha⟩ := (hS m a).mp h
    exact (coherence_l hℳ P R hWf hTrans hLocal H K m k hH hK m (Or.inl rfl) hm a).mp ha
  · intro ha
    obtain ⟨H, hH⟩ := hExist m hmn
    exact (hS m a).mpr ⟨hmn, H, hH,
      (coherence_l hℳ P R hWf hTrans hLocal H K m k hH hK m (Or.inl rfl) hm a).mpr ha⟩

#print axioms exists_l
#print axioms agrees_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedHistoryUnion
