import BMSConstructibleBridge.SecondOrderWellFoundedInduction

/-! # 内部良基关系上递归历史的共同初段一致性

任意两个局部历史的最小分歧会违反算子的严格前驱局部性。最小分歧集合
由实际理解公式构造；没有把内部良基证书提升为宿主良基关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedAgreement

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def prefix_l (R : set_l ℳ) (m n : num_l ℳ) : Prop := m = n ∨ relation_l R m n

def local_l (P : set_l ℳ → set_l ℳ → Prop) (R : set_l ℳ) : Prop :=
  ∀ H K U V, P H U → P K V → ∀ n,
    (∀ m, relation_l R m n → ∀ a, relation_l H m a ↔ relation_l K m a) →
      ∀ a, relation_l U n a ↔ relation_l V n a

def good_l (P : set_l ℳ → set_l ℳ → Prop) (R H : set_l ℳ) (n : num_l ℳ) : Prop :=
  ∃ U, P H U ∧ ∀ m, prefix_l R m n → ∀ a, relation_l H m a ↔ relation_l U m a

theorem prefix_predecessor_l (R : set_l ℳ)
    (hTrans : ∀ a b c, relation_l R a b → relation_l R b c → relation_l R a c)
    {a b c : num_l ℳ} (hab : relation_l R a b) (hbc : prefix_l R b c) : prefix_l R a c := by
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  · exact Or.inr (hTrans a b c hab hbc)

def prefix_m {Γ Δ : SortContext signature_m} (R : Term signature_m Γ Δ .set)
    (m n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .disj (.equal m n) (GraphSyntax.edge_m R m n)

theorem prefix_formula_l {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (R : Term signature_m Γ Δ .set) (m n : Term signature_m Γ Δ .num) :
    (prefix_m R m n).satisfies η ↔ prefix_l (R.eval η) (m.eval η) (n.eval η) := by
  simp only [prefix_m, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

/-- 自由槽为待检节点、两历史末端、前驱关系和两历史。 -/
def disagreement_m : Formula signature_m [] [.num, .num, .num, .set, .set, .set] :=
  .conj (prefix_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.fvar (.there .here))) <|
    .conj (prefix_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.fvar (.there (.there .here)))) <|
      .existsE .num <| .neg <| .iff
        (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.bvar .here))
        (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here) (.bvar .here))

theorem disagreement_pure_m : language_m disagreement_m = true := rfl

theorem disagreement_formula_l (R H K : set_l ℳ) (m n k : num_l ℳ) :
    disagreement_m.satisfies
      (((((((Env.empty (M := ℳ)).pushFree K).pushFree H).pushFree R).pushFree k).pushFree n).pushFree m) ↔
      prefix_l R m n ∧ prefix_l R m k ∧ ∃ a, ¬(relation_l H m a ↔ relation_l K m a) := by
  simp only [disagreement_m, Formula.satisfies, prefix_formula_l, SecondOrderPairing.edge_l, Term.eval]
  rfl

theorem coherence_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop) (R : set_l ℳ)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n)
    (hTrans : ∀ a b c, relation_l R a b → relation_l R b c → relation_l R a c)
    (hLocal : local_l P R) (H K : set_l ℳ) (n k : num_l ℳ)
    (hH : good_l P R H n) (hK : good_l P R K k) :
    ∀ m, prefix_l R m n → prefix_l R m k → ∀ a, relation_l H m a ↔ relation_l K m a := by
  classical
  obtain ⟨U, hU, hHU⟩ := hH
  obtain ⟨V, hV, hKV⟩ := hK
  let η := (((((Env.empty (M := ℳ)).pushFree K).pushFree H).pushFree R).pushFree k).pushFree n
  obtain ⟨B, hB⟩ := comprehension_l hℳ disagreement_m disagreement_pure_m η
  have hRead m : mem_l m B ↔ prefix_l R m n ∧ prefix_l R m k ∧
      ∃ a, ¬(relation_l H m a ↔ relation_l K m a) :=
    (hB m).trans (disagreement_formula_l R H K m n k)
  intro m hmn hmk a
  by_contra hBad
  obtain ⟨b, hb, hMin⟩ := SecondOrderGraphMinimum.subset_l hℳ R B
    ⟨m, (hRead m).mpr ⟨hmn, hmk, a, hBad⟩⟩ (fun i _ => hWf i)
  obtain ⟨hbn, hbk, c, hc⟩ := (hRead b).mp hb
  have hAgree : ∀ d, relation_l R d b → ∀ e, relation_l H d e ↔ relation_l K d e := by
    intro d hd e
    by_contra hde
    exact hMin d hd ((hRead d).mpr
      ⟨prefix_predecessor_l R hTrans hd hbn, prefix_predecessor_l R hTrans hd hbk, e, hde⟩)
  exact hc ((hHU b hbn c).trans ((hLocal H K U V hU hV b hAgree c).trans (hKV b hbk c).symm))

/-- 全局固定点唯一性；存在性仍由后续递归构造证明。 -/
theorem unique_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop) (R : set_l ℳ)
    (hWf : ∀ n, SecondOrderDomain.wf_l R n)
    (hTrans : ∀ a b c, relation_l R a b → relation_l R b c → relation_l R a c)
    (hLocal : local_l P R) (H K : set_l ℳ) (hH : P H H) (hK : P K K) : H = K := by
  apply SecondOrderRelations.ext_l hℳ
  intro n a
  exact coherence_l hℳ P R hWf hTrans hLocal H K n n
    ⟨H, hH, fun _ _ _ => Iff.rfl⟩ ⟨K, hK, fun _ _ _ => Iff.rfl⟩ n (Or.inl rfl) (Or.inl rfl) a

#print axioms coherence_l
#print axioms unique_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedAgreement
