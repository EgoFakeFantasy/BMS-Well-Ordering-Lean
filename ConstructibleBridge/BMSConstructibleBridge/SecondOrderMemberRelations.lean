import BMSConstructibleBridge.SecondOrderMemberNormalizer

/-!
# 成员代表之间的内部相等图与成员图

把正规化关系与最大内部双模拟组合为实际二元理解公式。得到整个模型数域
上的两个关系图，避免把外部商映射的任意逆像直接当成内部集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberRelations

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderMemberNormalizer (value_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def equality_m : Formula signature_m [] [.num, .num, .set, .set] :=
  .existsE .num <| .existsE .num <|
    .conj (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there .here))) <|
      .conj (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.bvar .here)) <|
        GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.bvar .here)

def membership_m : Formula signature_m [] [.num, .num, .set, .set, .set] :=
  .existsE .num <| .existsE .num <| .existsE .num <|
    .conj (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there (.there .here)))) <|
      .conj (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.bvar (.there .here))) <|
        .conj (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.bvar .here) (.bvar (.there .here))) <|
          GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there .here))) (.bvar .here)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (r a : num_l ℳ) :
    ∃ Q S : set_l ℳ,
      (∀ n m, relation_l Q n m ↔ SecondOrderBisimulation.eq_l R R (value_l R r a n) (value_l R r a m)) ∧
      ∀ n m, relation_l S n m ↔ ∃ b, relation_l R b (value_l R r a m) ∧
        SecondOrderBisimulation.eq_l R R (value_l R r a n) b := by
  obtain ⟨N, hN⟩ := SecondOrderMemberNormalizer.exists_l hℳ R r a
  obtain ⟨B, hB⟩ := SecondOrderBisimulation.maximum_l hℳ R R
  obtain ⟨Q, hQ⟩ := SecondOrderRelations.comprehension_l hℳ equality_m (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree B).pushFree N)
  obtain ⟨S, hS⟩ := SecondOrderRelations.comprehension_l hℳ membership_m (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree B).pushFree R).pushFree N)
  refine ⟨Q, S, ?_, ?_⟩
  · intro n m
    refine (hQ n m).trans ?_
    simp only [equality_m, Formula.satisfies, SecondOrderPairing.edge_l]
    change (∃ x y, relation_l N n x ∧ relation_l N m y ∧ relation_l B x y) ↔ _
    simp only [hN, hB]
    simp
  · intro n m
    refine (hS n m).trans ?_
    simp only [membership_m, Formula.satisfies, SecondOrderPairing.edge_l]
    change (∃ x y b, relation_l N n x ∧ relation_l N m y ∧ relation_l R b y ∧ relation_l B x b) ↔ _
    simp only [hN, hB]
    simp

theorem graphs_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) : ∃ Q S : set_l ℳ,
      (∀ n m, relation_l Q n m ↔ SecondOrderGraph.eq_l
        (SecondOrderMemberNormalizer.code_l hℳ A a ha n) (SecondOrderMemberNormalizer.code_l hℳ A a ha m)) ∧
      ∀ n m, relation_l S n m ↔ SecondOrderGraph.mem_l
        (SecondOrderMemberNormalizer.code_l hℳ A a ha n) (SecondOrderMemberNormalizer.code_l hℳ A a ha m) := by
  obtain ⟨Q, S, hQ, hS⟩ := exists_l hℳ A.real A.root a
  exact ⟨Q, S, hQ, hS⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberRelations
