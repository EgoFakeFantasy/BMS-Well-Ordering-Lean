import BMSConstructibleBridge.SecondOrderComparisonHistoryAgreement

/-! # 单层规范比较的纯对象证书

所有历史见证均为对象语言的集合存在量词。证书保留逐阶段规范方程及
已经由实际递归证明的不变量，不含外部编号、函数选取或外部良基性。
后续存在定理须实际构造此证书；定义本身不是存在性证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalLevelSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderObjectSyntax (member_m map_m)
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
private abbrev up₈ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₄ (up₄ t)

def history_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderComparisonIndexedConfiguration.configuration_m ω B A F r I J T) <|
    .conj (map_m G ω q) <|
      .conj (SecondOrderComparisonCanonicalSyntax.history_m ω e t₁ t₂ t₃ Pair Valid I J T G P₀ A) <|
        .forallE .set <| .imp (member_m (.bvar .here) (up A))
          (SecondOrderComparisonInvariant.at_m (up I) (up J) (up T) (up G) (.bvar .here))

def level_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid B P₀ a X P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
      let A : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
      let F := .bvar (.there (.there (.there (.there (.there (.there .here))))))
      let r := .bvar (.there (.there (.there (.there (.there .here)))))
      let I := .bvar (.there (.there (.there (.there .here))))
      let J := .bvar (.there (.there (.there .here)))
      let T := .bvar (.there (.there .here))
      let G := .bvar (.there .here)
      let q := .bvar .here
      .conj (history_m (up₈ ω) (up₈ e) (up₈ t₁) (up₈ t₂) (up₈ t₃) (up₈ Pair)
        (up₈ Valid) (up₈ B) (up₈ P₀) A F r I J T G q)
        (SecondOrderComparisonHistoryAgreementStep.read_m J T G (up₈ a) (up₈ X) (up₈ P))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

structure history_l (ω e t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q : type_l hℳ) : Prop where
  configuration : SecondOrderComparisonIndexedConfiguration.configuration_l ω B A F r I J T
  comparisonMap : map_l (ℳ := 𝒱) G ω q
  canonical : SecondOrderComparisonCanonicalSyntax.history_l ω e t₁ t₂ t₃ Pair Valid I J T G P₀ A
  invariant : ∀ a, mem_l hℳ a A → SecondOrderComparisonInvariant.at_l (𝒩 := 𝒱) I J T G a

def level_l (ω e t₁ t₂ t₃ Pair Valid B P₀ a X P : type_l hℳ) : Prop :=
  ∃ A F r I J T G q, history_l ω e t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q ∧
    SecondOrderComparisonHistoryAgreementStep.read_l (𝒩 := 𝒱) J T G a X P

theorem history_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q : Term ℒ Γ Δ .set) :
    (history_m ω e t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q).satisfies η ↔
      history_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
        (Valid.eval η) (B.eval η) (P₀.eval η) (A.eval η) (F.eval η) (r.eval η)
        (I.eval η) (J.eval η) (T.eval η) (G.eval η) (q.eval η) := by
  simp only [history_m, Formula.satisfies, SecondOrderComparisonIndexedConfiguration.configuration_formula_l K,
    map_formula_l, SecondOrderComparisonCanonicalSyntax.history_formula_l,
    SecondOrderComparisonInvariant.at_formula_l, member_m, up, Arguments.eval, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩,
    fun h => ⟨h.configuration, h.comparisonMap, h.canonical, h.invariant⟩⟩

theorem level_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ a X P : Term ℒ Γ Δ .set) :
    (level_m ω e t₁ t₂ t₃ Pair Valid B P₀ a X P).satisfies η ↔
      level_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
        (Valid.eval η) (B.eval η) (P₀.eval η) (a.eval η) (X.eval η) (P.eval η) := by
  simp only [level_m, level_l, Formula.satisfies, history_formula_l K,
    SecondOrderComparisonHistoryAgreementStep.read_formula_l, up₈, up₄, up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms level_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalLevelSyntax
