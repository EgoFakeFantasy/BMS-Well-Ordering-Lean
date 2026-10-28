import BMSConstructibleBridge.PowerlessLegacyTranslationBounded
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 原部分翻译证书的实际 Class 二元图

输出状态仍编码为原平方 pair(l,q)。显式两个 ω 守卫排除所有类外和
非数字坐标。此模块只证明有界证书关系的构图；参数正确性与原翻译
识别另行核验。对象出口是原 GraphTranslation 的构图推导模式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyTranslationGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def formula_m {Γ Δ : SortContext ℒ}
    (ω e N T t₁ t₂ t₃ t₄ G c s : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (member_m c ω) <| .conj (member_m s ω) <|
    membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <| .conj
      (PowerlessBoundedNumericPairing.formula_m (up₂ ω) (up₂ e) (up₂ N)
        (.bvar (.there .here)) (.bvar .here) (up₂ s))
      (PowerlessLegacyTranslationBounded.certificate_m (up₂ ω) (up₂ e) (up₂ N) (up₂ T)
        (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ t₄) (up₂ G) (up₂ c) (.bvar (.there .here)) (.bvar .here))

theorem delta_l {Γ Δ : SortContext ℒ}
    (ω e N T t₁ t₂ t₃ t₄ G c s : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e N T t₁ t₂ t₃ t₄ G c s) :=
  .conj (.rel _ _) <| .conj (.rel _ _) <| .bounded_exists ω <| .bounded_exists (up ω) <|
    .conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
      (PowerlessLegacyTranslationBounded.certificate_delta_l _ _ _ _ _ _ _ _ _ _ _ _)

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N T t₁ t₂ t₃ t₄ G c s : carrier_l 𝒩) : Prop :=
  member_l 𝒩 c ω ∧ member_l 𝒩 s ω ∧ ∃ l, member_l 𝒩 l ω ∧ ∃ q, member_l 𝒩 q ω ∧
    PowerlessBoundedNumericPairing.holds_l ω e N l q s ∧
      PowerlessLegacyTranslationBounded.certificate_holds_l ω e N T t₁ t₂ t₃ t₄ G c l q

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₁ t₂ t₃ t₄ G c s : Term ℒ Γ Δ .set) :
    (formula_m ω e N T t₁ t₂ t₃ t₄ G c s).satisfies η ↔ holds_l
      (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (t₄.eval η)
        (G.eval η) (c.eval η) (s.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessBoundedNumericPairing.formula_l, PowerlessLegacyTranslationBounded.certificate_formula_l,
    member_m, member_l, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def matrix_m {Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ t₄ G : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  let w (t : Term ℒ [] Δ .set) := (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
  formula_m (w ω) (w e) (w N) (w T) (w t₁) (w t₂) (w t₃) (w t₄) (w G)
    (.fvar .here) (.fvar (.there .here))

theorem matrix_delta_l {Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ t₄ G : Term ℒ [] Δ .set) :
    Formula.IsDelta0 membershipLevyBound (matrix_m ω e N T t₁ t₂ t₃ t₄ G) :=
  delta_l _ _ _ _ _ _ _ _ _ _ _

theorem matrix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 [] Δ) (ω e N T t₁ t₂ t₃ t₄ G : Term ℒ [] Δ .set) (c s : carrier_l 𝒩) :
    (matrix_m ω e N T t₁ t₂ t₃ t₄ G).satisfies ((η.pushFree s).pushFree c) ↔ holds_l
      (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (t₄.eval η)
        (G.eval η) c s := by
  simp only [matrix_m, formula_l, Term.eval_weakenFree,
    Term.eval, Env.pushFree_here, Env.pushFree_there]

set_option maxHeartbeats 800000 in
theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    (ω e N T t₁ t₂ t₃ t₄ G : type_l hℳ B) : ∃ F : type_l hℳ B,
      ∀ c s : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c s ↔
          holds_l («𝒩» := SecondOrderQuotient.structure_l hℳ)
            ω.val e.val N.val T.val t₁.val t₂.val t₃.val t₄.val G.val c s := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    (((((((((Env.empty).pushFree G).pushFree t₄).pushFree t₃).pushFree t₂).pushFree t₁).pushFree T).pushFree N).pushFree e).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let seq : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let t : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let b : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let d : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let v : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let g : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  obtain ⟨F, hF⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l
    (matrix_delta_l w z seq t a b d v g) η ω ω
  refine ⟨F, fun c s => ?_⟩
  have h := (hF c s).trans (and_congr Iff.rfl (and_congr Iff.rfl
    (matrix_formula_l (PowerlessRelativeClassRelativization.env_l η) w z seq t a b d v g c s)))
  change value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c s ↔
    mem_l hℳ c ω.val ∧ mem_l hℳ s ω.val ∧
      holds_l («𝒩» := SecondOrderQuotient.structure_l hℳ)
        ω.val e.val N.val T.val t₁.val t₂.val t₃.val t₄.val G.val c s at h
  exact h.trans ⟨And.right ∘ And.right, fun hBody => ⟨hBody.1, hBody.2.1, hBody⟩⟩

def sentence_m {Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ t₄ G : Term ℒ [] Δ .set) : Sentence ℒ :=
  PowerlessRelativeClassRelativization.guarded_m
    (SecondOrderDefinableRelationImageDerives.sentence_m (matrix_m ω e N T t₁ t₂ t₃ t₄ G))

theorem derives_m {Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ t₄ G : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m ω e N T t₁ t₂ t₃ t₄ G)) :=
  PowerlessRelativeClassRelation.derives_m (matrix_delta_l ω e N T t₁ t₂ t₃ t₄ G)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyTranslationGraph
