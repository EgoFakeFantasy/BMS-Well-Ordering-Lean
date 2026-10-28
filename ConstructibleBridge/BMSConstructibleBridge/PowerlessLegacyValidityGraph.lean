import BMSConstructibleBridge.PowerlessLegacyValidityBounded
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 原五标签有界证书的实际类集合图

在给定母集 ω×ω 中作纯 Δ₀ 分离，逐值规格量化全部原商坐标，
而不是只量化类坐标。证书自身的两个 ω 守卫吸收构图模式的坐标守卫；
类外坐标的排除与 Δ₀ 绝对性由通用关系图接口承担。

本构图不要求编码参数正确，也不将类成员资格当作实际 ω 守卫。
接口只精确表示给定 ω.val 上的 certificate；原实际 ω、完整 N、标签
读数以及与原旧合法性 V 的等价仍由识别阶段验证。对象模式证明的是
这个有界关系的构图，不是旧合法性识别、统一历史或 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyValidityGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def matrix_m {Δ : SortContext ℒ} (ω e N t₁ t₂ t₃ t₄ : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  let w (t : Term ℒ [] Δ .set) := (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
  PowerlessLegacyValidityBounded.certificate_m (w ω) (w e) (w N) (w t₁) (w t₂) (w t₃) (w t₄)
    (.fvar .here) (.fvar (.there .here))

theorem matrix_delta_l {Δ : SortContext ℒ} (ω e N t₁ t₂ t₃ t₄ : Term ℒ [] Δ .set) :
    Formula.IsDelta0 membershipLevyBound (matrix_m ω e N t₁ t₂ t₃ t₄) :=
  PowerlessLegacyValidityBounded.certificate_delta_l _ _ _ _ _ _ _ _ _

theorem matrix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 [] Δ) (ω e N t₁ t₂ t₃ t₄ : Term ℒ [] Δ .set) (c l : carrier_l 𝒩) :
    (matrix_m ω e N t₁ t₂ t₃ t₄).satisfies ((η.pushFree l).pushFree c) ↔
      PowerlessLegacyValidityBounded.certificate_holds_l (ω.eval η) (e.eval η) (N.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (t₄.eval η) c l := by
  simp only [matrix_m, PowerlessLegacyValidityBounded.certificate_formula_l, Term.eval_weakenFree,
    Term.eval, Env.pushFree_here, Env.pushFree_there]

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    (ω e N t₁ t₂ t₃ t₄ : type_l hℳ B) : ∃ F : type_l hℳ B,
      ∀ c l : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
          PowerlessLegacyValidityBounded.certificate_holds_l («𝒩» := SecondOrderQuotient.structure_l hℳ)
            ω.val e.val N.val t₁.val t₂.val t₃.val t₄.val c l := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set, .set, .set] :=
    (((((((Env.empty).pushFree t₄).pushFree t₃).pushFree t₂).pushFree t₁).pushFree N).pushFree e).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let s : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let b : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let d : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let t : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  obtain ⟨F, hF⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l (matrix_delta_l w z s a b d t) η ω ω
  refine ⟨F, fun c l => ?_⟩
  have h := (hF c l).trans (and_congr Iff.rfl (and_congr Iff.rfl
    (matrix_formula_l (PowerlessRelativeClassRelativization.env_l η) w z s a b d t c l)))
  change value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
    mem_l hℳ c ω.val ∧ mem_l hℳ l ω.val ∧
      PowerlessLegacyValidityBounded.certificate_holds_l («𝒩» := SecondOrderQuotient.structure_l hℳ)
        ω.val e.val N.val t₁.val t₂.val t₃.val t₄.val c l at h
  exact h.trans ⟨And.right ∘ And.right, fun hCertificate => ⟨hCertificate.1, hCertificate.2.1, hCertificate⟩⟩

def sentence_m {Δ : SortContext ℒ} (ω e N t₁ t₂ t₃ t₄ : Term ℒ [] Δ .set) : Sentence ℒ :=
  PowerlessRelativeClassRelativization.guarded_m
    (SecondOrderDefinableRelationImageDerives.sentence_m (matrix_m ω e N t₁ t₂ t₃ t₄))

theorem derives_m {Δ : SortContext ℒ} (ω e N t₁ t₂ t₃ t₄ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω e N t₁ t₂ t₃ t₄)) :=
  PowerlessRelativeClassRelation.derives_m (matrix_delta_l ω e N t₁ t₂ t₃ t₄)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyValidityGraph
