import BMSConstructibleBridge.PowerlessFiniteEvaluationQuery
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeClassValueCoordinates

/-! # 稳定有限求值查询的类内集合关系图

对实际有限历史检查式使用类内 Δ₀ 分离，产生集合关系，不收集所有列值。
所有静态参数由类内环境给定，故 C 与 Seq(C) 均必须已经属于相对类。
有界绝对性把类内图逐值规格接回原商查询；构图闭句有原 Z₂ 推导。
这仍不是良构公式的语义真值图，后者还需编码及局部规则正确性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationQueryGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def matrix_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  let w (t : Term ℒ [] Δ .set) := (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set
  PowerlessFiniteEvaluationQuery.formula_m (w C) (w ω) (w e) (w N) (w T) (w A) (w S)
    (w t₁) (w t₂) (w t₃) (w Q) (.fvar .here) (.fvar (.there .here))

theorem matrix_delta_l {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) :
    Formula.IsDelta0 membershipLevyBound (matrix_m C ω e N T A S t₁ t₂ t₃ Q) :=
  PowerlessFiniteEvaluationQuery.delta_l _ _ _ _ _ _ _ _ _ _ _ _ _

theorem matrix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 [] Δ) (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) (k f : carrier_l 𝒩) :
    (matrix_m C ω e N T A S t₁ t₂ t₃ Q).satisfies ((η.pushFree f).pushFree k) ↔
      PowerlessFiniteEvaluationQuery.holds_l (C.eval η) (ω.eval η) (e.eval η) (N.eval η)
        (T.eval η) (A.eval η) (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Q.eval η) k f := by
  simp only [matrix_m, PowerlessFiniteEvaluationQuery.formula_l, Term.eval_weakenFree, Term.eval,
    Env.pushFree_here, Env.pushFree_there]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) (X Y : type_l hℳ B) :
    ∃ G : type_l hℳ B, ∀ k f : type_l hℳ B,
      value_l (ℳ := structure_l hℳ B hBase) G k f ↔
        mem_l hℳ k.val X.val ∧ mem_l hℳ f.val Y.val ∧
          PowerlessFiniteEvaluationQuery.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
            (C.eval (PowerlessRelativeClassRelativization.env_l η))
            (ω.eval (PowerlessRelativeClassRelativization.env_l η))
            (e.eval (PowerlessRelativeClassRelativization.env_l η))
            (N.eval (PowerlessRelativeClassRelativization.env_l η))
            (T.eval (PowerlessRelativeClassRelativization.env_l η))
            (A.eval (PowerlessRelativeClassRelativization.env_l η))
            (S.eval (PowerlessRelativeClassRelativization.env_l η))
            (t₁.eval (PowerlessRelativeClassRelativization.env_l η))
            (t₂.eval (PowerlessRelativeClassRelativization.env_l η))
            (t₃.eval (PowerlessRelativeClassRelativization.env_l η))
            (Q.eval (PowerlessRelativeClassRelativization.env_l η)) k.val f.val := by
  obtain ⟨G, hRead⟩ := PowerlessRelativeClassRelationalGraph.exists_l
    (matrix_delta_l C ω e N T A S t₁ t₂ t₃ Q) η X Y
  refine ⟨G, fun k f => (hRead k f).trans (and_congr Iff.rfl (and_congr Iff.rfl ?_))⟩
  have hEnv : PowerlessRelativeClassRelativization.env_l
      ((η.pushFree (sort := SetTheory.SetSort.set) f).pushFree (sort := SetTheory.SetSort.set) k) =
      ((PowerlessRelativeClassRelativization.env_l η).pushFree (sort := SetTheory.SetSort.set) f.val).pushFree
        (sort := SetTheory.SetSort.set) k.val := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => rfl
      | there v => cases v <;> rfl
  have hAbsolute := PowerlessRelativeClassBounded.formula_l
    (matrix_delta_l C ω e N T A S t₁ t₂ t₃ Q) ((η.pushFree f).pushFree k)
  rw [hEnv] at hAbsolute
  exact hAbsolute.trans (matrix_formula_l (PowerlessRelativeClassRelativization.env_l η)
    C ω e N T A S t₁ t₂ t₃ Q k.val f.val)

/-- 同一类内图的规格覆盖所有原商输入，排除类外坐标上的伪取值。 -/
theorem exists_ambient_l {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) (X Y : type_l hℳ B) :
    ∃ G : type_l hℳ B, ∀ k f : SecondOrderQuotient.type_l hℳ,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val k f ↔
        mem_l hℳ k X.val ∧ mem_l hℳ f Y.val ∧
          PowerlessFiniteEvaluationQuery.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
            (C.eval (PowerlessRelativeClassRelativization.env_l η))
            (ω.eval (PowerlessRelativeClassRelativization.env_l η))
            (e.eval (PowerlessRelativeClassRelativization.env_l η))
            (N.eval (PowerlessRelativeClassRelativization.env_l η))
            (T.eval (PowerlessRelativeClassRelativization.env_l η))
            (A.eval (PowerlessRelativeClassRelativization.env_l η))
            (S.eval (PowerlessRelativeClassRelativization.env_l η))
            (t₁.eval (PowerlessRelativeClassRelativization.env_l η))
            (t₂.eval (PowerlessRelativeClassRelativization.env_l η))
            (t₃.eval (PowerlessRelativeClassRelativization.env_l η))
            (Q.eval (PowerlessRelativeClassRelativization.env_l η)) k f := by
  obtain ⟨G, hG⟩ := exists_l η C ω e N T A S t₁ t₂ t₃ Q X Y
  refine ⟨G, fun k f => ⟨?_, ?_⟩⟩
  · intro hValue
    obtain ⟨hk, hf⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase G hValue
    exact (hG ⟨k, hk⟩ ⟨f, hf⟩).mp
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G ⟨k, hk⟩ ⟨f, hf⟩).mpr hValue)
  · rintro ⟨hk, hf, hQuery⟩
    let k' : type_l hℳ B := ⟨k, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hk⟩
    let f' : type_l hℳ B := ⟨f, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hf⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G k' f').mp
      ((hG k' f').mpr ⟨hk, hf, hQuery⟩)

def sentence_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) : Sentence ℒ :=
  PowerlessRelativeClassRelativization.guarded_m
    (SecondOrderDefinableRelationImageDerives.sentence_m (matrix_m C ω e N T A S t₁ t₂ t₃ Q))

theorem derives_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m C ω e N T A S t₁ t₂ t₃ Q)) :=
  PowerlessRelativeClassRelation.derives_m (matrix_delta_l C ω e N T A S t₁ t₂ t₃ Q)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationQueryGraph
