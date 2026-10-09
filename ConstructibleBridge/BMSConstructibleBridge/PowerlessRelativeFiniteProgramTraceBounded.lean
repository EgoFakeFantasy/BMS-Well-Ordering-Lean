import BMSConstructibleBridge.PowerlessRelativeFiniteProgramStepBounded
import BMSConstructibleBridge.PowerlessDefinableFiniteTraceBounded
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramExecution

/-! # 实际程序有限历史的纯有界正文

将有界 Step 接入同一内部有限历史。历史陪域属于传递层 W，因而
所有实际状态读数都属于 W；只在这些读数上使用单步等价，不声称
任意层外输入上的两个转移关系相同。纯 Δ₀ 分类仍要求算子正文为 Δ₀。
对象出口精确回到原程序 relation_m 的原 trace，不更换执行语义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramTraceBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev free₂ {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) :=
  (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set

def relation_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: .set :: Δ) :=
  PowerlessRelativeFiniteProgramStepBounded.step_m
    (PowerlessDefinableFiniteTrace.lift_m (PowerlessDefinableFiniteTrace.lift_m φ))
    (free₂ B) (free₂ C) (free₂ W) (free₂ ω) (free₂ w) (free₂ e)
      (free₂ t₀) (free₂ t₁) (free₂ t₂) (.fvar (.there .here)) (.fvar .here)

private theorem lift_delta_l {Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    Formula.IsDelta0 membershipLevyBound (PowerlessDefinableFiniteTrace.lift_m φ) := by
  unfold PowerlessDefinableFiniteTrace.lift_m
  exact Formula.IsDelta0.substituteMapped
    (boundSubstitution := fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (freeSubstitution := _) hφ

theorem relation_delta_l {Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    Formula.IsDelta0 membershipLevyBound (relation_m φ B C W ω w e t₀ t₁ t₂) :=
  PowerlessRelativeFiniteProgramStepBounded.step_delta_l (lift_delta_l (lift_delta_l hφ))
    _ _ _ _ _ _ _ _ _ _ _

def trace_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set)
    (a n S D f : Term ℒ Γ Δ .set) (e₀ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessDefinableFiniteTraceBounded.trace_m (relation_m φ B C W ω w e t₀ t₁ t₂) e₀ a n S D f

theorem trace_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B C W ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set)
    (a n S D f e₀ : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (trace_m φ B C W ω w e t₀ t₁ t₂ a n S D f e₀) :=
  PowerlessDefinableFiniteTraceBounded.trace_delta_l (relation_delta_l hφ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem relation_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B β C W ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) (s t : type_l hℳ)
    (hB : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hβ : limit_l hℳ (β.eval η)) (hW : level_l hℳ (B.eval η) (β.eval η) (W.eval η))
    (hBW : mem_l hℳ (B.eval η) (W.eval η))
    (hC : ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x (W.eval η))
    (hw : mem_l hℳ (w.eval η) (W.eval η)) (he : mem_l hℳ (e.eval η) (W.eval η))
    (hs : mem_l hℳ s (W.eval η))
    (hφ : PowerlessRelativeFiniteProgramLimitStep.closed_l φ η (B.eval η) (W.eval η)) :
    (relation_m φ B C W ω w e t₀ t₁ t₂).satisfies ((η.pushFree s).pushFree t) ↔
      PowerlessRelativeFiniteProgramStep.step_l φ η (B.eval η) (C.eval η) (ω.eval η)
        (w.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) s t := by
  simpa only [relation_m, parameters_empty_l, free₂, Term.eval_weakenFree,
    Term.eval, Env.pushFree_here, Env.pushFree_there,
    PowerlessRelativeFiniteProgramStep.step_l, PowerlessRelativeFiniteProgramStep.good_l,
    PowerlessRelativeFiniteProgramStore.store_l, PowerlessRelativeFiniteProgramInstruction.computed_l,
    PowerlessRelativeFiniteProgramInstruction.good_l, PowerlessDefinableFiniteTrace.lift_formula_l] using
    PowerlessRelativeFiniteProgramStepBounded.step_formula_l
      (PowerlessDefinableFiniteTrace.lift_m (PowerlessDefinableFiniteTrace.lift_m φ))
      ((η.pushFree s).pushFree t) (free₂ B) (free₂ β) (free₂ C) (free₂ W)
      (free₂ ω) (free₂ w) (free₂ e) (free₂ t₀) (free₂ t₁) (free₂ t₂)
      (.fvar (.there .here)) (.fvar .here)
      (by simpa only [free₂, Term.eval_weakenFree] using hB)
      (by simpa only [free₂, Term.eval_weakenFree] using hβ)
      (by simpa only [free₂, Term.eval_weakenFree] using hW)
      (by simpa only [free₂, Term.eval_weakenFree] using hBW)
      (by simpa only [free₂, Term.eval_weakenFree] using hC)
      (by simpa only [free₂, Term.eval_weakenFree] using hw)
      (by simpa only [free₂, Term.eval_weakenFree] using he)
      (by simpa only [free₂, Term.eval_weakenFree, Term.eval, Env.pushFree_here,
        Env.pushFree_there] using hs)
      (by simpa only [PowerlessRelativeFiniteProgramLimitStep.closed_l, parameters_empty_l,
        free₂, Term.eval_weakenFree, PowerlessDefinableFiniteTrace.lift_formula_l] using hφ)

theorem trace_equiv_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B β C W ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) (e₀ a n S D f : type_l hℳ)
    (hB : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hβ : limit_l hℳ (β.eval η)) (hW : level_l hℳ (B.eval η) (β.eval η) (W.eval η))
    (hBW : mem_l hℳ (B.eval η) (W.eval η))
    (hC : ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x (W.eval η))
    (hw : mem_l hℳ (w.eval η) (W.eval η)) (he : mem_l hℳ (e.eval η) (W.eval η))
    (hD : mem_l hℳ D (W.eval η)) (hn : mem_l hℳ n K.omega)
    (hφ : PowerlessRelativeFiniteProgramLimitStep.closed_l φ η (B.eval η) (W.eval η)) :
    PowerlessDefinableFiniteTraceBounded.trace_l (relation_m φ B C W ω w e t₀ t₁ t₂) η e₀ a n S D f ↔
      PowerlessDefinableFiniteTrace.trace_l
        (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂) η e₀ a n S D f := by
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hB hW
  have hEq (x y : type_l hℳ) (hx : mem_l hℳ x D) :
      (relation_m φ B C W ω w e t₀ t₁ t₂).satisfies ((η.pushFree x).pushFree y) ↔
        (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂).satisfies
          ((η.pushFree x).pushFree y) :=
    (relation_formula_l φ η B β C W ω w e t₀ t₁ t₂ x y hB hβ hW hBW hC hw he
      (hTrans _ hD _ hx) hφ).trans
        (PowerlessRelativeFiniteProgramExecution.relation_formula_l K φ η B C ω w e t₀ t₁ t₂ x y).symm
  have hSame : PowerlessDefinableFiniteTraceBounded.trace_l
      (relation_m φ B C W ω w e t₀ t₁ t₂) η e₀ a n S D f ↔
        PowerlessDefinableFiniteTraceBounded.trace_l
          (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂) η e₀ a n S D f := by
    constructor
    · rintro ⟨hS, hf, h₀, hStep⟩
      exact ⟨hS, hf, h₀, fun i hi j hj x hx y hy hij hix hjy =>
        (hEq x y hx).mp (hStep i hi j hj x hx y hy hij hix hjy)⟩
    · rintro ⟨hS, hf, h₀, hStep⟩
      exact ⟨hS, hf, h₀, fun i hi j hj x hx y hy hij hix hjy =>
        (hEq x y hx).mpr (hStep i hi j hj x hx y hy hij hix hjy)⟩
  exact hSame.trans (PowerlessDefinableFiniteTraceBounded.equiv_l K _ η hn)

-- 自由参数环境保持不变，历史见证可在任意绑定上下文中传入。
theorem trace_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B β C W ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) (a n S D f e₀ : Term ℒ Γ Δ .set)
    (hB : ∀ x, mem_l hℳ x (B.eval (parameters_l η)) →
      ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval (parameters_l η)))
    (hβ : limit_l hℳ (β.eval (parameters_l η)))
    (hW : level_l hℳ (B.eval (parameters_l η)) (β.eval (parameters_l η)) (W.eval (parameters_l η)))
    (hBW : mem_l hℳ (B.eval (parameters_l η)) (W.eval (parameters_l η)))
    (hC : ∀ x, mem_l hℳ x (C.eval (parameters_l η)) → mem_l hℳ x (W.eval (parameters_l η)))
    (hw : mem_l hℳ (w.eval (parameters_l η)) (W.eval (parameters_l η)))
    (he : mem_l hℳ (e.eval (parameters_l η)) (W.eval (parameters_l η)))
    (hD : mem_l hℳ (D.eval η) (W.eval (parameters_l η))) (hn : mem_l hℳ (n.eval η) K.omega)
    (hφ : PowerlessRelativeFiniteProgramLimitStep.closed_l φ (parameters_l η)
      (B.eval (parameters_l η)) (W.eval (parameters_l η))) :
    (trace_m φ B C W ω w e t₀ t₁ t₂ a n S D f e₀).satisfies η ↔
      PowerlessDefinableFiniteTrace.trace_l
        (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂) (parameters_l η)
        (e₀.eval η) (a.eval η) (n.eval η) (S.eval η) (D.eval η) (f.eval η) := by
  rw [trace_m, PowerlessDefinableFiniteTraceBounded.trace_formula_l]
  exact trace_equiv_l K φ (parameters_l η) B β C W ω w e t₀ t₁ t₂
    (e₀.eval η) (a.eval η) (n.eval η) (S.eval η) (D.eval η) (f.eval η)
    hB hβ hW hBW hC hw he hD hn hφ

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w e t₀ t₁ t₂ a n S D f : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .imp (SecondOrderObjectSyntax.member_m B W) <| .imp (ThirdOrderTheory.subset_m C W) <|
          .imp (SecondOrderObjectSyntax.member_m w W) <| .imp (SecondOrderObjectSyntax.member_m e W) <|
            .imp (SecondOrderObjectSyntax.member_m D W) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
              .imp (SecondOrderObjectSyntax.member_m n ω) <|
                .imp (PowerlessRelativeFiniteProgramLimitStep.closed_m φ B W) <|
                  .iff (trace_m φ B C W ω w e t₀ t₁ t₂ a n S D f e)
                    (PowerlessDefinableFiniteTrace.trace_m
                      (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂) e a n S D f)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w e t₀ t₁ t₂ a n S D f : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β C W ω w e t₀ t₁ t₂ a n S D f)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B β C W ω w e t₀ t₁ t₂ a n S D f : Term ℒ [] Δ .set) :
    (sentence_m φ B β C W ω w e t₀ t₁ t₂ a n S D f).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K, subset_formula_l, SecondOrderOmegaSyntax.omega_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, PowerlessDefinableFiniteTrace.trace_formula_l,
    parameters_empty_l]
  intro η hB hβ hW hBW hC hw he hD hω hn hφ
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  simpa only [parameters_empty_l] using
    trace_formula_l K φ η B β C W ω w e t₀ t₁ t₂ a n S D f e
      (by simpa only [parameters_empty_l] using hB)
      (by simpa only [parameters_empty_l] using hβ)
      (by simpa only [parameters_empty_l] using hW)
      (by rw [parameters_empty_l]; exact hBW)
      (by rw [parameters_empty_l]; exact hC)
      (by rw [parameters_empty_l]; exact hw)
      (by rw [parameters_empty_l]; exact he)
      (by rw [parameters_empty_l]; exact hD) (hωEq ▸ hn)
      (by simpa only [parameters_empty_l] using hφ)

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω w e t₀ t₁ t₂ a n S D f : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β C W ω w e t₀ t₁ t₂ a n S D f)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B β C W ω w e t₀ t₁ t₂ a n S D f)

#print axioms relation_delta_l
#print axioms trace_delta_l
#print axioms trace_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramTraceBounded
