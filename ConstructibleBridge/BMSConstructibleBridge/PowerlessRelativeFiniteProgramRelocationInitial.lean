import BMSConstructibleBridge.PowerlessRelativeFiniteProgramRelocationStore
import BMSConstructibleBridge.SecondOrderFiniteConcatArithmetic
import BMSConstructibleBridge.PowerlessAdditionIterationSyntax

/-! # 右程序开始前的实际平移存储不变式

给定同一内部加法图 A(k)=n+k，证明单射、先后关系保持，以及任意
左侧存储图 g:n→D 在所有平移父坐标上与空图具有相同读数。
这消去了存储同步更新中的单射前提，并提供右段内部归纳的初始状态。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramRelocationInitial

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (injective_m)
open PowerlessRelativeFiniteProgramRelocationComputed (reading_m reading_l reading_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₂ t)

def order_m {Γ Δ : SortContext ℒ} (A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let k : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set :=
      .bvar (.there (.there (.there .here)))
    let l := .bvar (.there (.there .here))
    let i := .bvar (.there .here)
    let j := .bvar .here
    .imp (SecondOrderObjectSyntax.value_m (up₄ A) k i) <|
      .imp (SecondOrderObjectSyntax.value_m (up₄ A) l j) <|
        .iff (SecondOrderObjectSyntax.member_m k l) (SecondOrderObjectSyntax.member_m i j)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def order_l (A : type_l hℳ) : Prop :=
  ∀ k l i j, value_l (ℳ := 𝒱) A k i → value_l (ℳ := 𝒱) A l j →
    (mem_l hℳ k l ↔ mem_l hℳ i j)

theorem order_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (A : Term ℒ Γ Δ .set) :
    (order_m A).satisfies η ↔ order_l (A.eval η) := by
  simp only [order_m, order_l, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₄, up₂, up,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem properties_l (K : source_coding_l hℳ) {e n A D g : type_l hℳ}
    (he : ∀ x, ¬mem_l hℳ x e) (hn : mem_l hℳ n K.omega)
    (hA : map_l (ℳ := 𝒱) A K.omega K.omega)
    (hIteration : PowerlessAddition.iteration_l (ℳ := 𝒱) K.omega e n A)
    (hg : map_l (ℳ := 𝒱) g n D) : injective_l (ℳ := 𝒱) A ∧ order_l A ∧ reading_l A e g := by
  obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have haEq : (numberCode_l K a).val = n := congrArg Subtype.val ha
  have hIteration' : PowerlessAddition.iteration_l (ℳ := 𝒱)
      K.omega e (numberCode_l K a).val A := haEq.symm ▸ hIteration
  refine ⟨fun k l i hk hl => SecondOrderFiniteConcatArithmetic.cancel_l K a he hIteration' hA hk hl,
    fun k l i j hk hl => SecondOrderFiniteConcatArithmetic.order_l K a he hIteration' hA hk hl, ?_⟩
  intro k i hki x
  have hi : ¬mem_l hℳ i n := haEq ▸ SecondOrderFiniteConcatArithmetic.lower_l K a he hIteration' hA hki
  apply iff_of_false
  · rintro ⟨p, hp, _⟩
    exact he p hp
  · intro hx
    exact hi (SecondOrderFunctionProperties.value_mem_l hℳ hg hx).1

def schema_m {Δ : SortContext ℒ} (ω e n A D g : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
      .imp (SecondOrderObjectSyntax.member_m n ω) <|
        .imp (SecondOrderObjectSyntax.map_m A ω ω) <|
          .imp (PowerlessAdditionIterationSyntax.formula_m ω e n A) <|
            .imp (SecondOrderObjectSyntax.map_m g n D) <|
              .conj (injective_m A) (.conj (order_m A) (reading_m A e g))

def sentence_m {Δ : SortContext ℒ} (ω e n A D g : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω e n A D g)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω e n A D g : Term ℒ [] Δ .set) :
    (sentence_m ω e n A D g).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, PowerlessDefinableFiniteTraceDerives.zero_m, Formula.satisfies,
    SecondOrderOmegaSyntax.omega_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    map_formula_l, PowerlessAdditionIterationSyntax.formula_l,
    ThirdOrderSemantics.injective_formula_l,
    order_formula_l, reading_formula_l, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here]
  intro η hω he hn hA hIteration hg
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  rw [hωEq] at hn hA hIteration
  exact properties_l K he hn hA hIteration hg

theorem derives_m {Δ : SortContext ℒ} (ω e n A D g : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m ω e n A D g)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 ω e n A D g)

#print axioms properties_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramRelocationInitial
