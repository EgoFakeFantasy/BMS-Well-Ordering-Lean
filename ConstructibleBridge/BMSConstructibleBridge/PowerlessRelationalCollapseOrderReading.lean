import BMSConstructibleBridge.PowerlessRelationalCollapseOrderedCut
import BMSConstructibleBridge.SecondOrderOrdinalBounded

/-! # 前驱优先良序坍缩的真实序数索引

纯隶属 ℒ，原 Z₂。已有同一 J 的实际坍缩 P 时，J 的线序条款
推出 P 单射、其值域 α 是原商序数、J 边恰为两端 P 值的隶属。
P 与 α 无须先有 Class 身份；这些读数不使用完整 Collection，
也不把数值编号或宿主良基性充当原内部序数索引。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseOrderReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def reading_l (J P : Raw) : Prop :=
  ∀ x y a b, SecondOrderFunctionObjects.value_l hℳ P x a →
    SecondOrderFunctionObjects.value_l hℳ P y b →
      (SecondOrderFunctionObjects.value_l hℳ J x y ↔ mem_l hℳ a b)

theorem inject_l {I J α P : Raw} (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hP : SecondOrderCollapseFunction.spec_l hℳ J I α P) :
    SecondOrderFunctionObjects.injective_l hℳ P := by
  have hIrrefl (a : Raw) : ¬mem_l hℳ a a := by
    obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
    exact SecondOrderFoundation.irrefl_l hℳ A
  intro x y a hxa hya
  have hx := (SecondOrderFunctionProperties.value_mem_l hℳ hP.2.1 hxa).1
  have hy := (SecondOrderFunctionProperties.value_mem_l hℳ hP.2.1 hya).1
  rcases hJ.2.2.1 x y ⟨hx, hy⟩ with hxy | heq | hyx
  · exact (hIrrefl a ((hP.2.2.2 y a hy hya a).mpr ⟨x, hx, hxy, hxa⟩)).elim
  · exact heq
  · exact (hIrrefl a ((hP.2.2.2 x a hx hxa a).mpr ⟨y, hy, hyx, hya⟩)).elim

theorem reads_l {I J α P : Raw} (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hP : SecondOrderCollapseFunction.spec_l hℳ J I α P) : reading_l J P := by
  intro x y a b hxa hyb
  have hx := (SecondOrderFunctionProperties.value_mem_l hℳ hP.2.1 hxa).1
  have hy := (SecondOrderFunctionProperties.value_mem_l hℳ hP.2.1 hyb).1
  constructor
  · intro hxy
    exact (hP.2.2.2 y b hy hyb a).mpr ⟨x, hx, hxy, hxa⟩
  · intro hab
    obtain ⟨z, _hz, hzy, hza⟩ := (hP.2.2.2 y b hy hyb a).mp hab
    have hEq : z = x := inject_l hJ hP z x a hza hxa
    exact hEq ▸ hzy

theorem ordinal_l {I J α P : Raw} (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hP : SecondOrderCollapseFunction.spec_l hℳ J I α P) :
    SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α := by
  apply SecondOrderOrdinalBounded.of_transitive_l hℳ
  · exact fun a ha b hb => hP.1 a b ha hb
  · intro a ha b hb c hc
    obtain ⟨x, hx, hxa⟩ := hP.2.2.1 a ha
    obtain ⟨y, hy, hyx, hyb⟩ := (hP.2.2.2 x a hx hxa b).mp hb
    obtain ⟨z, hz, hzy, hzc⟩ := (hP.2.2.2 y b hy hyb c).mp hc
    exact (hP.2.2.2 x a hx hxa c).mpr ⟨z, hz, hJ.2.1 z y x ⟨hz, hy, hx⟩ hzy hyx, hzc⟩
  · intro a b ha hb
    obtain ⟨x, hx, hxa⟩ := hP.2.2.1 a ha
    obtain ⟨y, hy, hyb⟩ := hP.2.2.1 b hb
    rcases hJ.2.2.1 x y ⟨hx, hy⟩ with hxy | heq | hyx
    · exact Or.inl ((reads_l hJ hP x y a b hxa hyb).mp hxy)
    · exact Or.inr (Or.inl (SecondOrderFunctionProperties.value_unique_l hℳ hP.2.1 (heq ▸ hxa) hyb))
    · exact Or.inr (Or.inr ((reads_l hJ hP y x b a hyb hxa).mp hyx))

def reading_m {Γ Δ : SortContext ℒ} (J P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
    let x : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
    let y : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let a : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let b : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .imp (SecondOrderObjectSyntax.value_m (w P) x a) <|
      .imp (SecondOrderObjectSyntax.value_m (w P) y b) <|
        .iff (SecondOrderObjectSyntax.value_m (w J) x y) (member_m a b)

theorem reading_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (J P : Term ℒ Γ Δ .set) : (reading_m J P).satisfies η ↔ reading_l (J.eval η) (P.eval η) := by
  simp only [reading_m, reading_l, Formula.satisfies, SecondOrderObjectSyntax.value_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (I J α P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m I J) <|
    .imp (SecondOrderCollapseSyntax.formula_m J I α P) <|
      .conj (PowerlessOrdinalBounded.ordinal_m α) <|
        .conj (SecondOrderObjectSyntax.injective_m P) (reading_m J P)

def sentence_m {Δ : SortContext ℒ} (I J α P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m I J α P)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (I J α P : Term ℒ [] Δ .set) : (sentence_m I J α P).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    SecondOrderCollapseSyntax.formula_l, SecondOrderOrdinalBounded.formula_l,
    SecondOrderObjectSyntax.injective_l, reading_formula_l]
  exact fun hJ hP => ⟨ordinal_l (hℳ := hℳ) hJ hP, inject_l hJ hP, reads_l hJ hP⟩

theorem derives_m {Δ : SortContext ℒ} (I J α P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m I J α P)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ I J α P)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseOrderReading
