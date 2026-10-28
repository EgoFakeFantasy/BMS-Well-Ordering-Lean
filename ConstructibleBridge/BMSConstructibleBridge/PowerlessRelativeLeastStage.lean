import BMSConstructibleBridge.PowerlessRelativeClassCorrespondence
import BMSConstructibleBridge.SecondOrderOrdinalComparison

/-! # 相对并类对象的最小出现阶段

最小阶段由实际纯公式的类极小元模式取得；序数三歧性给出唯一性。该模式
不抽取全局秩函数，也没有把最小阶段值域的有界性当作已证明的 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLeastStage

open Logic FirstOrder PowerlessBMSQuotientCoding SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) := SecondOrderQuotient.structure_l hℳ

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def occurs_m {Γ Δ : SortContext ℒ} (B X a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.level_m (up B) (up a) (.bvar .here))
    (member_m (up X) (.bvar .here))

def rank_m {Γ Δ : SortContext ℒ} (B X a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (occurs_m B X a) <| .forallE .set <|
    .imp (member_m (.bvar .here) (up a)) (.neg (occurs_m (up B) (up X) (.bvar .here)))

def occurs_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B X a : type_l hℳ) : Prop :=
  ∃ c, PowerlessRelativeHierarchySemantics.level_l hℳ B a c ∧ mem_l hℳ X c

def rank_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B X a : type_l hℳ) : Prop :=
  occurs_l hℳ B X a ∧ ∀ b, mem_l hℳ b a → ¬occurs_l hℳ B X b

theorem occurs_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B X a : Term ℒ Γ Δ .set) :
    (occurs_m B X a).satisfies η ↔ occurs_l hℳ (B.eval η) (X.eval η) (a.eval η) := by
  simp only [occurs_m, up, Formula.satisfies, PowerlessRelativeHierarchySemantics.level_formula_l K,
    member_m, Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

theorem rank_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (B X a : Term ℒ Γ Δ .set) :
    (rank_m B X a).satisfies η ↔ rank_l hℳ (B.eval η) (X.eval η) (a.eval η) := by
  simp only [rank_m, up, Formula.satisfies, occurs_formula_l K,
    member_m, Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

theorem ordinal_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B X a : type_l hℳ}
    (ha : occurs_l hℳ B X a) :
    SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) a := by
  obtain ⟨c, ⟨A, _, _, hA, haA, _, _⟩, _⟩ := ha
  apply SetTheory.Structure.IsOrdinal.mem hA
  exact haA

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (K : source_coding_l hℳ)
    {B X : type_l hℳ} (hX : PowerlessRelativeClassCorrespondence.member_l hℳ B X) :
    ∃ a, rank_l hℳ B X a := by
  let φ : Formula ℒ [] [.set, .set, .set] :=
    occurs_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  let η : Env (quotient_l hℳ) [] [.set, .set] := Env.empty |>.pushFree X |>.pushFree B
  have hRead a : φ.satisfies (η.pushFree a) ↔ occurs_l hℳ B X a := occurs_formula_l K _ _ _ _
  have hSome : ∃ a, φ.satisfies (η.pushFree a) := by
    obtain ⟨a, c, hLevel, hXc⟩ := hX
    exact ⟨a, (hRead a).mpr ⟨c, hLevel, hXc⟩⟩
  obtain ⟨a, ha, hMin⟩ := PowerlessWeakSetInduction.minimum_l (SecondOrderWeakSetTheory.models_l hℳ) φ η hSome
  exact ⟨a, (hRead a).mp ha, fun b hb hOcc => hMin b hb ((hRead b).mpr hOcc)⟩

theorem unique_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B X a b : type_l hℳ}
    (ha : rank_l hℳ B X a) (hb : rank_l hℳ B X b) : a = b := by
  rcases SecondOrderOrdinalComparison.compare_l hℳ (ordinal_l hℳ ha.1) (ordinal_l hℳ hb.1) with h | h | h
  · exact h
  · exact False.elim (hb.2 a h ha.1)
  · exact False.elim (ha.2 b h hb.1)

def schema_m : Formula ℒ [] [.set, .set] :=
  .imp (PowerlessRelativeHierarchySyntax.class_m (.fvar .here) (.fvar (.there .here))) <|
    .existsE .set <| .conj (rank_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))
      (.forallE .set <| .imp (rank_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))
        (.equal (.bvar .here) (.bvar (.there .here))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem schema_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (K : source_coding_l hℳ)
    (η : Env (quotient_l hℳ) [] [.set, .set]) : schema_m.satisfies η := by
  intro hX
  have hClass := (PowerlessRelativeHierarchySemantics.class_formula_l K η (.fvar .here) (.fvar (.there .here))).mp hX
  obtain ⟨a, ha⟩ := exists_l hℳ K hClass
  refine ⟨a, (rank_formula_l K (η.pushBound a) (.fvar .here) (.fvar (.there .here)) (.bvar .here)).mpr ha, ?_⟩
  intro b hb
  have hb' := (rank_formula_l K ((η.pushBound a).pushBound b)
    (.fvar .here) (.fvar (.there .here)) (.bvar .here)).mp hb
  exact unique_l hℳ hb' ha

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn (quotient_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  exact schema_formula_l hℳ K

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLeastStage
