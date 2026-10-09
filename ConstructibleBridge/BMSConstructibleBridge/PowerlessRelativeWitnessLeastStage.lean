import BMSConstructibleBridge.PowerlessRelativeClassBounds

/-! # 实际公式见证的唯一最小出现阶段

对固定纯公式 φ(y,参数)，最小化的是包含某个合格见证的阶段，而非预先
指定见证的秩。正文可先作类相对化；这里保持传入的同一实际公式不变。
用弱集合归纳的可定义类极小元模式和序数比较证明存在唯一，不抽取
见证函数，也不宣称一族最小阶段已经有共同界或满足 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeWitnessLeastStage

open Logic FirstOrder SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l)
open PowerlessWeakSetInduction (at_m at_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :=
  SecondOrderQuotient.structure_l hℳ

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 自由头槽是候选阶段；两个绑定槽依次为见证与层。 -/
private def witnessParameters_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: Δ) [.set, .set] (.set :: Δ)
  | _, .here => .bvar .here
  | _, .there v => .fvar (.there v)

def occurs_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: Δ) :=
  .existsE .set <|
    .conj (PowerlessRelativeHierarchySyntax.level_m
      (up (B.weakenFree SetTheory.SetSort.set)) (.fvar .here) (.bvar .here)) <|
      .existsE .set <| .conj (member_m (.bvar .here) (.bvar (.there .here)))
        (φ.substitute (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
          witnessParameters_m))

def occurs_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (B a : type_l hℳ) : Prop :=
  ∃ C, level_l hℳ B a C ∧ ∃ y, mem_l hℳ y C ∧ φ.satisfies (η.pushFree y)

theorem occurs_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (quotient_l hℳ) [] Δ)
    (B : Term ℒ [] Δ .set) (a : type_l hℳ) :
    (occurs_m φ B).satisfies (η.pushFree a) ↔ occurs_l φ η (B.eval η) a := by
  have hWitness (C y : type_l hℳ) :
      (φ.substitute (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
        witnessParameters_m)).satisfies
        (((η.pushFree a).pushBound C).pushBound y) ↔ φ.satisfies (η.pushFree y) := by
    rw [Formula.satisfies_substitute]
    apply Iff.of_eq
    apply congrArg (fun ρ => φ.satisfies ρ)
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases v <;> rfl
  simp only [occurs_m, occurs_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.level_formula_l K, hWitness,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval_weakenFree, Term.eval]
  rfl

theorem at_occurs_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (ρ : Env (quotient_l hℳ) Γ Δ)
    (B : Term ℒ [] Δ .set) (a : Term ℒ Γ Δ .set) :
    (at_m (occurs_m φ B) a).satisfies ρ ↔
      occurs_l φ (parameters_l ρ) (B.eval (parameters_l ρ)) (a.eval ρ) :=
  (at_formula_l _ _ _).trans (occurs_formula_l K φ _ B _)

def rank_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B : Term ℒ [] Δ .set) (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (at_m (occurs_m φ B) a) <| .forallE .set <|
    .imp (member_m (.bvar .here) (up a)) (.neg (at_m (occurs_m φ B) (.bvar .here)))

def rank_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (B a : type_l hℳ) : Prop :=
  occurs_l φ η B a ∧ ∀ b, mem_l hℳ b a → ¬occurs_l φ η B b

theorem rank_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (ρ : Env (quotient_l hℳ) Γ Δ)
    (B : Term ℒ [] Δ .set) (a : Term ℒ Γ Δ .set) :
    (rank_m φ B a).satisfies ρ ↔
      rank_l φ (parameters_l ρ) (B.eval (parameters_l ρ)) (a.eval ρ) := by
  simp only [rank_m, rank_l, Formula.satisfies, at_occurs_formula_l K,
    parameters_pushBound_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem ordinal_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    {η : Env (quotient_l hℳ) [] Δ} {B a : type_l hℳ} (ha : occurs_l φ η B a) :
    SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) a := by
  obtain ⟨C, hC, _⟩ := ha
  exact PowerlessRelativeLevelClosure.ordinal_l hℳ hC

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (quotient_l hℳ) [] Δ)
    (B : Term ℒ [] Δ .set)
    (h : ∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧
      φ.satisfies (η.pushFree y)) : ∃ a, rank_l φ η (B.eval η) a := by
  have hSome : ∃ a, (occurs_m φ B).satisfies (η.pushFree a) := by
    obtain ⟨y, ⟨a, C, hC, hyC⟩, hy⟩ := h
    exact ⟨a, (occurs_formula_l K φ η B a).mpr ⟨C, hC, y, hyC, hy⟩⟩
  obtain ⟨a, ha, hMin⟩ := PowerlessWeakSetInduction.minimum_l
    (SecondOrderWeakSetTheory.models_l hℳ) (occurs_m φ B) η hSome
  exact ⟨a, (occurs_formula_l K φ η B a).mp ha,
    fun b hb hOcc => hMin b hb ((occurs_formula_l K φ η B b).mpr hOcc)⟩

theorem bound_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    {η : Env (quotient_l hℳ) [] Δ} {B a b : type_l hℳ}
    (ha : rank_l φ η B a) (hb : occurs_l φ η B b) : a = b ∨ mem_l hℳ a b := by
  rcases SecondOrderOrdinalComparison.compare_l hℳ (ordinal_l ha.1) (ordinal_l hb) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (ha.2 b h hb)

theorem unique_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    {η : Env (quotient_l hℳ) [] Δ} {B a b : type_l hℳ}
    (ha : rank_l φ η B a) (hb : rank_l φ η B b) : a = b := by
  rcases bound_l ha hb.1 with h | h
  · exact h
  · exact False.elim (hb.2 a h ha.1)

/-- 最小合格层内的实际见证，其自身最小出现阶段也是该阶段。 -/
theorem witness_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    {η : Env (quotient_l hℳ) [] Δ} {B a : type_l hℳ} (ha : rank_l φ η B a) :
    ∃ C y, level_l hℳ B a C ∧ mem_l hℳ y C ∧ φ.satisfies (η.pushFree y) ∧
      PowerlessRelativeLeastStage.rank_l hℳ B y a := by
  obtain ⟨C, hC, y, hyC, hy⟩ := ha.1
  refine ⟨C, y, hC, hyC, hy, ⟨C, hC, hyC⟩, ?_⟩
  rintro b hb ⟨D, hD, hyD⟩
  exact ha.2 b hb ⟨D, hD, y, hyD, hy⟩

/-- 有最小阶段恰好等于有类内见证，不另要求预选见证或共同层界。 -/
theorem exists_iff_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (quotient_l hℳ) [] Δ)
    (B : Term ℒ [] Δ .set) :
    (∃ a, rank_l φ η (B.eval η) a) ↔
      ∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧
        φ.satisfies (η.pushFree y) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨C, hC, y, hyC, hy⟩ := ha.1
    exact ⟨y, ⟨a, C, hC, hyC⟩, hy⟩
  · exact exists_l K φ η B

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (.existsE .set <| .conj
    (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) (at_m φ (.bvar .here))) <|
    .existsE .set <| .conj (rank_m φ B (.bvar .here)) <|
      .forallE .set <| .imp (rank_m φ B (.bvar .here))
        (.equal (.bvar .here) (.bvar (.there .here)))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B : Term ℒ [] Δ .set) : Sentence ℒ := Metatheory.Formula.forall_close (schema_m φ B)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) (B : Term ℒ [] Δ .set) :
    (sentence_m φ B).TrueIn (quotient_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    at_formula_l, rank_formula_l K, parameters_pushBound_l, parameters_empty_l,
    up, Term.eval_weakenBound, Term.eval]
  intro h
  obtain ⟨a, ha⟩ := exists_l K φ η B h
  exact ⟨a, ha, fun _ hb => unique_l hb ha⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ B)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ B)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeWitnessLeastStage
