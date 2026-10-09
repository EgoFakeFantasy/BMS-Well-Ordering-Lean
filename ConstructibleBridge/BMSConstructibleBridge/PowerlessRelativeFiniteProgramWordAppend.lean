import BMSConstructibleBridge.PowerlessRelativeFiniteProgramPrefix

/-! # 实际 Class 指令词的单点延拓

在旧定义域 n 的新坐标 n 加入一条属于 Q 的指令。保持同一指令
陪域 Q，域为 n∪{n}，全部旧坐标读数不变，新坐标读数精确为该指令。
这里只延长指令词，延长执行历史及新指令输出另行证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramWordAppend

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def append_m {Γ Δ : SortContext ℒ} (B w n Q q S v : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.class_m B S) <|
    .conj (PowerlessRelativeHierarchySyntax.class_m B v) <|
      .conj (PowerlessNaturalStep.successor_m n S) <|
        .conj (SecondOrderObjectSyntax.map_m v S Q)
          (SecondOrderFunctionAppendDerives.reading_m w n q v)

def result_m {Γ Δ : SortContext ℒ} (B w n Q q S v : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (append_m B w n Q q S v) <|
    .conj (PowerlessRelativeFiniteProgramPrefix.agree_m n w v) (SecondOrderObjectSyntax.value_m v n q)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def append_l (B w n Q q S v : type_l hℳ) : Prop :=
  PowerlessRelativeClassCorrespondence.member_l hℳ B S ∧
    PowerlessRelativeClassCorrespondence.member_l hℳ B v ∧
      PowerlessNatural.successor_l (ℳ := 𝒱) n S ∧ map_l (ℳ := 𝒱) v S Q ∧
        ∀ x y, value_l (ℳ := 𝒱) v x y ↔ value_l (ℳ := 𝒱) w x y ∨ x = n ∧ y = q

theorem append_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B w n Q q S v : Term ℒ Γ Δ .set) :
    (append_m B w n Q q S v).satisfies η ↔
      append_l (B.eval η) (w.eval η) (n.eval η) (Q.eval η) (q.eval η) (S.eval η) (v.eval η) := by
  simp only [append_m, append_l, SecondOrderFunctionAppendDerives.reading_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassCorrespondence.member_l, PowerlessNaturalStep.successor_formula_l,
    map_formula_l, value_formula_l, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]

theorem agreement_l {B w n Q q S v : type_l hℳ} (h : append_l B w n Q q S v) :
    PowerlessRelativeFiniteProgramPrefix.agree_l n w v := by
  intro i hi y
  constructor
  · intro hiy
    exact (h.2.2.2.2 i y).mpr (Or.inl hiy)
  · intro hiy
    rcases (h.2.2.2.2 i y).mp hiy with hiy | ⟨hin, _⟩
    · exact hiy
    · have hnn : mem_l hℳ n n := hin ▸ hi
      exact (SecondOrderNaturalCases.asymmetry_l hℳ hnn hnn).elim

theorem last_l {B w n Q q S v : type_l hℳ} (h : append_l B w n Q q S v) :
    value_l (ℳ := 𝒱) v n q :=
  (h.2.2.2.2 n q).mpr (Or.inr ⟨rfl, rfl⟩)

theorem exists_l {B w n Q q : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hwC : PowerlessRelativeClassCorrespondence.member_l hℳ B w)
    (hnC : PowerlessRelativeClassCorrespondence.member_l hℳ B n)
    (hQC : PowerlessRelativeClassCorrespondence.member_l hℳ B Q)
    (hw : map_l (ℳ := 𝒱) w n Q) (hq : mem_l hℳ q Q) :
    ∃ S v, append_l B w n Q q S v ∧
      PowerlessRelativeFiniteProgramPrefix.agree_l n w v ∧ value_l (ℳ := 𝒱) v n q := by
  have hFresh : ¬mem_l hℳ n n := fun h => SecondOrderNaturalCases.asymmetry_l hℳ h h
  have hqC := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hQC hq
  obtain ⟨S, E, v, hSC, _, hVC, hS, hE, hv, hRead⟩ :=
    PowerlessRelativeClassFunctionAppend.exists_l hBase hwC hnC hQC hnC hqC hw hFresh
  have hEQ : E = Q := by
    apply SecondOrderQuotient.ext_l hℳ
    intro y
    apply (hE y).trans
    exact ⟨fun h => h.elim id (fun hy => hy ▸ hq), fun hy => Or.inl hy⟩
  subst E
  have hAppend : append_l B w n Q q S v := ⟨hSC, hVC, hS, hv, hRead⟩
  exact ⟨S, v, hAppend, agreement_l hAppend, last_l hAppend⟩

def schema_m {Δ : SortContext ℒ} (B w n Q q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B w) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B n) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
          .imp (SecondOrderObjectSyntax.map_m w n Q) <|
            .imp (SecondOrderObjectSyntax.member_m q Q) <|
              .existsE .set <| .existsE .set <|
                result_m (up₂ B) (up₂ w) (up₂ n) (up₂ Q) (up₂ q)
                  (.bvar (.there .here)) (.bvar .here)

def sentence_m {Δ : SortContext ℒ} (B w n Q q : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B w n Q q)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B w n Q q : Term ℒ [] Δ .set) :
    (sentence_m B w n Q q).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, append_formula_l K,
    PowerlessRelativeFiniteProgramPrefix.agree_formula_l, map_formula_l, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hwC hnC hQC hw hq
  exact exists_l hBase hwC hnC hQC hw hq

theorem derives_m {Δ : SortContext ℒ} (B w n Q q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B w n Q q)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B w n Q q)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramWordAppend
