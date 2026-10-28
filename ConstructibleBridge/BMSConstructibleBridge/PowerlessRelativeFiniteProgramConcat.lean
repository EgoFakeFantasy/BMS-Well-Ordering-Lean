import BMSConstructibleBridge.PowerlessRelativeFiniteProgramWordRelocation

/-! # 原 Z₂ 中两实际程序词的统一重编号拼接

先固定一张属于 Class 的加法图，再沿同一图重编号右词的父坐标及
拼接两词。实际加法图、右侧新词、总长度和总词在对象句中共同存在量化；
不在两阶段换用未经核对的坐标图。这里尚不声明两程序执行输出保持。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConcat

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₂ t)

def joined_m {Γ Δ : SortContext ℒ} (B C ω e t₀ t₁ t₂ n w m z Q A r c v : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeFiniteProgramWordRelocation.relocation_m B C ω A t₀ t₁ t₂ z m Q r)
    (PowerlessRelativeFiniteProgramWordConcat.concat_m B ω e n w m r Q A c v)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def joined_l (B C ω e t₀ t₁ t₂ n w m z Q A r c v : type_l hℳ) : Prop :=
  PowerlessRelativeFiniteProgramWordRelocation.relocation_l B C ω A t₀ t₁ t₂ z m Q r ∧
    PowerlessRelativeFiniteProgramWordConcat.concat_l B ω e n w m r Q A c v

theorem joined_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B C ω e t₀ t₁ t₂ n w m z Q A r c v : Term ℒ Γ Δ .set) :
    (joined_m B C ω e t₀ t₁ t₂ n w m z Q A r c v).satisfies η ↔
      joined_l (B.eval η) (C.eval η) (ω.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
        (n.eval η) (w.eval η) (m.eval η) (z.eval η) (Q.eval η) (A.eval η) (r.eval η) (c.eval η) (v.eval η) := by
  simp only [joined_m, joined_l, Formula.satisfies,
    PowerlessRelativeFiniteProgramWordRelocation.relocation_formula_l K,
    PowerlessRelativeFiniteProgramWordConcat.concat_formula_l K]

theorem exists_l (K : source_coding_l hℳ) {B C e t₀ t₁ t₂ n w m z Q : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ B K.omega)
    (hQC : PowerlessRelativeClassCorrespondence.member_l hℳ B Q)
    (he : ∀ x, ¬mem_l hℳ x e) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hAlphabet : ∀ q, mem_l hℳ q Q ↔ PowerlessRelativeFiniteProgramAlphabet.instruction_l C K.omega t₀ t₁ t₂ q)
    (hn : mem_l hℳ n K.omega) (hm : mem_l hℳ m K.omega)
    (hw : map_l (ℳ := 𝒱) w n Q) (hz : map_l (ℳ := 𝒱) z m Q) :
    ∃ A r c v, joined_l B C K.omega e t₀ t₁ t₂ n w m z Q A r c v := by
  obtain ⟨a, ha⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have haEq : (numberCode_l K a).val = n := congrArg Subtype.val ha
  obtain ⟨A, hIteration, hMap⟩ := PowerlessBMSQuotientArithmetic.additionIteration_exists_l K a
  have hAC := PowerlessRelativeClassAdditionGraph.member_l (hBase := hBase) K
    (a := (numberCode_l K a).val) (numberCode_l K a).property hIteration hMap
  have heEq : (numberCode_l K (SecondOrderModel.zero_l ℳ)).val = e :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false
      (PowerlessBMSQuotientSuccessor.zero_l K x) (he x))
  rw [heEq, haEq] at hIteration
  obtain ⟨r, hRelocation⟩ := PowerlessRelativeFiniteProgramWordRelocation.exists_l K
    hBase rfl hωC hQC hMap hTags hAlphabet hm hz
  obtain ⟨c, v, hConcat⟩ := PowerlessRelativeFiniteProgramWordConcat.given_exists_l K
    hBase hωC hQC he hn hm hw hRelocation.2.1 hAC hMap hIteration
  exact ⟨A, r, c, v, hRelocation, hConcat⟩

def schema_m {Δ : SortContext ℒ} (B C ω e t₀ t₁ t₂ n w m z Q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
          .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
            .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂) <|
              .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                .imp (SecondOrderObjectSyntax.member_m n ω) <|
                  .imp (SecondOrderObjectSyntax.member_m m ω) <|
                    .imp (SecondOrderObjectSyntax.map_m w n Q) <|
                      .imp (SecondOrderObjectSyntax.map_m z m Q) <|
                        .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
                          joined_m (up₄ B) (up₄ C) (up₄ ω) (up₄ e) (up₄ t₀) (up₄ t₁) (up₄ t₂)
                            (up₄ n) (up₄ w) (up₄ m) (up₄ z) (up₄ Q)
                            (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
                            (.bvar (.there .here)) (.bvar .here)

def sentence_m {Δ : SortContext ℒ} (B C ω e t₀ t₁ t₂ n w m z Q : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B C ω e t₀ t₁ t₂ n w m z Q)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B C ω e t₀ t₁ t₂ n w m z Q : Term ℒ [] Δ .set) :
    (sentence_m B C ω e t₀ t₁ t₂ n w m z Q).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, PowerlessDefinableFiniteTraceDerives.zero_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    joined_formula_l K, map_formula_l, PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up₄, up₂, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hω hωC hQC he hTags hAlphabet hn hm hw hz
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  obtain ⟨A, r, c, v, hJoined⟩ := exists_l K hBase (hωEq ▸ hωC) hQC he hTags
    (hωEq ▸ hAlphabet) (hωEq ▸ hn) (hωEq ▸ hm) hw hz
  exact ⟨A, r, c, v, hωEq.symm ▸ hJoined⟩

theorem derives_m {Δ : SortContext ℒ} (B C ω e t₀ t₁ t₂ n w m z Q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B C ω e t₀ t₁ t₂ n w m z Q)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B C ω e t₀ t₁ t₂ n w m z Q)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConcat
