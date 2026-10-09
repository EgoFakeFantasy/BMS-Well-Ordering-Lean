import BMSConstructibleBridge.PowerlessRelativeFiniteProgramRelocation
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramWordConcat
import BMSConstructibleBridge.SecondOrderDefinableBoundedMap

/-! # 原 Z₂ 中实际有限词的父坐标重编号

给定实际 ω 自映射及合法词，在旧长度×字母表中构造精确新图，保持
同一长度与陪域，并取得 Class 成员性。源词不需另假定属于 Class；
结论在对象句中存在量化真实新词，不只给逐指令的宿主重编号关系。
此结论仍未包含执行输出保持，任意自映射也不自动保持父坐标的先后关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramWordRelocation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def body_m {Γ Δ : SortContext ℒ} (C ω A t₀ t₁ t₂ w i r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (SecondOrderObjectSyntax.value_m (up w) (up i) (.bvar .here))
    (PowerlessRelativeFiniteProgramRelocation.formula_m (up C) (up ω) (up A)
      (up t₀) (up t₁) (up t₂) (.bvar .here) (up r))

def reading_m {Γ Δ : SortContext ℒ} (C ω A t₀ t₁ t₂ w v : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .iff
    (SecondOrderObjectSyntax.value_m (up₂ v) (.bvar (.there .here)) (.bvar .here))
    (body_m (up₂ C) (up₂ ω) (up₂ A) (up₂ t₀) (up₂ t₁) (up₂ t₂) (up₂ w)
      (.bvar (.there .here)) (.bvar .here))

def relocation_m {Γ Δ : SortContext ℒ} (B C ω A t₀ t₁ t₂ w n Q v : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.class_m B v) <|
    .conj (SecondOrderObjectSyntax.map_m v n Q) (reading_m C ω A t₀ t₁ t₂ w v)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def body_l (C ω A t₀ t₁ t₂ w i r : type_l hℳ) : Prop :=
  ∃ q, value_l (ℳ := 𝒱) w i q ∧ PowerlessRelativeFiniteProgramRelocation.relation_l C ω A t₀ t₁ t₂ q r

def relocation_l (B C ω A t₀ t₁ t₂ w n Q v : type_l hℳ) : Prop :=
  PowerlessRelativeClassCorrespondence.member_l hℳ B v ∧ map_l (ℳ := 𝒱) v n Q ∧
    ∀ i r, value_l (ℳ := 𝒱) v i r ↔ body_l C ω A t₀ t₁ t₂ w i r

theorem body_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (C ω A t₀ t₁ t₂ w i r : Term ℒ Γ Δ .set) :
    (body_m C ω A t₀ t₁ t₂ w i r).satisfies η ↔ body_l
      (C.eval η) (ω.eval η) (A.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
        (w.eval η) (i.eval η) (r.eval η) := by
  simp only [body_m, body_l, Formula.satisfies, value_formula_l,
    PowerlessRelativeFiniteProgramRelocation.formula_l, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here]

theorem relocation_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B C ω A t₀ t₁ t₂ w n Q v : Term ℒ Γ Δ .set) :
    (relocation_m B C ω A t₀ t₁ t₂ w n Q v).satisfies η ↔ relocation_l
      (B.eval η) (C.eval η) (ω.eval η) (A.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
        (w.eval η) (n.eval η) (Q.eval η) (v.eval η) := by
  simp only [relocation_m, relocation_l, reading_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassCorrespondence.member_l, map_formula_l, value_formula_l,
    body_formula_l, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]

theorem exists_l (K : source_coding_l hℳ) {B C ω A t₀ t₁ t₂ w n Q : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : ω = K.omega) (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ B ω)
    (hQC : PowerlessRelativeClassCorrespondence.member_l hℳ B Q)
    (hA : map_l (ℳ := 𝒱) A ω ω) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hAlphabet : ∀ q, mem_l hℳ q Q ↔ PowerlessRelativeFiniteProgramAlphabet.instruction_l C ω t₀ t₁ t₂ q)
    (hn : mem_l hℳ n ω) (hw : map_l (ℳ := 𝒱) w n Q) :
    ∃ v, relocation_l B C ω A t₀ t₁ t₂ w n Q v := by
  have hBounds (i r : type_l hℳ) (h : body_l C ω A t₀ t₁ t₂ w i r) :
      mem_l hℳ i n ∧ mem_l hℳ r Q := by
    obtain ⟨q, hq, hr⟩ := h
    exact ⟨(SecondOrderFunctionProperties.value_mem_l hℳ hw hq).1,
      (hAlphabet r).mpr (PowerlessRelativeFiniteProgramRelocation.range_l hA hr)⟩
  have hTotal (i : type_l hℳ) (hi : mem_l hℳ i n) : ∃ r, body_l C ω A t₀ t₁ t₂ w i r := by
    obtain ⟨q, hq, _⟩ := hw.2 i hi
    obtain ⟨r, _, hr⟩ := PowerlessRelativeFiniteProgramRelocation.exists_l hA ((hAlphabet q).mp hq.1)
    exact ⟨r, q, hq.2, hr⟩
  have hUnique (i r s : type_l hℳ) (hr : body_l C ω A t₀ t₁ t₂ w i r)
      (hs : body_l C ω A t₀ t₁ t₂ w i s) : r = s := by
    obtain ⟨q, hq, hr⟩ := hr
    obtain ⟨q', hq', hs⟩ := hs
    have hEq := SecondOrderFunctionProperties.value_unique_l hℳ hw hq hq'
    subst q'
    exact PowerlessRelativeFiniteProgramRelocation.unique_l hA hTags hr hs
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set, .set, .set] :=
    (((((((Env.empty).pushFree w).pushFree t₂).pushFree t₁).pushFree t₀).pushFree A).pushFree ω).pushFree C
  let φ : Formula ℒ [] (.set :: .set :: [.set, .set, .set, .set, .set, .set, .set]) :=
    body_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
      (.fvar .here) (.fvar (.there .here))
  have hφ (i r : type_l hℳ) : φ.satisfies ((η.pushFree r).pushFree i) ↔ body_l C ω A t₀ t₁ t₂ w i r := by
    simp only [φ, body_formula_l, η, Term.eval, Env.pushFree, Assignment.push_here, Assignment.push_there]
  obtain ⟨v, hv, hRead⟩ := SecondOrderDefinableBoundedMap.exists_l hℳ φ η n Q
    (fun i hi => by
      obtain ⟨r, hr⟩ := hTotal i hi
      exact ⟨r, (hBounds i r hr).2, (hφ i r).mpr hr⟩)
    (fun i _ r s _ _ hr hs => hUnique i r s ((hφ i r).mp hr) ((hφ i s).mp hs))
  refine ⟨v, PowerlessRelativeFiniteProgramWordConcat.finite_class_l K hBase
    (hω ▸ hωC) hQC (hω ▸ hn) hv, hv, ?_⟩
  intro i r
  refine (hRead i r).trans ?_
  rw [hφ i r]
  exact ⟨fun h => h.2.2, fun h => ⟨(hBounds i r h).1, (hBounds i r h).2, h⟩⟩

def schema_m {Δ : SortContext ℒ} (B C ω A t₀ t₁ t₂ w n Q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
          .imp (SecondOrderObjectSyntax.map_m A ω ω) <|
            .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂) <|
              .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                .imp (SecondOrderObjectSyntax.member_m n ω) <|
                  .imp (SecondOrderObjectSyntax.map_m w n Q) <|
                    .existsE .set <| relocation_m (up B) (up C) (up ω) (up A)
                      (up t₀) (up t₁) (up t₂) (up w) (up n) (up Q) (.bvar .here)

def sentence_m {Δ : SortContext ℒ} (B C ω A t₀ t₁ t₂ w n Q : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B C ω A t₀ t₁ t₂ w n Q)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B C ω A t₀ t₁ t₂ w n Q : Term ℒ [] Δ .set) :
    (sentence_m B C ω A t₀ t₁ t₂ w n Q).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    relocation_formula_l K, map_formula_l, PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hω hωC hQC hA hTags hAlphabet hn hw
  exact exists_l K hBase (SecondOrderOmega.unique_l h𝒩 hω K.omega_spec) hωC hQC hA hTags hAlphabet hn hw

theorem derives_m {Δ : SortContext ℒ} (B C ω A t₀ t₁ t₂ w n Q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B C ω A t₀ t₁ t₂ w n Q)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B C ω A t₀ t₁ t₂ w n Q)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramWordRelocation
