import BMSConstructibleBridge.SecondOrderCanonicalOrderSyntax

/-! # 固定 Sat 的规范扩张：完整模型唯一性及对象推导

所有辅助见证允许在完整模型中取值。唯一性不是类内结论；条件存在句
明确保留规范候选存在前提，不以此伪装原 Def 步骤存在或内部历史已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderStep

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderCanonicalOrderSyntax (candidate_l candidate_m candidate_formula_l step_l step_m step_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem candidate_congr_l {ω A P R R' D L : type_l hℳ}
    (hR : ∀ c f, value_l (ℳ := 𝒱) R c f ↔ value_l (ℳ := 𝒱) R' c f) :
    candidate_l (ℳ₀ := 𝒱) ω A P R D L ↔ candidate_l (ℳ₀ := 𝒱) ω A P R' D L := by
  have transfer {T T' : type_l hℳ}
      (h : ∀ c f, value_l (ℳ := 𝒱) T c f ↔ value_l (ℳ := 𝒱) T' c f)
      (hCandidate : candidate_l (ℳ₀ := 𝒱) ω A P T D L) :
      candidate_l (ℳ₀ := 𝒱) ω A P T' D L := by
    obtain ⟨S, I, J, U, Q, Y, hIndex, hRead, hRows, hGraph, hSubset, hOrder⟩ := hCandidate
    refine ⟨S, I, J, U, Q, Y, hIndex, ?_, hRows, hGraph, hSubset, hOrder⟩
    intro t x
    exact (hRead t x).trans (and_congr Iff.rfl (and_congr Iff.rfl
      (PowerlessRelativeClassSatisfactionQueryUnique.slots_congr_l
        (fun _ => Iff.rfl) (fun _ => Iff.rfl) h)))
  exact ⟨transfer hR, transfer (fun c f => (hR c f).symm)⟩

theorem step_congr_l {ω A P R R' D E : type_l hℳ}
    (hR : ∀ c f, value_l (ℳ := 𝒱) R c f ↔ value_l (ℳ := 𝒱) R' c f) :
    step_l (ℳ₀ := 𝒱) ω A P R D E ↔ step_l (ℳ₀ := 𝒱) ω A P R' D E :=
  exists_congr fun L => and_congr (candidate_congr_l (L := L) hR) Iff.rfl

theorem candidate_unique_l {ω A P R D L L' : type_l hℳ}
    (h : candidate_l (ℳ₀ := 𝒱) ω A P R D L)
    (h' : candidate_l (ℳ₀ := 𝒱) ω A P R D L') : L = L' := by
  obtain ⟨S, I, J, U, Q, Y, hIndex, hRead, hRows, hGraph, _, _⟩ := h
  obtain ⟨S', I', J', U', Q', Y', hIndex', hRead', hRows', hGraph', _, _⟩ := h'
  obtain ⟨hS, hI, hJ, hU⟩ := SecondOrderCanonicalIndexUnique.unique_l hIndex hIndex'
  subst S'
  subst I'
  subst J'
  subst U'
  have hQ t x := (hRead t x).trans (hRead' t x).symm
  have hYEq : Y' = Y := by
    apply SecondOrderQuotient.ext_l hℳ Y' Y
    intro y
    refine (hRows' y).trans ((exists_congr fun i => and_congr Iff.rfl ?_).trans (hRows y).symm)
    exact (PowerlessRelativeClassRowOrderCanonical.row_congr_l hQ i y).symm
  subst Y'
  exact PowerlessRelativeClassSatisfactionQueryUnique.orders_l hQ hGraph hGraph'

theorem unique_l {ω A P R D E E' : type_l hℳ}
    (h : step_l (ℳ₀ := 𝒱) ω A P R D E) (h' : step_l (ℳ₀ := 𝒱) ω A P R D E') : E = E' := by
  obtain ⟨L, hL, hGraph⟩ := h
  obtain ⟨L', hL', hGraph'⟩ := h'
  have hEq : L' = L := candidate_unique_l hL' hL
  subst L'
  exact SecondOrderWellOrderEndExtensionUnique.unique_l hGraph hGraph'

theorem exists_unique_l {ω A P R D : type_l hℳ} (hP : wellOrder_l (ℳ := 𝒱) A P)
    (hCandidate : ∃ L, candidate_l (ℳ₀ := 𝒱) ω A P R D L) :
    ∃! E : type_l hℳ, step_l (ℳ₀ := 𝒱) ω A P R D E ∧ wellOrder_l (ℳ := 𝒱) D E := by
  obtain ⟨L, hL⟩ := hCandidate
  have hCopy := hL
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hSubset, hOrder⟩ := hCopy
  have hD := PowerlessRelativeClassAmbientWellOrder.of_subset_l hOrder hSubset
  obtain ⟨E, hGraph, hE⟩ := SecondOrderWellOrderEndExtensionUnique.exists_l hP hD
  exact ⟨E, ⟨⟨L, hL, hGraph⟩, hE⟩, fun E' hE' => unique_l hE'.1 ⟨L, hL, hGraph⟩⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def unique_m {Γ Δ : SortContext ℒ} (ω A P R D E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (step_m ω A P R D E) <| .forallE .set <|
    .imp (step_m (up ω) (up A) (up P) (up R) (up D) (.bvar .here))
      (.equal (up E) (.bvar .here))

def unique_schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  unique_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))

def unique_sentence_m : Sentence ℒ := Metatheory.Formula.forall_close unique_schema_m

theorem unique_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    unique_sentence_m.TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [unique_schema_m, unique_m, Formula.satisfies, step_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact fun h _ h' => unique_l (hℳ := hℳ) h h'

theorem unique_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m unique_sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => unique_models_l hℳ)

def existence_m {Γ Δ : SortContext ℒ} (ω A P R D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m A P) <|
    .imp (.existsE .set (candidate_m (up ω) (up A) (up P) (up R) (up D) (.bvar .here))) <|
      .existsE .set <|
        .conj (step_m (up ω) (up A) (up P) (up R) (up D) (.bvar .here)) <|
          .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (up D) (.bvar .here))
            (unique_m (up ω) (up A) (up P) (up R) (up D) (.bvar .here))

def existence_schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  existence_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))

def existence_sentence_m : Sentence ℒ := Metatheory.Formula.forall_close existence_schema_m

theorem existence_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    existence_sentence_m.TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [existence_schema_m, existence_m, unique_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, candidate_formula_l,
    step_formula_l, up, Term.eval_weakenBound, Term.eval]
  intro hP hCandidate
  obtain ⟨E, ⟨hE, hOrder⟩, _⟩ := exists_unique_l (hℳ := hℳ) hP hCandidate
  exact ⟨E, hE, hOrder, fun _ _ h' => unique_l hE h'⟩

theorem existence_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m existence_sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => existence_models_l hℳ)

#print axioms candidate_unique_l
#print axioms unique_derives_m
#print axioms existence_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderStep
