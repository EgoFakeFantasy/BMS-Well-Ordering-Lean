import BMSConstructibleBridge.SecondOrderTaggedDomain
import BMSConstructibleBridge.SecondOrderGraftSemantics
import BMSConstructibleBridge.SecondOrderAxioms

/-!
# 任意模型中的无序对及其对象公理

两张独立关系先进入互不相交的内部标签副本，再选择两个根进行拼接。
标签换码的双模拟由实际配对图理解构造，故配对对象覆盖任意不同图码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairSet

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderTaggedGraph GraphTranslation

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem tag_eq_l (hℳ : Theory.Models ℳ theory_m) (k : num_l ℳ) (R G : set_l ℳ)
    (hG : fiber_l k R G) (a : num_l ℳ) : SecondOrderBisimulation.eq_l R G a (value_l k a) := by
  let φ : Formula signature_m [] [.num, .num, .num] :=
    PrimitiveFormulas.pair_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  obtain ⟨H, hH⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree k)
  have h₀ : ∀ b c, relation_l H b c ↔ value_l k b = c :=
    fun b c => (hH b c).trans (SecondOrderPairing.formula_l _ _ _ _)
  refine ⟨H, ?_, (h₀ a (value_l k a)).mpr rfl⟩
  intro b c h
  obtain rfl := (h₀ b c).mp h
  constructor
  · intro d h
    exact ⟨value_l k d, (SecondOrderTaggedGraph.edge_l hℳ k R G hG d b).mpr h,
      (h₀ d (value_l k d)).mpr rfl⟩
  · intro d h
    obtain ⟨e, rfl, h₁⟩ := (hG d b).mp h
    exact ⟨e, h₁, (h₀ e (value_l k e)).mpr rfl⟩

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def one {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons zero .nil)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ) :
    ∃ C : SecondOrderGraph.code_l ℳ, ∀ D,
      SecondOrderGraph.mem_l D C ↔ SecondOrderGraph.eq_l D A ∨ SecondOrderGraph.eq_l D B := by
  obtain ⟨G, hG, hG₁⟩ := SecondOrderTaggedGraph.exists_l hℳ A.real B.real
  let φ : Formula signature_m [] [.num, .num, .num] :=
    .disj (PrimitiveFormulas.pair_m zero (.fvar (.there .here)) (.fvar .here))
      (PrimitiveFormulas.pair_m one (.fvar (.there (.there .here))) (.fvar .here))
  obtain ⟨P, hP⟩ := SecondOrderModel.comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree B.root).pushFree A.root)
  have h₀ : ∀ c, mem_l c P ↔ c = value_l (zero_l ℳ) A.root ∨
      c = value_l (succ_l (zero_l ℳ)) B.root := by
    intro c
    refine (hP c).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderPairing.formula_l]
    exact or_congr eq_comm eq_comm
  have h₁ : ∀ c, mem_l c P → SecondOrderDomain.wf_l G c := by
    intro c h
    rcases (h₀ c).mp h with rfl | rfl
    · exact SecondOrderTaggedDomain.wf_l hℳ (zero_l ℳ) A.real G hG A.root A.wf
    · exact SecondOrderTaggedDomain.wf_l hℳ (succ_l (zero_l ℳ)) B.real G hG₁ B.root B.wf
  obtain ⟨C, hC⟩ := SecondOrderGraftSemantics.exists_l hℳ G P h₁
  have hA := tag_eq_l hℳ (zero_l ℳ) A.real G hG A.root
  have hB := tag_eq_l hℳ (succ_l (zero_l ℳ)) B.real G hG₁ B.root
  refine ⟨C, fun D => (hC D).trans ?_⟩
  constructor
  · rintro ⟨c, h, h₂⟩
    rcases (h₀ c).mp h with rfl | rfl
    · exact Or.inl (SecondOrderBisimulation.trans_l hℳ D.real G A.real D.root _ A.root h₂
        (SecondOrderBisimulation.symm_l hℳ _ _ _ _ hA))
    · exact Or.inr (SecondOrderBisimulation.trans_l hℳ D.real G B.real D.root _ B.root h₂
        (SecondOrderBisimulation.symm_l hℳ _ _ _ _ hB))
  · rintro (h | h)
    · exact ⟨_, (h₀ _).mpr (Or.inl rfl),
        SecondOrderBisimulation.trans_l hℳ D.real A.real G D.root A.root _ h hA⟩
    · exact ⟨_, (h₀ _).mpr (Or.inr rfl),
        SecondOrderBisimulation.trans_l hℳ D.real B.real G D.root B.root _ h hB⟩

/-- 纯集合论配对公理，与算术配对函数的总性是不同命题。 -/
def formula_m : Sentence ℒ :=
  .forallE .set <| .forallE .set <| .existsE .set <| .forallE .set <|
    .iff (.rel .membership (.cons (.bvar .here) (.cons (.bvar (.there .here)) .nil)))
      (.disj (.equal (.bvar .here) (.bvar (.there (.there (.there .here)))))
        (.equal (.bvar .here) (.bvar (.there (.there .here)))))

theorem models_l (hℳ : Theory.Models ℳ theory_m) :
    formula_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  change ∀ a b : SecondOrderQuotient.type_l hℳ, ∃ c, ∀ d,
    SecondOrderQuotient.mem_l hℳ d c ↔ d = a ∨ d = b
  intro a b
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
  obtain ⟨C, hC⟩ := exists_l hℳ A B
  refine ⟨SecondOrderQuotient.mk_l hℳ C, fun d => ?_⟩
  obtain ⟨D, rfl⟩ := SecondOrderQuotient.surj_l hℳ d
  exact (hC D).trans (or_congr (SecondOrderQuotient.eq_iff_l hℳ D A).symm
    (SecondOrderQuotient.eq_iff_l hℳ D B).symm)

theorem derives_m : Derives theory_m [] (form_m formula_m) :=
  SecondOrderAxioms.interpretation_m formula_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairSet
