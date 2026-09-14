import BMSConstructibleBridge.SecondOrderGraftSemantics
import BMSConstructibleBridge.SecondOrderAxioms

/-!
# 任意模型中的传递超集

直接用完整理解选取同一关系中满足原根域公式的全部节点，再拼接成一个新根。
子根域保持给出传递性，因此不需要外部可达性或预先选择有限路径族。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTransitiveSuperset

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing GraphTranslation
open SetTheory

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def transitive_l (T : SecondOrderGraph.code_l ℳ) : Prop :=
  ∀ B C, SecondOrderGraph.mem_l B T → SecondOrderGraph.mem_l C B → SecondOrderGraph.mem_l C T

/-- 取一个以原对象为成员的传递对象，比仅要求包含其所有成员更强。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) :
    ∃ T, SecondOrderGraph.mem_l A T ∧ transitive_l T := by
  let φ : Formula signature_m [] [.num, .set] := domain_m (.fvar (.there .here)) (.fvar .here)
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ (domain_pure_m _ _ rfl rfl)
    ((Env.empty (M := ℳ)).pushFree A.real)
  have h₀ : ∀ a, mem_l a P ↔ SecondOrderDomain.wf_l A.real a :=
    fun a => (hP a).trans (SecondOrderInterpretation.domain_l _ _ _)
  obtain ⟨T, hT⟩ := SecondOrderGraftSemantics.exists_l hℳ A.real P
    (fun a ha => (h₀ a).mp ha)
  refine ⟨T, (hT A).mpr ⟨A.root, (h₀ A.root).mpr A.wf,
    SecondOrderBisimulation.refl_l hℳ A.real A.root⟩, ?_⟩
  intro B C hB hC
  obtain ⟨b, hb, h₁⟩ := (hT B).mp hB
  obtain ⟨c, hc, h₂⟩ := hC
  obtain ⟨d, hd, h₃⟩ := (SecondOrderBisimulation.match_l B.real A.real B.root b h₁).1 c hc
  exact (hT C).mpr ⟨d, (h₀ d).mpr
    (SecondOrderDomain.child_l hℳ A.real b d ((h₀ b).mp hb) hd),
    SecondOrderBisimulation.trans_l hℳ C.real B.real A.real C.root c d h₂ h₃⟩

private def member {Γ Δ : SortContext ℒ} (s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .rel .membership (.cons s (.cons t .nil))

private def subset {Γ Δ : SortContext ℒ} (s t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp (member (.bvar .here) (s.weakenBound SetSort.set))
    (member (.bvar .here) (t.weakenBound SetSort.set)))

private def transitive {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.forallE .set (.imp
    (member (.bvar (.there .here)) ((t.weakenBound SetSort.set).weakenBound SetSort.set))
    (.imp (member (.bvar .here) (.bvar (.there .here)))
      (member (.bvar .here) ((t.weakenBound SetSort.set).weakenBound SetSort.set)))))

/-- TMC 的 TrSups：每个对象有传递超集；没有附加幂集或收集。 -/
def formula_m : Sentence ℒ :=
  .forallE .set <| .existsE .set <| .conj
    (subset (.bvar (.there .here)) (.bvar .here)) (transitive (.bvar .here))

theorem models_l (hℳ : Theory.Models ℳ theory_m) :
    formula_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  change ∀ a : SecondOrderQuotient.type_l hℳ, ∃ t,
    (∀ b, SecondOrderQuotient.mem_l hℳ b a → SecondOrderQuotient.mem_l hℳ b t) ∧
      ∀ b c, SecondOrderQuotient.mem_l hℳ b t →
        SecondOrderQuotient.mem_l hℳ c b → SecondOrderQuotient.mem_l hℳ c t
  intro a
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨T, hA, hT⟩ := exists_l hℳ A
  refine ⟨SecondOrderQuotient.mk_l hℳ T, ?_, ?_⟩
  · intro b hb
    obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
    exact hT A B hA hb
  · intro b c hb hc
    obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
    obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
    exact hT B C hb hc

theorem derives_m : Derives theory_m [] (form_m formula_m) :=
  SecondOrderAxioms.interpretation_m formula_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTransitiveSuperset
