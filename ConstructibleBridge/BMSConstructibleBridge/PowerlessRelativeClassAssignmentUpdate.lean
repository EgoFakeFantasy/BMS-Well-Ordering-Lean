import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessRelativeClassFunctionProperties
import BMSConstructibleBridge.PowerlessAssignmentUpdate
import BMSConstructibleBridge.PowerlessValueBounded

/-! # 类内赋值更新的实际存在性及原 Z₂ 推导

在原定义域和给定值域上构造纯 Δ₀ 函数图。更新位置属于原域，结论覆盖
全部坐标，不是只在合法输入上的关系，也不是域外单点延拓。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassAssignmentUpdate

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def matrix_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  .disj (.conj (.equal (.fvar .here) (.fvar (.there (.there (.there .here)))))
    (.equal (.fvar (.there .here)) (.fvar (.there (.there (.there (.there .here)))))))
    (.conj (.neg (.equal (.fvar .here) (.fvar (.there (.there (.there .here))))))
      (PowerlessValueBounded.formula_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))))

theorem matrix_delta_l : Formula.IsDelta0 membershipLevyBound matrix_m :=
  .disj (.conj (.equal _ _) (.equal _ _)) (.conj (.neg (.equal _ _)) (PowerlessValueBounded.delta_l _ _ _))

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B} {f D A i a : type_l hℳ B}
    (hf : map_l (ℳ := structure_l hℳ B hBase) f D A) (hi : mem_l hℳ i.val D.val) (ha : mem_l hℳ a.val A.val) :
    ∃ g : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) g D A ∧
      PowerlessAssignmentUpdate.update_l (ℳ := structure_l hℳ B hBase) f i a g := by
  classical
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set] :=
    (((Env.empty).pushFree a).pushFree i).pushFree f
  have hRead (x y : type_l hℳ B) : matrix_m.satisfies ((η.pushFree y).pushFree x) ↔
      (x = i ∧ y = a) ∨ (x ≠ i ∧ value_l (ℳ := structure_l hℳ B hBase) f x y) := by
    simp only [matrix_m, Formula.satisfies, PowerlessValueBounded.formula_l, Term.eval]
    rfl
  have hTotal (x : type_l hℳ B) (hx : mem_l hℳ x.val D.val) :
      ∃! y : type_l hℳ B, mem_l hℳ y.val A.val ∧ matrix_m.satisfies ((η.pushFree y).pushFree x) := by
    by_cases hxi : x = i
    · refine ⟨a, ⟨ha, (hRead x a).mpr (Or.inl ⟨hxi, rfl⟩)⟩, ?_⟩
      intro y hy
      rcases (hRead x y).mp hy.2 with ⟨_, hya⟩ | ⟨hne, _⟩
      · exact hya
      · exact (hne hxi).elim
    · obtain ⟨y, hy, hUnique⟩ := hf.2 x hx
      refine ⟨y, ⟨hy.1, (hRead x y).mpr (Or.inr ⟨hxi, hy.2⟩)⟩, ?_⟩
      intro z hz
      rcases (hRead x z).mp hz.2 with ⟨hEq, _⟩ | ⟨_, hValue⟩
      · exact (hxi hEq).elim
      · exact hUnique z ⟨hz.1, hValue⟩
  obtain ⟨g, hg, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l matrix_delta_l η D A hTotal
  refine ⟨g, hg, fun x y => (hValue x y).trans ?_⟩
  constructor
  · exact fun h => (hRead x y).mp h.2.2
  · intro h
    have hBounds : mem_l hℳ x.val D.val ∧ mem_l hℳ y.val A.val := by
      rcases h with ⟨rfl, rfl⟩ | ⟨_, hxy⟩
      · exact ⟨hi, ha⟩
      · exact PowerlessRelativeClassFunctionProperties.value_mem_l hf hxy
    exact ⟨hBounds.1, hBounds.2, (hRead x y).mpr h⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def schema_m {Γ Δ : SortContext ℒ} (f D A i a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (SecondOrderObjectSyntax.map_m f D A) <|
    .imp (SecondOrderObjectSyntax.member_m i D) <|
      .imp (SecondOrderObjectSyntax.member_m a A) <|
        .existsE .set <| .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (up D) (up A))
          (PowerlessAssignmentUpdate.update_m (up f) (up i) (up a) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (f D A i a : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m f D A i a)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) {Δ : SortContext ℒ}
    (f D A i a : Term ℒ [] Δ .set) : (sentence_m f D A i a).TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, map_formula_l, PowerlessAssignmentUpdate.update_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact fun hf hi ha => exists_l (hBase := hBase) hf hi ha

theorem derives_m {Δ : SortContext ℒ} (f D A i a : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m (sentence_m f D A i a))) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ hℳ B hBase => models_l hℳ B hBase f D A i a)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassAssignmentUpdate
