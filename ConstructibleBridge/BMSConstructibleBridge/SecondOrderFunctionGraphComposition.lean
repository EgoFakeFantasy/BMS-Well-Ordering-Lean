import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.SecondOrderFunctionLaws
import BMSConstructibleBridge.SecondOrderAxioms
import BMSConstructibleBridge.ThirdOrderSemantics
import YesMetaZFC.Automation.ModelClosure

/-! # 任意原商集合函数图的实际复合

复合的两张图不预设属于相对类。关系像产生原商中的实际复合图，完整
逐值规格没有域外边；原 Z₂ 推导出口保持所有参数和原映射守卫。
用于有限赋值提升时，仅最终有限图须提升入类，无需把母集枚举先放入类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionGraphComposition

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

def query_m {Γ Δ : SortContext ℒ} (F G x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj
    (value_m (F.weakenBound SetTheory.SetSort.set) (x.weakenBound SetTheory.SetSort.set) (.bvar .here))
    (value_m (G.weakenBound SetTheory.SetSort.set) (.bvar .here) (y.weakenBound SetTheory.SetSort.set))

theorem query_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (F G x y : Term ℒ Γ Δ .set) :
    (query_m F G x y).satisfies η ↔
      ∃ z, value_l (F.eval η) (x.eval η) z ∧ value_l (G.eval η) z (y.eval η) := by
  simp only [query_m, Formula.satisfies, value_formula_l, Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_l {F G A D E : type_l hℳ}
    (hF : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F A D)
    (hG : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) G D E) :
    ∃ H : type_l hℳ, map_l (ℳ := SecondOrderQuotient.structure_l hℳ) H A E ∧
      ∀ x y : type_l hℳ, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) H x y ↔
        ∃ z : type_l hℳ, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F x z ∧
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G z y := by
  let φ : Formula ℒ [] [.set, .set, .set, .set] := query_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar .here) (.fvar (.there .here))
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set] := (Env.empty.pushFree G).pushFree F
  have hφ (x y : type_l hℳ) : φ.satisfies ((η.pushFree y).pushFree x) ↔
      ∃ z, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F x z ∧
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G z y := query_formula_l _ _ _ _ _
  obtain ⟨H, hH⟩ := SecondOrderDefinableRelationImage.exists_l hℳ φ η A E
  have hRead (x y : type_l hℳ) : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) H x y ↔
      ∃ z, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F x z ∧
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G z y := by
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨a, b, _, _, hab, hp'⟩ := (hH p).mp hp
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hp').mp rfl
      exact (hφ x y).mp hab
    · rintro ⟨z, hxz, hzy⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      exact ⟨p, (hH p).mpr ⟨x, y, (SecondOrderFunctionLaws.value_mem_l hℳ hF hxz).1,
        (SecondOrderFunctionLaws.value_mem_l hℳ hG hzy).2, (hφ x y).mpr ⟨z, hxz, hzy⟩, hp⟩, hp⟩
  refine ⟨H, ⟨?_, ?_⟩, hRead⟩
  · intro p hp
    obtain ⟨x, y, hx, hy, _, hxy⟩ := (hH p).mp hp
    exact ⟨x, y, hx, hy, hxy⟩
  · intro x hx
    obtain ⟨z, ⟨hz, hxz⟩, _⟩ := hF.2 x hx
    obtain ⟨y, ⟨hy, hzy⟩, _⟩ := hG.2 z hz
    refine ⟨y, ⟨hy, (hRead x y).mpr ⟨z, hxz, hzy⟩⟩, ?_⟩
    rintro y' ⟨_, hxy'⟩
    obtain ⟨z', hxz', hzy'⟩ := (hRead x y').mp hxy'
    have hEq := SecondOrderFunctionLaws.value_unique_l hℳ hF hxz' hxz
    subst z'
    exact SecondOrderFunctionLaws.value_unique_l hℳ hG hzy' hzy

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def specification_m {Γ Δ : SortContext ℒ} (F G A E H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (map_m H A E) <| .forallE .set <| .forallE .set <|
    .iff (value_m (up (up H)) (.bvar (.there .here)) (.bvar .here))
      (query_m (up (up F)) (up (up G)) (.bvar (.there .here)) (.bvar .here))

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (F G A E H : Term ℒ Γ Δ .set) :
    (specification_m F G A E H).satisfies η ↔ map_l (H.eval η) (A.eval η) (E.eval η) ∧
      ∀ x y, value_l (H.eval η) x y ↔ ∃ z, value_l (F.eval η) x z ∧ value_l (G.eval η) z y := by
  simp only [specification_m, Formula.satisfies, map_formula_l, value_formula_l, query_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let F : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let G : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let A : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let D : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let E : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  .imp (map_m F A D) <| .imp (map_m G D E) <|
    .existsE .set (specification_m (up F) (up G) (up A) (up E) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, map_formula_l, specification_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact fun hF hG => exists_l hF hG

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionGraphComposition
