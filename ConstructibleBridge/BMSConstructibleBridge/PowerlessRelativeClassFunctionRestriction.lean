import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessRelativeClassFunctionProperties
import BMSConstructibleBridge.PowerlessValueBounded

/-! # 类内集合函数的外延性与实际定义域限制

限制图由有界求值关系构造，属于同一相对类。该接口用于内部序列的
前缀，不要求母集可数、完整 Collection 或宿主选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionRestriction

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

theorem ext_l {f g A D E C : type_l hℳ B}
    (hf : map_l (ℳ := 𝒩) f A D) (hg : map_l (ℳ := 𝒩) g E C)
    (h : ∀ x y : type_l hℳ B, value_l (ℳ := 𝒩) f x y ↔ value_l (ℳ := 𝒩) g x y) : f = g := by
  have hForward {f g A D : type_l hℳ B} (hf : map_l (ℳ := 𝒩) f A D)
      (h : ∀ x y : type_l hℳ B, value_l (ℳ := 𝒩) f x y → value_l (ℳ := 𝒩) g x y) :
      ∀ p : type_l hℳ B, mem_l hℳ p.val f.val → mem_l hℳ p.val g.val := by
    intro p hp
    obtain ⟨x, y, _, _, hxy⟩ := hf.1 p hp
    obtain ⟨q, hq, hxy'⟩ := h x y ⟨p, hp, hxy⟩
    have hpq : p = q := Subtype.ext (SecondOrderPairObjects.ordered_unique_l hℳ
      ((PowerlessRelativeClassFunctionAbsolute.ordered_l x y p).mp hxy)
      ((PowerlessRelativeClassFunctionAbsolute.ordered_l x y q).mp hxy'))
    exact hpq.symm ▸ hq
  apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
  exact fun p => ⟨hForward hf (fun x y => (h x y).mp) p,
    hForward hg (fun x y => (h x y).mpr) p⟩

theorem exists_l {f A D E : type_l hℳ B} (hf : map_l (ℳ := 𝒩) f A D)
    (hE : subset_l (ℳ := 𝒩) E A) :
    ∃ g : type_l hℳ B, map_l (ℳ := 𝒩) g E D ∧ ∀ x y : type_l hℳ B,
      value_l (ℳ := 𝒩) g x y ↔ mem_l hℳ x.val E.val ∧ value_l (ℳ := 𝒩) f x y := by
  let η : Env 𝒩 [] [.set] := (Env.empty).pushFree f
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessValueBounded.formula_m
    (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  have hφ (x y : type_l hℳ B) : φ.satisfies ((η.pushFree y).pushFree x) ↔ value_l (ℳ := 𝒩) f x y :=
    PowerlessValueBounded.formula_l _ _ _ _
  have hTotal (x : type_l hℳ B) (hx : mem_l hℳ x.val E.val) :
      ∃! y : type_l hℳ B, mem_l hℳ y.val D.val ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
    obtain ⟨y, ⟨hy, hxy⟩, _⟩ := hf.2 x (hE x hx)
    refine ⟨y, ⟨hy, (hφ x y).mpr hxy⟩, ?_⟩
    intro z hz
    exact PowerlessRelativeClassFunctionProperties.value_unique_l hf ((hφ x z).mp hz.2) hxy
  obtain ⟨g, hg, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (φ := φ) (PowerlessValueBounded.delta_l _ _ _) η E D hTotal
  refine ⟨g, hg, fun x y => (hRead x y).trans ?_⟩
  constructor
  · exact fun h => ⟨h.1, (hφ x y).mp h.2.2⟩
  · rintro ⟨hx, hxy⟩
    exact ⟨hx, (PowerlessRelativeClassFunctionProperties.value_mem_l hf hxy).2, (hφ x y).mpr hxy⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def specification_m {Γ Δ : SortContext ℒ} (f E D g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (map_m g E D) <| .forallE .set <| .forallE .set <|
    .iff (value_m (up (up g)) (.bvar (.there .here)) (.bvar .here))
      (.conj (member_m (.bvar (.there .here)) (up (up E)))
        (value_m (up (up f)) (.bvar (.there .here)) (.bvar .here)))

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (f E D g : Term ℒ Γ Δ .set) :
    (specification_m f E D g).satisfies η ↔ map_l (g.eval η) (E.eval η) (D.eval η) ∧
      ∀ x y, value_l (g.eval η) x y ↔ member_l ℳ₀ x (E.eval η) ∧ value_l (f.eval η) x y := by
  simp only [specification_m, Formula.satisfies, map_formula_l, value_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let f : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let A : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let D : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let E : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  .imp (map_m f A D) <| .imp (ThirdOrderTheory.subset_m E A) <|
    .existsE .set (specification_m (up f) (up E) (up D) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, map_formula_l, subset_formula_l,
    specification_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact fun hf hE => exists_l (hBase := hBase) hf hE

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms ext_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionRestriction
