import BMSConstructibleBridge.PowerlessRelativeClassProduct
import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation
import BMSConstructibleBridge.SecondOrderDefinableRelationImageDerives

/-! # 类内有界可定义关系的集合图

在实际类内积上应用已证明的 Δ₀ 分离模式。参数仍留在原有限环境中，
首自由变量为左坐标，次自由变量为右坐标；不从宿主谓词抽取集合图。
每个有界公式实例的关系图存在句都有原 Z₂ 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRelation

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set, .set] (.set :: .set :: .set :: Δ)
  | _, .here => .bvar (.there .here)
  | _, .there .here => .bvar .here
  | _, .there (.there v) => .fvar (.there (.there (.there v)))

private def inner_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [.set, .set] (.set :: .set :: .set :: Δ) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ)
    [.set, .set] (.set :: .set :: .set :: Δ) from .map (fun v => nomatch v) insert_m)

def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: Δ) :=
  membershipLevyBound.boundedExists (.fvar (.there .here)) <|
    membershipLevyBound.boundedExists (.fvar (.there (.there .here))) <|
      .conj (PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar .here)) (inner_m φ)

theorem body_delta_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) : Formula.IsDelta0 membershipLevyBound (body_m φ) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
    (hφ.substituteMapped
      (show VariableSubstitution ℒ [] [.set, .set] (.set :: .set :: .set :: Δ) from fun v => nomatch v) insert_m)))

private theorem inner_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (X Y p x y : carrier_l 𝒩) :
    (inner_m φ).satisfies (((((η.pushFree Y).pushFree X).pushFree p).pushBound x).pushBound y) ↔
      φ.satisfies ((η.pushFree y).pushFree x) := by
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro _ v; nomatch v
  · intro s v
    cases s
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (X Y p : carrier_l 𝒩) :
    (body_m φ).satisfies (((η.pushFree Y).pushFree X).pushFree p) ↔ ∃ x y,
      member_l 𝒩 x X ∧ member_l 𝒩 y Y ∧ ordered_l x y p ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  simp only [body_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
    inner_formula_l, Arguments.eval, Term.eval]
  exact ⟨fun ⟨x, hx, y, hy, hp, hφ⟩ => ⟨x, y, hx, hy, hp, hφ⟩,
    fun ⟨x, y, hx, hy, hp, hφ⟩ => ⟨x, hx, y, hy, hp, hφ⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env (structure_l hℳ B hBase) [] Δ)
    (X Y : type_l hℳ B) : ∃ f : type_l hℳ B, ∀ p : type_l hℳ B,
      mem_l hℳ p.val f.val ↔ ∃ x y : type_l hℳ B,
        mem_l hℳ x.val X.val ∧ mem_l hℳ y.val Y.val ∧
          ordered_l (ℳ := structure_l hℳ B hBase) x y p ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  obtain ⟨P, hP⟩ := PowerlessRelativeClassProduct.exists_l hBase X Y
  obtain ⟨f, hf⟩ := PowerlessRelativeClassDeltaSeparation.exists_l (body_delta_l hφ)
    ((η.pushFree (sort := SetTheory.SetSort.set) Y).pushFree (sort := SetTheory.SetSort.set) X) P
  refine ⟨f, fun p => (hf p).trans ?_⟩
  have hBody := body_formula_l φ η X Y p
  constructor
  · rintro ⟨_, hp⟩
    exact hBody.mp hp
  · rintro ⟨x, y, hx, hy, hp, hxy⟩
    exact ⟨(hP p).mpr ⟨x, y, hx, hy, hp⟩, hBody.mpr ⟨x, y, hx, hy, hp, hxy⟩⟩

theorem schema_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (structure_l hℳ B hBase) [] Δ) :
    (SecondOrderDefinableRelationImageDerives.schema_m φ).satisfies η ↔
      ∀ X Y : type_l hℳ B, ∃ f : type_l hℳ B, ∀ p : type_l hℳ B,
        mem_l hℳ p.val f.val ↔ ∃ x y : type_l hℳ B,
          mem_l hℳ x.val X.val ∧ mem_l hℳ y.val Y.val ∧ φ.satisfies ((η.pushFree y).pushFree x) ∧
            ordered_l (ℳ := structure_l hℳ B hBase) x y p :=
  SecondOrderDefinableRelationImageDerives.schema_generic_l φ η

theorem models_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    (SecondOrderDefinableRelationImageDerives.sentence_m φ).TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  apply (schema_formula_l φ η).mpr
  intro X Y
  obtain ⟨f, hf⟩ := exists_l hφ η X Y
  exact ⟨f, fun p => (hf p).trans (exists_congr fun _ => exists_congr fun _ =>
    and_congr Iff.rfl (and_congr Iff.rfl and_comm))⟩

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m
      (SecondOrderDefinableRelationImageDerives.sentence_m φ))) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ _ _ _ => models_l hφ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRelation
