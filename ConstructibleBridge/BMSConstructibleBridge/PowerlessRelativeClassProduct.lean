import BMSConstructibleBridge.PowerlessRelativeClassFunctionAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassRelativization
import BMSConstructibleBridge.PowerlessPairBounded
import BMSConstructibleBridge.SecondOrderMemberDefBoundedSlice
import BMSConstructibleBridge.SecondOrderDefinableRelationImage

/-! # 相对类的实际笛卡尔积

两个共同层参数的全部有序对都落在第二个后继层；其 Δ₀ 切片进入第三个
后继 Def。因此积确实属于类，而不只是环境中存在。对象出口为原 Z₂
中的类相对化积公理，没有使用 Collection 或选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProduct

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (X Y p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists X <| membershipLevyBound.boundedExists (up Y) <|
    PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (up (up p))

theorem body_delta_l {Γ Δ : SortContext ℒ} (X Y p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m X Y p) :=
  .bounded_exists X (.bounded_exists (up Y) (PowerlessPairBounded.ordered_delta_l _ _ _))

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (X Y p : Term ℒ Γ Δ .set) :
    (body_m X Y p).satisfies η ↔ ∃ x y, member_l 𝒩 x (X.eval η) ∧ member_l 𝒩 y (Y.eval η) ∧
      ordered_l x y (p.eval η) := by
  simp only [body_m, Formula.LevyBound.boundedExists, Formula.satisfies,
    Formula.LevyBound.membership, membershipLevyBound, PowerlessPairBounded.ordered_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨x, hx, y, hy, hp⟩ => ⟨x, y, hx, hy, hp⟩,
    fun ⟨x, y, hx, hy, hp⟩ => ⟨x, hx, y, hy, hp⟩⟩

def formula_m : Formula ℒ [] [.set, .set] :=
  .existsE .set <| .forallE .set <| .iff
    (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
    (body_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close formula_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

theorem member_l (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {X Y P : SecondOrderQuotient.type_l hℳ}
    (hX : PowerlessRelativeClassCorrespondence.member_l hℳ B X)
    (hY : PowerlessRelativeClassCorrespondence.member_l hℳ B Y)
    (hP : ∀ p, mem_l hℳ p P ↔ ∃ x y, mem_l hℳ x X ∧ mem_l hℳ y Y ∧
      SecondOrderPairObjects.ordered_l hℳ x y p) : PowerlessRelativeClassCorrespondence.member_l hℳ B P := by
  obtain ⟨a, c, hc, hXc, hYc⟩ := PowerlessRelativeClassBounds.common_l hℳ hBase hX hY
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc
  obtain ⟨a₁, c₁, _, hc₁, hDef₁⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hc
  obtain ⟨a₂, c₂, _, hc₂, hDef₂⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hc₁
  obtain ⟨a₃, c₃, _, hc₃, hDef₃⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hc₂
  have hTrans₁ := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc₁
  have hTrans₂ := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc₂
  have hKeep₁ := SecondOrderMemberDefProperties.contains_l hℳ hDef₁ (fun x y hx hy => hTrans x hx y hy)
  have hKeep₂ := SecondOrderMemberDefProperties.contains_l hℳ hDef₂ (fun x y hx hy => hTrans₁ x hx y hy)
  have hPairs {x y p : SecondOrderQuotient.type_l hℳ} (hx : mem_l hℳ x X) (hy : mem_l hℳ y Y)
      (hp : SecondOrderPairObjects.ordered_l hℳ x y p) : mem_l hℳ p c₂ := by
    obtain ⟨s, t, hs, ht, hp⟩ := hp
    have hxC := hTrans X hXc x hx
    have hyC := hTrans Y hYc y hy
    exact SecondOrderMemberDefPair.member_l hℳ hDef₂
      (SecondOrderMemberDefPair.member_l hℳ hDef₁ hxC hxC hs)
      (SecondOrderMemberDefPair.member_l hℳ hDef₁ hxC hyC ht) hp
  let η := (Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushFree
    (sort := SetTheory.SetSort.set) Y |>.pushFree (sort := SetTheory.SetSort.set) X
  let φ : Formula ℒ [] [.set, .set, .set] := body_m (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar .here)
  have hParams : ∀ (s : SetTheory.SetSort) (v : Variable [SetTheory.SetSort.set, SetTheory.SetSort.set] s), mem_l hℳ (η.freeVal v) c₂ := by
    intro s v
    cases s
    cases v with
    | here => exact hKeep₂ X (hKeep₁ X hXc)
    | there v => cases v with
      | here => exact hKeep₂ Y (hKeep₁ Y hYc)
      | there v => nomatch v
  have hSlice : ∀ p, mem_l hℳ p P ↔ mem_l hℳ p c₂ ∧ φ.satisfies (η.pushFree p) := by
    intro p
    have hBody := body_formula_l (η.pushFree (sort := SetTheory.SetSort.set) p)
      (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
    constructor
    · intro hp
      obtain ⟨x, y, hx, hy, hxy⟩ := (hP p).mp hp
      exact ⟨hPairs hx hy hxy, hBody.mpr ⟨x, y, hx, hy, hxy⟩⟩
    · rintro ⟨_, hp⟩
      exact (hP p).mpr (hBody.mp hp)
  exact ⟨a₃, c₃, hc₃, SecondOrderMemberDefBoundedSlice.member_l hℳ hDef₃ hTrans₂
    (body_delta_l _ _ _) η hParams hSlice⟩

theorem exists_l (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (X Y : type_l hℳ B) : ∃ P : type_l hℳ B, ∀ p : type_l hℳ B,
      mem_l hℳ p.val P.val ↔ ∃ x y : type_l hℳ B,
        mem_l hℳ x.val X.val ∧ mem_l hℳ y.val Y.val ∧
          ThirdOrderSemantics.ordered_l (ℳ := structure_l hℳ B hBase) x y p := by
  obtain ⟨P, hP⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (Δ := []) .truth
    (Env.empty (M := SecondOrderQuotient.structure_l hℳ)) X.val Y.val
  have hP' : ∀ p, mem_l hℳ p P ↔ ∃ x y, mem_l hℳ x X.val ∧ mem_l hℳ y Y.val ∧
      SecondOrderPairObjects.ordered_l hℳ x y p := by
    simpa only [Formula.satisfies, true_and] using hP
  refine ⟨⟨P, member_l hBase X.property Y.property hP'⟩, fun p => ?_⟩
  constructor
  · intro hp
    obtain ⟨x, y, hx, hy, hxy⟩ := (hP' p.val).mp hp
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hx⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩
    exact ⟨x', y', hx, hy, (PowerlessRelativeClassFunctionAbsolute.ordered_l x' y' p).mpr hxy⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact (hP' p.val).mpr ⟨x.val, y.val, hx, hy, (PowerlessRelativeClassFunctionAbsolute.ordered_l x y p).mp hxy⟩

theorem models_l (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  obtain ⟨P, hP⟩ := exists_l hBase (η.freeVal .here) (η.freeVal (.there .here))
  refine ⟨P, fun p => ?_⟩
  have hBody := body_formula_l ((η.pushBound (sort := SetTheory.SetSort.set) P).pushBound (sort := SetTheory.SetSort.set) p)
    (.fvar .here) (.fvar (.there .here)) (.bvar .here)
  change (body_m (.fvar .here) (.fvar (.there .here)) (.bvar .here)).satisfies
    ((η.pushBound P).pushBound p) ↔ ∃ x y : type_l hℳ B,
      mem_l hℳ x.val (η.freeVal .here).val ∧ mem_l hℳ y.val (η.freeVal (.there .here)).val ∧
        ThirdOrderSemantics.ordered_l (ℳ := structure_l hℳ B hBase) x y p at hBody
  exact (hP p).trans hBody.symm

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ _ _ hBase => models_l hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProduct
