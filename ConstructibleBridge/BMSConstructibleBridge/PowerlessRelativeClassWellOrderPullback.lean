import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationWellOrder

/-! # 沿实际类内单射拉回良序

只要求给定类内单射，不要求满射、ω 枚举或预设逆函数。对内部子集，
其像由目标母集上的 Δ₀ 分离取得；这足以将最小元传回源集。
后续元组编码可以消费本接口，不必把内部有限长度换成宿主长度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassWellOrderPullback

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassEnumerationWellOrder (wellOrder_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def comparison_m {Γ Δ : SortContext ℒ} (Y F R x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists Y <| membershipLevyBound.boundedExists (up Y) <|
    .conj (PowerlessValueBounded.formula_m (up (up F)) (up (up x)) (.bvar (.there .here))) <|
      .conj (PowerlessValueBounded.formula_m (up (up F)) (up (up y)) (.bvar .here))
        (PowerlessValueBounded.formula_m (up (up R)) (.bvar (.there .here)) (.bvar .here))

theorem comparison_delta_l {Γ Δ : SortContext ℒ} (Y F R x y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (comparison_m Y F R x y) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessValueBounded.delta_l _ _ _)
    (.conj (PowerlessValueBounded.delta_l _ _ _) (PowerlessValueBounded.delta_l _ _ _))))

def comparison_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (Y F R x y : carrier_l ℳ₀) : Prop :=
  ∃ a b, member_l ℳ₀ a Y ∧ member_l ℳ₀ b Y ∧ value_l F x a ∧ value_l F y b ∧ value_l R a b

theorem comparison_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (Y F R x y : Term ℒ Γ Δ .set) :
    (comparison_m Y F R x y).satisfies η ↔
      comparison_l (Y.eval η) (F.eval η) (R.eval η) (x.eval η) (y.eval η) := by
  simp only [comparison_m, comparison_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨a, ha, b, hb, hxa, hyb, hab⟩ => ⟨a, b, ha, hb, hxa, hyb, hab⟩,
    fun ⟨a, b, ha, hb, hxa, hyb, hab⟩ => ⟨a, ha, b, hb, hxa, hyb, hab⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

theorem exists_l {X Y F R : type_l hℳ B}
    (hF : map_l (ℳ := 𝒩) F X Y) (hInject : injective_l (ℳ := 𝒩) F)
    (hR : wellOrder_l (ℳ := 𝒩) Y R) :
    ∃ L : type_l hℳ B, wellOrder_l (ℳ := 𝒩) X L ∧
      ∀ x y : type_l hℳ B, value_l (ℳ := 𝒩) L x y ↔
        mem_l hℳ x.val X.val ∧ mem_l hℳ y.val X.val ∧ comparison_l (ℳ₀ := 𝒩) Y F R x y := by
  let η : Env 𝒩 [] [.set, .set, .set] := (((Env.empty).pushFree R).pushFree F).pushFree Y
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := comparison_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  have hφ (x y : type_l hℳ B) : φ.satisfies ((η.pushFree y).pushFree x) ↔
      comparison_l (ℳ₀ := 𝒩) Y F R x y := comparison_formula_l _ _ _ _ _ _
  obtain ⟨L, hL⟩ := PowerlessRelativeClassRelationalGraph.exists_l
    (φ := φ) (comparison_delta_l _ _ _ _ _) η X X
  have hRead (x y : type_l hℳ B) : value_l (ℳ := 𝒩) L x y ↔
      mem_l hℳ x.val X.val ∧ mem_l hℳ y.val X.val ∧ comparison_l (ℳ₀ := 𝒩) Y F R x y :=
    (hL x y).trans (and_congr Iff.rfl (and_congr Iff.rfl (hφ x y)))
  have hUnique {x a b : type_l hℳ B}
      (ha : value_l (ℳ := 𝒩) F x a) (hb : value_l (ℳ := 𝒩) F x b) : a = b :=
    PowerlessRelativeClassFunctionProperties.value_unique_l hF ha hb
  refine ⟨L, ?_, hRead⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _ hxx
    obtain ⟨_, _, a, b, ha, _, hxa, hxb, hab⟩ := (hRead x x).mp hxx
    have heq := hUnique hxa hxb
    subst b
    exact hR.1 a ha hab
  · intro x y z _ hxy hyz
    obtain ⟨hx, _, a, b, ha, hb, hxa, hyb, hab⟩ := (hRead x y).mp hxy
    obtain ⟨_, hz, b', c, _, hc, hyb', hzc, hbc⟩ := (hRead y z).mp hyz
    have heq := hUnique hyb hyb'
    subst b'
    exact (hRead x z).mpr ⟨hx, hz, a, c, ha, hc, hxa, hzc,
      hR.2.1 a b c ⟨ha, hb, hc⟩ hab hbc⟩
  · intro x y hxy
    obtain ⟨a, ⟨ha, hxa⟩, _⟩ := hF.2 x hxy.1
    obtain ⟨b, ⟨hb, hyb⟩, _⟩ := hF.2 y hxy.2
    rcases hR.2.2.1 a b ⟨ha, hb⟩ with hab | rfl | hba
    · exact Or.inl ((hRead x y).mpr ⟨hxy.1, hxy.2, a, b, ha, hb, hxa, hyb, hab⟩)
    · exact Or.inr (Or.inl (hInject x y a hxa hyb))
    · exact Or.inr (Or.inr ((hRead y x).mpr ⟨hxy.2, hxy.1, b, a, hb, ha, hyb, hxa, hba⟩))
  · intro U hU
    let ψ : Formula ℒ [] [.set, .set, .set] := membershipLevyBound.boundedExists (.fvar (.there .here))
      (PowerlessValueBounded.formula_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar .here))
    let ξ : Env 𝒩 [] [.set, .set] := ((Env.empty).pushFree F).pushFree U
    have hψ : Formula.IsDelta0 membershipLevyBound ψ :=
      .bounded_exists _ (PowerlessValueBounded.delta_l _ _ _)
    have hψRead (a : type_l hℳ B) : ψ.satisfies (ξ.pushFree a) ↔
        ∃ x : type_l hℳ B, mem_l hℳ x.val U.val ∧ value_l (ℳ := 𝒩) F x a := by
      simp only [ψ, ξ, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
        membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l, Arguments.eval, Term.eval]
      rfl
    obtain ⟨V, hV⟩ := PowerlessRelativeClassDeltaSeparation.exists_l hψ ξ Y
    have hVRead (a : type_l hℳ B) : mem_l hℳ a.val V.val ↔ mem_l hℳ a.val Y.val ∧
        ∃ x : type_l hℳ B, mem_l hℳ x.val U.val ∧ value_l (ℳ := 𝒩) F x a :=
      (hV a).trans (and_congr Iff.rfl (hψRead a))
    obtain ⟨x, hx⟩ := hU.2
    obtain ⟨a, ⟨ha, hxa⟩, _⟩ := hF.2 x (hU.1 x hx)
    obtain ⟨b, hbV, hMin⟩ := hR.2.2.2 V ⟨fun c hc => ((hVRead c).mp hc).1,
      a, (hVRead a).mpr ⟨ha, x, hx, hxa⟩⟩
    obtain ⟨_, y, hy, hyb⟩ := (hVRead b).mp hbV
    refine ⟨y, hy, ?_⟩
    intro z hz hzy
    obtain ⟨_, _, c, b', hc, _, hzc, hyb', hcb⟩ := (hRead z y).mp hzy
    have heq := hUnique hyb' hyb
    subst b'
    exact hMin c ((hVRead c).mpr ⟨hc, z, hz, hzc⟩) hcb

def specification_m {Γ Δ : SortContext ℒ} (X Y F R L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (wellOrder_m X L) <| .forallE .set <| .forallE .set <|
    .iff (value_m (up (up L)) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (member_m (.bvar (.there .here)) (up (up X))) <|
        .conj (member_m (.bvar .here) (up (up X)))
          (comparison_m (up (up Y)) (up (up F)) (up (up R)) (.bvar (.there .here)) (.bvar .here))

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (X Y F R L : Term ℒ Γ Δ .set) :
    (specification_m X Y F R L).satisfies η ↔
      wellOrder_l (X.eval η) (L.eval η) ∧ ∀ x y, value_l (L.eval η) x y ↔
        member_l ℳ₀ x (X.eval η) ∧ member_l ℳ₀ y (X.eval η) ∧
          comparison_l (Y.eval η) (F.eval η) (R.eval η) x y := by
  simp only [specification_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, value_formula_l,
    member_m, Arguments.eval, comparison_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let X : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let Y : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let F : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let R : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  .imp (map_m F X Y) <| .imp (injective_m F) <| .imp (wellOrder_m Y R) <|
    .existsE .set (specification_m (up X) (up Y) (up F) (up R) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, map_formula_l, injective_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    specification_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact fun hF hInject hR => exists_l (hBase := hBase) hF hInject hR

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassWellOrderPullback
