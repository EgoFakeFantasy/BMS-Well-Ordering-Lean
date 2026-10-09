import BMSConstructibleBridge.PowerlessRelativeClassWellOrderPullback

/-! # 良序满射的最小代表逆图与像集良序

对象语言为纯集合语言，经类相对化与图翻译回到原 Z₂ 推导核。
已给定实际类内满射及其定义域良序时，每个纤维经 Δ₀ 分离取得；
纤维最小元构成实际逆图。没有 Type 选择、Collection 或 ω 枚举前提。
本工具不提供 Def 的表示满射，也不声称不同层所得良序相容。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassWellOrderSection

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassEnumerationWellOrder (wellOrder_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def minimal_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (X R F y x : carrier_l ℳ₀) : Prop :=
  value_l F x y ∧ ∀ z, member_l ℳ₀ z X → value_l F z y → ¬value_l R z x

def minimal_m {Γ Δ : SortContext ℒ} (X R F y x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessValueBounded.formula_m F x y) <|
    membershipLevyBound.boundedForall X <|
      .imp (PowerlessValueBounded.formula_m (up F) (.bvar .here) (up y))
        (.neg (PowerlessValueBounded.formula_m (up R) (.bvar .here) (up x)))

theorem minimal_delta_l {Γ Δ : SortContext ℒ} (X R F y x : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (minimal_m X R F y x) :=
  .conj (PowerlessValueBounded.delta_l _ _ _) (.bounded_forall _
    (.imp (PowerlessValueBounded.delta_l _ _ _) (.neg (PowerlessValueBounded.delta_l _ _ _))))

theorem minimal_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (X R F y x : Term ℒ Γ Δ .set) :
    (minimal_m X R F y x).satisfies η ↔
      minimal_l (X.eval η) (R.eval η) (F.eval η) (y.eval η) (x.eval η) := by
  simp only [minimal_m, minimal_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

theorem minimum_l {X R F y : type_l hℳ B} (hR : wellOrder_l (ℳ := 𝒩) X R)
    (hNonempty : ∃ x : type_l hℳ B, mem_l hℳ x.val X.val ∧ value_l (ℳ := 𝒩) F x y) :
    ∃! x : type_l hℳ B, mem_l hℳ x.val X.val ∧ minimal_l (ℳ₀ := 𝒩) X R F y x := by
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessValueBounded.formula_m
    (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒩 [] [.set, .set] := ((Env.empty).pushFree F).pushFree y
  obtain ⟨U, hU⟩ := PowerlessRelativeClassDeltaSeparation.exists_l
    (φ := φ) (PowerlessValueBounded.delta_l _ _ _) η X
  have hRead (x : type_l hℳ B) : mem_l hℳ x.val U.val ↔
      mem_l hℳ x.val X.val ∧ value_l (ℳ := 𝒩) F x y :=
    (hU x).trans (and_congr Iff.rfl (PowerlessValueBounded.formula_l (η.pushFree x) _ _ _))
  obtain ⟨a, ha, hay⟩ := hNonempty
  obtain ⟨x, hxU, hMin⟩ := hR.2.2.2 U ⟨fun z hz => ((hRead z).mp hz).1,
    a, (hRead a).mpr ⟨ha, hay⟩⟩
  obtain ⟨hx, hxy⟩ := (hRead x).mp hxU
  have hLeast : minimal_l (ℳ₀ := 𝒩) X R F y x :=
    ⟨hxy, fun z hz hzy => hMin z ((hRead z).mpr ⟨hz, hzy⟩)⟩
  refine ⟨x, ⟨hx, hLeast⟩, ?_⟩
  rintro z ⟨hz, hzLeast⟩
  rcases hR.2.2.1 z x ⟨hz, hx⟩ with hzx | hEq | hxz
  · exact (hLeast.2 z hz hzLeast.1 hzx).elim
  · exact hEq
  · exact (hzLeast.2 x hx hxy hxz).elim

theorem exists_l {X Y F R : type_l hℳ B}
    (hF : map_l (ℳ := 𝒩) F X Y) (hR : wellOrder_l (ℳ := 𝒩) X R)
    (hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val Y.val → ∃ x : type_l hℳ B,
      mem_l hℳ x.val X.val ∧ value_l (ℳ := 𝒩) F x y) :
    ∃ J : type_l hℳ B, map_l (ℳ := 𝒩) J Y X ∧ injective_l (ℳ := 𝒩) J ∧
      ∀ y x : type_l hℳ B, value_l (ℳ := 𝒩) J y x ↔
        mem_l hℳ y.val Y.val ∧ mem_l hℳ x.val X.val ∧ minimal_l (ℳ₀ := 𝒩) X R F y x := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := minimal_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒩 [] [.set, .set, .set] := (((Env.empty).pushFree F).pushFree R).pushFree X
  have hφ (y x : type_l hℳ B) : φ.satisfies ((η.pushFree x).pushFree y) ↔
      minimal_l (ℳ₀ := 𝒩) X R F y x := minimal_formula_l _ _ _ _ _ _
  obtain ⟨J, hJ, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (φ := φ) (minimal_delta_l _ _ _ _ _) η Y X (by
      intro y hy
      obtain ⟨x, ⟨hx, hMin⟩, hUnique⟩ := minimum_l hR (hOnto y hy)
      exact ⟨x, ⟨hx, (hφ y x).mpr hMin⟩,
        fun z hz => hUnique z ⟨hz.1, (hφ y z).mp hz.2⟩⟩)
  have hRead (y x : type_l hℳ B) : value_l (ℳ := 𝒩) J y x ↔
      mem_l hℳ y.val Y.val ∧ mem_l hℳ x.val X.val ∧ minimal_l (ℳ₀ := 𝒩) X R F y x :=
    (hValue y x).trans (and_congr Iff.rfl (and_congr Iff.rfl (hφ y x)))
  refine ⟨J, hJ, ?_, hRead⟩
  intro y z x hy hz
  exact PowerlessRelativeClassFunctionProperties.value_unique_l hF
    ((hRead y x).mp hy).2.2.1 ((hRead z x).mp hz).2.2.1

def specification_m {Γ Δ : SortContext ℒ} (X Y F R J : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (map_m J Y X) <| .conj (injective_m J) <| .forallE .set <| .forallE .set <|
    .iff (value_m (up (up J)) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (member_m (.bvar (.there .here)) (up (up Y))) <|
        .conj (member_m (.bvar .here) (up (up X)))
          (minimal_m (up (up X)) (up (up R)) (up (up F)) (.bvar (.there .here)) (.bvar .here))

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (X Y F R J : Term ℒ Γ Δ .set) :
    (specification_m X Y F R J).satisfies η ↔
      map_l (J.eval η) (Y.eval η) (X.eval η) ∧ injective_l (J.eval η) ∧
        ∀ y x, value_l (J.eval η) y x ↔ member_l ℳ₀ y (Y.eval η) ∧
          member_l ℳ₀ x (X.eval η) ∧ minimal_l (X.eval η) (R.eval η) (F.eval η) y x := by
  simp only [specification_m, Formula.satisfies, map_formula_l, injective_formula_l,
    value_formula_l, member_m, Arguments.eval, minimal_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let X : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let Y : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let F : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let R : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  .imp (map_m F X Y) <| .imp (wellOrder_m X R) <|
    .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m F X Y) <|
      .existsE .set <| .existsE .set <|
        .conj (specification_m (up (up X)) (up (up Y)) (up (up F)) (up (up R)) (.bvar (.there .here)))
          (PowerlessRelativeClassWellOrderPullback.specification_m (up (up Y)) (up (up X))
            (.bvar (.there .here)) (up (up R)) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, map_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    specification_formula_l, PowerlessRelativeClassWellOrderPullback.specification_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  intro hF hR hOnto
  obtain ⟨J, hJ, hInject, hRead⟩ := exists_l (hBase := hBase) hF hR hOnto
  obtain ⟨L, hL⟩ := PowerlessRelativeClassWellOrderPullback.exists_l hJ hInject hR
  exact ⟨J, L, ⟨hJ, hInject, hRead⟩, hL⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms minimum_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassWellOrderSection
