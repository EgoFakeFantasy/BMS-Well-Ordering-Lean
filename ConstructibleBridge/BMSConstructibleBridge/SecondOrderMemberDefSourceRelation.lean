import BMSConstructibleBridge.SecondOrderMemberDefSourceSlice
import BMSConstructibleBridge.PowerlessSourceGraphAbsolute
import BMSConstructibleBridge.PowerlessRelativeLimitClosure

/-! # 实际源公式定义的关系图进入 Def

输入域是源成员，输出坐标可遍历整个源域；不要求源域自身属于源域。
任意有限矩阵生成实际 Kuratowski 关系图，并精确回读其函数值关系。
图只保证属于 Def(C)，不声称属于 C；每个公式实例复用原 Z₂ 的对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefSourceRelation

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set, .set] (.set :: .set :: Δ)
  | _, .here => .bvar (.there .here)
  | _, .there .here => .bvar .here
  | _, .there (.there v) => .fvar (.there (.there v))

private def inner_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [.set, .set] (.set :: .set :: Δ) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ)
    [.set, .set] (.set :: .set :: Δ) from .map (fun v => nomatch v) insert_m)

def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  .existsE .set <| .existsE .set <|
    .conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.fvar (.there .here))) <|
      .conj (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
        (inner_m φ)

private theorem inner_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (X p x y : carrier_l 𝒩) :
    (inner_m φ).satisfies ((((η.pushFree X).pushFree p).pushBound x).pushBound y) ↔
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

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (X p : carrier_l 𝒩) :
    (body_m φ).satisfies ((η.pushFree X).pushFree p) ↔ ∃ x y,
      member_l 𝒩 x X ∧ ordered_l x y p ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  simp only [body_m, Formula.satisfies, ThirdOrderSemantics.ordered_formula_l,
    inner_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {C D : SecondOrderQuotient.type_l hℳ} (hC : ∃ c, mem_l hℳ c C)
    (hCT : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ) C)
    (hOrdered : ∀ x y p, mem_l hℳ x C → mem_l hℳ y C →
      SecondOrderPairObjects.ordered_l hℳ x y p → mem_l hℳ p C)
    (hDef : SecondOrderMemberDef.spec_l hℳ C D) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) C hC) [] Δ)
    (X : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C) :
    ∃ f, mem_l hℳ f D ∧ ∀ p, mem_l hℳ p f ↔
      ∃ x y : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C,
        mem_l hℳ x.val X.val ∧
          ordered_l (ℳ := SecondOrderQuotient.structure_l hℳ) x.val y.val p ∧
            φ.satisfies ((η.pushFree y).pushFree x) := by
  obtain ⟨f, hf, hRead⟩ := SecondOrderMemberDefSourceSlice.exists_l hC hDef (body_m φ) (η.pushFree X)
  refine ⟨f, hf, fun p => ?_⟩
  constructor
  · intro hp
    have hpC := SecondOrderMemberDefProperties.subset_l hℳ hDef hf p hp
    obtain ⟨x, y, hx, hxy, hφ⟩ := (body_formula_l φ η X ⟨p, hpC⟩).mp ((hRead ⟨p, hpC⟩).mp hp)
    exact ⟨x, y, hx, (PowerlessSourceGraphAbsolute.ordered_l hCT).mp hxy, hφ⟩
  · rintro ⟨x, y, hx, hxy, hφ⟩
    have hpC := hOrdered x.val y.val p x.property y.property hxy
    exact (hRead ⟨p, hpC⟩).mpr ((body_formula_l φ η X ⟨p, hpC⟩).mpr
      ⟨x, y, hx, (PowerlessSourceGraphAbsolute.ordered_l hCT).mpr hxy, hφ⟩)

theorem value_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {C : SecondOrderQuotient.type_l hℳ} (hC : ∃ c, mem_l hℳ c C) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) C hC) [] Δ)
    (X : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C)
    {f : SecondOrderQuotient.type_l hℳ}
    (hRead : ∀ p, mem_l hℳ p f ↔
      ∃ x y : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C,
        mem_l hℳ x.val X.val ∧
          ordered_l (ℳ := SecondOrderQuotient.structure_l hℳ) x.val y.val p ∧
            φ.satisfies ((η.pushFree y).pushFree x))
    (x y : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C) :
    ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f x.val y.val ↔
      mem_l hℳ x.val X.val ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  constructor
  · rintro ⟨p, hp, hxy⟩
    obtain ⟨a, b, ha, hab, hφ⟩ := (hRead p).mp hp
    obtain ⟨haEq, hbEq⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hab hxy).mp rfl
    have haX : a = x := Subtype.ext haEq
    have hbY : b = y := Subtype.ext hbEq
    subst a
    subst b
    exact ⟨ha, hφ⟩
  · rintro ⟨hx, hφ⟩
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x.val y.val
    exact ⟨p, (hRead p).mpr ⟨x, y, hx, hp, hφ⟩, hp⟩

/-- 任意环境坐标的读取同时给出真实的源成员证据。 -/
theorem raw_value_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {C : SecondOrderQuotient.type_l hℳ} (hC : ∃ c, mem_l hℳ c C) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) C hC) [] Δ)
    (X : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C)
    {f : SecondOrderQuotient.type_l hℳ}
    (hRead : ∀ p, mem_l hℳ p f ↔
      ∃ x y : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C,
        mem_l hℳ x.val X.val ∧
          ordered_l (ℳ := SecondOrderQuotient.structure_l hℳ) x.val y.val p ∧
            φ.satisfies ((η.pushFree y).pushFree x))
    (a b : SecondOrderQuotient.type_l hℳ) :
    ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f a b ↔
      ∃ x y : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C,
        x.val = a ∧ y.val = b ∧ mem_l hℳ x.val X.val ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  constructor
  · rintro ⟨p, hp, hab⟩
    obtain ⟨x, y, hx, hxy, hφ⟩ := (hRead p).mp hp
    obtain ⟨hxEq, hyEq⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hab).mp rfl
    exact ⟨x, y, hxEq, hyEq, hx, hφ⟩
  · rintro ⟨x, y, rfl, rfl, hx, hφ⟩
    exact (value_l hℳ hC φ η X hRead x y).mpr ⟨hx, hφ⟩

/-- 源公式的总性、单值性及实际值域界产生原商中的合法函数图。 -/
theorem map_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {C Y : SecondOrderQuotient.type_l hℳ} (hC : ∃ c, mem_l hℳ c C)
    (hCT : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ) C)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) C hC) [] Δ)
    (X : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C)
    {f : SecondOrderQuotient.type_l hℳ}
    (hRead : ∀ p, mem_l hℳ p f ↔
      ∃ x y : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C,
        mem_l hℳ x.val X.val ∧
          ordered_l (ℳ := SecondOrderQuotient.structure_l hℳ) x.val y.val p ∧
            φ.satisfies ((η.pushFree y).pushFree x))
    (hTotal : ∀ x : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C,
      mem_l hℳ x.val X.val → ∃! y, φ.satisfies ((η.pushFree y).pushFree x))
    (hRange : ∀ x y : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C,
      mem_l hℳ x.val X.val → φ.satisfies ((η.pushFree y).pushFree x) → mem_l hℳ y.val Y) :
    ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f X.val Y := by
  constructor
  · intro p hp
    obtain ⟨x, y, hx, hxy, hφ⟩ := (hRead p).mp hp
    exact ⟨x.val, y.val, hx, hRange x y hx hφ, hxy⟩
  · intro a ha
    let x : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C :=
      ⟨a, hCT X.val a X.property ha⟩
    obtain ⟨y, hy, hUnique⟩ := hTotal x ha
    refine ⟨y.val, ⟨hRange x y ha hy, (value_l hℳ hC φ η X hRead x y).mpr ⟨ha, hy⟩⟩, ?_⟩
    intro b hb
    obtain ⟨x', y', hxEq, hyEq, hx', hφ⟩ := (raw_value_l hℳ hC φ η X hRead a b).mp hb.2
    have hxX : x' = x := Subtype.ext hxEq
    subst x'
    exact hyEq.symm.trans (congrArg Subtype.val (hUnique y' hφ))

theorem limit_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B β C D : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hC : ∃ c, mem_l hℳ c C) (hDef : SecondOrderMemberDef.spec_l hℳ C D)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) C hC) [] Δ)
    (X : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C) :
    ∃ f, mem_l hℳ f D ∧ ∀ p, mem_l hℳ p f ↔
      ∃ x y : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C,
        mem_l hℳ x.val X.val ∧
          ordered_l (ℳ := SecondOrderQuotient.structure_l hℳ) x.val y.val p ∧
            φ.satisfies ((η.pushFree y).pushFree x) :=
  exists_l hℳ hC (fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel x hx y hy)
    (fun _ _ _ hx hy hp => PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hLevel hx hy hp)
    hDef φ η X

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  SecondOrderMemberDefSourceSlice.sentence_m (body_m φ)

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderMemberDefSourceSlice.derives_m (body_m φ)

#print axioms exists_l
#print axioms value_l
#print axioms map_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefSourceRelation
