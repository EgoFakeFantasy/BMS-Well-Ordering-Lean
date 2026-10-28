import BMSConstructibleBridge.PowerlessHereditaryPairing
import BMSConstructibleBridge.PowerlessHereditarySubset
import BMSConstructibleBridge.PowerlessRelativeClassPairFamilyEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassBinaryUnion

/-! # 原遗传参数的笛卡尔积及干净关系图仍遗传

纯隶属 ℒ，背景原 Z₂。两个原可数传递包络合并后，两次全部无序对
闭包统一容纳 Kuratowski 有序对及其成员。实际枚举逐次交错，得到
同一传递母包络；不以每个输出分别遗传代替整张图的统一证书。

原积 P 不更换。任意 Class 关系图只要全部坐标落在两个遗传参数中，
就作为该原积的子集取得遗传性，不要求关系总性或任意像集公理。
公开对象出口仍为原推导核 Derives，不能据此宣称 Collection 完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryProduct

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

private theorem envelope_l {X Y Z : type_l hℳ B}
    (hX : PowerlessHereditaryClassInternals.envelope_l (𝒩 := 𝒩₀) X)
    (hY : PowerlessHereditaryClassInternals.envelope_l (𝒩 := 𝒩₀) Y)
    (hZ : ∀ p : type_l hℳ B, ε p.val Z.val ↔ ∃ x y : type_l hℳ B,
      ε x.val X.val ∧ ε y.val Y.val ∧ ordered_l (ℳ := 𝒩₀) x y p) :
    PowerlessHereditaryClassInternals.envelope_l (𝒩 := 𝒩₀) Z := by
  obtain ⟨U, G, ω, hXU, hUTrans, hω, hG, hGOnto⟩ := hX
  obtain ⟨V, H, ω', hYV, hVTrans, hω', hH, hHOnto⟩ := hY
  have hEq : ω' = ω := Subtype.ext (SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mp hω')
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω))
  subst ω'
  obtain ⟨T, hT, F, hF, hFOnto⟩ := PowerlessRelativeClassBinaryUnion.enumeration_l hω hG hH hGOnto hHOnto
  have hTTrans (x : type_l hℳ B) (hx : ε x.val T.val)
      (y : type_l hℳ B) (hy : ε y.val x.val) : ε y.val T.val :=
    (hT y).mpr (((hT x).mp hx).elim
      (fun hxU => Or.inl (hUTrans x hxU y hy)) (fun hxV => Or.inr (hVTrans x hxV y hy)))
  have hXT : ε X.val T.val := (hT X).mpr (Or.inl hXU)
  have hYT : ε Y.val T.val := (hT Y).mpr (Or.inr hYV)
  obtain ⟨P, hP, GP, hGP, hPonto⟩ := PowerlessRelativeClassPairFamilyEnumeration.exists_l hω hF hFOnto
  obtain ⟨Q, hQ, GQ, hGQ, hQonto⟩ := PowerlessRelativeClassPairFamilyEnumeration.exists_l hω hGP hPonto
  obtain ⟨L, hL, GL, hGL, hLonto⟩ := PowerlessRelativeClassBinaryUnion.enumeration_l hω hF hGP hFOnto hPonto
  obtain ⟨W, hW, GW, hGW, hWonto⟩ := PowerlessRelativeClassBinaryUnion.enumeration_l hω hGL hGQ hLonto hQonto
  have hTW (x : type_l hℳ B) (hx : ε x.val T.val) : ε x.val W.val :=
    (hW x).mpr (Or.inl ((hL x).mpr (Or.inl hx)))
  have hPW (x : type_l hℳ B) (hx : ε x.val P.val) : ε x.val W.val :=
    (hW x).mpr (Or.inl ((hL x).mpr (Or.inr hx)))
  have hWTrans (x : type_l hℳ B) (hx : ε x.val W.val)
      (y : type_l hℳ B) (hy : ε y.val x.val) : ε y.val W.val := by
    rcases (hW x).mp hx with hx | hx
    · rcases (hL x).mp hx with hx | hx
      · exact hTW y (hTTrans x hx y hy)
      · obtain ⟨a, b, ha, hb, hPair⟩ := (hP x).mp hx
        rcases (hPair y).mp hy with rfl | rfl
        · exact hTW _ ha
        · exact hTW _ hb
    · obtain ⟨a, b, ha, hb, hPair⟩ := (hQ x).mp hx
      rcases (hPair y).mp hy with rfl | rfl
      · exact hPW _ ha
      · exact hPW _ hb
  have hZW (p : type_l hℳ B) (hp : ε p.val Z.val) : ε p.val W.val := by
    obtain ⟨x, y, hx, hy, s, t, hs, ht, hpPair⟩ := (hZ p).mp hp
    have hxT := hTTrans X hXT x hx
    have hyT := hTTrans Y hYT y hy
    have hsP := (hP s).mpr ⟨x, x, hxT, hxT, hs⟩
    have htP := (hP t).mpr ⟨x, y, hxT, hyT, ht⟩
    exact (hW p).mpr (Or.inr ((hQ p).mpr ⟨s, t, hsP, htP, hpPair⟩))
  exact PowerlessHereditaryExtension.exists_l ω Z W GW hω hWTrans hZW hGW hWonto

include hBase in
theorem member_l {X Y P : SecondOrderQuotient.type_l hℳ}
    (hX : PowerlessHereditaryClass.member_l hℳ B X)
    (hY : PowerlessHereditaryClass.member_l hℳ B Y)
    (hP : ∀ p, ε p P ↔ ∃ x y, ε x X ∧ ε y Y ∧ SecondOrderPairObjects.ordered_l hℳ x y p) :
    PowerlessHereditaryClass.member_l hℳ B P := by
  have hXC := PowerlessHereditaryClass.contained_l hℳ hBase hX
  have hYC := PowerlessHereditaryClass.contained_l hℳ hBase hY
  have hPC := PowerlessRelativeClassProduct.member_l hBase hXC hYC hP
  let X' : type_l hℳ B := ⟨X, hXC⟩
  let Y' : type_l hℳ B := ⟨Y, hYC⟩
  let P' : type_l hℳ B := ⟨P, hPC⟩
  have hRead (p : type_l hℳ B) : ε p.val P ↔ ∃ x y : type_l hℳ B,
      ε x.val X ∧ ε y.val Y ∧ ordered_l (ℳ := 𝒩₀) x y p := by
    apply (hP p.val).trans
    constructor
    · rintro ⟨x, y, hx, hy, hxy⟩
      let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hXC hx⟩
      let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hYC hy⟩
      exact ⟨x', y', hx, hy, (PowerlessRelativeClassFunctionAbsolute.ordered_l x' y' p).mpr hxy⟩
    · rintro ⟨x, y, hx, hy, hxy⟩
      exact ⟨x.val, y.val, hx, hy, (PowerlessRelativeClassFunctionAbsolute.ordered_l x y p).mp hxy⟩
  exact (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) P').mpr
    (envelope_l ((PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) X').mp hX)
      ((PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) Y').mp hY) hRead)

include hBase in
/-- 整张关系图的同一母界；不要求总性，因而也覆盖部分图。 -/
theorem relation_l {X Y R : SecondOrderQuotient.type_l hℳ}
    (hX : PowerlessHereditaryClass.member_l hℳ B X)
    (hY : PowerlessHereditaryClass.member_l hℳ B Y)
    (hR : PowerlessRelativeClassCorrespondence.member_l hℳ B R)
    (hClean : ∀ p, ε p R → ∃ x y, ε x X ∧ ε y Y ∧ SecondOrderPairObjects.ordered_l hℳ x y p) :
    PowerlessHereditaryClass.member_l hℳ B R := by
  obtain ⟨P, hP⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (Δ := []) .truth Env.empty X Y
  have hRead : ∀ p, ε p P ↔ ∃ x y, ε x X ∧ ε y Y ∧ SecondOrderPairObjects.ordered_l hℳ x y p := by
    simpa only [Formula.satisfies, true_and] using hP
  exact PowerlessHereditarySubset.member_l hℳ hBase (member_l (hBase := hBase) hX hY hRead) hR
    (fun p hp => (hRead p).mpr (hClean p hp))

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def product_m {Γ Δ : SortContext ℒ} (X Y P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up P))
    (PowerlessRelativeClassProduct.body_m (up X) (up Y) (.bvar .here))

def clean_m {Γ Δ : SortContext ℒ} (X Y R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up R))
    (PowerlessRelativeClassProduct.body_m (up X) (up Y) (.bvar .here))

def schema_m {Δ : SortContext ℒ} (B X Y P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessHereditaryClass.formula_m B X) <|
      .imp (PowerlessHereditaryClass.formula_m B Y) <|
        .imp (product_m X Y P) (PowerlessHereditaryClass.formula_m B P)

def relation_schema_m {Δ : SortContext ℒ} (B X Y R : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessHereditaryClass.formula_m B X) <|
      .imp (PowerlessHereditaryClass.formula_m B Y) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B R) <|
          .imp (clean_m X Y R) (PowerlessHereditaryClass.formula_m B R)

theorem models_l (h𝒩₀ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B X Y P : Term ℒ [] Δ .set) :
    (Metatheory.Formula.forall_close (schema_m B X Y P)).TrueIn (SecondOrderQuotient.structure_l h𝒩₀) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩₀
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, product_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, PowerlessHereditaryClass.formula_l K,
    PowerlessRelativeClassProduct.body_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  intro η hBase hX hY hP
  exact member_l (hBase := hBase) hX hY hP

theorem relation_models_l (h𝒩₀ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B X Y R : Term ℒ [] Δ .set) :
    (Metatheory.Formula.forall_close (relation_schema_m B X Y R)).TrueIn
      (SecondOrderQuotient.structure_l h𝒩₀) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩₀
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [relation_schema_m, clean_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, PowerlessHereditaryClass.formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, PowerlessRelativeClassProduct.body_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hX hY hR hClean
  exact relation_l (hBase := hBase) hX hY hR hClean

theorem derives_m {Δ : SortContext ℒ} (B X Y P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close (schema_m B X Y P))) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩₀ => models_l h𝒩₀ B X Y P)

theorem relation_derives_m {Δ : SortContext ℒ} (B X Y R : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close (relation_schema_m B X Y R))) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩₀ => relation_models_l h𝒩₀ B X Y R)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryProduct
