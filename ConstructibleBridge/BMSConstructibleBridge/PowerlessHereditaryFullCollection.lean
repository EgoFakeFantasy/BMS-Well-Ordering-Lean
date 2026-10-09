import BMSConstructibleBridge.PowerlessHereditaryIntrinsicUniformRange
import BMSConstructibleBridge.PowerlessHereditaryEnumeration
import BMSConstructibleBridge.PowerlessHereditaryFullSeparation
import BMSConstructibleBridge.SecondOrderAllCountableSourceCollection

/-! # 实际遗传子模型的完整 Collection 模式

对象语言为纯隶属 ℒ，背景原 Z₂。原矩阵 φ 的全部参数和量词按实际
遗传子模型解释。非空母集以遗传域内逆枚举重排为 ω 请求，遗传收集
集合再覆盖原请求；空母集直接使用遗传 ω。没有全类可数分支假设。

每个外部公式实例沿原 SecondOrderAllCountableSourceCollection 的
Collection 句子回传原 Derives 核。实例模式不是内部统一真值断言。
此模块只完成 Collection 一项，不声明最终固定高度 BMS 良序完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFullCollection

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  structure_l type_l

universe u

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set] (.set :: .set :: .set :: .set :: Δ)
  | _, .here => .fvar .here
  | _, .there .here => .bvar .here
  | _, .there (.there v) => .fvar (.there (.there (.there (.there v))))

private def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [.set] (.set :: .set :: .set :: .set :: Δ) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) [.set] (.set :: .set :: .set :: .set :: Δ) from
    .map (fun v => nomatch v) insert_m)

/-- 输出、内部编号、实际遗传枚举、母集及原参数，全部保持原对象。 -/
def pullback_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: .set :: Δ) :=
  .existsE .set <| .conj
    (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there (.there (.there .here))))) <|
      .conj (PowerlessValueBounded.formula_m (.fvar (.there (.there .here)))
        (.fvar (.there .here)) (.bvar .here)) (body_m φ)

theorem pullback_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (A F n y : carrier_l 𝒩) :
    (pullback_m φ).satisfies (((((η.pushFree A).pushFree F).pushFree n).pushFree y)) ↔
      ∃ x, member_l 𝒩 x A ∧ value_l (ℳ := 𝒩) F n x ∧
        φ.satisfies ((η.pushFree x).pushFree y) := by
  have hBody (x : carrier_l 𝒩) : (body_m φ).satisfies
      (((((η.pushFree A).pushFree F).pushFree n).pushFree y).pushBound x) ↔
        φ.satisfies ((η.pushFree x).pushFree y) := by
    rw [body_m, Formula.satisfies_substitute]
    apply Iff.of_eq
    apply congrArg (fun ξ => φ.satisfies ξ)
    apply Env.ext
    · intro s v; nomatch v
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v <;> rfl
  simp only [pullback_m, Formula.satisfies, PowerlessValueBounded.formula_l,
    hBody, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₁" => structure_l hℳ B hBase
local notation "N" => type_l hℳ B

theorem exists_l (K : source_coding_l hℳ)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩₁ [] Δ) (A : N)
    (hSome : ∀ x : N, mem_l hℳ x.val A.val → ∃ y : N,
      φ.satisfies ((η.pushFree x).pushFree y)) :
    ∃ C : N, ∀ x : N, mem_l hℳ x.val A.val → ∃ y : N,
      mem_l hℳ y.val C.val ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  classical
  let O : N := ⟨K.omega, PowerlessHereditaryOmega.member_l hℳ hBase K.omega_spec⟩
  by_cases hA : ∃ d : N, mem_l hℳ d.val A.val
  · obtain ⟨F, hMap, hOnto⟩ :=
      PowerlessHereditaryEnumeration.exists_l (hBase := hBase) K O A K.omega_spec hA
    let ξ : Env 𝒩₁ [] (.set :: .set :: Δ) := (η.pushFree A).pushFree F
    have hSome' (n : N) (hn : mem_l hℳ n.val K.omega) : ∃ y : N,
        (pullback_m φ).satisfies ((ξ.pushFree n).pushFree y) := by
      obtain ⟨x, ⟨hxA, hnx⟩, _⟩ := hMap.2 n hn
      obtain ⟨y, hφ⟩ := hSome x hxA
      exact ⟨y, (pullback_formula_l φ η A F n y).mpr ⟨x, hxA, hnx, hφ⟩⟩
    obtain ⟨_U, _hU, _H, _hTrace, C, hCHC, _hRange, hCover⟩ :=
      PowerlessHereditaryIntrinsicUniformRange.hereditary_l K hB hNonempty (pullback_m φ) ξ hSome'
    refine ⟨⟨C, hCHC⟩, fun x hx => ?_⟩
    obtain ⟨n, hn, hnx⟩ := hOnto x hx
    obtain ⟨y, hyC, hPullback⟩ := hCover n hn
    obtain ⟨z, hzA, hnz, hφ⟩ := (pullback_formula_l φ η A F n y).mp hPullback
    obtain ⟨_, _, hUnique⟩ := hMap.2 n hn
    have hzx : z = x := (hUnique z ⟨hzA, hnz⟩).trans (hUnique x ⟨hx, hnx⟩).symm
    exact ⟨y, hyC, hzx ▸ hφ⟩
  · exact ⟨O, fun x hx => False.elim (hA ⟨x, hx⟩)⟩

theorem source_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    (SecondOrderAllCountableSourceCollection.source_sentence_m φ).TrueIn
      (structure_l hℳ B hBase) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  apply (SecondOrderAllCountableSourceCollection.schema_formula_l φ η).mpr
  exact fun A hSome => exists_l K hB hNonempty φ η A hSome

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close <|
    .imp (PowerlessHereditaryFullSeparation.base_m (.fvar .here))
      (PowerlessHereditaryRelativization.formula_m
        (SecondOrderAllCountableSourceCollection.source_sentence_m φ))

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hGuard
  obtain ⟨hBase, hB, hNonempty⟩ :=
    (PowerlessHereditaryFullSeparation.base_formula_l K η (.fvar .here)).mp hGuard
  have hEnv : η = (Env.empty (M := SecondOrderQuotient.structure_l h𝒩)).pushFree
      (sort := SetTheory.SetSort.set) (η.freeVal .here) := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; cases v with
      | here => rfl
      | there v => nomatch v
  rw [hEnv]
  exact (PowerlessHereditaryRelativization.sentence_l (hBase := hBase) K
    (SecondOrderAllCountableSourceCollection.source_sentence_m φ)).mpr
    (source_models_l h𝒩 (η.freeVal .here) hBase hB hNonempty φ)

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ)

#print axioms pullback_formula_l
#print axioms exists_l
#print axioms source_models_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFullCollection
