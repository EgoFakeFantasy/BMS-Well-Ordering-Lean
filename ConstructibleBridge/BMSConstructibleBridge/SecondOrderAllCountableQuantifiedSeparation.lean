import BMSConstructibleBridge.SecondOrderAllCountableSourceCollection
import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation

/-! # 全类可数分支中的单步量词分离

先用已证的实际源 Collection 对任意存在请求取得类内见证界。
当矩阵为 Δ₀ 时，有界存在式仍为 Δ₀，因而得到实际类子模型的
存在量词分离；全称情形通过母集内补集处理。这不是完整 Separation。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableQuantifiedSeparation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l)
open SecondOrderCanonicalLevelDerives (guard_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.type_l PowerlessRelativeClassStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

def exists_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] (.set :: Δ) :=
  .existsE .set φ.abstractFreeTop

def forall_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] (.set :: Δ) :=
  .forallE .set φ.abstractFreeTop

theorem exists_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (x : carrier_l 𝒩) :
    (exists_m φ).satisfies (η.pushFree x) ↔ ∃ y, φ.satisfies ((η.pushFree x).pushFree y) := by
  simp only [exists_m, Formula.satisfies, Formula.satisfies_abstractFreeTop]

theorem forall_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (x : carrier_l 𝒩) :
    (forall_m φ).satisfies (η.pushFree x) ↔ ∀ y, φ.satisfies ((η.pushFree x).pushFree y) := by
  simp only [forall_m, Formula.satisfies, Formula.satisfies_abstractFreeTop]

/-- 无见证时返回输入本身；只在 Prop 内使用经典逻辑。 -/
private def totalized_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  .disj φ (.conj (.neg ((exists_m φ).weakenFree SetTheory.SetSort.set))
    (.equal (.fvar .here) (.fvar (.there .here))))

private theorem totalized_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (x y : carrier_l 𝒩) :
    (totalized_m φ).satisfies ((η.pushFree x).pushFree y) ↔
      φ.satisfies ((η.pushFree x).pushFree y) ∨
        (¬(∃ z, φ.satisfies ((η.pushFree x).pushFree z)) ∧ y = x) := by
  simp only [totalized_m, Formula.satisfies, Formula.satisfies_weakenFree, Term.eval,
    exists_formula_l]
  rfl

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set] (.set :: .set :: Δ)
  | _, .here => .bvar .here
  | _, .there .here => .fvar .here
  | _, .there (.there v) => .fvar (.there (.there v))

private def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [.set] (.set :: .set :: Δ) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) [.set] (.set :: .set :: Δ) from
    .map (fun v => nomatch v) insert_m)

private def bounded_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  membershipLevyBound.boundedExists (.fvar (.there .here)) (body_m φ)

private theorem bounded_delta_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) : Formula.IsDelta0 membershipLevyBound (bounded_m φ) := by
  apply Formula.IsDelta0.bounded_exists
  exact Formula.IsDelta0.substituteMapped
    (show VariableSubstitution ℒ [] [.set] (.set :: .set :: Δ) from fun v => nomatch v) insert_m hφ

private theorem bounded_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (C x : carrier_l 𝒩) :
    (bounded_m φ).satisfies ((η.pushFree C).pushFree x) ↔
      ∃ y, member_l 𝒩 y C ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  have hBody (y : carrier_l 𝒩) :
      (body_m φ).satisfies (((η.pushFree C).pushFree x).pushBound y) ↔
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
  simp only [bounded_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, Arguments.eval, Term.eval, Term.eval_weakenBound, hBody]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  {t₁ t₂ t₃ Pair Valid P₀ S : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "CType" => PowerlessRelativeClassStructure.type_l hℳ B

variable (K : source_coding_l hℳ)
  (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
  (hGuard : guard_l B P₀)
  (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
  (hAll : ∀ a, SetTheory.Structure.IsOrdinal
    (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) a →
    PowerlessRelativeOrdinalCutoff.countable_l B K.omega a)

include K hCoding hGuard hS hAll in
/-- 任意矩阵的存在量词可在指定母集上限制到一个实际类内集合。 -/
theorem bound_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env ClassModel [] Δ) (A : CType) : ∃ C : CType, ∀ x : CType, mem_l hℳ x.val A.val →
      ((∃ y : CType, φ.satisfies ((η.pushFree x).pushFree y)) ↔
        ∃ y : CType, mem_l hℳ y.val C.val ∧ φ.satisfies ((η.pushFree x).pushFree y)) := by
  classical
  have hSome (x : CType) (_ : mem_l hℳ x.val A.val) :
      ∃ y : CType, (totalized_m φ).satisfies ((η.pushFree x).pushFree y) := by
    by_cases h : ∃ y : CType, φ.satisfies ((η.pushFree x).pushFree y)
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, (totalized_formula_l φ η x y).mpr (.inl hy)⟩
    · exact ⟨x, (totalized_formula_l φ η x x).mpr (.inr ⟨h, rfl⟩)⟩
  obtain ⟨C, hC⟩ := SecondOrderAllCountableSourceCollection.collection_l
    K hCoding hGuard hS hAll (totalized_m φ) η A hSome
  refine ⟨C, fun x hx => ⟨?_, fun ⟨y, _, hy⟩ => ⟨y, hy⟩⟩⟩
  intro h
  obtain ⟨y, hyC, hy⟩ := hC x hx
  refine ⟨y, hyC, ?_⟩
  rcases (totalized_formula_l φ η x y).mp hy with hy | hy
  · exact hy
  · exact False.elim (hy.1 h)

include K hCoding hGuard hS hAll in
theorem exists_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env ClassModel [] Δ) (A : CType) :
    ∃ Y : CType, ∀ x : CType, mem_l hℳ x.val Y.val ↔ mem_l hℳ x.val A.val ∧
      ∃ y : CType, φ.satisfies ((η.pushFree x).pushFree y) := by
  obtain ⟨C, hC⟩ := bound_l K hCoding hGuard hS hAll φ η A
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassDeltaSeparation.exists_l (bounded_delta_l hφ) (η.pushFree C) A
  refine ⟨Y, fun x => (hY x).trans ?_⟩
  apply and_congr_right
  intro hx
  exact (bounded_formula_l φ η C x).trans (hC x hx).symm

include K hCoding hGuard hS hAll in
theorem forall_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env ClassModel [] Δ) (A : CType) :
    ∃ Y : CType, ∀ x : CType, mem_l hℳ x.val Y.val ↔ mem_l hℳ x.val A.val ∧
      ∀ y : CType, φ.satisfies ((η.pushFree x).pushFree y) := by
  classical
  obtain ⟨C, hC⟩ := exists_l K hCoding hGuard hS hAll (.neg hφ) η A
  let ξ : Env ClassModel [] [.set] := (Env.empty).pushFree C
  let ψ : Formula ℒ [] [.set, .set] := .neg (SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there .here)))
  have hψ : Formula.IsDelta0 membershipLevyBound ψ := .neg (.rel _ _)
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassDeltaSeparation.exists_l hψ ξ A
  refine ⟨Y, fun x => (hY x).trans ?_⟩
  change (mem_l hℳ x.val A.val ∧ ¬mem_l hℳ x.val C.val) ↔ _
  apply and_congr_right
  intro hx
  rw [hC x]
  simp only [hx, true_and, Formula.satisfies, not_exists, not_not]

#print axioms bound_l
#print axioms exists_l
#print axioms forall_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableQuantifiedSeparation
