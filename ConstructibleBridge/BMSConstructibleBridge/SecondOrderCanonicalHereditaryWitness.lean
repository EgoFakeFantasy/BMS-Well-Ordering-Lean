import BMSConstructibleBridge.PowerlessHereditaryRealRequestDecode
import BMSConstructibleBridge.SecondOrderCanonicalRealWitness

/-! # 遗传见证的规范带根实数族

对实际纯请求逐内部自然数选择最小类内带根码，再用原二阶理解统一
为一张环境实数 H。每行码同时包含图和根；并未断言 H 属于相对类，
也没有将此中间结果冒充完整 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalHereditaryWitness

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open YesMetaZFC.Automation.PrefixQuantification (weaken_m weaken_l env_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

abbrev support_m : SortContext ℒ := [.set, .set, .set, .set, .set]

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set] (.set :: .set :: (support_m ++ Δ))
  | _, .here => .bvar .here
  | _, .there .here => .fvar (.there .here)
  | _, .there (.there v) => weaken_m (SetTheory.SetSort.set :: SetTheory.SetSort.set :: support_m) (.fvar v)

private def witness_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [.set] (.set :: .set :: (support_m ++ Δ)) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) [.set] (.set :: .set :: (support_m ++ Δ)) from
    .map (fun v => nomatch v) insert_m)

def formula_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: (support_m ++ Δ)) :=
  .existsE .set <|
    let B : Term ℒ [.set] (.set :: .set :: (support_m ++ Δ)) .set := .fvar (.there (.there .here))
    let ω := .fvar (.there (.there (.there .here)))
    let e := .fvar (.there (.there (.there (.there .here))))
    let o := .fvar (.there (.there (.there (.there (.there .here)))))
    let S := .fvar (.there (.there (.there (.there (.there (.there .here))))))
    .conj (PowerlessHereditaryClass.formula_m B (.bvar .here)) <|
      .conj (witness_m φ) (PowerlessHereditaryRealRequest.formula_m B ω e o S (.bvar .here) (.fvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def support_env_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ)
    (B ω e o S : SecondOrderQuotient.type_l hℳ) : Env 𝒱 [] (support_m ++ Δ) :=
  env_l η (.cons B (.cons ω (.cons e (.cons o (.cons S .nil)))))

private theorem witness_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B ω e o S x V X : SecondOrderQuotient.type_l hℳ) :
    (witness_m φ).satisfies ((((support_env_l η B ω e o S).pushFree x).pushFree V).pushBound X) ↔
      φ.satisfies ((η.pushFree x).pushFree X) := by
  rw [witness_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v =>
        exact weaken_l (η.pushBound X) (.cons V (.cons x (.cons B (.cons ω (.cons e (.cons o (.cons S .nil))))))) (.fvar v)

theorem formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B ω e o S x V : SecondOrderQuotient.type_l hℳ) :
    (formula_m φ).satisfies (((support_env_l η B ω e o S).pushFree x).pushFree V) ↔
      ∃ X, PowerlessHereditaryClass.member_l hℳ B X ∧ φ.satisfies ((η.pushFree x).pushFree X) ∧
        PowerlessHereditaryRealRequest.holds_l B ω e o S X V := by
  simp only [formula_m, Formula.satisfies, PowerlessHereditaryClass.formula_l K,
    PowerlessHereditaryRealRequest.formula_l K, Term.eval]
  change (∃ X, PowerlessHereditaryClass.member_l hℳ B X ∧
    (witness_m φ).satisfies ((((support_env_l η B ω e o S).pushFree x).pushFree V).pushBound X) ∧
    PowerlessHereditaryRealRequest.holds_l B ω e o S X V) ↔ _
  exact exists_congr (fun X => and_congr Iff.rfl (and_congr (witness_formula_l φ η B ω e o S x V X) Iff.rfl))

/-- 已有逐数遗传见证的实际请求获得统一图根码；输出 H 仍只在环境中。 -/
theorem family_l (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid B P₀ S : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : SecondOrderCanonicalLevelDerives.guard_l B P₀)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (hSome : ∀ x, mem_l hℳ x K.omega → ∃ X,
      PowerlessHereditaryClass.member_l hℳ B X ∧ φ.satisfies ((η.pushFree x).pushFree X)) :
    ∃ H : SecondOrderModel.set_l ℳ, ∀ n, ∃ V X,
      PowerlessHereditaryClass.member_l hℳ B X ∧
        φ.satisfies ((η.pushFree (numberCode_l K n).val).pushFree X) ∧
        PowerlessHereditaryRealRequest.holds_l B K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
          (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val S X V ∧
        ∀ m, SecondOrderPairing.relation_l H n m ↔ mem_l hℳ (numberCode_l K m).val V := by
  let e := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
  let o := (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val
  let ξ := support_env_l η B K.omega e o S
  have hBase x hx y hy := hGuard.2.1 x y hx hy
  have hSome' (x : SecondOrderQuotient.type_l hℳ) (hx : mem_l hℳ x K.omega) :
      ∃ V, PowerlessRelativeClassCorrespondence.member_l hℳ B V ∧
      (formula_m φ).satisfies ((ξ.pushFree x).pushFree V) := by
    obtain ⟨X, hX, hφ⟩ := hSome x hx
    obtain ⟨V, hV⟩ := PowerlessHereditaryRealRequest.exists_l (hBase := hBase) K hS hX
    exact ⟨V, PowerlessHereditaryRealRequest.class_l hV,
      (formula_l K φ η B K.omega e o S x V).mpr ⟨X, hX, hφ, hV⟩⟩
  have hReal (x V : SecondOrderQuotient.type_l hℳ) (_ : mem_l hℳ x K.omega)
      (hV : (formula_m φ).satisfies ((ξ.pushFree x).pushFree V)) :
      ∀ c, mem_l hℳ c V → mem_l hℳ c K.omega := by
    obtain ⟨_, _, _, hRequest⟩ := (formula_l K φ η B K.omega e o S x V).mp hV
    exact PowerlessHereditaryRealRequest.real_l hRequest
  obtain ⟨H, hH⟩ := SecondOrderCanonicalRealWitness.real_family_l K hCoding hGuard (formula_m φ) ξ hSome' hReal
  refine ⟨H, fun n => ?_⟩
  obtain ⟨V, ⟨hMin, _, hRead⟩, _⟩ := hH n
  obtain ⟨X, hX, hφ, hRequest⟩ := (formula_l K φ η B K.omega e o S (numberCode_l K n).val V).mp hMin.2.1
  exact ⟨V, X, hX, hφ, hRequest, hRead⟩

#print axioms formula_l
#print axioms family_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalHereditaryWitness
