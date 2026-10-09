import BMSConstructibleBridge.PowerlessHereditaryRealRequest
import BMSConstructibleBridge.PowerlessHereditaryClassInternals

/-! # 同一带根实数请求的实际 Class 内公式

纯隶属 ℒ，原 Z₂ 背景。包络改用 Class 内部公式，码的图／根正文
保持同一有界 AST。通过传递类的有界绝对性和实际枚举绝对性，证明
任意满足请求的原码双向对应，而非只核对某个构造出来的码。

这只是后续统一遗传对象见证族的原请求接线；尚未完成 Collection
或固定高度 BMS 良序对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealRequestIntrinsic

open Logic FirstOrder StabilityFrame ThirdOrderSemantics
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def reading_m {Γ Δ : SortContext ℒ} (ω e o S X V T f r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessHereditaryRealRequest.real_m ω V) <|
    .conj (SecondOrderObjectSyntax.member_m r ω) <|
      .conj (PowerlessValueBounded.formula_m f r X) <|
        .conj (PowerlessHereditaryRealRequest.graph_m ω e S V T f)
          (PowerlessHereditaryRealRequest.root_m ω e o S V r)

theorem reading_delta_m {Γ Δ : SortContext ℒ} (ω e o S X V T f r : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (reading_m ω e o S X V T f r) :=
  .conj (.bounded_forall _ (.rel _ _)) <|
    .conj (.rel _ _) <| .conj (PowerlessValueBounded.delta_l _ _ _) <|
      .conj (.bounded_forall _ (.bounded_forall _ (.iff
        (PowerlessRootedRealSyntax.edge_delta_m _ _ _ _ _ _)
        (PowerlessHereditaryGraphPresentation.edge_delta_m _ _ _ _))))
        (.bounded_forall _ (.iff (PowerlessRootedRealSyntax.row_delta_m _ _ _ _ _ _) (.equal _ _)))

def body_m {Γ Δ : SortContext ℒ} (ω e o S X V T f r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessHereditaryClassInternals.body_m X T f ω) (reading_m ω e o S X V T f r)

def formula_m {Γ Δ : SortContext ℒ} (ω e o S X V : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    body_m (up (up (up ω))) (up (up (up e))) (up (up (up o)))
      (up (up (up S))) (up (up (up X))) (up (up (up V)))
      (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B
local notation "ε" => mem_l hℳ

private theorem term_l {Γ Δ : SortContext ℒ} (η : Env 𝒩₀ Γ Δ) (t : Term ℒ Γ Δ .set) :
    t.eval (PowerlessRelativeClassRelativization.env_l η) = (t.eval η).val := by
  match t with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app f _ => nomatch f

theorem body_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒩₀ Γ Δ)
    (ω e o S X V T f r : Term ℒ Γ Δ .set) :
    (body_m ω e o S X V T f r).satisfies η ↔
      PowerlessHereditaryRealRequest.body_l B (ω.eval η).val (e.eval η).val (o.eval η).val
        (S.eval η).val (X.eval η).val (V.eval η).val (T.eval η).val (f.eval η).val (r.eval η).val := by
  have hEnvelope :
      (PowerlessHereditaryClassInternals.body_m X T f ω).satisfies η ↔
        PowerlessHereditaryClass.body_l hℳ B (X.eval η).val (T.eval η).val (f.eval η).val (ω.eval η).val := by
    simp only [PowerlessHereditaryClassInternals.body_m, Formula.satisfies,
      PowerlessHereditaryClassInternals.transitive_formula_l, ThirdOrderSemantics.omega_formula_l,
      ThirdOrderSemantics.map_formula_l, PowerlessHereditaryClassInternals.onto_formula_l,
      SecondOrderObjectSyntax.member_m, Arguments.eval]
    constructor
    · rintro ⟨hXT, hT, hω, hMap, hOnto⟩
      exact ⟨(T.eval η).property, (f.eval η).property, hXT,
        (PowerlessHereditaryClassInternals.transitive_l (hBase := hBase) (T.eval η)).mp hT,
        (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) (ω.eval η)).mp hω,
        (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) (f.eval η) (ω.eval η) (T.eval η)).mp hMap,
        (PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) (f.eval η) (ω.eval η) (T.eval η)).mp hOnto⟩
    · rintro ⟨_, _, hXT, hT, hω, hMap, hOnto⟩
      exact ⟨hXT,
        (PowerlessHereditaryClassInternals.transitive_l (hBase := hBase) (T.eval η)).mpr hT,
        (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) (ω.eval η)).mpr hω,
        (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) (f.eval η) (ω.eval η) (T.eval η)).mpr hMap,
        (PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) (f.eval η) (ω.eval η) (T.eval η)).mpr hOnto⟩
  have hReading :
      (reading_m ω e o S X V T f r).satisfies η ↔
        (∀ c, ε c (V.eval η).val → ε c (ω.eval η).val) ∧
          ε (r.eval η).val (ω.eval η).val ∧
            value_l (ℳ := 𝒱) (f.eval η).val (r.eval η).val (X.eval η).val ∧
              (∀ a, ε a (ω.eval η).val → ∀ b, ε b (ω.eval η).val →
                (PowerlessRootedRealSyntax.edge_l (𝒩 := 𝒱) (ω.eval η).val (e.eval η).val
                  (S.eval η).val (V.eval η).val a b ↔
                    PowerlessHereditaryGraphPresentation.edge_l (ℳ₀ := 𝒱) (T.eval η).val (f.eval η).val a b)) ∧
              (∀ a, ε a (ω.eval η).val →
                (PowerlessRootedRealSyntax.row_l (𝒩 := 𝒱) (ω.eval η).val (e.eval η).val
                  (S.eval η).val (V.eval η).val (o.eval η).val a ↔ a = (r.eval η).val)) := by
    refine (PowerlessRelativeClassBounded.formula_l (reading_delta_m ω e o S X V T f r) η).trans ?_
    simp only [reading_m, Formula.satisfies, PowerlessHereditaryRealRequest.real_formula_l,
      PowerlessValueBounded.formula_l, PowerlessHereditaryRealRequest.graph_formula_l,
      PowerlessHereditaryRealRequest.root_formula_l, SecondOrderObjectSyntax.member_m,
      Arguments.eval, term_l]
    rfl
  exact (and_congr hEnvelope hReading).trans
    ⟨fun h => ⟨h.1, (V.eval η).property, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

/-- 全部原请求码的双向对应，存在的图、根及枚举保持实际同一。 -/
theorem formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒩₀ Γ Δ)
    (ω e o S X V : Term ℒ Γ Δ .set) :
    (formula_m ω e o S X V).satisfies η ↔
      PowerlessHereditaryRealRequest.holds_l B (ω.eval η).val (e.eval η).val (o.eval η).val
        (S.eval η).val (X.eval η).val (V.eval η).val := by
  simp only [formula_m, Formula.satisfies, body_formula_l, up, Term.eval_weakenBound, Term.eval]
  change (∃ T f r : M, PowerlessHereditaryRealRequest.body_l B
    (ω.eval η).val (e.eval η).val (o.eval η).val (S.eval η).val (X.eval η).val (V.eval η).val
      T.val f.val r.val) ↔ _
  constructor
  · rintro ⟨T, f, r, h⟩
    exact ⟨T.val, f.val, r.val, h⟩
  · rintro ⟨T, f, r, h⟩
    exact ⟨⟨T, h.1.1⟩, ⟨f, h.1.2.1⟩,
      ⟨r, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase (ω.eval η).property h.2.2.2.1⟩, h⟩

#print axioms reading_delta_m
#print axioms body_formula_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealRequestIntrinsic
