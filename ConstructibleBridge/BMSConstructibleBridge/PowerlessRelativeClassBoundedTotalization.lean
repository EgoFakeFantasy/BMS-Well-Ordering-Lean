import BMSConstructibleBridge.PowerlessRelativeClassFunctionGraph
import BMSConstructibleBridge.PowerlessBMSQuotientSubsetImageDerives

/-! # 有界部分关系的同一 Class 总化图

原背景为 Z₂，正文为纯隶属 Δ₀ 公式。真实输出仅限制到指定 Class 母域 W；
仅在 W 中不存在输出时取指定 e∈W。所有合法输出保持不变，不能用缺省值
覆盖原输出，也不要求作为参数的原图属于 W。

这是实际程序像装配的语义中间工具，附有纯 AST、复杂度与全 raw 读数。
调用者仍须提供实际部分关系的单值性；没有预供总化图、可数性或 Collection，
不在 Type 中抽取见证函数。本模块不是最终固定高度 BMS 对象闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBoundedTotalization

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev free₂ {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) :=
  (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set

private def insert_m {Γ Δ : SortContext ℒ}
    (x y : Term ℒ Γ (.set :: .set :: Δ) .set) :
    VariableSubstitution ℒ (.set :: .set :: Δ) Γ (.set :: .set :: Δ)
  | _, .here => y
  | _, .there .here => x
  | _, .there (.there v) => .fvar (.there (.there v))

private def read_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (x y : Term ℒ Γ (.set :: .set :: Δ) .set) : Formula ℒ Γ (.set :: .set :: Δ) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) Γ (.set :: .set :: Δ) from
    .map (fun v => nomatch v) (insert_m x y))

private theorem read_delta_l {Γ Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (x y : Term ℒ Γ (.set :: .set :: Δ) .set) :
    Formula.IsDelta0 membershipLevyBound (read_m φ x y) := by
  unfold read_m
  exact Formula.IsDelta0.substituteMapped
    (boundSubstitution := fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (freeSubstitution := _) hφ

private def suffix_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ (.set :: .set :: Δ)) : Env 𝒩 [] Δ :=
  ⟨Assignment.empty, fun {_} v => η.freeVal (.there (.there v))⟩

private theorem suffix_bound_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ (.set :: .set :: Δ)) (x : carrier_l 𝒩) :
    suffix_l (η.pushBound x) = suffix_l η := rfl

private theorem suffix_pair_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 [] Δ) (x y : carrier_l 𝒩) : suffix_l ((η.pushFree y).pushFree x) = η := by
  apply Env.ext
  · intro _ v; nomatch v
  · intro _ v; rfl

private theorem read_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ (.set :: .set :: Δ))
    (x y : Term ℒ Γ (.set :: .set :: Δ) .set) :
    (read_m φ x y).satisfies η ↔
      φ.satisfies (((suffix_l η).pushFree (x.eval η)).pushFree (y.eval η)) := by
  refine (Formula.satisfies_substitute η _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext
  · intro _ v; nomatch v
  · intro _ v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

def graph_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (W e : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: .set :: Δ) :=
  let x : Term ℒ [] (.set :: .set :: Δ) .set := .fvar .here
  let y : Term ℒ [] (.set :: .set :: Δ) .set := .fvar (.there .here)
  .disj (read_m φ x y) <| .conj
    (.neg (membershipLevyBound.boundedExists (free₂ W) (read_m φ (up x) (.bvar .here))))
    (.equal y (free₂ e))

theorem delta_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (W e : Term ℒ [] Δ .set) :
    Formula.IsDelta0 membershipLevyBound (graph_m φ W e) :=
  .disj (read_delta_l hφ _ _) (.conj (.neg (.bounded_exists _ (read_delta_l hφ _ _))) (.equal _ _))

def default_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (R : carrier_l 𝒩 → carrier_l 𝒩 → Prop) (W e x y : carrier_l 𝒩) : Prop :=
  R x y ∨ ((¬∃ z, member_l 𝒩 z W ∧ R x z) ∧ y = e)

theorem graph_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (W e : Term ℒ [] Δ .set)
    (η : Env 𝒩 [] Δ) (x y : carrier_l 𝒩) :
    (graph_m φ W e).satisfies ((η.pushFree y).pushFree x) ↔
      default_l (fun s Z => φ.satisfies ((η.pushFree s).pushFree Z)) (W.eval η) (e.eval η) x y := by
  simp only [graph_m, default_l, Formula.satisfies, read_formula_l,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    suffix_bound_l, suffix_pair_l, Arguments.eval, free₂, up,
    Term.eval_weakenBound, Term.eval_weakenFree, Term.eval,
    Env.pushFree_here, Env.pushFree_there, Env.pushBound_bound_here]
  rfl

private theorem unique_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {R : carrier_l 𝒩 → carrier_l 𝒩 → Prop} {W e x y z : carrier_l 𝒩}
    (hUnique : ∀ Y Z, member_l 𝒩 Y W → member_l 𝒩 Z W → R x Y → R x Z → Y = Z)
    (hyW : member_l 𝒩 y W) (hzW : member_l 𝒩 z W)
    (hy : default_l R W e x y) (hz : default_l R W e x z) : y = z := by
  rcases hy with hy | ⟨hy, rfl⟩
  · rcases hz with hz | ⟨hz, rfl⟩
    · exact hUnique _ _ hyW hzW hy hz
    · exact (hz ⟨y, hyW, hy⟩).elim
  · rcases hz with hz | ⟨_hz, rfl⟩
    · exact (hy ⟨z, hzW, hz⟩).elim
    · rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

/-- 由实际部分关系构造总图，全 raw 读数及合法输出一并保留。 -/
theorem exists_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env 𝒞 [] Δ)
    (W e : Term ℒ [] Δ .set) (he : mem_l hℳ (e.eval η).val (W.eval η).val)
    (hUnique : ∀ x y z : Raw, mem_l hℳ x (W.eval η).val →
      mem_l hℳ y (W.eval η).val → mem_l hℳ z (W.eval η).val →
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree x).pushFree y) →
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree x).pushFree z) → y = z) :
    ∃ F : type_l hℳ B, map_l (ℳ := 𝒱) F.val (W.eval η).val (W.eval η).val ∧
      ∀ x y : Raw, value_l (ℳ := 𝒱) F.val x y ↔
        mem_l hℳ x (W.eval η).val ∧ mem_l hℳ y (W.eval η).val ∧
          default_l (fun s Z => φ.satisfies
            (((PowerlessRelativeClassRelativization.env_l η).pushFree s).pushFree Z))
              (W.eval η).val (e.eval η).val x y := by
  classical
  let ψ := graph_m φ W e
  have hψ := delta_l hφ W e
  have hTerm (t : Term ℒ [] Δ .set) :
      t.eval (PowerlessRelativeClassRelativization.env_l η) = (t.eval η).val := by
    simpa only [Term.eval_weakenFree] using PowerlessRelativeClassRelativization.term_l η t
  have hRead (x y : Raw) : ψ.satisfies
      (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x) ↔
        default_l (fun s Z => φ.satisfies
          (((PowerlessRelativeClassRelativization.env_l η).pushFree s).pushFree Z))
            (W.eval η).val (e.eval η).val x y := by
    simpa only [hTerm] using
      graph_formula_l φ W e (PowerlessRelativeClassRelativization.env_l η) x y
  have hTotal (x : type_l hℳ B) (hx : mem_l hℳ x.val (W.eval η).val) :
      ∃! y : type_l hℳ B, mem_l hℳ y.val (W.eval η).val ∧ ψ.satisfies ((η.pushFree y).pushFree x) := by
    have hRaw : ∃ y : Raw, mem_l hℳ y (W.eval η).val ∧
        default_l (fun s Z => φ.satisfies
          (((PowerlessRelativeClassRelativization.env_l η).pushFree s).pushFree Z))
            (W.eval η).val (e.eval η).val x.val y := by
      by_cases h : ∃ y : Raw, mem_l hℳ y (W.eval η).val ∧ φ.satisfies
          (((PowerlessRelativeClassRelativization.env_l η).pushFree x.val).pushFree y)
      · obtain ⟨y, hy, hxy⟩ := h
        exact ⟨y, hy, Or.inl hxy⟩
      · exact ⟨(e.eval η).val, he, Or.inr ⟨h, rfl⟩⟩
    obtain ⟨y, hy, hxy⟩ := hRaw
    let y' : type_l hℳ B := ⟨y,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase (W.eval η).property hy⟩
    have hEnv (z : type_l hℳ B) :
        PowerlessRelativeClassRelativization.env_l ((η.pushFree z).pushFree x) =
          ((PowerlessRelativeClassRelativization.env_l η).pushFree
            (sort := SetTheory.SetSort.set) z.val).pushFree (sort := SetTheory.SetSort.set) x.val := by
      apply Env.ext
      · intro _ v; nomatch v
      · intro k v
        cases k
        cases v with
        | here => rfl
        | there v => cases v <;> rfl
    have hAbsolute (z : type_l hℳ B) :=
      PowerlessRelativeClassBounded.formula_l hψ ((η.pushFree z).pushFree x)
    have hClassRead (z : type_l hℳ B) : ψ.satisfies ((η.pushFree z).pushFree x) ↔
        default_l (fun s Z => φ.satisfies
          (((PowerlessRelativeClassRelativization.env_l η).pushFree s).pushFree Z))
            (W.eval η).val (e.eval η).val x.val z.val := by
      have h := hAbsolute z
      rw [hEnv] at h
      exact h.trans (hRead x.val z.val)
    refine ⟨y', ⟨hy, (hClassRead y').mpr hxy⟩, ?_⟩
    intro z hz
    exact Subtype.ext (unique_l (𝒩 := 𝒱)
      (R := fun s Z => φ.satisfies
        (((PowerlessRelativeClassRelativization.env_l η).pushFree s).pushFree Z))
      (W := (W.eval η).val) (e := (e.eval η).val) (x := x.val)
      (fun Y Z => hUnique x.val Y Z hx) hz.1 hy ((hClassRead z).mp hz.2) hxy)
  obtain ⟨F, hF, hValue⟩ := PowerlessRelativeClassFunctionGraph.exists_l hψ η (W.eval η) (W.eval η) hTotal
  exact ⟨F, hF, fun x y => (hValue x y).trans
    (and_congr Iff.rfl (and_congr Iff.rfl (hRead x y)))⟩

#print axioms delta_l
#print axioms graph_formula_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBoundedTotalization
