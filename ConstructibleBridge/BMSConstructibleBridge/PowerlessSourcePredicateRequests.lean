import BMSConstructibleBridge.PowerlessSourceRequests
import BMSConstructibleBridge.PowerlessSourceTuplePairing
import BMSConstructibleBridge.PowerlessSourceInclusion

/-!
# 谓词有限请求闭包与原公式反射

仍使用原 requests_m .truth 的实际子公式请求。输入列和输出见证由
谓词 P 限定，原见证遍历环境结构，不要求 P 在结构中有集合载体。
存在分支捕获原矩阵见证，全称分支捕获否定矩阵反例。
实际成员包含出口直接比较 MemberI 与 MemberW，不增加 I∈W 前提。
这些语义中间工具不替代主路线最终的对象 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourcePredicateRequests

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 输入列与输出限制在同一谓词中，待捕获的原见证遍历环境结构。 -/
def closed_l {Δ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Δ))))
    (η : Env ℳ [] Δ) (P : carrier_l ℳ → Prop) : Prop :=
  ∀ n φ, Sigma.mk n φ ∈ Φ → ∀ v, PowerlessSourceTuplePairing.bounded_l P n v →
    (∃ y, φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y)) →
      ∃ y, P y ∧ φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y)

theorem subset_l {Δ : SortContext ℒ}
    {Φ Ψ : List (Σ n : Nat, Formula ℒ []
      (.set :: (List.replicate (α := (ℒ).SortSymbol) n .set ++ Δ)))}
    {η : Env ℳ [] Δ} {P : carrier_l ℳ → Prop}
    (h : ∀ p ∈ Ψ, p ∈ Φ) (hΦ : closed_l Φ η P) : closed_l Ψ η P :=
  fun n φ hφ => hΦ n φ (h _ hφ)

/-- 真域相对化保持原公式真值，不建立另一套满足谓词。 -/
theorem truth_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (η : Env ℳ Γ Δ) :
    (PowerlessSourceClass.form_m .truth φ).satisfies η ↔ φ.satisfies η := by
  match φ with
  | .falsum | .truth | .rel _ _ | .equal _ _ => exact Iff.rfl
  | .neg φ => exact not_congr (truth_formula_l φ η)
  | .conj φ ψ => exact and_congr (truth_formula_l φ η) (truth_formula_l ψ η)
  | .disj φ ψ => exact or_congr (truth_formula_l φ η) (truth_formula_l ψ η)
  | .imp φ ψ => exact imp_congr (truth_formula_l φ η) (truth_formula_l ψ η)
  | .iff φ ψ => exact iff_congr (truth_formula_l φ η) (truth_formula_l ψ η)
  | .existsE .set φ =>
    change (∃ x, True ∧ (PowerlessSourceClass.form_m .truth φ).satisfies (η.pushBound x)) ↔
      ∃ x, φ.satisfies (η.pushBound x)
    simp only [true_and]
    exact exists_congr fun x => truth_formula_l φ (η.pushBound x)
  | .forallE .set φ =>
    change (∀ x, True → (PowerlessSourceClass.form_m .truth φ).satisfies (η.pushBound x)) ↔
      ∀ x, φ.satisfies (η.pushBound x)
    simp only [true_imp_iff]
    exact forall_congr' fun x => truth_formula_l φ (η.pushBound x)

/-- 原绑定环境的实际值列逐项落入给定谓词。 -/
theorem bounded_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (P : carrier_l ℳ → Prop)
    (hη : ∀ v : Variable Γ .set, P (η.boundVal v)) :
    PowerlessSourceTuplePairing.bounded_l P Γ.length (PowerlessSourceOpening.values_l η) := by
  cases Γ with
  | nil => trivial
  | cons s Γ =>
    cases s
    exact ⟨hη .here, bounded_l (PowerlessSourceOpening.tail_l η) P
      (fun v => hη (.there v))⟩

/-- 读取真域请求的原矩阵见证，输出仍属于同一谓词。 -/
theorem witness_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: Γ) Δ)
    (η : Env ℳ Γ Δ) (P : carrier_l ℳ → Prop)
    {Φ : List (Σ n : Nat, Formula ℒ []
      (.set :: (List.replicate (α := (ℒ).SortSymbol) n .set ++ Δ)))}
    (hφ : PowerlessSourceRequests.entry_m .truth φ ∈ Φ)
    (hη : ∀ v : Variable Γ .set, P (η.boundVal v))
    (h : closed_l Φ (PowerlessSourceClass.free_l η) P)
    (h₀ : ∃ y, φ.satisfies (η.pushBound y)) :
    ∃ y, P y ∧ φ.satisfies (η.pushBound y) := by
  obtain ⟨y, hy⟩ := h₀
  obtain ⟨z, hz, h₁⟩ := h Γ.length _ hφ (PowerlessSourceOpening.values_l η)
    (bounded_l η P hη)
    ⟨y, (PowerlessSourceOpening.witness_l (PowerlessSourceClass.form_m .truth φ) η y).mpr
      ((truth_formula_l φ (η.pushBound y)).mpr hy)⟩
  exact ⟨z, hz, (truth_formula_l φ (η.pushBound z)).mp
    ((PowerlessSourceOpening.witness_l (PowerlessSourceClass.form_m .truth φ) η z).mp h₁)⟩

/-- 对全部实际子公式请求闭合的谓词子结构反射原公式。 -/
theorem formula_l {P : carrier_l ℳ → Prop} {hP : ∃ x, P x} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ Γ Δ) (η : Env (PowerlessSourceClass.structure_l P hP) Γ Δ)
    (h : closed_l (PowerlessSourceRequests.requests_m .truth φ)
      (PowerlessSourceClass.free_l (PowerlessSourceClass.env_l η)) P) :
    φ.satisfies (PowerlessSourceClass.env_l η) ↔ φ.satisfies η := by
  classical
  match φ with
  | .falsum => exact Iff.rfl
  | .truth => exact Iff.rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
    change member_l ℳ (s.eval (PowerlessSourceClass.env_l η)) (t.eval (PowerlessSourceClass.env_l η)) ↔
      member_l ℳ (s.eval η).val (t.eval η).val
    rw [PowerlessSourceClass.term_l, PowerlessSourceClass.term_l]
  | .equal (sort := .set) s t =>
    change s.eval (PowerlessSourceClass.env_l η) = t.eval (PowerlessSourceClass.env_l η) ↔
      s.eval η = t.eval η
    rw [PowerlessSourceClass.term_l, PowerlessSourceClass.term_l]
    exact ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
  | .neg φ => exact not_congr (formula_l φ η h)
  | .conj φ ψ =>
    exact and_congr
      (formula_l φ η (subset_l (fun _ hφ => List.mem_append_left _ hφ) h))
      (formula_l ψ η (subset_l (fun _ hψ => List.mem_append_right _ hψ) h))
  | .disj φ ψ =>
    exact or_congr
      (formula_l φ η (subset_l (fun _ hφ => List.mem_append_left _ hφ) h))
      (formula_l ψ η (subset_l (fun _ hψ => List.mem_append_right _ hψ) h))
  | .imp φ ψ =>
    exact imp_congr
      (formula_l φ η (subset_l (fun _ hφ => List.mem_append_left _ hφ) h))
      (formula_l ψ η (subset_l (fun _ hψ => List.mem_append_right _ hψ) h))
  | .iff φ ψ =>
    exact iff_congr
      (formula_l φ η (subset_l (fun _ hφ => List.mem_append_left _ hφ) h))
      (formula_l ψ η (subset_l (fun _ hψ => List.mem_append_right _ hψ) h))
  | .existsE .set φ =>
    have h₀ := subset_l (Ψ := PowerlessSourceRequests.requests_m .truth φ)
      (fun _ hφ => List.mem_cons_of_mem _ hφ) h
    have h₁ (x : PowerlessSourceClass.type_l P) :
        φ.satisfies ((PowerlessSourceClass.env_l η).pushBound x.val) ↔
          φ.satisfies (η.pushBound x) := by
      rw [← PowerlessSourceClass.push_l]
      exact formula_l φ (η.pushBound x) h₀
    change (∃ x : carrier_l ℳ, φ.satisfies ((PowerlessSourceClass.env_l η).pushBound x)) ↔
      ∃ x : PowerlessSourceClass.type_l P, φ.satisfies (η.pushBound x)
    constructor
    · intro hφ
      obtain ⟨z, hz, hψ⟩ := witness_l φ (PowerlessSourceClass.env_l η) P
        List.mem_cons_self (fun v => (η.boundVal v).property) h hφ
      exact ⟨⟨z, hz⟩, (h₁ ⟨z, hz⟩).mp hψ⟩
    · rintro ⟨x, hφ⟩
      exact ⟨x.val, (h₁ x).mpr hφ⟩
  | .forallE .set φ =>
    have h₀ := subset_l (Ψ := PowerlessSourceRequests.requests_m .truth φ)
      (fun _ hφ => List.mem_cons_of_mem _ hφ) h
    have h₁ (x : PowerlessSourceClass.type_l P) :
        φ.satisfies ((PowerlessSourceClass.env_l η).pushBound x.val) ↔
          φ.satisfies (η.pushBound x) := by
      rw [← PowerlessSourceClass.push_l]
      exact formula_l φ (η.pushBound x) h₀
    change (∀ x : carrier_l ℳ, φ.satisfies ((PowerlessSourceClass.env_l η).pushBound x)) ↔
      ∀ x : PowerlessSourceClass.type_l P, φ.satisfies (η.pushBound x)
    constructor
    · intro hφ x
      exact (h₁ x).mp (hφ x.val)
    · intro hφ x
      by_contra hxφ
      obtain ⟨z, hz, hψ⟩ := witness_l (.neg φ) (PowerlessSourceClass.env_l η) P
        List.mem_cons_self (fun v => (η.boundVal v).property) h ⟨x, hxφ⟩
      exact hψ ((h₁ ⟨z, hz⟩).mpr (hφ ⟨z, hz⟩))

/-- 一个共同请求族同时反射给定外部有限列表的全部原公式。 -/
theorem family_l {P : carrier_l ℳ → Prop} {hP : ∃ x, P x} {Γ Δ : SortContext ℒ}
    (Φ : List (Formula ℒ Γ Δ)) (η : Env (PowerlessSourceClass.structure_l P hP) Γ Δ)
    (h : closed_l (Φ.flatMap (PowerlessSourceRequests.requests_m .truth))
      (PowerlessSourceClass.free_l (PowerlessSourceClass.env_l η)) P) :
    ∀ φ ∈ Φ, φ.satisfies (PowerlessSourceClass.env_l η) ↔ φ.satisfies η := by
  intro φ hφ
  exact formula_l φ η (subset_l (fun p hp => List.mem_flatMap.mpr ⟨φ, hφ, hp⟩) h)

/-- 实际成员包含的反射出口；I 只需包含于 W，不必是 W 的载体对象。 -/
theorem member_l {I W : carrier_l ℳ}
    {hI : ∃ x, ThirdOrderSemantics.member_l ℳ x I}
    {hW : ∃ x, ThirdOrderSemantics.member_l ℳ x W}
    (hIW : ThirdOrderSemantics.subset_l I W) {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ)
    (η : Env (PowerlessMemberStructure.structure_l I hI) Γ Δ)
    (h : closed_l (PowerlessSourceRequests.requests_m .truth φ)
      (PowerlessSourceClass.free_l (PowerlessSourceInclusion.env_l (hU := hW) hIW η))
      (fun x : PowerlessMemberStructure.type_l W => ThirdOrderSemantics.member_l ℳ x.val I)) :
    φ.satisfies (PowerlessSourceInclusion.env_l (hU := hW) hIW η) ↔ φ.satisfies η := by
  classical
  match φ with
  | .falsum => exact Iff.rfl
  | .truth => exact Iff.rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
    exact PowerlessSourceInclusion.member_l hIW η s t
  | .equal (sort := .set) s t => exact PowerlessSourceInclusion.equal_l hIW η s t
  | .neg φ => exact not_congr (member_l hIW φ η h)
  | .conj φ ψ =>
    exact and_congr
      (member_l hIW φ η (subset_l (fun _ hφ => List.mem_append_left _ hφ) h))
      (member_l hIW ψ η (subset_l (fun _ hψ => List.mem_append_right _ hψ) h))
  | .disj φ ψ =>
    exact or_congr
      (member_l hIW φ η (subset_l (fun _ hφ => List.mem_append_left _ hφ) h))
      (member_l hIW ψ η (subset_l (fun _ hψ => List.mem_append_right _ hψ) h))
  | .imp φ ψ =>
    exact imp_congr
      (member_l hIW φ η (subset_l (fun _ hφ => List.mem_append_left _ hφ) h))
      (member_l hIW ψ η (subset_l (fun _ hψ => List.mem_append_right _ hψ) h))
  | .iff φ ψ =>
    exact iff_congr
      (member_l hIW φ η (subset_l (fun _ hφ => List.mem_append_left _ hφ) h))
      (member_l hIW ψ η (subset_l (fun _ hψ => List.mem_append_right _ hψ) h))
  | .existsE .set φ =>
    have h₀ := subset_l (Ψ := PowerlessSourceRequests.requests_m .truth φ)
      (fun _ hφ => List.mem_cons_of_mem _ hφ) h
    have h₁ (x : PowerlessMemberStructure.type_l I) :
        φ.satisfies ((PowerlessSourceInclusion.env_l (hU := hW) hIW η).pushBound
          (PowerlessSourceInclusion.inclusion_l hIW x)) ↔ φ.satisfies (η.pushBound x) := by
      rw [← PowerlessSourceInclusion.push_l]
      exact member_l hIW φ (η.pushBound x) h₀
    change (∃ x : PowerlessMemberStructure.type_l W,
      φ.satisfies ((PowerlessSourceInclusion.env_l (hU := hW) hIW η).pushBound x)) ↔
        ∃ x : PowerlessMemberStructure.type_l I, φ.satisfies (η.pushBound x)
    constructor
    · intro hφ
      obtain ⟨z, hz, hψ⟩ := witness_l φ (PowerlessSourceInclusion.env_l (hU := hW) hIW η)
        (fun x : PowerlessMemberStructure.type_l W => ThirdOrderSemantics.member_l ℳ x.val I)
        List.mem_cons_self (fun v => (η.boundVal v).property) h hφ
      let z₀ : PowerlessMemberStructure.type_l I := ⟨z.val, hz⟩
      have hz₀ : PowerlessSourceInclusion.inclusion_l hIW z₀ = z := Subtype.ext rfl
      have h₂ := h₁ z₀
      rw [hz₀] at h₂
      exact ⟨z₀, h₂.mp hψ⟩
    · rintro ⟨x, hφ⟩
      exact ⟨PowerlessSourceInclusion.inclusion_l hIW x, (h₁ x).mpr hφ⟩
  | .forallE .set φ =>
    have h₀ := subset_l (Ψ := PowerlessSourceRequests.requests_m .truth φ)
      (fun _ hφ => List.mem_cons_of_mem _ hφ) h
    have h₁ (x : PowerlessMemberStructure.type_l I) :
        φ.satisfies ((PowerlessSourceInclusion.env_l (hU := hW) hIW η).pushBound
          (PowerlessSourceInclusion.inclusion_l hIW x)) ↔ φ.satisfies (η.pushBound x) := by
      rw [← PowerlessSourceInclusion.push_l]
      exact member_l hIW φ (η.pushBound x) h₀
    change (∀ x : PowerlessMemberStructure.type_l W,
      φ.satisfies ((PowerlessSourceInclusion.env_l (hU := hW) hIW η).pushBound x)) ↔
        ∀ x : PowerlessMemberStructure.type_l I, φ.satisfies (η.pushBound x)
    constructor
    · intro hφ x
      exact (h₁ x).mp (hφ (PowerlessSourceInclusion.inclusion_l hIW x))
    · intro hφ x
      by_contra hxφ
      obtain ⟨z, hz, hψ⟩ := witness_l (.neg φ) (PowerlessSourceInclusion.env_l (hU := hW) hIW η)
        (fun x : PowerlessMemberStructure.type_l W => ThirdOrderSemantics.member_l ℳ x.val I)
        List.mem_cons_self (fun v => (η.boundVal v).property) h ⟨x, hxφ⟩
      let z₀ : PowerlessMemberStructure.type_l I := ⟨z.val, hz⟩
      have hz₀ : PowerlessSourceInclusion.inclusion_l hIW z₀ = z := Subtype.ext rfl
      have h₂ := h₁ z₀
      rw [hz₀] at h₂
      exact hψ (h₂.mpr (hφ z₀))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourcePredicateRequests
