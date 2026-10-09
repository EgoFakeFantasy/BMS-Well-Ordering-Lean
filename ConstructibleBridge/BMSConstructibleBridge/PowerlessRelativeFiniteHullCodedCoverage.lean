import BMSConstructibleBridge.PowerlessCodedHistoryCoverageSyntax
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity
import YesMetaZFC.SetTheory.Definitional.Project.Derivation

/-! # 同一成员子域捕获完整局部前史包

对象语言为纯隶属 ℒ。三槽覆盖存在式与二十槽完整点矩阵同时反射；
原自由上下文不变，不把外部 W／Ω 塞进捕获参数。十七个见证在同一
I 中取得，再将同一赋值的完整矩阵读回 MemberW。该矩阵含无界量词，
不能套 Δ₀ 绝对性；本证明不要求 I 传递或外延，亦不选择 Type 数据。
这里是共同族构造的语义消费接口，源模型及最终 Z₂ 良序推导仍待闭合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullCodedCoverage

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

/-- 二十个绑定槽仍按原矩阵顺序排列，不改变已有捕获族。 -/
abbrev context_m : SortContext ℒ := List.replicate 20 .set

def variable_m (i : Fin 20) : Variable context_m .set :=
  SetTheory.Definitional.Project.fo_bound_variable i

/-- 全部槽绑定，依次为 G/Q/V/F/N/P/t₄/t₃/t₂/t₁/e/f/D/U/A/y/a/x/ω/B。 -/
def matrix_m (Δ : SortContext ℒ) :
    Formula ℒ [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] Δ :=
  PowerlessCodedHistoryCoverageSyntax.point_m
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar (.there (.there (.there (.there (.there .here))))))
    (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

/-- 参数只有已在同一 I 中的 B、ω、x；见证共用一个存在块。 -/
def exists_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set, .set] Δ :=
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  matrix_m Δ

/-- 完整赋值上的原点读数：B/ω/x/a/y 为 19/18/17/16/15 槽。 -/
def point_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 context_m Δ) : Prop :=
  let v := fun i : Fin 20 => η.boundVal (variable_m i)
  PowerlessCodedHistoryCoverageSyntax.point_l
    (v 19) (v 18) (v 17) (v 16) (v 15) (v 14) (v 13) (v 12) (v 11) (v 10)
    (v 9) (v 8) (v 7) (v 6) (v 5) (v 4) (v 3) (v 2) (v 1) (v 0)

theorem matrix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ}
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩))
    (η : Env 𝒩 context_m Δ) : (matrix_m Δ).satisfies η ↔ point_l η :=
  PowerlessCodedHistoryCoverageSyntax.point_formula_l hExt η
    (.bvar (variable_m 19)) (.bvar (variable_m 18)) (.bvar (variable_m 17))
    (.bvar (variable_m 16)) (.bvar (variable_m 15)) (.bvar (variable_m 14))
    (.bvar (variable_m 13)) (.bvar (variable_m 12)) (.bvar (variable_m 11))
    (.bvar (variable_m 10)) (.bvar (variable_m 9)) (.bvar (variable_m 8))
    (.bvar (variable_m 7)) (.bvar (variable_m 6)) (.bvar (variable_m 5))
    (.bvar (variable_m 4)) (.bvar (variable_m 3)) (.bvar (variable_m 2))
    (.bvar (variable_m 1)) (.bvar (variable_m 0))

/-- 固定见证块先在抽象结构上展开，不展开成员结构的数据构造。 -/
theorem witnesses_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 [.set, .set, .set] Δ) :
    (exists_m Δ).satisfies η ↔ ∃ a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : carrier_l 𝒩,
      (matrix_m Δ).satisfies (η |>.pushBound (sort := SetTheory.SetSort.set) a |>.pushBound (sort := SetTheory.SetSort.set) y |>.pushBound (sort := SetTheory.SetSort.set) A |>.pushBound (sort := SetTheory.SetSort.set) U |>.pushBound (sort := SetTheory.SetSort.set) D |>.pushBound (sort := SetTheory.SetSort.set) f |>.pushBound (sort := SetTheory.SetSort.set) e |>.pushBound (sort := SetTheory.SetSort.set) t₁ |>.pushBound (sort := SetTheory.SetSort.set) t₂ |>.pushBound (sort := SetTheory.SetSort.set) t₃ |>.pushBound (sort := SetTheory.SetSort.set) t₄ |>.pushBound (sort := SetTheory.SetSort.set) P |>.pushBound (sort := SetTheory.SetSort.set) N |>.pushBound (sort := SetTheory.SetSort.set) F |>.pushBound (sort := SetTheory.SetSort.set) V |>.pushBound (sort := SetTheory.SetSort.set) Q |>.pushBound (sort := SetTheory.SetSort.set) G) := Iff.rfl

theorem exists_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ}
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩))
    (η : Env 𝒩 [.set, .set, .set] Δ) :
    (exists_m Δ).satisfies η ↔ PowerlessCodedHistoryCoverageSyntax.statement_l
      (η.boundVal (.there (.there .here))) (η.boundVal (.there .here)) (η.boundVal .here) := by
  simp only [exists_m, Formula.satisfies, matrix_m,
    PowerlessCodedHistoryCoverageSyntax.point_formula_l hExt,
    PowerlessCodedHistoryCoverageSyntax.statement_l, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]

def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m Δ :=
  [Sigma.mk ([.set, .set, .set] : SortContext ℒ) (exists_m Δ),
    Sigma.mk ([.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] : SortContext ℒ) (matrix_m Δ)]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {I₀ W₀ : carrier_l ℳ} {hI : ∃ z, member_l ℳ z I₀}
  {hW : ∃ z, member_l ℳ z W₀}

local notation "𝒩₀" => structure_l (ℳ := ℳ) I₀ hI
local notation "𝒲" => structure_l (ℳ := ℳ) W₀ hW

/-- 先在抽象公式上读取成员元素性，避免展开完整无界覆盖包。 -/
private theorem entry_member_l {Γ Δ Ε : SortContext ℒ} (φ : Formula ℒ Γ Δ)
    (ζ : Env ℳ [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env 𝒩₀ [] Δ) (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hIW : subset_l (ℳ := ℳ) I₀ W₀) (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (h : (PowerlessRelativeFiniteElementarity.entry_m φ I W τ).satisfies ζ)
    (η : Env 𝒩₀ Γ Δ) (hFree : ∀ s (v : Variable Δ s), η.freeVal v = ν.freeVal v) :
    φ.satisfies (PowerlessSourceInclusion.env_l (hU := hW) hIW η) ↔ φ.satisfies η := by
  have hReflect := ((PowerlessRelativeFiniteElementarity.entry_formula_l
    φ ζ I W τ (PowerlessRelativization.env_l ν) hτ).mp h)
    (PowerlessRelativization.env_l η) (fun s v => by
      cases s
      exact congrArg Subtype.val (hFree .set v))
    (fun v => by rw [hI₀]; exact (η.boundVal v).property)
  rw [hI₀, hW₀] at hReflect
  exact ((PowerlessRelativization.formula_l φ
    (PowerlessSourceInclusion.env_l (hU := hW) hIW η)).symm.trans hReflect).trans
    (PowerlessRelativization.formula_l φ η)

/-- 保留 MemberI 内的原覆盖 AST 真值，供实际坍缩全公式运输。 -/
theorem capture_formula_l {Δ Ε : SortContext ℒ} (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env 𝒩₀ [] Δ) (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hIW : subset_l (ℳ := ℳ) I₀ W₀) (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒲))
    (B ω x : type_l (ℳ := ℳ) I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hCover : PowerlessCodedHistoryCoverageSyntax.statement_l (𝒩 := 𝒲)
      (PowerlessSourceInclusion.inclusion_l hIW B)
      (PowerlessSourceInclusion.inclusion_l hIW ω)
      (PowerlessSourceInclusion.inclusion_l hIW x)) :
    (exists_m Δ).satisfies (ν |>.pushBound (sort := SetTheory.SetSort.set) B
      |>.pushBound (sort := SetTheory.SetSort.set) ω |>.pushBound (sort := SetTheory.SetSort.set) x) := by
  change (PowerlessRelativeFiniteElementarity.entry_m (exists_m Δ) I W τ).satisfies ζ ∧
    (PowerlessRelativeFiniteElementarity.entry_m (matrix_m Δ) I W τ).satisfies ζ ∧ True at h
  let η : Env 𝒩₀ [.set, .set, .set] Δ := ν |>.pushBound (sort := SetTheory.SetSort.set) B
    |>.pushBound (sort := SetTheory.SetSort.set) ω |>.pushBound (sort := SetTheory.SetSort.set) x
  have hTruth := (exists_formula_l hExt
    (PowerlessSourceInclusion.env_l (hU := hW) hIW η)).mpr hCover
  exact (entry_member_l (exists_m Δ) ζ I W τ ν hτ hIW hI₀ hW₀
    h.1 η (fun _ _ => rfl)).mp hTruth

/-- 保留同一完整赋值在 MemberI 与 MemberW 中的 AST 真值，供逐槽运输。 -/
theorem capture_env_l {Δ Ε : SortContext ℒ} (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env 𝒩₀ [] Δ) (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hIW : subset_l (ℳ := ℳ) I₀ W₀) (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒲))
    (B ω x : type_l (ℳ := ℳ) I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hCover : PowerlessCodedHistoryCoverageSyntax.statement_l (𝒩 := 𝒲)
      (PowerlessSourceInclusion.inclusion_l hIW B)
      (PowerlessSourceInclusion.inclusion_l hIW ω)
      (PowerlessSourceInclusion.inclusion_l hIW x)) :
    ∃ η : Env 𝒩₀ context_m Δ,
      η.boundVal (variable_m 19) = B ∧ η.boundVal (variable_m 18) = ω ∧
      η.boundVal (variable_m 17) = x ∧ (matrix_m Δ).satisfies η ∧
      (matrix_m Δ).satisfies (PowerlessSourceInclusion.env_l (hU := hW) hIW η) := by
  let η₀ : Env 𝒩₀ [.set, .set, .set] Δ := ν |>.pushBound (sort := SetTheory.SetSort.set) B
    |>.pushBound (sort := SetTheory.SetSort.set) ω |>.pushBound (sort := SetTheory.SetSort.set) x
  have hInside := capture_formula_l ζ I W τ ν hτ hIW hI₀ hW₀ hExt B ω x h hCover
  change (PowerlessRelativeFiniteElementarity.entry_m (exists_m Δ) I W τ).satisfies ζ ∧
    (PowerlessRelativeFiniteElementarity.entry_m (matrix_m Δ) I W τ).satisfies ζ ∧ True at h
  obtain ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, hPoint⟩ :=
    (witnesses_l η₀).mp hInside
  let η : Env 𝒩₀ [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set,
      .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] Δ :=
    η₀ |>.pushBound (sort := SetTheory.SetSort.set) a
    |>.pushBound (sort := SetTheory.SetSort.set) y |>.pushBound (sort := SetTheory.SetSort.set) A
    |>.pushBound (sort := SetTheory.SetSort.set) U |>.pushBound (sort := SetTheory.SetSort.set) D
    |>.pushBound (sort := SetTheory.SetSort.set) f |>.pushBound (sort := SetTheory.SetSort.set) e
    |>.pushBound (sort := SetTheory.SetSort.set) t₁ |>.pushBound (sort := SetTheory.SetSort.set) t₂
    |>.pushBound (sort := SetTheory.SetSort.set) t₃ |>.pushBound (sort := SetTheory.SetSort.set) t₄
    |>.pushBound (sort := SetTheory.SetSort.set) P |>.pushBound (sort := SetTheory.SetSort.set) N
    |>.pushBound (sort := SetTheory.SetSort.set) F |>.pushBound (sort := SetTheory.SetSort.set) V
    |>.pushBound (sort := SetTheory.SetSort.set) Q |>.pushBound (sort := SetTheory.SetSort.set) G
  exact ⟨η, rfl, rfl, rfl, hPoint,
    (entry_member_l (hW := hW) (matrix_m Δ) ζ I W τ ν hτ hIW hI₀ hW₀
      h.2.1 η (fun _ _ => rfl)).mpr hPoint⟩

/-- 见证属于 I，完整资格仍在同一个 W 中判定；不传播 I 的背景公理。 -/
theorem capture_l {Δ Ε : SortContext ℒ} (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env 𝒩₀ [] Δ) (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hIW : subset_l (ℳ := ℳ) I₀ W₀) (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒲))
    (B ω x : type_l (ℳ := ℳ) I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hCover : PowerlessCodedHistoryCoverageSyntax.statement_l (𝒩 := 𝒲)
      (PowerlessSourceInclusion.inclusion_l hIW B)
      (PowerlessSourceInclusion.inclusion_l hIW ω)
      (PowerlessSourceInclusion.inclusion_l hIW x)) :
    ∃ a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : type_l (ℳ := ℳ) I₀,
      PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := 𝒲)
      (PowerlessSourceInclusion.inclusion_l hIW B) (PowerlessSourceInclusion.inclusion_l hIW ω) (PowerlessSourceInclusion.inclusion_l hIW x) (PowerlessSourceInclusion.inclusion_l hIW a) (PowerlessSourceInclusion.inclusion_l hIW y)
      (PowerlessSourceInclusion.inclusion_l hIW A) (PowerlessSourceInclusion.inclusion_l hIW U) (PowerlessSourceInclusion.inclusion_l hIW D) (PowerlessSourceInclusion.inclusion_l hIW f) (PowerlessSourceInclusion.inclusion_l hIW e)
      (PowerlessSourceInclusion.inclusion_l hIW t₁) (PowerlessSourceInclusion.inclusion_l hIW t₂) (PowerlessSourceInclusion.inclusion_l hIW t₃) (PowerlessSourceInclusion.inclusion_l hIW t₄) (PowerlessSourceInclusion.inclusion_l hIW P)
      (PowerlessSourceInclusion.inclusion_l hIW N) (PowerlessSourceInclusion.inclusion_l hIW F) (PowerlessSourceInclusion.inclusion_l hIW V) (PowerlessSourceInclusion.inclusion_l hIW Q) (PowerlessSourceInclusion.inclusion_l hIW G) := by
  let η : Env 𝒩₀ [.set, .set, .set] Δ := ν |>.pushBound (sort := SetTheory.SetSort.set) B |>.pushBound (sort := SetTheory.SetSort.set) ω |>.pushBound (sort := SetTheory.SetSort.set) x
  have hInside := capture_formula_l ζ I W τ ν hτ hIW hI₀ hW₀ hExt B ω x h hCover
  change (PowerlessRelativeFiniteElementarity.entry_m (exists_m Δ) I W τ).satisfies ζ ∧
    (PowerlessRelativeFiniteElementarity.entry_m (matrix_m Δ) I W τ).satisfies ζ ∧ True at h
  obtain ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, hPoint⟩ := (witnesses_l η).mp hInside
  let ξ : Env 𝒩₀ [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] Δ := η |>.pushBound (sort := SetTheory.SetSort.set) a |>.pushBound (sort := SetTheory.SetSort.set) y |>.pushBound (sort := SetTheory.SetSort.set) A |>.pushBound (sort := SetTheory.SetSort.set) U |>.pushBound (sort := SetTheory.SetSort.set) D |>.pushBound (sort := SetTheory.SetSort.set) f |>.pushBound (sort := SetTheory.SetSort.set) e |>.pushBound (sort := SetTheory.SetSort.set) t₁ |>.pushBound (sort := SetTheory.SetSort.set) t₂ |>.pushBound (sort := SetTheory.SetSort.set) t₃ |>.pushBound (sort := SetTheory.SetSort.set) t₄ |>.pushBound (sort := SetTheory.SetSort.set) P |>.pushBound (sort := SetTheory.SetSort.set) N |>.pushBound (sort := SetTheory.SetSort.set) F |>.pushBound (sort := SetTheory.SetSort.set) V |>.pushBound (sort := SetTheory.SetSort.set) Q |>.pushBound (sort := SetTheory.SetSort.set) G
  have hBack := (entry_member_l (hW := hW) (matrix_m Δ) ζ I W τ ν hτ hIW hI₀ hW₀
    h.2.1 ξ (fun _ _ => rfl)).mpr hPoint
  refine ⟨a, y, A, U, D, f, e, t₁, t₂, t₃, t₄, P, N, F, V, Q, G, ?_⟩
  simpa only [PowerlessSourceInclusion.env_l, Term.eval, Env.pushBound_bound_here,
    Env.pushBound_bound_there, ξ, η] using
    (PowerlessCodedHistoryCoverageSyntax.point_formula_l hExt
      (PowerlessSourceInclusion.env_l (hU := hW) hIW ξ)
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar (.there (.there (.there (.there (.there .here))))))
    (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).mp hBack

#print axioms exists_formula_l
#print axioms matrix_formula_l
#print axioms capture_formula_l
#print axioms capture_env_l
#print axioms capture_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullCodedCoverage
