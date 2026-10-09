import BMSConstructibleBridge.PowerlessMemberDefDerives
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives
import BMSConstructibleBridge.SecondOrderMemberRelativization

/-! # 实际 Def 中任意公式的相对分离切片

背景为原 Z₂，公式使用原纯隶属语言。消费实际 Def(T,E)，在 E 中取得
X∈T 的精确切片；矩阵可含任意量词，其真值限制在原 T 的成员结构。
全部参数属于 T，T 传递，以保证 X 的每个成员也在该结构的量词域中。
不预供切片，不要求枚举图∈T，也不把此局部结论当作 W 的完整分离。
外部公式模式保留原 AST，并经原解释回传 Z₂ 的 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeDefSeparation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mk_l mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SecondOrderMemberStructure.structure_l

universe u

private def slice_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [.set] (.set :: Δ) :=
  .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar .here))
    (φ.abstractFreeTop.weakenFree SetTheory.SetSort.set)

private theorem slice_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒩 [] Δ)
    (X x : 𝒩.Carrier .set) :
    (slice_m φ).satisfies ((η.pushFree X).pushBound x) ↔
      𝒩.relInterp .membership (.cons x (.cons X .nil)) ∧ φ.satisfies (η.pushFree x) := by
  change 𝒩.relInterp .membership (.cons x (.cons X .nil)) ∧
    (φ.abstractFreeTop.weakenFree SetTheory.SetSort.set).satisfies ((η.pushBound x).pushFree X) ↔ _
  rw [Formula.satisfies_weakenFree, Formula.satisfies_abstractFreeTop]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 规格量化全部原商对象，不只量化 T 内对象。 -/
theorem exists_l {T E : type_l hℳ}
    (hTrans : ∀ x, mem_l hℳ x T → ∀ y, mem_l hℳ y x → mem_l hℳ y T)
    (hDef : SecondOrderMemberDef.spec_l hℳ T E)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    {X : type_l hℳ} (hX : mem_l hℳ X T)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) T) :
    ∃ Y, mem_l hℳ Y E ∧ ∀ x, mem_l hℳ x Y ↔ mem_l hℳ x X ∧
      (PowerlessRelativization.formula_m φ).satisfies ((η.pushFree x).pushFree T) := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ T
  obtain ⟨k, hk, _⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A hX
  let ξ : Env (SecondOrderMemberStructure.structure_l hℳ A k hk) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun v => ⟨η.freeVal v, hParams _ v⟩ }
  obtain ⟨Y, hY, hRead⟩ := SecondOrderMemberDefProperties.coverage_l hℳ A k hk hDef
    (ξ.pushFree (sort := SetTheory.SetSort.set) ⟨X, hX⟩) (slice_m φ)
  have hRead' n (hn : SecondOrderPairing.relation_l A.real n A.root) :
      mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) Y ↔
        mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) X ∧
          (PowerlessRelativization.formula_m φ).satisfies
            ((η.pushFree (sort := SetTheory.SetSort.set)
              (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn))).pushFree (mk_l hℳ A)) := by
    have hValue : (SecondOrderMemberStructure.value_l hℳ A k hk n).val =
        mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) := by
      change mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A k hk n) = _
      rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A k hk n hn]
    have hEnv : SecondOrderMemberBounded.env_l
        (ξ.pushFree (sort := SetTheory.SetSort.set) (SecondOrderMemberStructure.value_l hℳ A k hk n)) =
          η.pushFree (sort := SetTheory.SetSort.set) (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) := by
      apply Env.ext
      · intro _ v; nomatch v
      · intro s v
        cases s
        cases v with
        | here => exact hValue
        | there v => rfl
    have hSource := SecondOrderMemberRelativization.formula_l φ
      (ξ.pushFree (sort := SetTheory.SetSort.set) (SecondOrderMemberStructure.value_l hℳ A k hk n))
    rw [hEnv] at hSource
    have h := (hRead n hn).trans
      (slice_formula_l φ ξ ⟨X, hX⟩ (SecondOrderMemberStructure.value_l hℳ A k hk n))
    change mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) Y ↔
      mem_l hℳ (SecondOrderMemberStructure.value_l hℳ A k hk n).val X ∧
        φ.satisfies (ξ.pushFree (SecondOrderMemberStructure.value_l hℳ A k hk n)) at h
    rw [hValue] at h
    exact h.trans (and_congr Iff.rfl hSource.symm)
  refine ⟨Y, hY, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨n, hn, hxn⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A
      (SecondOrderMemberDefProperties.subset_l hℳ hDef hY x hx)
    rw [hxn] at hx ⊢
    exact (hRead' n hn).mp hx
  · rintro ⟨hx, hφ⟩
    obtain ⟨n, hn, hxn⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A (hTrans X hX x hx)
    rw [hxn] at hx hφ ⊢
    exact (hRead' n hn).mpr ⟨hx, hφ⟩

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set, .set, .set] (.set :: .set :: Δ)
  | _, .here => .fvar .here
  | _, .there .here => .bvar .here
  | _, .there (.there v) => .fvar (.there (.there v))

private def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [.set, .set, .set] (.set :: .set :: Δ) :=
  (PowerlessRelativization.formula_m φ).substitute
    (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v) insert_m)

/-- 自由头槽依次为 T、E；切片 Y 属于 E，而非预先假设 Y 属于 T。 -/
def separation_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar .here)) <|
    .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there .here))) <|
      .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
        (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there .here)))) (body_m φ))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .imp (PowerlessMemberDefSyntax.global_m (.fvar .here) (.fvar (.there .here))) <|
      .imp (parameters_m Δ (.fvar .here) (fun v => .fvar (.there (.there v)))) (separation_m φ)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hTrans hDef hParams
  have hTrans' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hTrans
  have hDef' := (PowerlessMemberDefDerives.formula_l K η (.fvar .here) (.fvar (.there .here))).mp hDef
  have hParams' := (parameters_formula_l Δ η (.fvar .here) (fun v => .fvar (.there (.there v)))).mp hParams
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun v => η.freeVal (.there (.there v)) }
  change ∀ X : type_l hℳ, mem_l hℳ X (η.freeVal .here) →
    ∃ Y, mem_l hℳ Y (η.freeVal (.there .here)) ∧ ∀ x,
      mem_l hℳ x Y ↔ mem_l hℳ x X ∧ (body_m φ).satisfies (((η.pushBound X).pushBound Y).pushBound x)
  intro X hX
  obtain ⟨Y, hY, hRead⟩ := exists_l hTrans' hDef' φ ξ hX hParams'
  refine ⟨Y, hY, fun x => (hRead x).trans (and_congr Iff.rfl ?_)⟩
  refine ((Formula.satisfies_substitute (((η.pushBound X).pushBound Y).pushBound x) _
    (PowerlessRelativization.formula_m φ)).trans ?_).symm
  apply Iff.of_eq
  apply congrArg (fun η => (PowerlessRelativization.formula_m φ).satisfies η)
  apply Env.ext
  · intro _ v; nomatch v
  · intro s v
    cases s
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeDefSeparation
