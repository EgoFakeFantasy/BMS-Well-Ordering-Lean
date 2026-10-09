import BMSConstructibleBridge.PowerlessRelativeCofinalMemberDefClosure
import BMSConstructibleBridge.PowerlessRelativeClassRawFunction
import BMSConstructibleBridge.PowerlessRelativeClassSequenceComposition
import BMSConstructibleBridge.PowerlessRelativeClassSequenceIndex
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationSection
import BMSConstructibleBridge.PowerlessRelativeLimitInjectionEnumeration
import BMSConstructibleBridge.PowerlessRelativeLimitRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeClassRowFamilyAmbient
import BMSConstructibleBridge.PowerlessMemberDefDerives

/-! # 已有层内枚举的原 Def 有限后继枚举

背景是原二阶算术模型及其纯隶属商语言 ℒ。输入枚举图 U 本身已属于实际
共尾极限层 W；仅有 Class 计数不能代替此条件。完整内部有限赋值通过 U
提升为数值序列，以序列数码和两次原平方分支配数编码受限旧翻译像指标。
最小编号、带默认值逆图及行映射只用固定 Δ₀ 矩阵和有限两 Def 界。

这里不构造长前史，不收集逐点枚举，不假定 Collection、HC=W 或完整
Class 算术超限递归。原 Def 的规范 raw 枚举与输入 U 严格分开；前者不
要求是 Class。全部见证保留 Prop，本文件为后续原对象句包装提供语义块。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalMemberDefEnumeration

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open SecondOrderQuotient (mem_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ t)
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₄ t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₅ t)
private abbrev up₇ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₆ t)

/-- l、q、序列编号 k 由原配数嵌套为一个内部自然数；所有见证均有实际界。 -/
def index_code_m {Γ Δ : SortContext ℒ}
    (ω e N one two A U Seq Idx i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <|
    membershipLevyBound.boundedExists (up ω) <|
      membershipLevyBound.boundedExists (up₂ Idx) <|
        membershipLevyBound.boundedExists (up₃ Seq) <|
          membershipLevyBound.boundedExists (up₄ N) <|
            membershipLevyBound.boundedExists (up₅ ω) <|
              membershipLevyBound.boundedExists (up₆ ω) <|
                let l : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
                  .bvar (.there (.there (.there (.there (.there (.there .here))))))
                let q : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
                  .bvar (.there (.there (.there (.there (.there .here)))))
                let t : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
                  .bvar (.there (.there (.there (.there .here))))
                let f : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
                  .bvar (.there (.there (.there .here)))
                let g : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
                  .bvar (.there (.there .here))
                let k : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
                  .bvar (.there .here)
                let c : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
                  .bvar .here
                .conj (PowerlessPairBounded.ordered_m q f t) <|
                  .conj (PowerlessPairBounded.ordered_m l t (up₇ j)) <|
                    .conj (PowerlessFiniteSequenceComposition.formula_m
                      (up₇ ω) (up₇ A) (up₇ U) g f) <|
                      .conj (PowerlessBoundedSequenceIndex.formula_m
                        (up₇ ω) (up₇ e) (up₇ N) (up₇ one) (up₇ two) k g) <|
                        .conj (PowerlessBoundedNumericPairing.formula_m (up₇ ω) (up₇ e) (up₇ N) q k c)
                          (PowerlessBoundedNumericPairing.formula_m (up₇ ω) (up₇ e) (up₇ N) l c (up₇ i))

theorem index_code_delta_l {Γ Δ : SortContext ℒ}
    (ω e N one two A U Seq Idx i j : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (index_code_m ω e N one two A U Seq Idx i j) :=
  .bounded_exists _ (.bounded_exists _ (.bounded_exists _ (.bounded_exists _
    (.bounded_exists _ (.bounded_exists _ (.bounded_exists _
      (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
        (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
          (.conj (PowerlessFiniteSequenceComposition.delta_l _ _ _ _ _)
            (.conj (PowerlessBoundedSequenceIndex.delta_l _ _ _ _ _ _ _)
              (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
                (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _))))))))))))

def index_code_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N one two A U Seq Idx i j : carrier_l 𝒩) : Prop :=
  ∃ l, member_l 𝒩 l ω ∧ ∃ q, member_l 𝒩 q ω ∧ ∃ t, member_l 𝒩 t Idx ∧
    ∃ f, member_l 𝒩 f Seq ∧ ∃ g, member_l 𝒩 g N ∧ ∃ k, member_l 𝒩 k ω ∧
      ∃ c, member_l 𝒩 c ω ∧ ordered_l (ℳ := 𝒩) q f t ∧ ordered_l (ℳ := 𝒩) l t j ∧
        PowerlessFiniteSequenceComposition.holds_l (𝒩 := 𝒩) ω A U g f ∧
          PowerlessBoundedSequenceIndex.holds_l (𝒩 := 𝒩) ω e N one two k g ∧
            PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e N q k c ∧
              PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e N l c i

theorem index_code_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N one two A U Seq Idx i j : Term ℒ Γ Δ .set) :
    (index_code_m ω e N one two A U Seq Idx i j).satisfies η ↔
      index_code_l (ω.eval η) (e.eval η) (N.eval η) (one.eval η) (two.eval η)
        (A.eval η) (U.eval η) (Seq.eval η) (Idx.eval η) (i.eval η) (j.eval η) := by
  simp only [index_code_m, index_code_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, PowerlessFiniteSequenceComposition.formula_l,
    PowerlessBoundedSequenceIndex.formula_l, PowerlessBoundedNumericPairing.formula_l,
    Arguments.eval, up₇, up₆, up₅, up₄, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β W : SecondOrderQuotient.type_l hℳ}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

variable (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
  (hLimit : limit_l hℳ β) (hW : level_l hℳ B β W)
  (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)

local notation "ClassModel" => structure_l hℳ B hBase

include hBase hLimit hW hCofinal in
/-- 固定 Δ₀ 函数图的所有参数已有 W 界时，有限两 Def 后仍严格留在 W。 -/
theorem function_member_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env RawModel [] Δ)
    {X Y G : SecondOrderQuotient.type_l hℳ}
    (hXW : mem_l hℳ X W) (hYW : mem_l hℳ Y W)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) W)
    (hG : map_l (ℳ := RawModel) G X Y)
    (hRead : ∀ x y, value_l (ℳ := RawModel) G x y ↔
      mem_l hℳ x X ∧ mem_l hℳ y Y ∧ φ.satisfies ((η.pushFree y).pushFree x)) :
    mem_l hℳ G W := by
  let ξ : Env RawModel [] (.set :: Δ) := η.pushFree Y
  have hParams' : ∀ s (v : Variable (.set :: Δ) s), mem_l hℳ (ξ.freeVal v) W := by
    intro s v
    cases v with
    | here => exact hYW
    | there v => exact hParams _ v
  obtain ⟨γ, C, hγβ, hC, hγLimit, hXC, hParamsC⟩ :=
    PowerlessRelativeCofinalLimitBounds.exists_l hBase hLimit hW hCofinal ξ hXW hParams'
  have hYC : mem_l hℳ Y C := hParamsC _ .here
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  obtain ⟨γ₁, D, hγ₁β, hD, hCD⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hW hγβ hC
  obtain ⟨γ₂, E, hγ₂β, hE, hDE⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hW hγ₁β hD
  have hSub := SecondOrderMemberDefProperties.contains_l hℳ hCD
    (fun x y hx hy => hTrans x hx y hy)
  have hGE := PowerlessRelativeLimitFunctionGraphBounded.member_l hℳ hBase hC hγLimit hCD hDE
    hφ η (fun s v => hSub _ (hParamsC s (.there v))) (hSub _ hXC) (hSub _ hYC)
    (fun x hx => hTrans X hXC x hx) (fun y hy => hTrans Y hYC y hy) hG hRead
  exact (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hW G).mpr
    ⟨γ₂, E, hγ₂β, hE, hGE⟩

include hBase hLimit hW hCofinal in
/-- 总性与唯一性完全量化原商坐标；实际 Class 图及其 W 界同时取得。 -/
theorem function_exists_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env ClassModel [] Δ)
    (X Y : type_l hℳ B) (hXW : mem_l hℳ X.val W) (hYW : mem_l hℳ Y.val W)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v).val W)
    (hTotal : ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x X.val →
      ∃! y : SecondOrderQuotient.type_l hℳ, mem_l hℳ y Y.val ∧
        φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x)) :
    ∃ G : type_l hℳ B, mem_l hℳ G.val W ∧ map_l (ℳ := RawModel) G.val X.val Y.val ∧
      ∀ x y : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := RawModel) G.val x y ↔ mem_l hℳ x X.val ∧ mem_l hℳ y Y.val ∧
          φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x) := by
  obtain ⟨G, hG, hRead⟩ := PowerlessRelativeClassRawFunction.exists_l (hBase := hBase) hφ η X Y hTotal
  exact ⟨G, function_member_l hBase hLimit hW hCofinal hφ
    (PowerlessRelativeClassRelativization.env_l η) hXW hYW hParams hG hRead, hG, hRead⟩

include hBase hLimit hW hCofinal in
/-- 覆盖关系只需单码单值，不需图为全域函数；原最小编号给实际层内注射。 -/
theorem injection_of_cover_l {ω X G : type_l hℳ B}
    (hΩ : omega_l (ℳ := ClassModel) ω)
    (hωW : mem_l hℳ ω.val W) (hXW : mem_l hℳ X.val W) (hGW : mem_l hℳ G.val W)
    (hCover : ∀ x, mem_l hℳ x X.val → ∃ i, mem_l hℳ i ω.val ∧ value_l (ℳ := RawModel) G.val i x)
    (hSingle : ∀ x y i, value_l (ℳ := RawModel) G.val i x →
      value_l (ℳ := RawModel) G.val i y → x = y) :
    ∃ R : type_l hℳ B, mem_l hℳ R.val W ∧ map_l (ℳ := RawModel) R.val X.val ω.val ∧
      ∀ x y i, value_l (ℳ := RawModel) R.val x i → value_l (ℳ := RawModel) R.val y i → x = y := by
  have hCoverClass (x : type_l hℳ B) (hx : mem_l hℳ x.val X.val) :
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := ClassModel) G i x := by
    obtain ⟨i, hi, hix⟩ := hCover x.val hx
    let i' : type_l hℳ B := ⟨i,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hi⟩
    exact ⟨i', hi, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G i' x).mpr hix⟩
  let η : Env ClassModel [] [.set] := Env.empty.pushFree G
  let φ := PowerlessRelativeClassEnumerationSection.formula_m
  have hFormula (x i : SecondOrderQuotient.type_l hℳ) :
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree i).pushFree x) ↔
      value_l (ℳ := RawModel) G.val i x ∧ ∀ j, mem_l hℳ j i → ¬value_l (ℳ := RawModel) G.val j x := by
    simp only [φ, η, PowerlessRelativeClassEnumerationSection.formula_m,
      Formula.LevyBound.boundedForall, Formula.LevyBound.membership, membershipLevyBound,
      Formula.satisfies, PowerlessValueBounded.formula_l, Arguments.eval, Term.eval]
    rfl
  have hAbsolute (x i : type_l hℳ B) :
      PowerlessRelativeClassEnumerationSection.minimal_l (hBase := hBase) G x i ↔
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree i.val).pushFree x.val) := by
    have hBounded := PowerlessRelativeClassBounded.formula_l (hBase := hBase) (φ := φ)
      PowerlessRelativeClassEnumerationSection.delta_l ((η.pushFree i).pushFree x)
    have hRead : φ.satisfies ((η.pushFree i).pushFree x) ↔
        φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree i.val).pushFree x.val) := by
      simpa only [PowerlessRelativeClassRawFunction.env_pushFree_l] using hBounded
    exact (PowerlessRelativeClassEnumerationSection.formula_l G x i).symm.trans hRead
  obtain ⟨R, hRW, hR, hRead⟩ := function_exists_l hBase hLimit hW hCofinal
    (φ := φ) PowerlessRelativeClassEnumerationSection.delta_l η X ω hXW hωW
    (by intro s v; cases v with | here => exact hGW | there v => nomatch v) (by
      intro x hx
      let x' : type_l hℳ B := ⟨x,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hx⟩
      obtain ⟨i, hi, hMin⟩ := PowerlessRelativeClassEnumerationSection.minimum_l
        (hBase := hBase) (ω := ω) (G := G) (X := X) (x := x') hΩ hCoverClass hx
      refine ⟨i.val, ⟨hi, (hAbsolute x' i).mp hMin⟩, ?_⟩
      rintro j ⟨hj, hMinJ⟩
      let j' : type_l hℳ B := ⟨j,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hj⟩
      exact congrArg Subtype.val (PowerlessRelativeClassEnumerationSection.unique_l
        (hBase := hBase) hΩ hj hi ((hAbsolute x' j').mpr hMinJ) hMin))
  refine ⟨R, hRW, hR, ?_⟩
  intro x y i hxi hyi
  exact hSingle x y i ((hFormula x i).mp ((hRead x i).mp hxi).2.2).1
    ((hFormula y i).mp ((hRead y i).mp hyi).2.2).1

include hBase hLimit hW hCofinal in
/-- 注射图的层内界是真实输入；带默认值反转后仍属于同一共尾极限层。 -/
theorem inverse_l (K : source_coding_l hℳ) {ω X R d : type_l hℳ B}
    (hωW : mem_l hℳ ω.val W) (hXW : mem_l hℳ X.val W)
    (hRW : mem_l hℳ R.val W) (hdW : mem_l hℳ d.val W)
    (hR : map_l (ℳ := RawModel) R.val X.val ω.val)
    (hInjective : ∀ x y i, value_l (ℳ := RawModel) R.val x i → value_l (ℳ := RawModel) R.val y i → x = y)
    (hd : mem_l hℳ d.val X.val) :
    ∃ U : type_l hℳ B, mem_l hℳ U.val W ∧ map_l (ℳ := RawModel) U.val ω.val X.val ∧
      ∀ x, mem_l hℳ x X.val → ∃ i, mem_l hℳ i ω.val ∧ value_l (ℳ := RawModel) U.val i x := by
  let η : Env RawModel [] [.set, .set, .set] :=
    ((Env.empty.pushFree d.val).pushFree R.val).pushFree X.val
  obtain ⟨γ, C, hγβ, hC, hγLimit, hωC, hParamsC⟩ :=
    PowerlessRelativeCofinalLimitBounds.exists_l hBase hLimit hW hCofinal η hωW
      (by
        intro s v
        cases v with
        | here => exact hXW
        | there v => cases v with
          | here => exact hRW
          | there v => cases v with
            | here => exact hdW
            | there v => nomatch v)
  obtain ⟨γ₁, D, hγ₁β, hD, hCD⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hW hγβ hC
  obtain ⟨γ₂, E, hγ₂β, hE, hDE⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hW hγ₁β hD
  obtain ⟨U, hUE, hU, hOnto, _⟩ := PowerlessRelativeLimitInjectionEnumeration.exists_l
    K hBase hγLimit hC hCD hDE hωC (hParamsC _ .here)
      (hParamsC _ (.there .here)) (hParamsC _ (.there (.there .here))) hR hInjective hd
  exact ⟨U, (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hW U.val).mpr
    ⟨γ₂, E, hγ₂β, hE, hUE⟩, hU, hOnto⟩

include hBase in
private theorem sequence_spec_class_l {ω A S : type_l hℳ B}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val A.val S.val) :
    PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω A S := by
  intro f
  constructor
  · intro hf
    obtain ⟨n, hn, hMap⟩ := (hS f.val).mp hf
    let n' : type_l hℳ B := ⟨n,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hn⟩
    exact ⟨n', hn, (PowerlessRelativeClassFunctionAbsolute.map_l
      (hBase := hBase) f n' A).mpr hMap⟩
  · rintro ⟨n, hn, hMap⟩
    exact (hS f.val).mpr ⟨n.val, hn,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f n A).mp hMap⟩

include hBase in
private theorem composition_absolute_l (ω A U g f : type_l hℳ B) :
    PowerlessFiniteSequenceComposition.holds_l (𝒩 := ClassModel) ω A U g f ↔
      PowerlessFiniteSequenceComposition.holds_l (𝒩 := RawModel) ω.val A.val U.val g.val f.val := by
  let η : Env ClassModel [] [.set, .set, .set, .set, .set] :=
    ((((Env.empty.pushFree f).pushFree g).pushFree U).pushFree A).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let a : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let u : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let n : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let s : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  exact (PowerlessFiniteSequenceComposition.formula_l η w a u n s).symm.trans
    ((PowerlessRelativeClassBounded.formula_l (hBase := hBase)
      (PowerlessFiniteSequenceComposition.delta_l w a u n s) η).trans
      (PowerlessFiniteSequenceComposition.formula_l (PowerlessRelativeClassRelativization.env_l η) w a u n s))

/-- 原数码单射和原配数单射同时处理全部内部坐标。 -/
private theorem numeric_pair_unique_l (K : source_coding_l hℳ) {N : SecondOrderQuotient.type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) K.omega K.omega N)
    {a b c a' b' : SecondOrderQuotient.type_l hℳ}
    (ha : mem_l hℳ a K.omega) (hb : mem_l hℳ b K.omega)
    (ha' : mem_l hℳ a' K.omega) (hb' : mem_l hℳ b' K.omega)
    (hPair : PowerlessBoundedNumericPairing.holds_l (𝒩 := RawModel)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val N a b c)
    (hPair' : PowerlessBoundedNumericPairing.holds_l (𝒩 := RawModel)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val N a' b' c) : a = a' ∧ b = b' := by
  obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨a, ha⟩
  obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨b, hb⟩
  obtain ⟨n', hn'⟩ := numberCode_surjective_l K ⟨a', ha'⟩
  obtain ⟨m', hm'⟩ := numberCode_surjective_l K ⟨b', hb'⟩
  have hn₀ := congrArg Subtype.val hn
  have hm₀ := congrArg Subtype.val hm
  have hn₁ := congrArg Subtype.val hn'
  have hm₁ := congrArg Subtype.val hm'
  change (numberCode_l K n).val = a at hn₀
  change (numberCode_l K m).val = b at hm₀
  change (numberCode_l K n').val = a' at hn₁
  change (numberCode_l K m').val = b' at hm₁
  rw [← hn₀, ← hm₀] at hPair
  rw [← hn₁, ← hm₁] at hPair'
  have hCode := ((PowerlessBoundedNumericPairing.instance_l K hN n m c).mp hPair).symm.trans
    ((PowerlessBoundedNumericPairing.instance_l K hN n' m' c).mp hPair')
  have hNum := numberCode_injective_l K (Subtype.ext hCode)
  obtain ⟨h₁, h₂⟩ := SecondOrderPairingBounds.injective_l hℳ n m n' m' hNum
  exact ⟨hn₀.symm.trans ((congrArg (fun v => (numberCode_l K v).val) h₁).trans hn₁),
    hm₀.symm.trans ((congrArg (fun v => (numberCode_l K v).val) h₂).trans hm₁)⟩

include hBase in
private theorem index_code_unique_l (K : source_coding_l hℳ)
    {ω e N one two A U Seq Idx : type_l hℳ B}
    (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) K.omega K.omega N.val)
    {i j j' : SecondOrderQuotient.type_l hℳ}
    (hCode : index_code_l (𝒩 := RawModel) ω.val e.val N.val one.val two.val
      A.val U.val Seq.val Idx.val i j)
    (hCode' : index_code_l (𝒩 := RawModel) ω.val e.val N.val one.val two.val
      A.val U.val Seq.val Idx.val i j') : j = j' := by
  obtain ⟨l, hl, q, hq, t, _ht, f, hf, g, hg, k, hk, c, hc,
    hqf, hlt, hComp, hIndex, hInner, hOuter⟩ := hCode
  obtain ⟨l', hl', q', hq', t', _ht', f', hf', g', hg', k', hk', c', hc',
    hqf', hlt', hComp', hIndex', hInner', hOuter'⟩ := hCode'
  rw [hω, he] at hOuter hOuter' hInner hInner' hIndex hIndex'
  have hOuterEq := numeric_pair_unique_l K hN
    (hω ▸ hl) (hω ▸ hc) (hω ▸ hl') (hω ▸ hc') hOuter hOuter'
  obtain ⟨rfl, rfl⟩ := hOuterEq
  have hInnerEq := numeric_pair_unique_l K hN
    (hω ▸ hq) (hω ▸ hk) (hω ▸ hq') (hω ▸ hk') hInner hInner'
  obtain ⟨rfl, rfl⟩ := hInnerEq
  have hgg : g = g' := PowerlessBoundedSequenceIndex.unique_l K hN hIndex hIndex'
  subst g'
  let gClass : type_l hℳ B := ⟨g,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase N.property hg⟩
  let fClass : type_l hℳ B := ⟨f,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Seq.property hf⟩
  let fClass' : type_l hℳ B := ⟨f',
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Seq.property hf'⟩
  have hff : f = f' := congrArg Subtype.val (PowerlessRelativeClassSequenceComposition.unique_l
    (hBase := hBase) ((composition_absolute_l hBase ω A U gClass fClass).mpr hComp)
      ((composition_absolute_l hBase ω A U gClass fClass').mpr hComp'))
  subst f'
  have htt : t = t' := SecondOrderPairObjects.ordered_unique_l hℳ hqf hqf'
  subst t'
  exact SecondOrderPairObjects.ordered_unique_l hℳ hlt hlt'

private abbrev code_parameters_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set]

include hBase hLimit hW hCofinal in
/-- 只要 I 的每个 raw 指标是 (l,(q,f))，已有层内 U 就给 I 的层内注射。 -/
theorem indices_injection_l (K : source_coding_l hℳ)
    {ω A U Seq Idx I : type_l hℳ B}
    (hω : ω.val = K.omega) (hΩ : omega_l (ℳ := ClassModel) ω)
    (hωW : mem_l hℳ ω.val W) (hAW : mem_l hℳ A.val W) (hUW : mem_l hℳ U.val W)
    (hSeqW : mem_l hℳ Seq.val W) (hIdxW : mem_l hℳ Idx.val W) (hIW : mem_l hℳ I.val W)
    (hU : map_l (ℳ := RawModel) U.val ω.val A.val)
    (hOnto : ∀ x, mem_l hℳ x A.val → ∃ i, mem_l hℳ i ω.val ∧ value_l (ℳ := RawModel) U.val i x)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) ω.val A.val Seq.val)
    (hCoordinates : ∀ j, mem_l hℳ j I.val →
      ∃ l, mem_l hℳ l ω.val ∧ ∃ t, mem_l hℳ t Idx.val ∧
        ∃ q, mem_l hℳ q ω.val ∧ ∃ f, mem_l hℳ f Seq.val ∧
          ordered_l (ℳ := RawModel) l t j ∧ ordered_l (ℳ := RawModel) q f t) :
    ∃ R : type_l hℳ B, mem_l hℳ R.val W ∧ map_l (ℳ := RawModel) R.val I.val ω.val ∧
      ∀ x y i, value_l (ℳ := RawModel) R.val x i → value_l (ℳ := RawModel) R.val y i → x = y := by
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  have hNumW (n : SecondOrderModel.num_l ℳ) : mem_l hℳ (numberCode_l K n).val W :=
    hTrans ω.val hωW _ (hω.symm ▸ (numberCode_l K n).property)
  let e : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val,
    ⟨β, W, hW, hNumW _⟩⟩
  let one : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val,
    ⟨β, W, hW, hNumW _⟩⟩
  let two : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.succ_l
    (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))).val, ⟨β, W, hW, hNumW _⟩⟩
  obtain ⟨NRaw, hNW, hN₀⟩ := PowerlessRelativeLimitFiniteSequencesDirect.exists_l
    hBase hLimit hW K.omega_spec (hω ▸ hωW) (hω ▸ hωW)
  let N : type_l hℳ B := ⟨NRaw, ⟨β, W, hW, hNW⟩⟩
  have hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) K.omega K.omega N.val := hN₀
  let η : Env RawModel [] code_parameters_m :=
    ((((((((Env.empty.pushFree Idx.val).pushFree Seq.val).pushFree U.val).pushFree A.val).pushFree two.val).pushFree one.val).pushFree N.val).pushFree e.val).pushFree ω.val
  let p (v : Variable code_parameters_m .set) : Term ℒ [] (.set :: .set :: code_parameters_m) .set :=
    .fvar (.there (.there v))
  let w := p .here
  let z := p (.there .here)
  let s := p (.there (.there .here))
  let o := p (.there (.there (.there .here)))
  let b := p (.there (.there (.there (.there .here))))
  let a := p (.there (.there (.there (.there (.there .here)))))
  let u := p (.there (.there (.there (.there (.there (.there .here))))))
  let f := p (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let t := p (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let φ := index_code_m w z s o b a u f t (.fvar .here) (.fvar (.there .here))
  have hFormula (i j : SecondOrderQuotient.type_l hℳ) :
      φ.satisfies ((η.pushFree j).pushFree i) ↔
      index_code_l (𝒩 := RawModel) ω.val e.val N.val one.val two.val
        A.val U.val Seq.val Idx.val i j :=
    index_code_formula_l ((η.pushFree j).pushFree i) w z s o b a u f t (.fvar .here) (.fvar (.there .here))
  have hParams : ∀ s (v : Variable code_parameters_m s), mem_l hℳ (η.freeVal v) W := by
    intro s v
    cases s
    match v with
    | .here => exact hωW
    | .there .here => exact hNumW _
    | .there (.there .here) => exact hNW
    | .there (.there (.there .here)) => exact hNumW _
    | .there (.there (.there (.there .here))) => exact hNumW _
    | .there (.there (.there (.there (.there .here)))) => exact hAW
    | .there (.there (.there (.there (.there (.there .here))))) => exact hUW
    | .there (.there (.there (.there (.there (.there (.there .here)))))) => exact hSeqW
    | .there (.there (.there (.there (.there (.there (.there (.there .here))))))) => exact hIdxW
  obtain ⟨GRaw, hGW, hRead⟩ := PowerlessRelativeLimitRelationalGraph.exists_l hBase hLimit hW
    (φ := φ) (index_code_delta_l _ _ _ _ _ _ _ _ _ _ _) η hωW hIW hParams
  let G : type_l hℳ B := ⟨GRaw, ⟨β, W, hW, hGW⟩⟩
  have hUClass := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) U ω A).mpr hU
  have hOntoClass (x : type_l hℳ B) (hx : mem_l hℳ x.val A.val) :
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := ClassModel) U i x := by
    obtain ⟨i, hi, hix⟩ := hOnto x.val hx
    let i' : type_l hℳ B := ⟨i,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hi⟩
    exact ⟨i', hi, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) U i' x).mpr hix⟩
  have hSeqClass := sequence_spec_class_l hBase hSeq
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  have hCover (j : SecondOrderQuotient.type_l hℳ) (hj : mem_l hℳ j I.val) :
      ∃ i, mem_l hℳ i ω.val ∧ value_l (ℳ := RawModel) G.val i j := by
    obtain ⟨l, hl, t₀, ht₀, q, hq, f₀, hf₀, hlt, hqf⟩ := hCoordinates j hj
    let fClass : type_l hℳ B := ⟨f₀,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Seq.property hf₀⟩
    obtain ⟨g, hComp⟩ := PowerlessRelativeClassSequenceComposition.lift_l
      (hBase := hBase) hΩ hUClass hOntoClass ((hSeqClass fClass).mp hf₀)
    have hgN : mem_l hℳ g.val N.val := by
      obtain ⟨n, hn, hgMap, _, _⟩ := hComp
      have hgRaw : SecondOrderFunctionObjects.map_l hℳ g.val n.val ω.val :=
        (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) g n ω).mp hgMap
      rw [hω] at hgRaw
      have hgRaw' : map_l (ℳ := RawModel) g.val n.val K.omega := by
        change SecondOrderFunctionObjects.map_l hℳ g.val n.val K.omega
        exact hgRaw
      exact (hN g.val).mpr ⟨n.val, hω ▸ hn, hgRaw'⟩
    obtain ⟨k, hk, hIndex⟩ := PowerlessRelativeClassSequenceIndex.exists_l
      (hBase := hBase) K (ω := ω) (e := e) (S := N) (one := one) (two := two) (f := g)
        hN hE hω (show e.val = _ from rfl)
        (show one.val = _ from rfl) (show two.val = _ from rfl) hgN
    obtain ⟨ln, hln⟩ := numberCode_surjective_l K ⟨l, hω ▸ hl⟩
    obtain ⟨qn, hqn⟩ := numberCode_surjective_l K ⟨q, hω ▸ hq⟩
    obtain ⟨kn, hkn⟩ := numberCode_surjective_l K ⟨k.val, hω ▸ hk⟩
    have hlnRaw := congrArg Subtype.val hln
    have hqnRaw := congrArg Subtype.val hqn
    have hknRaw := congrArg Subtype.val hkn
    change (numberCode_l K ln).val = l at hlnRaw
    change (numberCode_l K qn).val = q at hqnRaw
    change (numberCode_l K kn).val = k.val at hknRaw
    let cn := SecondOrderPairing.value_l qn kn
    let i : SecondOrderQuotient.type_l hℳ := (numberCode_l K (SecondOrderPairing.value_l ln cn)).val
    have hcPair : PowerlessBoundedNumericPairing.holds_l (𝒩 := RawModel)
        ω.val e.val N.val q k.val (numberCode_l K cn).val := by
      rw [hω]
      change PowerlessBoundedNumericPairing.holds_l (𝒩 := RawModel)
        K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val N.val q k.val (numberCode_l K cn).val
      rw [← hqnRaw, ← hknRaw]
      exact (PowerlessBoundedNumericPairing.instance_l K hN qn kn _).mpr rfl
    have hiPair : PowerlessBoundedNumericPairing.holds_l (𝒩 := RawModel)
        ω.val e.val N.val l (numberCode_l K cn).val i := by
      rw [hω]
      change PowerlessBoundedNumericPairing.holds_l (𝒩 := RawModel)
        K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val N.val l (numberCode_l K cn).val i
      rw [← hlnRaw]
      exact (PowerlessBoundedNumericPairing.instance_l K hN ln cn _).mpr rfl
    have hiω : mem_l hℳ i ω.val := by
      rw [hω]
      change mem_l hℳ (numberCode_l K (SecondOrderPairing.value_l ln cn)).val K.omega
      exact (numberCode_l K (SecondOrderPairing.value_l ln cn)).property
    refine ⟨i, hiω, (hRead i j).mpr ⟨hiω, hj, (hFormula i j).mpr ?_⟩⟩
    exact ⟨l, hl, q, hq, t₀, ht₀, f₀, hf₀, g.val, hgN, k.val, hk,
      (numberCode_l K cn).val, hω.symm ▸ (numberCode_l K cn).property, hqf, hlt,
      (composition_absolute_l hBase ω A U g fClass).mp hComp,
      (PowerlessRelativeClassSequenceIndex.absolute_l (hBase := hBase) ω e N one two k g).mp hIndex,
      hcPair, hiPair⟩
  exact injection_of_cover_l hBase hLimit hW hCofinal hΩ hωW hIW hGW hCover
    (fun x y i hix hiy => index_code_unique_l hBase K hω rfl hN
      ((hFormula i x).mp ((hRead i x).mp hix).2.2)
      ((hFormula i y).mp ((hRead i y).mp hiy).2.2))

include hBase hLimit hW hCofinal in
/-- 精确原商行像的统一行图；陪域 H 的已有 W 界排除逐行选择。 -/
theorem row_function_l {I A Q H : type_l hℳ B}
    (hIW : mem_l hℳ I.val W) (hAW : mem_l hℳ A.val W)
    (hQW : mem_l hℳ Q.val W) (hHW : mem_l hℳ H.val W)
    (hImage : ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z H.val ↔
      ∃ j, mem_l hℳ j I.val ∧
        PowerlessRelativeClassRowFamily.row_l (ℳ₀ := RawModel) A.val Q.val j Z) :
    ∃ P : type_l hℳ B, mem_l hℳ P.val W ∧ map_l (ℳ := RawModel) P.val I.val H.val ∧
      ∀ j Z, value_l (ℳ := RawModel) P.val j Z ↔ mem_l hℳ j I.val ∧ mem_l hℳ Z H.val ∧
        PowerlessRelativeClassRowFamily.row_l (ℳ₀ := RawModel) A.val Q.val j Z := by
  let η : Env ClassModel [] [.set, .set] := (Env.empty.pushFree Q).pushFree A
  let a : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let q : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let φ := PowerlessRelativeClassRowFamily.row_m a q (.fvar .here) (.fvar (.there .here))
  have hFormula (j Z : SecondOrderQuotient.type_l hℳ) :
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree Z).pushFree j) ↔
      PowerlessRelativeClassRowFamily.row_l (ℳ₀ := RawModel) A.val Q.val j Z :=
    PowerlessRelativeClassRowFamily.row_formula_l _ _ _ _ _
  obtain ⟨P, hPW, hP, hRead⟩ := function_exists_l hBase hLimit hW hCofinal
    (φ := φ) (PowerlessRelativeClassRowFamily.row_delta_l _ _ _ _) η I H hIW hHW
    (by
      intro s v
      cases v with
      | here => exact hAW
      | there v => cases v with
        | here => exact hQW
        | there v => nomatch v) (by
      intro j hj
      let j' : type_l hℳ B := ⟨j,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase I.property hj⟩
      obtain ⟨Z, hRow, _⟩ := PowerlessRelativeClassRowFamily.row_exists_l (hBase := hBase) A Q j'
      have hRowRaw := (PowerlessRelativeClassRowFamilyAmbient.row_absolute_l
        (hBase := hBase) A Q j' Z).mp hRow
      refine ⟨Z.val, ⟨(hImage Z.val).mpr ⟨j, hj, hRowRaw⟩, (hFormula j Z.val).mpr hRowRaw⟩, ?_⟩
      rintro Z' ⟨_, hZ'⟩
      exact SecondOrderQuotient.ext_l hℳ Z' Z.val
        (fun x => (((hFormula j Z').mp hZ') x).trans (hRowRaw x).symm))
  exact ⟨P, hPW, hP, fun j Z => (hRead j Z).trans
    (and_congr Iff.rfl (and_congr Iff.rfl (hFormula j Z)))⟩

include hBase hLimit hW hCofinal in
/-- 两个已经在 W 内的实际函数图的有限复合，也以完整原商坐标读数留在 W。 -/
theorem composition_l {X Y Z F G : type_l hℳ B}
    (hXW : mem_l hℳ X.val W) (hYW : mem_l hℳ Y.val W) (hZW : mem_l hℳ Z.val W)
    (hFW : mem_l hℳ F.val W) (hGW : mem_l hℳ G.val W)
    (hF : map_l (ℳ := RawModel) F.val X.val Y.val)
    (hG : map_l (ℳ := RawModel) G.val Y.val Z.val) :
    ∃ E : type_l hℳ B, mem_l hℳ E.val W ∧ map_l (ℳ := RawModel) E.val X.val Z.val ∧
      ∀ x z, value_l (ℳ := RawModel) E.val x z ↔ mem_l hℳ x X.val ∧ mem_l hℳ z Z.val ∧
        ∃ y, mem_l hℳ y Y.val ∧ value_l (ℳ := RawModel) F.val x y ∧ value_l (ℳ := RawModel) G.val y z := by
  let η : Env ClassModel [] [.set, .set, .set] :=
    ((Env.empty.pushFree G).pushFree F).pushFree Y
  let φ := PowerlessRelativeClassFunctionComposition.formula_m
  have hFormula (x z : SecondOrderQuotient.type_l hℳ) :
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree z).pushFree x) ↔
      ∃ y, mem_l hℳ y Y.val ∧ value_l (ℳ := RawModel) F.val x y ∧ value_l (ℳ := RawModel) G.val y z := by
    simp only [φ, η, PowerlessRelativeClassFunctionComposition.formula_m,
      Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
      Formula.satisfies, PowerlessValueBounded.formula_l, Arguments.eval, Term.eval]
    rfl
  obtain ⟨E, hEW, hE, hRead⟩ := function_exists_l hBase hLimit hW hCofinal
    (φ := φ) PowerlessRelativeClassFunctionComposition.delta_l η X Z hXW hZW
    (by
      intro s v
      cases v with
      | here => exact hYW
      | there v => cases v with
        | here => exact hFW
        | there v => cases v with
          | here => exact hGW
          | there v => nomatch v) (by
      intro x hx
      obtain ⟨y, ⟨hy, hxy⟩, _⟩ := hF.2 x hx
      obtain ⟨z, ⟨hz, hyz⟩, _⟩ := hG.2 y hy
      refine ⟨z, ⟨hz, (hFormula x z).mpr ⟨y, hy, hxy, hyz⟩⟩, ?_⟩
      rintro z' ⟨_, hz'⟩
      obtain ⟨y', _, hxy', hyz'⟩ := (hFormula x z').mp hz'
      have hyy := SecondOrderFunctionProperties.value_unique_l hℳ hF hxy' hxy
      subst y'
      exact SecondOrderFunctionProperties.value_unique_l hℳ hG hyz' hyz)
  exact ⟨E, hEW, hE, fun x z => (hRead x z).trans
    (and_congr Iff.rfl (and_congr Iff.rfl (hFormula x z)))⟩

include hBase hLimit hW hCofinal in
/-- 有精确行像、层内指标注射和真实非空陪域时，枚举图留在 W。 -/
theorem image_enumeration_l (K : source_coding_l hℳ) {ω I A Q H R : type_l hℳ B}
    (hωW : mem_l hℳ ω.val W) (hIW : mem_l hℳ I.val W) (hAW : mem_l hℳ A.val W)
    (hQW : mem_l hℳ Q.val W) (hHW : mem_l hℳ H.val W) (hRW : mem_l hℳ R.val W)
    (hR : map_l (ℳ := RawModel) R.val I.val ω.val)
    (hInjective : ∀ x y i, value_l (ℳ := RawModel) R.val x i → value_l (ℳ := RawModel) R.val y i → x = y)
    (hNonempty : ∃ Z, mem_l hℳ Z H.val)
    (hImage : ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z H.val ↔
      ∃ j, mem_l hℳ j I.val ∧
        PowerlessRelativeClassRowFamily.row_l (ℳ₀ := RawModel) A.val Q.val j Z) :
    ∃ E : type_l hℳ B, mem_l hℳ E.val W ∧ map_l (ℳ := RawModel) E.val ω.val H.val ∧
      ∀ Z, mem_l hℳ Z H.val → ∃ i, mem_l hℳ i ω.val ∧ value_l (ℳ := RawModel) E.val i Z := by
  obtain ⟨Z₀, hZ₀⟩ := hNonempty
  obtain ⟨dRaw, hd, _⟩ := (hImage Z₀).mp hZ₀
  have hdW := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW I.val hIW dRaw hd
  let d : type_l hℳ B := ⟨dRaw, ⟨β, W, hW, hdW⟩⟩
  obtain ⟨V, hVW, hV, hVOnto⟩ := inverse_l hBase hLimit hW hCofinal
    K (ω := ω) (X := I) (R := R) (d := d) hωW hIW hRW hdW hR hInjective hd
  obtain ⟨P, hPW, hP, hPRead⟩ := row_function_l hBase hLimit hW hCofinal
    hIW hAW hQW hHW hImage
  obtain ⟨E, hEW, hE, hRead⟩ := composition_l hBase hLimit hW hCofinal
    hωW hIW hHW hVW hPW hV hP
  refine ⟨E, hEW, hE, ?_⟩
  intro Z hZ
  obtain ⟨j, hj, hRow⟩ := (hImage Z).mp hZ
  obtain ⟨i, hi, hij⟩ := hVOnto j hj
  exact ⟨i, hi, (hRead i Z).mpr ⟨hi, hZ, j, hj, hij, (hPRead j Z).mpr ⟨hj, hZ, hRow⟩⟩⟩

include hBase hLimit hW hCofinal in
/-- 实际 A 枚举图已经在 W 时，给定原 Def(A) 的实际 ω 枚举图也在 W。
规范旧呈现枚举 U₀ 只用于证明原行像，绝不把它替换成输入枚举 U。 -/
theorem exists_l (K : source_coding_l hℳ) {A H U : SecondOrderQuotient.type_l hℳ}
    (hωW : mem_l hℳ K.omega W) (hAW : mem_l hℳ A W) (hUW : mem_l hℳ U W)
    (hU : map_l (ℳ := RawModel) U K.omega A)
    (hOnto : ∀ x, mem_l hℳ x A → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := RawModel) U i x)
    (hDef : SecondOrderMemberDef.spec_l hℳ A H) :
    ∃ E : type_l hℳ B, mem_l hℳ E.val W ∧ map_l (ℳ := RawModel) E.val K.omega H ∧
      ∀ Z, mem_l hℳ Z H → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := RawModel) E.val i Z := by
  have hHW := PowerlessRelativeCofinalMemberDefClosure.member_l hBase K hLimit hW hCofinal hωW hAW hDef
  have hMother := SecondOrderMemberDefProperties.mother_member_l hℳ hDef
  have hANonempty : ∃ x, mem_l hℳ x A := by
    obtain ⟨x, ⟨hx, _⟩, _⟩ := hU.2 (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
    exact ⟨x, hx⟩
  rcases hDef with ⟨hEmpty, _⟩ | hNonempty
  · obtain ⟨x, hx⟩ := hANonempty
    exact False.elim (hEmpty x hx)
  · obtain ⟨A₀, a, ha, V₅, Powers, Domain, Q₀, R₀, T₀, F₀, H₀, rfl, h, rfl⟩ := hNonempty
    let AClass : type_l hℳ B := ⟨mk_l hℳ A₀, ⟨β, W, hW, hAW⟩⟩
    let HClass : type_l hℳ B := ⟨mk_l hℳ H₀, ⟨β, W, hW, hHW⟩⟩
    let UClass : type_l hℳ B := ⟨U, ⟨β, W, hW, hUW⟩⟩
    let ω : type_l hℳ B := ⟨K.omega, ⟨β, W, hW, hωW⟩⟩
    have hΩ : omega_l (ℳ := ClassModel) ω :=
      (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr K.omega_spec
    obtain ⟨e, t₁, t₂, t₃, Pair, N, Valid, heW, _ht₁W, _ht₂W, _ht₃W,
      hPairW, hNW, _hValidW, hStatic, hDomain⟩ :=
      PowerlessRelativeCofinalSatisfactionForDomain.exists_l (hBase := hBase)
        K hLimit hW hCofinal ω hωW rfl
    obtain ⟨Sat, hSatW, hSat⟩ := hDomain AClass hAW
    obtain ⟨SeqRaw, hSeqW, hSeqRaw⟩ := PowerlessRelativeLimitFiniteSequencesDirect.exists_l
      hBase hLimit hW K.omega_spec hωW hAW
    let Seq : type_l hℳ B := ⟨SeqRaw, ⟨β, W, hW, hSeqW⟩⟩
    have hSeq := sequence_spec_class_l hBase (ω := ω) (A := AClass) (S := Seq) hSeqRaw
    obtain ⟨he, ht₁, ht₂, ht₃, hN, hPairMap, hPair, hValidReading⟩ :=
      PowerlessRelativeClassStaticCodingReading.reading_l (hBase := hBase) K rfl hStatic
    obtain ⟨V₄, hV₄, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
    have hValid := hValidReading V₄ hV₄
    obtain ⟨U₀, hU₀, hNumber, hU₀Onto, hEquality, hMembership⟩ :=
      PowerlessLegacyMemberEnumeration.exists_l K h (A := AClass) rfl
    obtain ⟨C, hC, _⟩ := SecondOrderLegacyFormulaTranslation.exists_l hℳ
    obtain ⟨_OldValid, Translation, _hOldValidW, hTranslationW,
      _hOldValidRaw, _hOldValidNumeric, _hTranslationRaw, hTranslationNumeric⟩ :=
      PowerlessRelativeLimitLegacySyntaxGraphs.exists_l (hBase := hBase)
        K hLimit hW hΩ rfl hωW hNW hPairW hN hPairMap hPair h.formula_codes hC
    have hPreservation := PowerlessLegacyEvaluationPreservation.preservation_l
      (hBase := hBase) K hΩ rfl he hPairMap hPair hValid hSat ht₁ ht₂ ht₃
        hV₄ hC h.powers h.domain h.evaluation hU₀ hU₀Onto hEquality hMembership
    obtain ⟨Idx, I, hIdxW, hIW, hIdxRaw, hI⟩ :=
      PowerlessRelativeLimitLegacyImageIndices.exists_l hBase hLimit hW
        ω e N Translation AClass Seq hωW heW hNW hTranslationW hAW hSeqW
    have hIdxIncludes (q f t : type_l hℳ B)
        (hq : mem_l hℳ q.val ω.val) (hf : mem_l hℳ f.val Seq.val)
        (ht : ordered_l (ℳ := ClassModel) q f t) : mem_l hℳ t.val Idx.val :=
      (hIdxRaw t.val).mpr ⟨q.val, f.val, hq, hf,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) q f t).mp ht⟩
    have hImage := PowerlessLegacyImageDefIdentification.image_iff_l
      hBase K (ω := ω) (A := AClass) (Seq := Seq) (Sat := Sat)
        (e := e.val) (N₂ := N.val) (F := Translation.val) (Idx := Idx.val) (I := I.val) (U := U₀)
        rfl h rfl he hN hTranslationNumeric hC hU₀ hNumber hSeq hPreservation hIdxIncludes hI
    obtain ⟨R, hRW, hR, hInjective⟩ := indices_injection_l hBase hLimit hW hCofinal
      K (ω := ω) (A := AClass) (U := UClass) (Seq := Seq) (Idx := Idx) (I := I)
        rfl hΩ hωW hAW hUW hSeqW hIdxW hIW hU hOnto hSeqRaw (by
          intro j hj
          obtain ⟨l, hl, t, ht, q, hq, f, hf, hlt, hqf, _⟩ := (hI j).mp hj
          exact ⟨l, hl, t, ht, q, hq, f, hf, hlt, hqf⟩)
    obtain ⟨Q, hQW, hQ⟩ := PowerlessRelativeLimitSelectedSatisfactionRows.query_exists_l
      hBase hLimit hW ω AClass Seq Idx Sat I hωW hAW hSeqW hIdxW hSatW hIW
    have hRows (Z : SecondOrderQuotient.type_l hℳ) : mem_l hℳ Z HClass.val ↔
        ∃ j, mem_l hℳ j I.val ∧
          PowerlessRelativeClassRowFamily.row_l (ℳ₀ := RawModel) AClass.val Q.val j Z := by
      refine (hImage Z).trans ?_
      apply exists_congr
      intro j
      apply and_congr_right
      intro hj
      constructor
      · intro hRow x
        constructor
        · intro hx
          have h := (hRow x).mp hx
          exact ⟨h.1, (hQ j x).mpr ⟨hj, h.1, h.2⟩⟩
        · rintro ⟨hx, hValue⟩
          exact (hRow x).mpr ⟨hx, ((hQ j x).mp hValue).2.2⟩
      · intro hRow x
        constructor
        · intro hx
          have h := (hRow x).mp hx
          exact ⟨h.1, ((hQ j x).mp h.2).2.2⟩
        · rintro ⟨hx, hQuery⟩
          exact (hRow x).mpr ⟨hx, (hQ j x).mpr ⟨hj, hx, hQuery⟩⟩
    exact image_enumeration_l hBase hLimit hW hCofinal K
      (ω := ω) (I := I) (A := AClass) (Q := Q) (H := HClass) (R := R)
      hωW hIW hAW hQW hHW hRW hR hInjective ⟨AClass.val, hMother⟩ hRows

open SecondOrderObjectSyntax

/-- 满射守卫只量化原商坐标；不缩为类内指标。 -/
def onto_m {Γ Δ : SortContext ℒ} (U X Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up Y)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up₂ X))
      (value_m (up₂ U) (.bvar .here) (.bvar (.there .here)))

theorem onto_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (U X Y : Term ℒ Γ Δ .set) :
    (onto_m U X Y).satisfies η ↔ ∀ y, member_l 𝒩 y (Y.eval η) →
      ∃ x, member_l 𝒩 x (X.eval η) ∧ value_l (ℳ := 𝒩) (U.eval η) x y := by
  simp only [onto_m, Formula.satisfies, value_formula_l, member_m, Arguments.eval,
    up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 七对象守卫：实际层、内部 ω、母集及输入图的层内界；结论也显式含 H∈W。 -/
def step_m {Γ Δ : SortContext ℒ} (B β W ω A U H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (PowerlessRelativeCofinalLimitBounds.cofinal_m β) <|
          .imp (SecondOrderOmegaSyntax.omega_m ω) <|
            .imp (member_m ω W) <| .imp (member_m A W) <| .imp (member_m U W) <|
              .imp (map_m U ω A) <| .imp (onto_m U ω A) <|
                .imp (PowerlessMemberDefSyntax.global_m A H) <|
                  .conj (member_m H W) <| .existsE .set <|
                    .conj (member_m (.bvar .here) (up W)) <|
                      .conj (map_m (.bvar .here) (up ω) (up H))
                        (onto_m (.bvar .here) (up ω) (up H))

private abbrev context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set]

def schema_m : Formula ℒ [] context_m :=
  step_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

/-- 原商模型中的对象闭句；原 Def 只经 global_m 的 raw 对应读取。 -/
theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ρ
  simp only [schema_m, step_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeCofinalLimitBounds.cofinal_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessMemberDefDerives.formula_l K,
    map_formula_l, onto_formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  intro hBase' hW' hLimit' hCofinal' hΩ hωW hAW hUW hU hOnto hDef
  have hωEq := SecondOrderOmega.unique_l h𝒩 hΩ K.omega_spec
  have hHW := PowerlessRelativeCofinalMemberDefClosure.member_l hBase' K
    hLimit' hW' hCofinal' (hωEq ▸ hωW) hAW hDef
  obtain ⟨E, hEW, hE, hEOnto⟩ := exists_l hBase' hLimit' hW' hCofinal' K
    (hωEq ▸ hωW) hAW hUW (hωEq ▸ hU) (hωEq ▸ hOnto) hDef
  exact ⟨hHW, E.val, hEW, hωEq.symm ▸ hE, hωEq.symm ▸ hEOnto⟩

/-- 实际有限后继句经原图翻译返回原 Z₂ 推导核，不是完整超限枚举断言。 -/
theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩)

#print axioms index_code_delta_l
#print axioms index_code_formula_l
#print axioms function_member_l
#print axioms function_exists_l
#print axioms injection_of_cover_l
#print axioms inverse_l
#print axioms indices_injection_l
#print axioms row_function_l
#print axioms composition_l
#print axioms image_enumeration_l
#print axioms exists_l
#print axioms onto_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalMemberDefEnumeration
