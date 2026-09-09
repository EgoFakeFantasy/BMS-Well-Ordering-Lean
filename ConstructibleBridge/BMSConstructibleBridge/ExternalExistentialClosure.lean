import BMSConstructibleBridge.ExternalBoundedLevyHierarchy
import YesMetaZFC.BMS.FiniteLevyHierarchy

/-!
# 外部公式的有限存在闭包

逐次关闭末尾坐标，证明其语义等价于存在一个完整的有限见证元组。证明只使用
元组追加的通用交换律，避免在每次使用时展开长串 de Bruijn 赋值。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible

/-- 两种末尾追加元组的实现逐坐标相同。 -/
theorem externalSnoc_eq_finSnoc_l {Carrier : Type u} {arity : Nat}
    (tuple : Tuple Carrier arity) (value : Carrier) :
    Constructible.snoc tuple value = Fin.snoc tuple value := by
  funext index
  refine Fin.lastCases ?_ (fun prior => ?_) index
  · rw [Constructible.snoc_last, Fin.snoc_last]
  · rw [Constructible.snoc_castSucc, Fin.snoc_castSucc]

/-- 在元组右侧追加一个坐标与整体追加交换。 -/
theorem tupleAppend_snoc_l {Carrier : Type u} {leftArity rightArity : Nat}
    (left : Tuple Carrier leftArity) (right : Tuple Carrier rightArity)
    (value : Carrier) :
    Fin.append left (Constructible.snoc right value) =
      Constructible.snoc (Fin.append left right) value := by
  simp only [externalSnoc_eq_finSnoc_l]
  exact Fin.append_snoc left right value

/-- 依次关闭外部公式的末尾 `count` 个坐标。 -/
def externalExistentialClosure_l {arity : Nat} :
    (count : Nat) → FOFormula (arity + count) → FOFormula arity
  | 0, φ => φ
  | count + 1, φ => externalExistentialClosure_l count (.ex φ)

/-- 有限存在闭包保持真正有界外部分类中的同一 `Sigma` 层。 -/
theorem externalExistentialClosure_isSigmaFinite_l
    {arity level : Nat} (count : Nat) (φ : FOFormula (arity + count))
    (hφ : ExternalBoundedIsSigmaFinite_l level φ) :
    ExternalBoundedIsSigmaFinite_l level
      (externalExistentialClosure_l count φ) := by
  induction count with
  | zero => exact hφ
  | succ count ih => exact ih (.ex φ) (.ex hφ)

/-- 有限闭包在原生翻译下保持同一 Sigma 层级。 -/
theorem translateExternalExistentialClosure_isSigmaFinite_l
    {arity level : Nat} (count : Nat) (φ : FOFormula (arity + count))
    (hφ : Logic.FirstOrder.Formula.IsSigmaFinite StabilityFrame.membershipLevyBound
      level (translateExternalFormula φ)) :
    Logic.FirstOrder.Formula.IsSigmaFinite StabilityFrame.membershipLevyBound
      level (translateExternalFormula (externalExistentialClosure_l count φ)) := by
  induction count with
  | zero => exact hφ
  | succ count ih => exact ih (.ex φ) (.existsE _ hφ)

/-- 有限存在闭包的满足关系等价于存在完整的有限见证元组。 -/
theorem satisfies_externalExistentialClosure_l
    {Carrier : Type u} (membership : Carrier → Carrier → Prop)
    {arity : Nat} (count : Nat) (φ : FOFormula (arity + count))
    (assignment : Tuple Carrier arity) :
    FOFormula.Satisfies membership (externalExistentialClosure_l count φ)
        assignment ↔
      ∃ witnesses : Tuple Carrier count,
        FOFormula.Satisfies membership φ (Fin.append assignment witnesses) := by
  induction count with
  | zero =>
      simp only [externalExistentialClosure_l]
      constructor
      · intro hφ
        refine ⟨Fin.elim0, ?_⟩
        simpa using hφ
      · rintro ⟨witnesses, hφ⟩
        have hEmpty : witnesses = Fin.elim0 := Subsingleton.elim _ _
        rw [hEmpty] at hφ
        simpa using hφ
  | succ count ih =>
      rw [externalExistentialClosure_l, ih]
      simp only [FOFormula.Satisfies]
      constructor
      · rintro ⟨witnesses, value, hφ⟩
        refine ⟨Constructible.snoc witnesses value, ?_⟩
        rw [tupleAppend_snoc_l]
        exact hφ
      · rintro ⟨witnesses, hφ⟩
        refine ⟨Fin.init witnesses, witnesses (Fin.last count), ?_⟩
        rw [← tupleAppend_snoc_l, externalSnoc_eq_finSnoc_l,
          Fin.snoc_init_self]
        exact hφ

/-- 原始受限满足关系中的有限闭包；每个见证的载体成员资格都显式保留。 -/
theorem satisfiesIn_externalExistentialClosure_l
    (M : Set ZFSet.{u}) {arity : Nat} (count : Nat)
    (φ : FOFormula (arity + count)) (assignment : Tuple ZFSet.{u} arity) :
    Model.SatisfiesIn M (externalExistentialClosure_l count φ) assignment ↔
      ∃ witnesses : Tuple ZFSet.{u} count, (∀ index, witnesses index ∈ M) ∧
        Model.SatisfiesIn M φ (Fin.append assignment witnesses) := by
  induction count with
  | zero =>
      simp only [externalExistentialClosure_l]
      constructor
      · intro hφ
        exact ⟨Fin.elim0, fun index => Fin.elim0 index, by simpa using hφ⟩
      · rintro ⟨witnesses, _, hφ⟩
        have hEmpty : witnesses = Fin.elim0 := Subsingleton.elim _ _
        rw [hEmpty] at hφ
        simpa using hφ
  | succ count ih =>
      rw [externalExistentialClosure_l, ih]
      simp only [Model.SatisfiesIn]
      constructor
      · rintro ⟨witnesses, hWitnesses, value, hValue, hφ⟩
        refine ⟨snoc witnesses value, ?_, ?_⟩
        · intro index
          refine Fin.lastCases ?_ (fun prior => ?_) index
          · simpa only [snoc_last] using hValue
          · simpa only [snoc_castSucc] using hWitnesses prior
        · rw [tupleAppend_snoc_l]
          exact hφ
      · rintro ⟨witnesses, hWitnesses, hφ⟩
        refine ⟨Fin.init witnesses, (fun index => hWitnesses index.castSucc),
          witnesses (Fin.last count), hWitnesses (Fin.last count), ?_⟩
        rw [← tupleAppend_snoc_l, externalSnoc_eq_finSnoc_l,
          Fin.snoc_init_self]
        exact hφ

end YesMetaZFC.BMS.ConstructibleBridge
