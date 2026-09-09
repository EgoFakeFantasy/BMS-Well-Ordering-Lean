import BMSConstructibleBridge.FormulaTranslation
import YesMetaZFC.BMS.FiniteLevyHierarchy

/-!
# 外部成员公式的有限 Lévy 层级

`lean-constructible-universe` 的 `FOFormula` 只把存在量词作为原始构造子；
全称量词由否定与存在量词派生。本模块在这套语法上给出累积的有限
`Sigma` / `Pi` 证书，并证明前序的纯成员语言翻译保持证书。

这个接口刻意只处理语法复杂度，不把 `L_alpha` 初等性或真谓词的语义
混入分类定义。后续内部公式码分类器只需产生这里的证书，便可无损接入
YesMetaZFC 的 `IsSigmaFinite` / `IsPiFinite` 反射定理。
-/

namespace YesMetaZFC
namespace BMS
namespace ConstructibleBridge

open Logic FirstOrder

mutual
  /-- 外部成员公式的累积 `Sigma_level` 证书。 -/
  inductive ExternalIsSigmaFinite :
      {arity : Nat} -> Nat -> Constructible.FOFormula arity -> Prop where
    | mem {arity level : Nat} (left right : Fin arity) :
        ExternalIsSigmaFinite level (.mem left right)
    | eq {arity level : Nat} (left right : Fin arity) :
        ExternalIsSigmaFinite level (.eq left right)
    | neg {arity level : Nat} {body : Constructible.FOFormula arity} :
        ExternalIsPiFinite level body ->
          ExternalIsSigmaFinite level (.neg body)
    | conj {arity level : Nat} {left right : Constructible.FOFormula arity} :
        ExternalIsSigmaFinite level left ->
        ExternalIsSigmaFinite level right ->
          ExternalIsSigmaFinite level (.conj left right)
    | ex {arity level : Nat} {body : Constructible.FOFormula (arity + 1)} :
        ExternalIsSigmaFinite level body ->
          ExternalIsSigmaFinite level (.ex body)
    | lift {arity level : Nat} {formula : Constructible.FOFormula arity} :
        ExternalIsSigmaFinite level formula ->
          ExternalIsSigmaFinite (level + 1) formula
    | ofPi {arity level : Nat} {formula : Constructible.FOFormula arity} :
        ExternalIsPiFinite level formula ->
          ExternalIsSigmaFinite (level + 1) formula

  /-- 外部成员公式的累积 `Pi_level` 证书。 -/
  inductive ExternalIsPiFinite :
      {arity : Nat} -> Nat -> Constructible.FOFormula arity -> Prop where
    | mem {arity level : Nat} (left right : Fin arity) :
        ExternalIsPiFinite level (.mem left right)
    | eq {arity level : Nat} (left right : Fin arity) :
        ExternalIsPiFinite level (.eq left right)
    | neg {arity level : Nat} {body : Constructible.FOFormula arity} :
        ExternalIsSigmaFinite level body ->
          ExternalIsPiFinite level (.neg body)
    | conj {arity level : Nat} {left right : Constructible.FOFormula arity} :
        ExternalIsPiFinite level left ->
        ExternalIsPiFinite level right ->
          ExternalIsPiFinite level (.conj left right)
    | lift {arity level : Nat} {formula : Constructible.FOFormula arity} :
        ExternalIsPiFinite level formula ->
          ExternalIsPiFinite (level + 1) formula
    | ofSigma {arity level : Nat} {formula : Constructible.FOFormula arity} :
        ExternalIsSigmaFinite level formula ->
          ExternalIsPiFinite (level + 1) formula
end

/-- 外部 `Sigma` 证书经翻译后成为 YesMetaZFC 的同层证书。 -/
theorem translateExternalFormula_isSigmaFinite_l
    {arity level : Nat} {formula : Constructible.FOFormula arity}
    (hFormula : ExternalIsSigmaFinite level formula) :
    FirstOrder.Formula.IsSigmaFinite membershipLevyBound level
      (translateExternalFormula formula) := by
  exact ExternalIsSigmaFinite.rec
    (motive_1 := fun level formula _ =>
      FirstOrder.Formula.IsSigmaFinite membershipLevyBound level
        (translateExternalFormula formula))
    (motive_2 := fun level formula _ =>
      FirstOrder.Formula.IsPiFinite membershipLevyBound level
        (translateExternalFormula formula))
    (fun _ _ => .delta0 (.rel _ _))
    (fun _ _ => .delta0 (.equal _ _))
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ hBody => by
      simp only [translateExternalFormula]
      exact @FirstOrder.Formula.IsSigmaFinite.existsE
        SetTheory.signature membershipLevyBound _ _ [] SetTheory.SetSort.set
        _ hBody)
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofPi hBody)
    (fun _ _ => .delta0 (.rel _ _))
    (fun _ _ => .delta0 (.equal _ _))
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofSigma hBody)
    hFormula

/-- 外部 `Pi` 证书经翻译后成为 YesMetaZFC 的同层证书。 -/
theorem translateExternalFormula_isPiFinite_l
    {arity level : Nat} {formula : Constructible.FOFormula arity}
    (hFormula : ExternalIsPiFinite level formula) :
    FirstOrder.Formula.IsPiFinite membershipLevyBound level
      (translateExternalFormula formula) := by
  exact ExternalIsPiFinite.rec
    (motive_1 := fun level formula _ =>
      FirstOrder.Formula.IsSigmaFinite membershipLevyBound level
        (translateExternalFormula formula))
    (motive_2 := fun level formula _ =>
      FirstOrder.Formula.IsPiFinite membershipLevyBound level
        (translateExternalFormula formula))
    (fun _ _ => .delta0 (.rel _ _))
    (fun _ _ => .delta0 (.equal _ _))
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ hBody => by
      simp only [translateExternalFormula]
      exact @FirstOrder.Formula.IsSigmaFinite.existsE
        SetTheory.signature membershipLevyBound _ _ [] SetTheory.SetSort.set
        _ hBody)
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofPi hBody)
    (fun _ _ => .delta0 (.rel _ _))
    (fun _ _ => .delta0 (.equal _ _))
    (fun _ hBody => .neg hBody)
    (fun _ _ hLeft hRight => .conj hLeft hRight)
    (fun _ hBody => .lift hBody)
    (fun _ hBody => .ofSigma hBody)
    hFormula

/-- 外部 `Sigma` 证书随层级上升保持成立。 -/
theorem ExternalIsSigmaFinite.mono_l
    {arity lowerLevel upperLevel : Nat}
    {formula : Constructible.FOFormula arity}
    (hFormula : ExternalIsSigmaFinite lowerLevel formula)
    (hLevels : lowerLevel <= upperLevel) :
    ExternalIsSigmaFinite upperLevel formula := by
  induction upperLevel, hLevels using Nat.le_induction with
  | base => exact hFormula
  | succ upperLevel _ ih =>
      exact ExternalIsSigmaFinite.lift ih

/-- 外部 `Pi` 证书随层级上升保持成立。 -/
theorem ExternalIsPiFinite.mono_l
    {arity lowerLevel upperLevel : Nat}
    {formula : Constructible.FOFormula arity}
    (hFormula : ExternalIsPiFinite lowerLevel formula)
    (hLevels : lowerLevel <= upperLevel) :
    ExternalIsPiFinite upperLevel formula := by
  induction upperLevel, hLevels using Nat.le_induction with
  | base => exact hFormula
  | succ upperLevel _ ih =>
      exact ExternalIsPiFinite.lift ih

/-- 每个外部成员公式都在某个有限层同时拥有 `Sigma` 与 `Pi` 证书。 -/
theorem exists_externalFiniteLevyLevel_l
    {arity : Nat} (formula : Constructible.FOFormula arity) :
    exists level,
      ExternalIsSigmaFinite level formula /\
      ExternalIsPiFinite level formula := by
  induction formula with
  | mem left right =>
      exact ⟨0, .mem left right, .mem left right⟩
  | eq left right =>
      exact ⟨0, .eq left right, .eq left right⟩
  | neg body ih =>
      rcases ih with ⟨level, hSigma, hPi⟩
      exact ⟨level, .neg hPi, .neg hSigma⟩
  | conj left right ihLeft ihRight =>
      rcases ihLeft with ⟨leftLevel, hLeftSigma, hLeftPi⟩
      rcases ihRight with ⟨rightLevel, hRightSigma, hRightPi⟩
      let level := max leftLevel rightLevel
      have hLeftLevel : leftLevel <= level := Nat.le_max_left _ _
      have hRightLevel : rightLevel <= level := Nat.le_max_right _ _
      exact ⟨level,
        .conj (hLeftSigma.mono_l hLeftLevel)
          (hRightSigma.mono_l hRightLevel),
        .conj (hLeftPi.mono_l hLeftLevel)
          (hRightPi.mono_l hRightLevel)⟩
  | @ex arity body ih =>
      rcases ih with ⟨level, hSigma, _hPi⟩
      have hExistsSigma :
          ExternalIsSigmaFinite level
            (Constructible.FOFormula.ex body) :=
        .ex hSigma
      exact ⟨level + 1, .lift hExistsSigma, .ofSigma hExistsSigma⟩

/-- 变量重命名保持外部 `Sigma` 层级。 -/
theorem ExternalIsSigmaFinite.rename_l
    {arity level targetArity : Nat}
    {formula : Constructible.FOFormula arity}
    (hFormula : ExternalIsSigmaFinite level formula)
    (rename : Fin arity -> Fin targetArity) :
    ExternalIsSigmaFinite level (Constructible.FOFormula.rename rename formula) := by
  exact ExternalIsSigmaFinite.rec
    (motive_1 := fun {arity} level formula _ =>
      forall {targetArity}, (rename : Fin arity -> Fin targetArity) ->
        ExternalIsSigmaFinite level
          (Constructible.FOFormula.rename rename formula))
    (motive_2 := fun {arity} level formula _ =>
      forall {targetArity}, (rename : Fin arity -> Fin targetArity) ->
        ExternalIsPiFinite level
          (Constructible.FOFormula.rename rename formula))
    (fun left right _ rename => .mem (rename left) (rename right))
    (fun left right _ rename => .eq (rename left) (rename right))
    (fun _ ih _ rename => .neg (ih rename))
    (fun _ _ ihLeft ihRight _ rename =>
      .conj (ihLeft rename) (ihRight rename))
    (fun _ ih _ rename => .ex (ih (Constructible.FOFormula.liftRename rename)))
    (fun _ ih _ rename => .lift (ih rename))
    (fun _ ih _ rename => .ofPi (ih rename))
    (fun left right _ rename => .mem (rename left) (rename right))
    (fun left right _ rename => .eq (rename left) (rename right))
    (fun _ ih _ rename => .neg (ih rename))
    (fun _ _ ihLeft ihRight _ rename =>
      .conj (ihLeft rename) (ihRight rename))
    (fun _ ih _ rename => .lift (ih rename))
    (fun _ ih _ rename => .ofSigma (ih rename))
    hFormula rename

/-- 变量重命名保持外部 `Pi` 层级。 -/
theorem ExternalIsPiFinite.rename_l
    {arity level targetArity : Nat}
    {formula : Constructible.FOFormula arity}
    (hFormula : ExternalIsPiFinite level formula)
    (rename : Fin arity -> Fin targetArity) :
    ExternalIsPiFinite level (Constructible.FOFormula.rename rename formula) := by
  exact ExternalIsPiFinite.rec
    (motive_1 := fun {arity} level formula _ =>
      forall {targetArity}, (rename : Fin arity -> Fin targetArity) ->
        ExternalIsSigmaFinite level
          (Constructible.FOFormula.rename rename formula))
    (motive_2 := fun {arity} level formula _ =>
      forall {targetArity}, (rename : Fin arity -> Fin targetArity) ->
        ExternalIsPiFinite level
          (Constructible.FOFormula.rename rename formula))
    (fun left right _ rename => .mem (rename left) (rename right))
    (fun left right _ rename => .eq (rename left) (rename right))
    (fun _ ih _ rename => .neg (ih rename))
    (fun _ _ ihLeft ihRight _ rename =>
      .conj (ihLeft rename) (ihRight rename))
    (fun _ ih _ rename => .ex (ih (Constructible.FOFormula.liftRename rename)))
    (fun _ ih _ rename => .lift (ih rename))
    (fun _ ih _ rename => .ofPi (ih rename))
    (fun left right _ rename => .mem (rename left) (rename right))
    (fun left right _ rename => .eq (rename left) (rename right))
    (fun _ ih _ rename => .neg (ih rename))
    (fun _ _ ihLeft ihRight _ rename =>
      .conj (ihLeft rename) (ihRight rename))
    (fun _ ih _ rename => .lift (ih rename))
    (fun _ ih _ rename => .ofSigma (ih rename))
    hFormula rename

/-- 加入一个未使用的末变量保持外部 `Sigma` 层级。 -/
theorem ExternalIsSigmaFinite.weaken_l
    {arity level : Nat} {formula : Constructible.FOFormula arity}
    (hFormula : ExternalIsSigmaFinite level formula) :
    ExternalIsSigmaFinite level (Constructible.FOFormula.weaken formula) :=
  hFormula.rename_l Fin.castSucc

end ConstructibleBridge
end BMS
end YesMetaZFC
