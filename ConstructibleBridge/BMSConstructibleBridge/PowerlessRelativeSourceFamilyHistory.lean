import BMSConstructibleBridge.PowerlessRelativeSourceFamilyTransport
import BMSConstructibleBridge.PowerlessRelativeSourceFamilyElementaryImage
import BMSConstructibleBridge.PowerlessRelativeFiniteHullHistory
import BMSConstructibleBridge.PowerlessRelativeFiniteHullValue
import BMSConstructibleBridge.PowerlessRelativeFiniteHullClosure
import BMSConstructibleBridge.PowerlessRelativeFiniteHullExtensionality
import BMSConstructibleBridge.PowerlessRelativeFiniteHullSatisfaction
import BMSConstructibleBridge.PowerlessRelativeFiniteHullSatCoding
import BMSConstructibleBridge.PowerlessRelativeFiniteHullMaps
import BMSConstructibleBridge.PowerlessRelativeFiniteHullOmega
import BMSConstructibleBridge.PowerlessRelativeFiniteHullEvaluation
import BMSConstructibleBridge.PowerlessRelativeFiniteHullStatic
import BMSConstructibleBridge.PowerlessRelativeFiniteHullDefImage
import BMSConstructibleBridge.PowerlessMemberDefImageBoundedReading
import BMSConstructibleBridge.PowerlessRelativeMemberStaticAbsolute
import BMSConstructibleBridge.PowerlessRelativeMemberSatisfactionAbsolute
import BMSConstructibleBridge.PowerlessRelativeCutoffLimit
import BMSConstructibleBridge.PowerlessRelativeCutoffInnerLimits
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapse
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseDefImage
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseValues
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseClosure
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseBase
import BMSConstructibleBridge.PowerlessRealSeed

/-! # 同一个实际有限初等闭包像的历史捕获字段

原参数上下文前增加 B/D/A/U 四槽，原八项闭包正文、原图族、标签与
有限元素性全部保留。沿原存在量词树使用同一批图和同一个 I，只在
末端追加：若给定 f 是同一完整 Def 图上的原前史且 f∈W，则 f∈I。
capture 接口消费这一已成立守卫后，在同一完整末端直接断言 f∈I。
有限族另加求值存在式、完整有界矩阵、真实配对／二元并的四式，
以及区别成员／上邻居的两式和完整规范 Sat 矩阵及见证正文；同一 I 的实际坍缩
存在亦保留在原末端。十二个 Sat 参数均绑定，反射不依赖 I 传递。
实际 ω、九参数完整无界 Sat 和八参数完整静态公式也在同一族中；
原静态包与完整 Sat 沿原共尾 MemberW 的真实规格送入同一 MemberI，
不以 Class 静态或有界规格替代成员域中的完整规格。
原 Def 像检查器另作为八参数反射矩阵；它保留全部局部数据与行覆盖，
但不是原 global_m。指定较早极限层和原编码整包给出同一 I 内的
检查器正确性，不预供 I 内枚举或原 Def 真值。
同一 I 对实际 Def 图 D 和原前史 f 的读值封闭，且对全部已捕获、陪域
包含于真实 W 的集合函数读值封闭；完整 map 矩阵也由同 I 请求反射，
从而任意 I 内图的原规格与 MemberI 原规格同值。若原 W 具真实基础
闭包，则同一 I 也具此闭包，种子含全部 ω 时取得全部内部有限赋值。
同一实际坍缩图另保留精确实数基集的固定规格；全部 ω 和指定实数
属于 I 时才推出 B⊆I，B 自身属于 I 时才断言 H(B)=B。
这些操作资格在实际截断装配中取得，新增矩阵中的函数图是绑定变量，
f 仍不入种子。
不会把 f 加入常量种子，也不会由旧图族另选一个相似的闭包像。

对象语言为纯隶属 ℒ，背景为原 Z₂；正式出口为原 Derives 的图翻译句。
本模块是已构造图族的末端补强，历史和图条件仍明确保留；完整 Def
截迹、弱凝聚及最终候选源存在性尚未由本模块证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyHistory

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open PowerlessBMSQuotientCoding
open SecondOrderObjectSyntax (member_m)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)
open PowerlessRelativeSourceFamilyClosedImage (term_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

abbrev context_m (Δ : SortContext ℒ) := .set :: .set :: .set :: .set :: Δ

def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m (context_m Δ) :=
  PowerlessRelativeFiniteHullHistory.family_m (context_m Δ) ++
    (PowerlessRelativeFiniteHullValue.family_m (context_m Δ) ++
      (PowerlessRelativeFiniteHullClosure.family_m (context_m Δ) ++
        (PowerlessRelativeFiniteHullExtensionality.family_m (context_m Δ) ++
          (PowerlessRelativeFiniteHullSatisfaction.family_m (context_m Δ) ++
            (PowerlessRelativeFiniteHullMaps.family_m (context_m Δ) ++
              (PowerlessRelativeFiniteHullOmega.family_m (context_m Δ) ++
                (PowerlessRelativeFiniteHullEvaluation.family_m (context_m Δ) ++
                  (PowerlessRelativeFiniteHullStatic.family_m (context_m Δ) ++
                    PowerlessRelativeFiniteHullDefImage.family_m (context_m Δ)))))))))

private theorem family_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set) :
    (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ ↔
      (PowerlessRelativeFiniteElementarity.form_m
        (PowerlessRelativeFiniteHullHistory.family_m (context_m Δ)) I W τ).satisfies ζ ∧
      (PowerlessRelativeFiniteElementarity.form_m
        (PowerlessRelativeFiniteHullValue.family_m (context_m Δ)) I W τ).satisfies ζ ∧
      (PowerlessRelativeFiniteElementarity.form_m
        (PowerlessRelativeFiniteHullClosure.family_m (context_m Δ)) I W τ).satisfies ζ ∧
      (PowerlessRelativeFiniteElementarity.form_m
        (PowerlessRelativeFiniteHullExtensionality.family_m (context_m Δ)) I W τ).satisfies ζ ∧
      (PowerlessRelativeFiniteElementarity.form_m
        (PowerlessRelativeFiniteHullSatisfaction.family_m (context_m Δ)) I W τ).satisfies ζ ∧
      (PowerlessRelativeFiniteElementarity.form_m
        (PowerlessRelativeFiniteHullMaps.family_m (context_m Δ)) I W τ).satisfies ζ ∧
      (PowerlessRelativeFiniteElementarity.form_m
        (PowerlessRelativeFiniteHullOmega.family_m (context_m Δ)) I W τ).satisfies ζ ∧
      (PowerlessRelativeFiniteElementarity.form_m
        (PowerlessRelativeFiniteHullEvaluation.family_m (context_m Δ)) I W τ).satisfies ζ ∧
      (PowerlessRelativeFiniteElementarity.form_m
        (PowerlessRelativeFiniteHullStatic.family_m (context_m Δ)) I W τ).satisfies ζ ∧
      (PowerlessRelativeFiniteElementarity.form_m
        (PowerlessRelativeFiniteHullDefImage.family_m (context_m Δ)) I W τ).satisfies ζ := by
  rw [family_m, PowerlessRelativeFiniteElementarity.append_formula_l,
    PowerlessRelativeFiniteElementarity.append_formula_l,
    PowerlessRelativeFiniteElementarity.append_formula_l,
    PowerlessRelativeFiniteElementarity.append_formula_l,
    PowerlessRelativeFiniteElementarity.append_formula_l,
    PowerlessRelativeFiniteElementarity.append_formula_l,
    PowerlessRelativeFiniteElementarity.append_formula_l,
    PowerlessRelativeFiniteElementarity.append_formula_l,
    PowerlessRelativeFiniteElementarity.append_formula_l]

/-- 原轻量历史矩阵及其存在式，仍属于同一个共同反射族。 -/
theorem history_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeFiniteHullHistory.family_m (context_m Δ)) I W τ).satisfies ζ :=
  ((family_formula_l ζ I W τ).mp h).1

/-- 原共同族的四项基础操作字段，仍是同一实际 I/W。 -/
theorem closure_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeFiniteHullClosure.family_m (context_m Δ)) I W τ).satisfies ζ :=
  ((family_formula_l ζ I W τ).mp h).2.2.1

/-- 同一完整共同族给出真实闭包和配对矩阵读数，不预供 I 的真实闭包。 -/
theorem closure_member_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    {I₀ W₀ : SecondOrderQuotient.type_l hℳ} {Δ Ε : SortContext ℒ}
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (hI : I.eval ζ = I₀) (hW : W.eval ζ = W₀)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ) W₀)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    PowerlessRelativeFiniteHullClosure.pair_matrix_reflection_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀ ∧
        PowerlessRelativeFiniteHullAssignments.closed_l
          (𝒩 := SecondOrderQuotient.structure_l hℳ) I₀ := by
  have hField := closure_l ζ I W τ h
  have hRead := (PowerlessRelativeFiniteHullClosure.family_formula_l ζ I W τ).mp hField
  rw [hI, hW] at hRead
  exact ⟨hRead.2.1, PowerlessRelativeFiniteHullClosure.closure_l ζ I W τ
    (fun a b => SecondOrderPairObjects.pair_exists_l hℳ a b)
    (PowerlessRelativeFiniteHullClosure.binary_exists_l hℳ)
    (fun a b hz => SecondOrderQuotient.ext_l hℳ a b hz)
    hTrans hClosed hIW hI hW hField⟩

/-- 原共同族的真实闭包送入同一个实际坍缩目标，不预供目标闭包。 -/
theorem closure_image_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    {I₀ W₀ T H : SecondOrderQuotient.type_l hℳ} {Δ Ε : SortContext ℒ}
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ) W₀)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I₀ T H) :
    PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := SecondOrderQuotient.structure_l hℳ) T :=
  PowerlessRelativeMembershipCollapseClosure.closed_l hH
    (closure_member_l ζ I W τ hI₀ hW₀ hTrans hClosed hIW h).2

/-- 原共同族与实际 ω 守卫给出目标 T 的全部内部有限赋值。 -/
theorem assignments_image_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    {I₀ W₀ T H n A f : SecondOrderQuotient.type_l hℳ} {Δ Ε : SortContext ℒ}
    (K : source_coding_l hℳ) (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ) W₀)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I₀ T H)
    (hωI : ∀ x, SecondOrderQuotient.mem_l hℳ x K.omega →
      SecondOrderQuotient.mem_l hℳ x I₀)
    (hn : SecondOrderQuotient.mem_l hℳ n K.omega)
    (hf : SecondOrderFunctionObjects.map_l hℳ f n A)
    (hValues : ∀ x y, SecondOrderFunctionObjects.value_l hℳ f x y →
      SecondOrderQuotient.mem_l hℳ y T) : SecondOrderQuotient.mem_l hℳ f T :=
  PowerlessRelativeMembershipCollapseClosure.assignments_l K hH
    (closure_member_l ζ I W τ hI₀ hW₀ hTrans hClosed hIW h).2 hωI hn hf hValues

/-- 共同族的同一 I 与实际坍缩运输任意原关系值，不要求关系是函数。 -/
theorem value_image_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    {I₀ W₀ T H : SecondOrderQuotient.type_l hℳ} {Δ Ε : SortContext ℒ}
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ) W₀)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hI : ∃ x, SecondOrderQuotient.mem_l hℳ x I₀)
    (hT : ∃ x, SecondOrderQuotient.mem_l hℳ x T)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I₀ T H)
    (f a b : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀)
    (g x y : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) T)
    (hfg : PowerlessMemberCollapseTransport.relation_l H f g)
    (hax : PowerlessMemberCollapseTransport.relation_l H a x)
    (hby : PowerlessMemberCollapseTransport.relation_l H b y) :
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val a.val b.val ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g.val x.val y.val := by
  have hRead := closure_member_l ζ I W τ hI₀ hW₀ hTrans hClosed hIW h
  exact PowerlessRelativeMembershipCollapseValues.model_l hI hT hH hTrans hIW
    hRead.1 hRead.2.1 f a b g x y hfg hax hby

/-- 同一共同族直接保持旧翻译使用的全部内部数字坐标。 -/
theorem numeric_image_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    {I₀ W₀ T H : SecondOrderQuotient.type_l hℳ} {Δ Ε : SortContext ℒ}
    (K : source_coding_l hℳ) (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ) W₀)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hI : ∃ x, SecondOrderQuotient.mem_l hℳ x I₀)
    (hT : ∃ x, SecondOrderQuotient.mem_l hℳ x T)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I₀ T H)
    (hωI : ∀ x, SecondOrderQuotient.mem_l hℳ x K.omega →
      SecondOrderQuotient.mem_l hℳ x I₀)
    (f : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀)
    (g : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) T)
    (hfg : PowerlessMemberCollapseTransport.relation_l H f g) :
    ∀ n s : SecondOrderModel.num_l ℳ,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ)
        f.val (PowerlessFormulaValidityReading.code_l K n) (PowerlessFormulaValidityReading.code_l K s) ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ)
        g.val (PowerlessFormulaValidityReading.code_l K n) (PowerlessFormulaValidityReading.code_l K s) := by
  have hRead := closure_member_l ζ I W τ hI₀ hW₀ hTrans hClosed hIW h
  exact PowerlessRelativeMembershipCollapseValues.numeric_l K hI hT hH hTrans hIW
    hRead.1 hRead.2.1 hωI f g hfg

/-- 消费原共同族的完整 Sat 矩阵字段，不要求重新构造请求树。 -/
theorem satisfaction_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeFiniteHullSatisfaction.family_m (context_m Δ)) I W τ).satisfies ζ :=
  ((family_formula_l ζ I W τ).mp h).2.2.2.2.1

/-- 同一个 I 的完整 map 反射字段；不预供映射绝对性。 -/
theorem maps_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeFiniteHullMaps.family_m (context_m Δ)) I W τ).satisfies ζ :=
  ((family_formula_l ζ I W τ).mp h).2.2.2.2.2.1

/-- 原共同族保留实际 ω 原公式的元素性，不将其误分类为 Δ₀。 -/
theorem omega_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeFiniteHullOmega.family_m (context_m Δ)) I W τ).satisfies ζ :=
  ((family_formula_l ζ I W τ).mp h).2.2.2.2.2.2.1

/-- 同一实际 I 的完整原 Sat 公式元素性，不以有界检查器替代。 -/
theorem evaluation_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeFiniteHullEvaluation.family_m (context_m Δ)) I W τ).satisfies ζ :=
  ((family_formula_l ζ I W τ).mp h).2.2.2.2.2.2.2.1

/-- 原共同族中的八参数完整静态公式字段，与其他字段共用同一 I。 -/
theorem static_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeFiniteHullStatic.family_m (context_m Δ)) I W τ).satisfies ζ :=
  ((family_formula_l ζ I W τ).mp h).2.2.2.2.2.2.2.2.1

/-- 原 Def 像检查器的实际字段，与历史和完整编码共用同一 I。 -/
theorem def_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (PowerlessRelativeFiniteElementarity.form_m
      (PowerlessRelativeFiniteHullDefImage.family_m (context_m Δ)) I W τ).satisfies ζ :=
  ((family_formula_l ζ I W τ).mp h).2.2.2.2.2.2.2.2.2

/-- 原编码包和真实 Def 输出给出同一 MemberI 的完整检查器；不要求 I 内枚举。 -/
theorem def_member_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    {B β U I₀ W₀ : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (K : source_coding_l hℳ)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hU : PowerlessRelativeHierarchySemantics.level_l hℳ B β U)
    {ω e t₁ t₂ t₃ T N F Q G : PowerlessRelativeClassStructure.type_l hℳ B}
    {C : SecondOrderModel.set_l ℳ}
    (hωU : SecondOrderQuotient.mem_l hℳ ω.val U)
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l (W := U) hBase K ω e t₁ t₂ t₃ T N F Q G C)
    {Δ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (hI : ∃ x, SecondOrderQuotient.mem_l hℳ x I₀)
    (ν : Env (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
      [] (context_m Δ))
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, SecondOrderQuotient.mem_l hℳ x W₀ → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    {A D : SecondOrderQuotient.type_l hℳ} (hAU : SecondOrderQuotient.mem_l hℳ A U)
    (η : Env (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
      PowerlessRelativeFiniteHullDefImage.context_m (context_m Δ))
    (hη : ∀ v : Variable PowerlessRelativeFiniteHullDefImage.context_m .set,
      (η.boundVal v).val =
        (PowerlessRelativeFiniteHullDefImage.env_l (PowerlessRelativization.env_l ν)
          ω.val e.val N.val Q.val U G.val A D).boundVal v) :
    SecondOrderMemberDef.spec_l hℳ A D ↔
      (PowerlessRelativeFiniteHullDefImage.matrix_m (context_m Δ)).satisfies η := by
  have hModel := PowerlessRelativeFiniteHullDefImage.model_l hI ζ I W τ ν hτ
    hI₀ hW₀ hW hIW (def_l ζ I W τ h)
    (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.here)))))))))
    (η.boundVal (.there (.there (.there (.there (.there (.there (.here))))))))
    (η.boundVal (.there (.there (.there (.there (.there (.here)))))))
    (η.boundVal (.there (.there (.there (.there (.here))))))
    (η.boundVal (.there (.there (.there (.here)))))
    (η.boundVal (.there (.there (.here))))
    (η.boundVal (.there (.here)))
    (η.boundVal (.here))
  have hRead := PowerlessRelativeFiniteHullDefImage.formula_l η
  have hRaw := hModel.trans hRead.symm
  simp only [hη, PowerlessRelativeFiniteHullDefImage.env_l,
    Env.pushBound_bound_here, Env.pushBound_bound_there] at hRaw
  exact (PowerlessMemberDefImageBoundedReading.checkeriff_l hBase K hLimit hU
    hωU hCoding hAU).symm.trans hRaw

/-- 同一实际 I 内的 ω 满足原最小归纳集定义；无需 I 传递。 -/
theorem omega_model_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} {I₀ W₀ : carrier_l 𝒩}
    (hI : ∃ x, member_l 𝒩 x I₀) (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (ν : Env (PowerlessMemberStructure.structure_l I₀ hI) [] (context_m Δ))
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, member_l 𝒩 x W₀ → ∀ y, member_l 𝒩 y x → member_l 𝒩 y W₀)
    (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (ω : PowerlessMemberStructure.type_l (ℳ := 𝒩) I₀)
    (hω : ThirdOrderSemantics.omega_l (ℳ := 𝒩) ω.val) :
    ThirdOrderSemantics.omega_l (ℳ := PowerlessMemberStructure.structure_l I₀ hI) ω :=
  PowerlessRelativeFiniteHullOmega.model_l hI ζ I W τ ν hτ hI₀ hW₀ hW hIW
    (omega_l ζ I W τ h) ω hω

/-- 原共同族直接恢复 I 内的真实 Seq/Sat 见证，消费同一原共尾编码包。 -/
theorem satisfaction_capture_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B U I₀ W₀ : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (K : source_coding_l hℳ)
    {ω e t₁ t₂ t₃ T N F Q G : PowerlessRelativeClassStructure.type_l hℳ B} {C : SecondOrderModel.set_l ℳ}
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l (W := U) hBase K ω e t₁ t₂ t₃ T N F Q G C)
    {Δ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (ν : Env (SecondOrderQuotient.structure_l hℳ) [] (context_m Δ)) (hτ : ∀ v, (τ v).eval ζ = ν.freeVal v)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, SecondOrderQuotient.mem_l hℳ x W₀ → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (hFree : ∀ v : Variable (context_m Δ) .set, SecondOrderQuotient.mem_l hℳ (ν.freeVal v) I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m
      (family_m Δ) I W τ).satisfies ζ)
    {A R : SecondOrderQuotient.type_l hℳ}
    (hBound : ∀ v : Variable PowerlessRelativeFiniteHullSatisfaction.context_m .set,
      SecondOrderQuotient.mem_l hℳ
        ((PowerlessRelativeFiniteHullSatCoding.env_l ν ω.val A e.val N.val T.val U
          t₁.val t₂.val t₃.val F.val R).boundVal v) I₀)
    (hValue : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val A R) :
    ∃ S, SecondOrderQuotient.mem_l hℳ S I₀ ∧ SecondOrderQuotient.mem_l hℳ S U ∧
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val A S ∧
      PowerlessSatisfactionSpecification.spec_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val A e.val t₁.val t₂.val t₃.val T.val F.val R ∧
      PowerlessSatisfactionGraphClean.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) ω.val S R := by
  exact PowerlessRelativeFiniteHullSatCoding.capture_l hBase K hCoding ζ I W τ ν hτ
    hI₀ hW₀ hW hIW hFree (satisfaction_l ζ I W τ h) hBound hValue

/-- 同一实际 S 具两侧完整 Seq，且 MemberI 的实际 ω 正确；不新增见证前提。 -/
theorem satisfaction_member_sequences_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B U I₀ W₀ : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (K : source_coding_l hℳ)
    {ω e t₁ t₂ t₃ T N F Q G : PowerlessRelativeClassStructure.type_l hℳ B} {C : SecondOrderModel.set_l ℳ}
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l (W := U) hBase K ω e t₁ t₂ t₃ T N F Q G C)
    {Δ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (hI : ∃ x, SecondOrderQuotient.mem_l hℳ x I₀)
    (ν : Env (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
      [] (context_m Δ)) (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, SecondOrderQuotient.mem_l hℳ x W₀ → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m
      (family_m Δ) I W τ).satisfies ζ)
    {A R : SecondOrderQuotient.type_l hℳ}
    (hBound : ∀ v : Variable PowerlessRelativeFiniteHullSatisfaction.context_m .set,
      SecondOrderQuotient.mem_l hℳ
        ((PowerlessRelativeFiniteHullSatCoding.env_l (PowerlessRelativization.env_l ν)
          ω.val A e.val N.val T.val U t₁.val t₂.val t₃.val F.val R).boundVal v) I₀)
    (hValue : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val A R)
    (hωI : ∀ n, SecondOrderQuotient.mem_l hℳ n ω.val → SecondOrderQuotient.mem_l hℳ n I₀) :
    ∃ S : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀,
      SecondOrderQuotient.mem_l hℳ S.val U ∧
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val A S.val ∧
      ThirdOrderSemantics.omega_l
        (ℳ := PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
        ⟨ω.val, hBound (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))⟩ ∧
      PowerlessFiniteSequencesSyntax.spec_l
        (ℳ := PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
        ⟨ω.val, hBound (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))⟩
        ⟨A, hBound (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))⟩ S ∧
      PowerlessSatisfactionSpecification.spec_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val A e.val t₁.val t₂.val t₃.val T.val F.val R ∧
      PowerlessSatisfactionGraphClean.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) ω.val S.val R := by
  obtain ⟨S, hSI, hSU, hSeq, hSat, hClean⟩ := satisfaction_capture_l hBase K hCoding
    ζ I W τ (PowerlessRelativization.env_l ν) hτ hI₀ hW₀ hW hIW
    (fun v => (ν.freeVal v).property) h hBound hValue
  let S₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ := ⟨S, hSI⟩
  have hωRaw : ThirdOrderSemantics.omega_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val :=
    hCoding.omega_eq.symm ▸ K.omega_spec
  refine ⟨S₀, hSU, hSeq, ?_, ?_, hSat, hClean⟩
  · exact omega_model_l hI ζ I W τ ν hτ hI₀ hW₀ hW hIW h
      ⟨ω.val, hBound (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))⟩ hωRaw
  · exact PowerlessRelativeFiniteHullMaps.sequences_l hI ζ I W τ ν hτ hI₀ hW₀ hW hIW
      (maps_l ζ I W τ h) ⟨ω.val, hBound (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))⟩
      ⟨A, hBound (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))⟩ S₀ hωI hSeq

/-- 同一个 G 的原 Sat 读值在 MemberI 满足完整规格，资格来自原首不可数截断。 -/
theorem satisfaction_member_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    {B U I₀ W₀ Ω : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (K : source_coding_l hℳ)
    {ω e t₁ t₂ t₃ T N F Q G : PowerlessRelativeClassStructure.type_l hℳ B}
    {C : SecondOrderModel.set_l ℳ}
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l (W := U) hBase K ω e t₁ t₂ t₃ T N F Q G C)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω.val Ω)
    (hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W₀)
    {Δ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (hI : ∃ x, SecondOrderQuotient.mem_l hℳ x I₀)
    (ν : Env (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
      [] (context_m Δ)) (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    {A R : SecondOrderQuotient.type_l hℳ}
    (hBound : ∀ v : Variable PowerlessRelativeFiniteHullSatisfaction.context_m .set,
      SecondOrderQuotient.mem_l hℳ
        ((PowerlessRelativeFiniteHullSatCoding.env_l (PowerlessRelativization.env_l ν)
          ω.val A e.val N.val T.val U t₁.val t₂.val t₃.val F.val R).boundVal v) I₀)
    (hValue : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val A R) :
    PowerlessSatisfactionSpecification.spec_l
      (𝒩 := PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
      ⟨ω.val, hBound (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))⟩
      ⟨A, hBound (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))⟩
      ⟨e.val, hBound (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))⟩
      ⟨t₁.val, hBound (.there (.there (.there (.there (.here)))))⟩
      ⟨t₂.val, hBound (.there (.there (.there (.here))))⟩
      ⟨t₃.val, hBound (.there (.there (.here)))⟩
      ⟨T.val, hBound (.there (.there (.there (.there (.there (.there (.there (.here))))))))⟩
      ⟨F.val, hBound (.there (.here))⟩
      ⟨R, hBound (.here)⟩ := by
  have hTrans : ∀ x, SecondOrderQuotient.mem_l hℳ x W₀ → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y W₀ :=
    PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel
  obtain ⟨_, _, _, _, hSat, _⟩ := satisfaction_capture_l hBase K hCoding
    ζ I W τ (PowerlessRelativization.env_l ν) hτ hI₀ hW₀ hTrans hIW
    (fun v => (ν.freeVal v).property) h hBound hValue
  let ω₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨ω.val, hBound (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))⟩
  let A₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨A, hBound (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))⟩
  let e₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨e.val, hBound (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))⟩
  let t₁₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨t₁.val, hBound (.there (.there (.there (.there (.here)))))⟩
  let t₂₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨t₂.val, hBound (.there (.there (.there (.here))))⟩
  let t₃₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨t₃.val, hBound (.there (.there (.here)))⟩
  let T₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨T.val, hBound (.there (.there (.there (.there (.there (.there (.there (.here))))))))⟩
  let F₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨F.val, hBound (.there (.here))⟩
  let R₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨R, hBound (.here)⟩
  have hNonempty : ∃ x, SecondOrderQuotient.mem_l hℳ x W₀ :=
    ⟨ω.val, hIW _ ω₀.property⟩
  have hωRaw : SecondOrderOmega.omega_l hℳ ω.val := hCoding.omega_eq.symm ▸ K.omega_spec
  have he : ∀ x, ¬SecondOrderQuotient.mem_l hℳ x e.val :=
    (PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp hCoding.static.1.1
  obtain ⟨_, _, _, _, _, hT, _, _⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l (hBase := hBase) K hCoding.omega_eq hCoding.static
  have hTω : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val ω.val ω.val := by
    simpa only [hCoding.omega_eq] using hT
  have hSatW : PowerlessSatisfactionSpecification.spec_l
      (𝒩 := PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) W₀ hNonempty)
      (PowerlessSourceInclusion.inclusion_l hIW ω₀)
      (PowerlessSourceInclusion.inclusion_l hIW A₀)
      (PowerlessSourceInclusion.inclusion_l hIW e₀)
      (PowerlessSourceInclusion.inclusion_l hIW t₁₀)
      (PowerlessSourceInclusion.inclusion_l hIW t₂₀)
      (PowerlessSourceInclusion.inclusion_l hIW t₃₀)
      (PowerlessSourceInclusion.inclusion_l hIW T₀)
      (PowerlessSourceInclusion.inclusion_l hIW F₀)
      (PowerlessSourceInclusion.inclusion_l hIW R₀) :=
    PowerlessRelativeMemberSatisfactionAbsolute.guarded_l hBase
      (PowerlessRelativeCutoffLimit.limit_l K hBase hωRaw hΩ) hLevel
      (PowerlessRelativeCutoffInnerLimits.cofinal_l K hBase hωRaw hΩ) hωRaw he hTω hSat
  exact (PowerlessRelativeFiniteHullEvaluation.model_l hI hNonempty ζ I W τ ν hτ hI₀ hW₀ hIW
    (evaluation_l ζ I W τ h) ω₀ A₀ e₀ t₁₀ t₂₀ t₃₀ T₀ F₀ R₀).mp hSatW

/-- 同一实际编码包在 MemberI 满足完整静态规格；极限与共尾资格取自原截断。 -/
theorem static_member_l
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    {B U I₀ W₀ Ω : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (K : source_coding_l hℳ)
    {ω e t₁ t₂ t₃ T N F Q G : PowerlessRelativeClassStructure.type_l hℳ B}
    {C : SecondOrderModel.set_l ℳ}
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l (W := U) hBase K ω e t₁ t₂ t₃ T N F Q G C)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω.val Ω)
    (hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W₀)
    {Δ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (hI : ∃ x, SecondOrderQuotient.mem_l hℳ x I₀)
    (ν : Env (PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
      [] (context_m Δ)) (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hBound : ∀ v : Variable PowerlessRelativeFiniteHullStatic.context_m .set,
      SecondOrderQuotient.mem_l hℳ
        ((PowerlessRelativeFiniteHullStatic.env_l (PowerlessRelativization.env_l ν)
          ω.val e.val t₁.val t₂.val t₃.val T.val N.val F.val).boundVal v) I₀) :
    PowerlessSatisfactionExistenceSyntax.static_l
      (𝒩 := PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ hI)
      ⟨ω.val, hBound (.there (.there (.there (.there (.there (.there (.there .here)))))))⟩
      ⟨e.val, hBound (.there (.there (.there (.there (.there (.there .here))))))⟩
      ⟨t₁.val, hBound (.there (.there (.there (.there (.there .here)))))⟩
      ⟨t₂.val, hBound (.there (.there (.there (.there .here))))⟩
      ⟨t₃.val, hBound (.there (.there (.there .here)))⟩
      ⟨T.val, hBound (.there (.there .here))⟩
      ⟨N.val, hBound (.there .here)⟩ ⟨F.val, hBound .here⟩ := by
  let ω₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨ω.val, hBound (.there (.there (.there (.there (.there (.there (.there .here)))))))⟩
  let e₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨e.val, hBound (.there (.there (.there (.there (.there (.there .here))))))⟩
  let t₁₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨t₁.val, hBound (.there (.there (.there (.there (.there .here)))))⟩
  let t₂₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨t₂.val, hBound (.there (.there (.there (.there .here))))⟩
  let t₃₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨t₃.val, hBound (.there (.there (.there .here)))⟩
  let T₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨T.val, hBound (.there (.there .here))⟩
  let N₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨N.val, hBound (.there .here)⟩
  let F₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ :=
    ⟨F.val, hBound .here⟩
  have hNonempty : ∃ x, SecondOrderQuotient.mem_l hℳ x W₀ :=
    ⟨ω.val, hIW _ ω₀.property⟩
  have hωRaw : SecondOrderOmega.omega_l hℳ ω.val := hCoding.omega_eq.symm ▸ K.omega_spec
  have hStaticW : PowerlessSatisfactionExistenceSyntax.static_l
      (𝒩 := PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) W₀ hNonempty)
      (PowerlessSourceInclusion.inclusion_l hIW ω₀)
      (PowerlessSourceInclusion.inclusion_l hIW e₀)
      (PowerlessSourceInclusion.inclusion_l hIW t₁₀)
      (PowerlessSourceInclusion.inclusion_l hIW t₂₀)
      (PowerlessSourceInclusion.inclusion_l hIW t₃₀)
      (PowerlessSourceInclusion.inclusion_l hIW T₀)
      (PowerlessSourceInclusion.inclusion_l hIW N₀)
      (PowerlessSourceInclusion.inclusion_l hIW F₀) :=
    PowerlessRelativeMemberStaticAbsolute.spec_l K hBase
      (PowerlessRelativeCutoffLimit.limit_l K hBase hωRaw hΩ) hLevel
      (PowerlessRelativeCutoffInnerLimits.cofinal_l K hBase hωRaw hΩ)
      hCoding.omega_eq hCoding.static
  exact (PowerlessRelativeFiniteHullStatic.model_l hI hNonempty ζ I W τ ν hτ hI₀ hW₀ hIW
    (static_l ζ I W τ h) ω₀ e₀ t₁₀ t₂₀ t₃₀ T₀ N₀ F₀).mp hStaticW

private abbrev Entry (Ε : SortContext ℒ) := Term ℒ [] Ε .set × Term ℒ [] Ε .set
private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev free {Ε : SortContext ℒ} (t : Term ℒ [] Ε .set) :=
  t.weakenFree SetTheory.SetSort.set

private def binding_m {Ε : SortContext ℒ} : Substitution ℒ [] (.set :: Ε) [.set] Ε :=
  .map (fun v => nomatch v) (fun {s} v => match s with
    | .set => match v with
      | .here => .bvar .here
      | .there v => .fvar v)

private def elementary_m {Δ Ε : SortContext ℒ}
    (W : Term ℒ [] Ε .set) (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set) :
    Formula ℒ [.set] Ε :=
  (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) (.fvar .here) (free W)
    (fun v => free (τ v))).substitute binding_m

private theorem elementary_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Ε : SortContext ℒ} (W : Term ℒ [] Ε .set)
    (τ : Variable (context_m Δ) .set → Term ℒ [] Ε .set)
    (ζ : Env 𝒩 [] Ε) (I : carrier_l 𝒩) :
    (elementary_m (Δ := Δ) W τ).satisfies (ζ.pushBound I) ↔
      (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) (.fvar .here) (free W)
        (fun v => free (τ v))).satisfies (ζ.pushFree I) := by
  rw [elementary_m, Formula.satisfies_substitute]
  have h : (ζ.pushBound I).pullback binding_m = ζ.pushFree I := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; cases v <;> rfl
  rw [h]

private def original_m {Θ Δ : SortContext ℒ}
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) (v : Variable (context_m Δ) .set) : Term ℒ [] Θ .set :=
  τ (PowerlessSourceOpening.skip_m
    (PowerlessRelativeFiniteRequestFamilyClosure.requests_m (family_m Δ)).length v)

def guard_m {Γ Ε : SortContext ℒ} (B D A U W f : Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .conj (PowerlessNaturalOrder.transitive_m W) <|
    .conj (PowerlessRelativeCofinalDefGraph.graph_m U D) <|
      .conj (PowerlessRelativeHierarchySyntax.ordinal_m A) <|
        .conj (PowerlessRelativeHierarchySyntax.history_m B A f U) (member_m f W)

theorem guard_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} (K : source_coding_l hℳ)
    {Γ Ε : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Ε)
    (B D A U W f : Term ℒ Γ Ε .set) :
    (guard_m B D A U W f).satisfies η ↔
      (∀ x y, SecondOrderQuotient.mem_l hℳ x (W.eval η) →
        SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y (W.eval η)) ∧
      PowerlessRelativeCofinalDefGraph.graph_l (U.eval η) (D.eval η) ∧
      SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
        (A.eval η) ∧ PowerlessRelativeHierarchySemantics.history_l hℳ
          (B.eval η) (A.eval η) (f.eval η) (U.eval η) ∧
            SecondOrderQuotient.mem_l hℳ (f.eval η) (W.eval η) := by
  simp only [guard_m, Formula.satisfies, PowerlessNaturalOrder.transitive_formula_l,
    PowerlessNaturalOrder.transitive_l,
    PowerlessRelativeCofinalDefGraph.graph_formula_l K,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeHierarchySemantics.history_formula_l K,
    member_m, Arguments.eval, SecondOrderQuotient.structure_l]
  rfl

/-- 原完整末端保留，再对同一 I 追加原历史捕获。 -/
def terminal_m {Θ Δ Ε : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε)) : Formula ℒ [] Ε :=
  let ρ := fun v => term_m (original_m (Δ := Δ) τ v) σ
  .existsE .set <| .conj
    (PowerlessRelativeSourceFamilyElementaryImage.body_m J (term_m B σ) (term_m C σ)
      (term_m W σ) (term_m ω σ) (term_m Q σ) (term_m e σ) (term_m t₀ σ)
      (term_m t₁ σ) (term_m t₂ σ) (term_m a σ) (term_m P σ)) <|
    .conj (elementary_m (Δ := Δ) (term_m W σ) ρ) <|
      .conj (parameters_m (context_m Δ) (.bvar .here) (fun v => up (ρ v))) <|
        .imp (guard_m (up (ρ .here)) (up (ρ (.there .here)))
          (up (ρ (.there (.there .here)))) (up (ρ (.there (.there (.there .here)))))
          (up (term_m W σ)) (up (term_m f σ)))
          (member_m (up (term_m f σ)) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem terminal_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ Ε : SortContext ℒ} (B C W ω Q e t₀ t₁ t₂ a P f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set)
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε))
    (h : (PowerlessRelativeSourceFamilyElementaryImage.terminal_m (family_m Δ)
      B C W ω Q e t₀ t₁ t₂ a P τ σ J).satisfies ζ) :
    (terminal_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P f τ σ J).satisfies ζ := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  let ρ : Variable (context_m Δ) .set → Term ℒ [] Ε .set :=
    fun v => term_m (original_m (Δ := Δ) τ v) σ
  let w := term_m W σ
  change ∃ I, (PowerlessRelativeSourceFamilyElementaryImage.body_m J (term_m B σ)
    (term_m C σ) w (term_m ω σ) (term_m Q σ) (term_m e σ) (term_m t₀ σ)
    (term_m t₁ σ) (term_m t₂ σ) (term_m a σ) (term_m P σ)).satisfies (ζ.pushBound I) ∧
    (elementary_m (Δ := Δ) w ρ).satisfies (ζ.pushBound I) ∧
    (parameters_m (context_m Δ) (.bvar .here) (fun v => up (ρ v))).satisfies (ζ.pushBound I) at h
  obtain ⟨I, hBody, hElem, hParams⟩ := h
  change ∃ I, (PowerlessRelativeSourceFamilyElementaryImage.body_m J (term_m B σ)
    (term_m C σ) w (term_m ω σ) (term_m Q σ) (term_m e σ) (term_m t₀ σ)
    (term_m t₁ σ) (term_m t₂ σ) (term_m a σ) (term_m P σ)).satisfies (ζ.pushBound I) ∧
    (elementary_m (Δ := Δ) w ρ).satisfies (ζ.pushBound I) ∧
    (parameters_m (context_m Δ) (.bvar .here) (fun v => up (ρ v))).satisfies (ζ.pushBound I) ∧
    ((guard_m (up (ρ .here)) (up (ρ (.there .here)))
      (up (ρ (.there (.there .here)))) (up (ρ (.there (.there (.there .here)))))
      (up w) (up (term_m f σ))).satisfies (ζ.pushBound I) →
      (member_m (up (term_m f σ)) (.bvar .here)).satisfies (ζ.pushBound I))
  refine ⟨I, hBody, hElem, hParams, ?_⟩
  intro hg
  simp only [guard_m, Formula.satisfies, PowerlessNaturalOrder.transitive_formula_l,
    PowerlessRelativeCofinalDefGraph.graph_formula_l K,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeHierarchySemantics.history_formula_l K,
    member_m, Arguments.eval, up, Term.eval_weakenBound, SecondOrderQuotient.structure_l] at hg
  obtain ⟨hW, hGraph, hA, hf, hfW⟩ := hg
  have hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I (w.eval ζ) := by
    simpa only [ThirdOrderSemantics.subset_formula_l, subset_l, ThirdOrderSemantics.member_l,
      up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here,
      SecondOrderQuotient.structure_l] using hBody.2.2.1
  have hρ : ∀ v : Variable (context_m Δ) .set,
      SecondOrderQuotient.mem_l hℳ ((ρ v).eval ζ) I := by
    have h := (parameters_formula_l (context_m Δ) (ζ.pushBound I) (.bvar .here)
      (fun v => up (ρ v))).mp hParams
    intro v
    simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here,
      SecondOrderQuotient.structure_l] using h _ v
  let ν : Env (SecondOrderQuotient.structure_l hℳ) [] (context_m Δ) :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (ρ v).eval ζ }
  have hElem' := (elementary_formula_l (Δ := Δ) w ρ ζ I).mp hElem
  have hParts := (family_formula_l (Δ := Δ) (ζ.pushFree I) (.fvar .here)
    (free w) (fun v => free (ρ v))).mp hElem'
  have hfI := PowerlessRelativeFiniteHullHistory.member_l hℳ
    (Δ := context_m Δ) (I₀ := I) (W₀ := w.eval ζ)
    (B := (ρ .here).eval ζ) (D := (ρ (.there .here)).eval ζ)
    (A := (ρ (.there (.there .here))).eval ζ)
    (U := (ρ (.there (.there (.there .here)))).eval ζ) (f := (term_m f σ).eval ζ)
    (ζ.pushFree I) (.fvar .here) (free w) (fun v => free (ρ v)) ν
    (fun v => by simp only [free, Term.eval_weakenFree, ν])
    hρ rfl (by simp only [free, Term.eval_weakenFree])
    (fun x hx y hy => hW x y hx hy) hIW (hρ .here) (hρ (.there .here))
    (hρ (.there (.there .here))) (hρ (.there (.there (.there .here))))
    hParts.1 hGraph hA hf hfW
  simpa only [member_m, Formula.satisfies, Arguments.eval, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, SecondOrderQuotient.structure_l] using hfI

def conclusion_m {Θ Δ : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let Ψ := PowerlessRelativeFiniteRequestFamilyClosure.requests_m (family_m Δ)
  let m := Ψ.length
  PowerlessRelativeSourceFamilyExtension.extension_m
    (terminal_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P f τ)
    (PowerlessRelativeFiniteRequestFamilyClosure.family_m m Ψ)
    (PowerlessSourceRequestParameters.tags_m (context_m Δ) m) B W R τ [] (fun v => .fvar v)

-- 后续仅消费已证历史族，不在装配参数统一时展开请求树。
attribute [local irreducible] family_m

/-- 常量像含整个种子；原 W 闭包和 ω 种子守卫给同一 I 的实际有限赋值。 -/
def closure_m {Γ Ε : SortContext ℒ} (C W ω I : Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .conj (ThirdOrderTheory.subset_m C I) <|
    .imp (PowerlessRelativeFiniteHullAssignments.closed_m W) <|
      .conj (PowerlessRelativeFiniteHullAssignments.closed_m I) <|
        .imp (SecondOrderOmegaSyntax.omega_m ω) <|
          .imp (ThirdOrderTheory.subset_m ω C) (PowerlessRelativeFiniteHullAssignments.finite_m I ω)

/-- 原绑定 I 上的外延性和上邻居句；W 的真实闭包由实际截断装配提供。 -/
def extensional_m {Ε : SortContext ℒ} (W : Term ℒ [] Ε .set) : Formula ℒ [.set] Ε :=
  .imp (PowerlessRelativeFiniteHullAssignments.closed_m (up W))
    ((PowerlessRelativeFiniteHullExtensionality.conclusion_m
      (.fvar (.here : Variable (.set :: Ε) .set))).substitute binding_m)

theorem extensional_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε) (W : Term ℒ [] Ε .set) (I : carrier_l 𝒩) :
    (extensional_m W).satisfies (ζ.pushBound I) ↔
      ((PowerlessRelativeFiniteHullAssignments.closed_m W).satisfies ζ →
        (PowerlessRelativeFiniteHullExtensionality.conclusion_m
          (.fvar (.here : Variable (.set :: Ε) .set))).satisfies (ζ.pushFree I)) := by
  rw [extensional_m]
  change ((PowerlessRelativeFiniteHullAssignments.closed_m (up W)).satisfies (ζ.pushBound I) →
    ((PowerlessRelativeFiniteHullExtensionality.conclusion_m
      (.fvar (.here : Variable (.set :: Ε) .set))).substitute binding_m).satisfies (ζ.pushBound I)) ↔ _
  rw [Formula.satisfies_substitute]
  have h : (ζ.pushBound I).pullback binding_m = ζ.pushFree I := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; cases v <;> rfl
  rw [h, PowerlessRelativeFiniteHullAssignments.closed_formula_l,
    PowerlessRelativeFiniteHullAssignments.closed_formula_l, up, Term.eval_weakenBound]

/-- 精确实数基集的固定证据保留在 Prop，不能以 B∈I 代替完整 B⊆I。 -/
def real_fixed_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B ω I H : SecondOrderQuotient.type_l hℳ) : Prop :=
  (∀ x, SecondOrderQuotient.mem_l hℳ x ω → SecondOrderQuotient.mem_l hℳ x I) →
    ∀ R, SecondOrderQuotient.mem_l hℳ R I →
      (∀ x, SecondOrderQuotient.mem_l hℳ x B ↔ SecondOrderQuotient.mem_l hℳ x ω ∨ x = R) →
      (∀ x, SecondOrderQuotient.mem_l hℳ x B → SecondOrderFunctionObjects.value_l hℳ H x x) ∧
        (SecondOrderQuotient.mem_l hℳ B I → SecondOrderFunctionObjects.value_l hℳ H B B) ∧
        (SecondOrderQuotient.mem_l hℳ ω I → SecondOrderFunctionObjects.value_l hℳ H ω ω) ∧
        SecondOrderFunctionObjects.value_l hℳ H R R

/-- 固定每个精确基集的成员；基集对象本身仍保留真实域成员守卫。 -/
def real_fixed_m {Γ Ε : SortContext ℒ} (B ω I H : Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .imp (ThirdOrderTheory.subset_m ω I) <|
    .forallE .set <| .imp (member_m (.bvar .here) (up I)) <|
      .imp (PowerlessRealSeed.spec_m (up ω) (.bvar .here) (up B)) <|
        .conj (PowerlessRelativeMembershipCollapseBase.fixed_m (up B) (up H))
          (.conj (.imp (member_m (up B) (up I))
            (SecondOrderObjectSyntax.value_m (up H) (up B) (up B))) <|
            .conj (.imp (member_m (up ω) (up I))
              (SecondOrderObjectSyntax.value_m (up H) (up ω) (up ω)))
              (SecondOrderObjectSyntax.value_m (up H) (.bvar .here) (.bvar .here)))

theorem real_fixed_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) Γ Ε)
    (B ω I H : Term ℒ Γ Ε .set) :
    (real_fixed_m B ω I H).satisfies ζ ↔ real_fixed_l hℳ (B.eval ζ) (ω.eval ζ) (I.eval ζ) (H.eval ζ) := by
  simp only [real_fixed_m, real_fixed_l, Formula.satisfies, ThirdOrderSemantics.subset_formula_l,
    ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l,
    PowerlessRealSeed.spec_formula_l, PowerlessRelativeMembershipCollapseBase.fixed_formula_l,
    SecondOrderObjectSyntax.value_l, member_m, Arguments.eval, up, Term.eval_weakenBound,
    Term.eval, SecondOrderQuotient.structure_l]
  rfl

/-- 同一绑定 I 与同一 H；不要求 I 传递或塌缩图属于相对类。 -/
def collapse_m {Ε : SortContext ℒ} (B ω W : Term ℒ [] Ε .set) : Formula ℒ [.set] Ε :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (up B)) <|
    .imp (SecondOrderOmegaSyntax.omega_m (up ω)) <|
      .imp (PowerlessRelativeFiniteHullAssignments.closed_m (up W)) <|
        .existsE .set <| .existsE .set <|
          .conj (PowerlessRelativeMembershipCollapse.spec_m
            (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
            (real_fixed_m (up (up (up B))) (up (up (up ω)))
              (.bvar (.there (.there .here))) (.bvar .here))

theorem collapse_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (B ω W : Term ℒ [] Ε .set) (I : SecondOrderQuotient.type_l hℳ) :
    (collapse_m B ω W).satisfies (ζ.pushBound I) ↔
      ((∀ x, SecondOrderQuotient.mem_l hℳ x (B.eval ζ) → ∀ y,
          SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y (B.eval ζ)) →
        SecondOrderOmega.omega_l hℳ (ω.eval ζ) →
        PowerlessRelativeFiniteHullAssignments.closed_l
          (𝒩 := SecondOrderQuotient.structure_l hℳ) (W.eval ζ) →
        ∃ T H, PowerlessRelativeMembershipCollapse.spec_l I T H ∧
          real_fixed_l hℳ (B.eval ζ) (ω.eval ζ) I H) := by
  simp only [collapse_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeFiniteHullAssignments.closed_formula_l,
    PowerlessRelativeMembershipCollapse.spec_formula_l, real_fixed_formula_l hℳ,
    up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

/-- 在同一原末端显式保留 f∈I；不再把它放在未消费的守卫蕴含后。 -/
def captured_m {Θ Δ Ε : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε)) : Formula ℒ [] Ε :=
  let ρ := fun v => term_m (original_m (Δ := Δ) τ v) σ
  .existsE .set <| .conj
    (PowerlessRelativeSourceFamilyElementaryImage.body_m J (term_m B σ) (term_m C σ)
      (term_m W σ) (term_m ω σ) (term_m Q σ) (term_m e σ) (term_m t₀ σ)
      (term_m t₁ σ) (term_m t₂ σ) (term_m a σ) (term_m P σ)) <|
    .conj (elementary_m (Δ := Δ) (term_m W σ) ρ) <|
      .conj (parameters_m (context_m Δ) (.bvar .here) (fun v => up (ρ v)))
        (.conj (member_m (up (term_m f σ)) (.bvar .here)) <|
          .conj (PowerlessRelativeFiniteHullValue.closed_m
            (up (ρ (.there .here))) (.bvar .here))
            (.conj (PowerlessRelativeFiniteHullValue.closed_m (up (term_m f σ)) (.bvar .here))
              (.conj (closure_m (up (term_m C σ)) (up (term_m W σ)) (up (term_m ω σ)) (.bvar .here))
                (.conj (extensional_m (term_m W σ)) <|
                  .conj (PowerlessRelativeFiniteHullValue.functions_m
                    (.bvar .here) (up (term_m W σ)))
                    (collapse_m (term_m B σ) (term_m ω σ) (term_m W σ))))))

private theorem captured_terminal_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ Δ Ε : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) (σ : Variable Θ .set → Term ℒ [] Ε .set) (J : List (Entry Ε))
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (hGuard : (guard_m (term_m (original_m (Δ := Δ) τ .here) σ)
      (term_m (original_m (Δ := Δ) τ (.there .here)) σ)
      (term_m (original_m (Δ := Δ) τ (.there (.there .here))) σ)
      (term_m (original_m (Δ := Δ) τ (.there (.there (.there .here)))) σ)
      (term_m W σ) (term_m f σ)).satisfies ζ)
    (h : (terminal_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P f τ σ J).satisfies ζ) :
    (captured_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P f τ σ J).satisfies ζ := by
  let ρ := fun v => term_m (original_m (Δ := Δ) τ v) σ
  change ∃ I, (PowerlessRelativeSourceFamilyElementaryImage.body_m J (term_m B σ)
    (term_m C σ) (term_m W σ) (term_m ω σ) (term_m Q σ) (term_m e σ)
    (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m a σ) (term_m P σ)).satisfies (ζ.pushBound I) ∧
    (elementary_m (Δ := Δ) (term_m W σ) ρ).satisfies (ζ.pushBound I) ∧
    (parameters_m (context_m Δ) (.bvar .here) (fun v => up (ρ v))).satisfies (ζ.pushBound I) ∧
    ((guard_m (up (ρ .here)) (up (ρ (.there .here)))
      (up (ρ (.there (.there .here)))) (up (ρ (.there (.there (.there .here)))))
      (up (term_m W σ)) (up (term_m f σ))).satisfies (ζ.pushBound I) →
      (member_m (up (term_m f σ)) (.bvar .here)).satisfies (ζ.pushBound I)) at h
  obtain ⟨I, hBody, hElem, hParams, hCap⟩ := h
  change ∃ I, (PowerlessRelativeSourceFamilyElementaryImage.body_m J (term_m B σ)
    (term_m C σ) (term_m W σ) (term_m ω σ) (term_m Q σ) (term_m e σ)
    (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m a σ) (term_m P σ)).satisfies (ζ.pushBound I) ∧
    (elementary_m (Δ := Δ) (term_m W σ) ρ).satisfies (ζ.pushBound I) ∧
    (parameters_m (context_m Δ) (.bvar .here) (fun v => up (ρ v))).satisfies (ζ.pushBound I) ∧
    (member_m (up (term_m f σ)) (.bvar .here)).satisfies (ζ.pushBound I) ∧
    (PowerlessRelativeFiniteHullValue.closed_m (up (ρ (.there .here))) (.bvar .here)).satisfies
      (ζ.pushBound I) ∧
    (PowerlessRelativeFiniteHullValue.closed_m (up (term_m f σ)) (.bvar .here)).satisfies
      (ζ.pushBound I) ∧
    (closure_m (up (term_m C σ)) (up (term_m W σ)) (up (term_m ω σ)) (.bvar .here)).satisfies
      (ζ.pushBound I) ∧ (extensional_m (term_m W σ)).satisfies (ζ.pushBound I) ∧
    (PowerlessRelativeFiniteHullValue.functions_m (.bvar .here) (up (term_m W σ))).satisfies
      (ζ.pushBound I) ∧
    (collapse_m (term_m B σ) (term_m ω σ) (term_m W σ)).satisfies (ζ.pushBound I)
  have hGuard' := (guard_formula_l K ζ (ρ .here) (ρ (.there .here))
    (ρ (.there (.there .here))) (ρ (.there (.there (.there .here))))
    (term_m W σ) (term_m f σ)).mp hGuard
  have hFI := hCap (by
    apply (guard_formula_l K (ζ.pushBound I) (up (ρ .here)) (up (ρ (.there .here)))
      (up (ρ (.there (.there .here)))) (up (ρ (.there (.there (.there .here)))))
      (up (term_m W σ)) (up (term_m f σ))).mpr
    simpa only [up, Term.eval_weakenBound] using hGuard')
  have hfI : SecondOrderQuotient.mem_l hℳ ((term_m f σ).eval ζ) I := by
    simpa only [member_m, Formula.satisfies, Arguments.eval, up, Term.eval_weakenBound,
      Term.eval, Env.pushBound_bound_here, SecondOrderQuotient.structure_l] using hFI
  have hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I ((term_m W σ).eval ζ) := by
    simpa only [ThirdOrderSemantics.subset_formula_l, subset_l, ThirdOrderSemantics.member_l,
      up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here,
      SecondOrderQuotient.structure_l] using hBody.2.2.1
  have hρ : ∀ v : Variable (context_m Δ) .set,
      SecondOrderQuotient.mem_l hℳ ((ρ v).eval ζ) I := by
    have h := (parameters_formula_l (context_m Δ) (ζ.pushBound I) (.bvar .here)
      (fun v => up (ρ v))).mp hParams
    intro v
    simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here,
      SecondOrderQuotient.structure_l] using h _ v
  let ν : Env (SecondOrderQuotient.structure_l hℳ) [] (context_m Δ) :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (ρ v).eval ζ }
  have hElem' := (elementary_formula_l (Δ := Δ) (term_m W σ) ρ ζ I).mp hElem
  have hParts := (family_formula_l (Δ := Δ) (ζ.pushFree I) (.fvar .here)
    (free (term_m W σ)) (fun v => free (ρ v))).mp hElem'
  have hClosed {F A C : SecondOrderQuotient.type_l hℳ}
      (hF : SecondOrderQuotient.mem_l hℳ F I)
      (hMap : SecondOrderFunctionObjects.map_l hℳ F A C)
      (hCW : ∀ y, SecondOrderQuotient.mem_l hℳ y C →
        SecondOrderQuotient.mem_l hℳ y ((term_m W σ).eval ζ)) :
      ∀ x, SecondOrderQuotient.mem_l hℳ x I → ∀ y,
        SecondOrderFunctionObjects.value_l hℳ F x y → SecondOrderQuotient.mem_l hℳ y I :=
    PowerlessRelativeFiniteHullValue.closed_l hℳ (Δ := context_m Δ)
      (I₀ := I) (W₀ := (term_m W σ).eval ζ) (F := F) (A := A) (C := C)
      (ζ.pushFree I) (.fvar .here) (free (term_m W σ)) (fun v => free (ρ v)) ν
      (fun v => by simp only [free, Term.eval_weakenFree, ν]) hρ rfl
      (by simp only [free, Term.eval_weakenFree])
      (fun x hx y hy => hGuard'.1 x y hx hy) hIW hF hParts.2.1 hMap hCW
  have hUI : member_l (SecondOrderQuotient.structure_l hℳ)
      ((ρ (.there (.there (.there .here)))).eval ζ) I := by
    simpa only [ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using
      hρ (.there (.there (.there .here)))
  have hUW (y : SecondOrderQuotient.type_l hℳ)
      (hy : SecondOrderQuotient.mem_l hℳ y ((ρ (.there (.there (.there .here)))).eval ζ)) :
      SecondOrderQuotient.mem_l hℳ y ((term_m W σ).eval ζ) :=
    hGuard'.1 ((ρ (.there (.there (.there .here)))).eval ζ) y
      (hIW ((ρ (.there (.there (.there .here)))).eval ζ) hUI) hy
  have hExtensional : (extensional_m (term_m W σ)).satisfies (ζ.pushBound I) := by
    apply (extensional_formula_l ζ (term_m W σ) I).mpr
    intro hWClosed
    have hBIn : member_l (SecondOrderQuotient.structure_l hℳ) ((ρ .here).eval ζ) I := by
      simpa only [ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using hρ .here
    have hNonempty : ∃ x, member_l (SecondOrderQuotient.structure_l hℳ) x ((term_m W σ).eval ζ) :=
      ⟨(ρ .here).eval ζ, hIW ((ρ .here).eval ζ) hBIn⟩
    apply PowerlessRelativeFiniteHullExtensionality.closed_formula_l hℳ
      (Δ := context_m Δ) (I₁ := I) (W₁ := (term_m W σ).eval ζ)
      (ζ.pushFree I) (.fvar .here) (free (term_m W σ)) (fun v => free (ρ v))
      (fun x y hx hy => hGuard'.1 x y hx hy)
      ((PowerlessRelativeFiniteHullAssignments.closed_formula_l ζ (term_m W σ)).mp hWClosed)
      hNonempty hIW rfl (by simp only [free, Term.eval_weakenFree]) hParts.2.2.2.1
  refine ⟨I, hBody, hElem, hParams, hFI, ?_, ?_, ?_, hExtensional, ?_, ?_⟩
  · apply (PowerlessRelativeFiniteHullValue.closed_formula_l hℳ (ζ.pushBound I)
      (up (ρ (.there .here))) (.bvar .here)).mpr
    simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using
      hClosed (hρ (.there .here)) hGuard'.2.1.1 hUW
  · apply (PowerlessRelativeFiniteHullValue.closed_formula_l hℳ (ζ.pushBound I)
      (up (term_m f σ)) (.bvar .here)).mpr
    simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using
      hClosed hfI hGuard'.2.2.2.1.1 hUW
  · have hCI := PowerlessRelativeSourceFamilyElementaryImage.seed_l J (term_m B σ)
      (term_m C σ) (term_m W σ) (term_m ω σ) (term_m Q σ) (term_m e σ)
      (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m a σ) (term_m P σ) ζ I hBody
    simp only [closure_m, Formula.satisfies, ThirdOrderSemantics.subset_formula_l,
      PowerlessRelativeFiniteHullAssignments.closed_formula_l, SecondOrderOmegaSyntax.omega_l,
      PowerlessRelativeFiniteHullAssignments.finite_formula_l,
      up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
    refine ⟨hCI, fun hWClosed => ?_⟩
    have hIClosed := PowerlessRelativeFiniteHullClosure.closure_l
      (Δ := context_m Δ) (I₀ := I) (W₀ := (term_m W σ).eval ζ)
      (ζ.pushFree I) (.fvar .here) (free (term_m W σ))
      (fun v => free (ρ v))
      (fun a b => SecondOrderPairObjects.pair_exists_l hℳ a b)
      (PowerlessRelativeFiniteHullClosure.binary_exists_l hℳ)
      (fun a b hz => SecondOrderQuotient.ext_l hℳ a b hz)
      (fun x y hx hy => hGuard'.1 x y hx hy) hWClosed hIW rfl
      (by simp only [free, Term.eval_weakenFree]) hParts.2.2.1
    refine ⟨hIClosed, fun hω hωC n hn A g hg hValues => ?_⟩
    have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
    exact PowerlessRelativeFiniteHullAssignments.member_l K
      (fun x hx => hCI x (hωC x (hωEq.symm ▸ hx))) hIClosed (hωEq ▸ hn) hg hValues
  · apply (PowerlessRelativeFiniteHullValue.functions_formula_l hℳ (ζ.pushBound I)
      (.bvar .here) (up (term_m W σ))).mpr
    simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using
      fun F A C hF hMap hCW => hClosed (F := F) (A := A) (C := C) hF hMap hCW
  · apply (collapse_formula_l hℳ ζ (term_m B σ) (term_m ω σ) (term_m W σ) I).mpr
    intro hBase hω hWClosed
    have hExtUpper := (PowerlessRelativeFiniteHullExtensionality.conclusion_formula_l
      (ζ.pushFree I) (.fvar .here)).mp
      ((extensional_formula_l ζ (term_m W σ) I).mp hExtensional
        ((PowerlessRelativeFiniteHullAssignments.closed_formula_l ζ (term_m W σ)).mpr hWClosed))
    have hExt : PowerlessRelativeMembershipCollapseInjectivity.ext_l hℳ I := by
      simpa only [PowerlessRelativeMembershipCollapseInjectivity.ext_l, Term.eval,
        Env.pushFree_here, ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using
        hExtUpper.1
    have hUpper : ∀ x, SecondOrderQuotient.mem_l hℳ x I → ∃ p,
        SecondOrderQuotient.mem_l hℳ p I ∧ SecondOrderQuotient.mem_l hℳ x p := by
      simpa only [Term.eval, Env.pushFree_here, ThirdOrderSemantics.member_l,
        SecondOrderQuotient.structure_l] using hExtUpper.2
    have hClass : PowerlessRelativeClassCorrespondence.member_l hℳ ((term_m B σ).eval ζ) I := by
      simpa only [PowerlessRelativeClassCorrespondence.member_l,
        up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using
        (PowerlessRelativeHierarchySemantics.class_formula_l K (ζ.pushBound I)
          (up (term_m B σ)) (.bvar .here)).mp hBody.1
    have hCount : PowerlessRelativeOrdinalCutoff.countable_l
        ((term_m B σ).eval ζ) ((term_m ω σ).eval ζ) I := by
      simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using
        (PowerlessRelativeOrdinalCutoff.countable_formula_l K (ζ.pushBound I)
          (up (term_m B σ)) (up (term_m ω σ)) (.bvar .here)).mp hBody.2.1
    obtain ⟨T, H, hH⟩ := PowerlessRelativeMembershipCollapse.exists_l (hBase := hBase)
      K hω hClass hCount hExt hUpper ⟨(ρ .here).eval ζ, hρ .here⟩
    refine ⟨T, H, hH, ?_⟩
    intro hωI R hR hSpec
    have hBI : ∀ x, SecondOrderQuotient.mem_l hℳ x ((term_m B σ).eval ζ) →
        SecondOrderQuotient.mem_l hℳ x I := by
      intro x hx
      rcases (hSpec x).mp hx with hn | rfl
      · exact hωI x hn
      · exact hR
    have hFixed := PowerlessRelativeMembershipCollapseBase.fixed_l hℳ _ I T H
      hBase hBI hH.2.1 hH.2.2.2.1
    exact ⟨hFixed,
      PowerlessRelativeMembershipCollapseBase.base_l hℳ _ I T H
        hBase hBI hH.2.1 hH.2.2.2.1,
      PowerlessRelativeMembershipCollapseBase.base_l hℳ _ I T H
        (fun _ hx _ hy => SecondOrderOmegaTransitive.member_l hℳ hω hx hy)
        hωI hH.2.1 hH.2.2.2.1,
      hFixed R ((hSpec R).mpr (Or.inr rfl))⟩

def captured_conclusion_m {Θ Δ : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let Ψ := PowerlessRelativeFiniteRequestFamilyClosure.requests_m (family_m Δ)
  let m := Ψ.length
  PowerlessRelativeSourceFamilyExtension.extension_m
    (captured_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P f τ)
    (PowerlessRelativeFiniteRequestFamilyClosure.family_m m Ψ)
    (PowerlessSourceRequestParameters.tags_m (context_m Δ) m) B W R τ [] (fun v => .fvar v)

def input_m {Θ Δ : SortContext ℒ} (W f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  guard_m (original_m (Δ := Δ) τ .here) (original_m (Δ := Δ) τ (.there .here))
    (original_m (Δ := Δ) τ (.there (.there .here)))
    (original_m (Δ := Δ) τ (.there (.there (.there .here)))) W f

/-- 原四个指定参数严格跨过请求标签前缀，标签槽不充当历史参数。 -/
theorem input_eq_m {Θ Δ : SortContext ℒ} (W f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) :
    input_m (Δ := Δ) W f τ =
      let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m (family_m Δ)).length
      guard_m (τ (PowerlessSourceOpening.skip_m m .here))
        (τ (PowerlessSourceOpening.skip_m m (.there .here)))
        (τ (PowerlessSourceOpening.skip_m m (.there (.there .here))))
        (τ (PowerlessSourceOpening.skip_m m (.there (.there (.there .here))))) W f := rfl

/-- 原参数逐项同值即保持历史守卫，不展开请求标签前缀。 -/
theorem input_eval_l {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    (K : source_coding_l hℳ) {Θ Δ Ε : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (W f : Term ℒ [] Θ .set) (W' f' : Term ℒ [] Ε .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set)
    (σ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Ε .set)
    (hW : W'.eval ζ = W.eval η) (hf : f'.eval ζ = f.eval η)
    (hτ : ∀ v, (σ v).eval ζ = (τ v).eval η) :
    (input_m (Δ := Δ) W' f' σ).satisfies ζ ↔ (input_m (Δ := Δ) W f τ).satisfies η := by
  simp only [input_eq_m, guard_formula_l K, hW, hf, hτ]

theorem input_free_l {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    (K : source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ) (j : SecondOrderQuotient.type_l hℳ)
    (W f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) :
    (input_m (Δ := Δ) (free W) (free f) (fun v => free (τ v))).satisfies (η.pushFree j) ↔
      (input_m (Δ := Δ) W f τ).satisfies η := by
  simp only [input_eq_m, guard_formula_l K, free, Term.eval_weakenFree]

theorem capture_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (B C W ω Q e t₀ t₁ t₂ a P R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (hGuard : (input_m (Δ := Δ) W f τ).satisfies η)
    (h : (conclusion_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P R f τ).satisfies η) :
    (captured_conclusion_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P R f τ).satisfies η := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  let Ψ := PowerlessRelativeFiniteRequestFamilyClosure.requests_m (family_m Δ)
  let m := Ψ.length
  apply PowerlessRelativeSourceFamilyTransport.imp_read_l
    (𝒩 := SecondOrderQuotient.structure_l hℳ) (Θ := Θ)
    (Δ := PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) η
    (terminal_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P f τ)
    (captured_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P f τ) (fun ζ σ J hσ h₀ => ?_)
    (PowerlessRelativeFiniteRequestFamilyClosure.family_m m Ψ)
    (PowerlessSourceRequestParameters.tags_m (context_m Δ) m) η B W R τ []
    (fun v => .fvar v) (fun _ => rfl) h
  apply captured_terminal_l hℳ K (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P f τ σ J ζ ?_ h₀
  apply (guard_formula_l K ζ
    (term_m (original_m (Δ := Δ) τ .here) σ)
    (term_m (original_m (Δ := Δ) τ (.there .here)) σ)
    (term_m (original_m (Δ := Δ) τ (.there (.there .here))) σ)
    (term_m (original_m (Δ := Δ) τ (.there (.there (.there .here)))) σ)
    (term_m W σ) (term_m f σ)).mpr
  have hRead (t : Term ℒ [] Θ .set) :=
    PowerlessRelativeSourceFamilyClosedImage.term_formula_l t σ ζ η hσ
  simpa only [hRead] using
    (guard_formula_l K η (original_m (Δ := Δ) τ .here)
      (original_m (Δ := Δ) τ (.there .here))
      (original_m (Δ := Δ) τ (.there (.there .here)))
      (original_m (Δ := Δ) τ (.there (.there (.there .here)))) W f).mp hGuard

def capture_schema_m {Θ Δ : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (input_m (Δ := Δ) W f τ) <|
    .imp (conclusion_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P R f τ)
      (captured_conclusion_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P R f τ)

theorem capture_derives_m {Θ Δ : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close
        (capture_schema_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P R f τ))) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff
    (ℳ := SecondOrderQuotient.structure_l hℳ)
    (capture_schema_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P R f τ)).mpr
  intro η hGuard h
  exact capture_l hℳ (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P R f τ η hGuard h

-- 原元素性包装需要原定义的透明性；捕获段的局部护栏不传播到此段。
attribute [local semireducible] family_m

def schema_m {Θ Δ : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeSourceFamilyElementaryImage.conclusion_m (family_m Δ)
    B C W ω Q e t₀ t₁ t₂ a P R τ)
    (conclusion_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P R f τ)

def sentence_m {Θ Δ : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P R f τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (B C W ω Q e t₀ t₁ t₂ a P R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) :
    (sentence_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P R f τ).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  exact PowerlessRelativeSourceFamilyElementaryImage.transport_closed_l (family_m Δ)
    B C W ω Q e t₀ t₁ t₂ a P R τ
    (terminal_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P f τ)
    (fun ζ σ J h => terminal_l hℳ (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P f τ ζ σ J h)

theorem derives_m {Θ Δ : SortContext ℒ}
    (B C W ω Q e t₀ t₁ t₂ a P R f : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m (family_m Δ)) .set →
      Term ℒ [] Θ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P R f τ)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ hℳ => models_l hℳ (Δ := Δ) B C W ω Q e t₀ t₁ t₂ a P R f τ)

#print axioms terminal_l
#print axioms history_l
#print axioms closure_l
#print axioms closure_member_l
#print axioms closure_image_l
#print axioms assignments_image_l
#print axioms value_image_l
#print axioms numeric_image_l
#print axioms satisfaction_l
#print axioms satisfaction_capture_l
#print axioms satisfaction_member_sequences_l
#print axioms maps_l
#print axioms omega_l
#print axioms omega_model_l
#print axioms evaluation_l
#print axioms static_l
#print axioms def_l
#print axioms def_member_l
#print axioms static_member_l
#print axioms satisfaction_member_l
#print axioms guard_formula_l
#print axioms input_eq_m
#print axioms input_eval_l
#print axioms input_free_l
#print axioms extensional_formula_l
#print axioms real_fixed_formula_l
#print axioms collapse_formula_l
#print axioms capture_l
#print axioms capture_derives_m
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyHistory
