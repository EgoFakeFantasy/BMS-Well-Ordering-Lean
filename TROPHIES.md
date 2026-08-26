# YesMetaZFC Lean 形式化奖杯表

本页是项目里程碑与可复用形式化资产的稳定展示出口。这里不建立重复的包装定理：
每一项都直接指向仓库中参与正常构建的真实 Lean 声明。

收录标准：

1. 声明具有明确的数学内容或可复用的证明工程价值。
2. 声明使用其实际需要的假设，不以更强前提换取临时闭合。
3. 声明所在依赖链不含 `sorry`，并通过项目的 `lake build`。
4. 基础设施与终局定理同等计入成果，不把大部分工作隐藏在单个终局名字后面。

截至 2026-08-15，本页所列 Rosser 依赖链已通过全仓 `lake build`，共 456 个构建任务。
这里的“无 `sorry`”表示该依赖链未引入 `sorryAx`；项目的可信计算边界仍包括 Lean
内核及仓库既有的 `native_decide` 使用。

## Lean 入口

```lean
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCRosserIncompleteness

#check YesMetaZFC.Logic.FirstOrder.FormalSystem.fs_zfc_rosser_incompleteness
#check YesMetaZFC.Logic.FirstOrder.FormalSystem.Rosser.fs_checked_hilbertized_proof_code_for
#check YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation.fs_diagonal_lemma
```

## 终局里程碑

| 编号 | Lean 声明 | 形式化成果 | 源码 |
| --- | --- | --- | --- |
| ZFC-R01 | `fs_zfc_rosser_incompleteness` | 仅由内部 ZFC 支持理论的一致性，得到一个句子及其否定均不可由该理论 Hilbert 推导。全部内容在对象语法与 Hilbert 推导内完成。 | [ZFCRosserIncompleteness.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCRosserIncompleteness.lean) |
| ZFC-R02 | `fs_zfc_rosser_independence_of_diagonal` | 将真实 quotation、Rosser 固定点、正负内部化与一致性装配为独立性结论。对象证明码和有限比较均封装在定理体内。 | [ZFCRosserIncompleteness.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCRosserIncompleteness.lean) |
| CORE-R01 | `Rosser.independent_of_fixed_point_internalization` | 通用的纯 Hilbert Rosser 终局：固定点等价式加正负两个内部化蕴含及一致性即可推出双向不可证。 | [RosserFinite.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/RosserFinite.lean) |

终局定理的实际 Lean 类型为：

```lean
theorem fs_zfc_rosser_incompleteness
    (hConsistent :
      Derives.Consistent fs_zfc_support_theory []) :
    ∃ fixedPoint : SetFormula,
      Formula.Sentence fixedPoint ∧
        (¬ HilbertDerives fs_zfc_support_theory fixedPoint) ∧
        (¬ HilbertDerives fs_zfc_support_theory
          (Formula.neg fixedPoint))
```

这一定理没有把 proof code、replay trace、对象 verifier、模型或元层传输暴露为参数。

## 通用证明码内核

| 编号 | Lean 声明 | 形式化资产 | 复用边界 | 源码 |
| --- | --- | --- | --- | --- |
| CODE-01 | `Rosser.fs_checked_hilbertized_proof_code_for` | 将“代码 replay 成功且目标公式出现在最终证明状态中”封装为二元证明码关系。 | 参数化于任意带 Hilbert 理论枚举的理论。 | [CheckedCompleteness.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/CheckedCompleteness.lean) |
| CODE-02 | `Rosser.fs_checked_hilbertized_proof_code_for_sound` | 从 checked proof code 恢复 Hilbert 可推导性。 | 只消费 replay 的可靠性，不要求对象理论反射。 | [CheckedCompleteness.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/CheckedCompleteness.lean) |
| CODE-03 | `Rosser.fs_checked_hilbertized_proof_code_for_exists_of_derives` | 每个有限 Hilbert 推导都可编译为真实 checked proof code。 | 仅要求理论枚举和理论对 Hilbert 化闭合。 | [CheckedCompleteness.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/CheckedCompleteness.lean) |
| CODE-04 | `Rosser.fs_replay_raw_rows_nil_some_alignment` | 成功 replay 精确恢复规范解码行、最终 proof 与证书序列。 | 这是已完成的成功反演层；下游只调用，不再扩张。 | [RawAlignment.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/CheckedReplay/RawAlignment.lean) |
| CODE-05 | `Rosser.FSReplayCodeFailure`、`Rosser.fs_replay_code_failure_of_none` | 将总 replay 的 `none` 分解为证书解码失败或逐行 replay 失败。 | 只作为失败适配器的内部视图，不进入 Rosser 终局接口。 | [Failure.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/CheckedReplay/Failure.lean) |

这组接口形成可复用的往返边界：

```lean
HilbertDerives theory formula
  -> ∃ proofCode,
       fs_checked_hilbertized_proof_code_for
         enumeration proofCode formula

fs_checked_hilbertized_proof_code_for
    enumeration proofCode formula
  -> HilbertDerives theory
       (Formula.hilbertize SetSort.set formula)
```

## 对象证书系统

| 编号 | Lean 声明 | 形式化资产 | 复用边界 | 源码 |
| --- | --- | --- | --- | --- |
| CERT-01 | `ObjectCertificateVerifier` | 对象层理论证书 verifier 的最小合同，只规定公式合法性条件与证书条件。 | 与具体 ZFC 编码解耦，其他对象理论可以提供自己的证书条件实例。 | [CertifiedProofCodeEncoding.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/CertifiedProofCodeEncoding.lean) |
| CERT-02 | `fs_zfc_object_certificate_verifier` | ZFC 的闭合对象证书 verifier，统一覆盖有限公理表、分离模式和收集模式。 | 两个公理模式被放入证书检查层，不扩张 Rosser 终局假设。 | [ZFCObjectVerifier.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCObjectVerifier.lean) |
| CERT-03 | `fs_zfc_support_raw_certified_code_condition_of_derives_at_quote` | 从 ZFC Hilbert 推导构造标准证明码，并在公式的真实 quotation 上证明对象层证书条件。 | Rosser 正向内部化的公共入口。 | [ZFCCheckedProofInternalization.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCCheckedProofInternalization.lean) |
| CERT-04 | `fs_zfc_support_raw_certified_code_condition_neg_of_checked_not` | checked 二元关系不成立时，在对象理论中否定相同 numeral 与真实 quotation 上的证书条件。 | Rosser 负向内部化的公共入口；失败 trace 不向外泄漏。 | [ZFCCertifiedProofRelationRejection.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCCertifiedProofRelationRejection.lean) |
| CERT-05 | `CertifiedProof.fs_zfc_support_raw_logical_certificate_condition_neg_of_failure` | 将逻辑证书检查失败统一转换为对象层否证。 | 失败适配器的逻辑公理出口，不建立新的 tag 反演层。 | [ZFCLogicalTailFailureAssembly.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCLogicalTailFailureAssembly.lean) |

正负两个公共入口精确对齐同一个二元外部关系：

```lean
HilbertDerives fs_zfc_support_theory formula
  -> ∃ proofCode,
       Derives fs_zfc_support_raw_theory []
         (certified_code_condition proofCode (quote formula))

¬ fs_zfc_checked_hilbertized_proof_code_for proofCode formula
  -> Derives fs_zfc_support_raw_theory []
       (¬ certified_code_condition proofCode (quote formula))
```

上式使用数学形状省略了 fresh base、numeral 项及 quotation 等式；仓库中的 Lean
声明保留这些必要的语法参数。

## Gödel 编码与对角化

| 编号 | Lean 声明 | 形式化资产 | 复用边界 | 源码 |
| --- | --- | --- | --- | --- |
| QUOTE-01 | `GodelQuotation.fs_named_hilbert_tokens_decode_with_env_canonical_forall_open` | 在 token 新鲜性下，将规范 binder 正文打开为自由变量，并证明解码结果等于公式层 `openAt`。 | 为量词逻辑证书的正向解码与失败反演提供统一语法接口。 | [FormalSystemNamedTokenDecoderOpening.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/GodelQuotation/FormalSystemNamedTokenDecoderOpening.lean) |
| QUOTE-02 | `GodelQuotation.fs_diagonal_lemma` | 对任意扩展编码理论、可接受且只含指定代码变量的公式，生成闭句、真实 quotation 与目标理论内的 Hilbert 固定点。 | 与 ZFC 和 Rosser 谓词无关的通用内部对角引理。 | [Diagonal.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/GodelQuotation/Diagonal.lean) |
| QUOTE-03 | `fs_zfc_rosser_diagonal` | 将通用对角引理实例化到 ZFC Rosser 谓词，得到真实 quotation 对齐的 Rosser 句。 | 不增加模型、标准性或额外对象理论层。 | [ZFCRosser.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCRosser.lean) |

## 对象有限算术与 Rosser 装配

| 编号 | Lean 声明 | 形式化资产 | 复用边界 | 源码 |
| --- | --- | --- | --- | --- |
| ARITH-01 | `fs_zfc_support_raw_rosser_natural_cut` | 对任意对象自然数和标准 numeral `q`，在对象理论内证明其落在 `≤ q` 或 `> q` 一侧。 | 只暴露二元成员关系，分离见证和归纳细节封装在模块内部。 | [ZFCRosserNaturalCut.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCRosserNaturalCut.lean) |
| ARITH-02 | `fs_zfc_support_raw_certified_code_comparison_of_numeral_branches` | 一个正证明码加所有严格较小码的有限逐点否证，装配为对象层 Rosser 比较。 | 只消费有限逐点分支。 | [ZFCRosserFiniteAssembly.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCRosserFiniteAssembly.lean) |
| ARITH-03 | `fs_zfc_support_raw_certified_code_comparison_neg_of_right_numeral` | 一个右侧证明码加其以下左侧代码的有限否证，推出 Rosser 比较的对象层否定。 | 为 Rosser 负向内部化提供有限分支终点。 | [ZFCRosserFiniteAssembly.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCRosserFiniteAssembly.lean) |
| BRIDGE-01 | `fs_zfc_support_hilbert_derives_of_raw` | 将 raw 支持理论中的对象推导编译为 ZFC 支持理论中的 Hilbert 推导。 | 终局只通过这一方向提升，不暴露 raw 理论实现细节。 | [ZFCCheckedReplay.lean](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/ZFCCheckedReplay.lean) |

## Rosser 依赖链

```text
通用 checked proof code
  -> 成功 replay 对齐
  -> ZFC 对象证书 verifier
  -> quotation 上的正向内部化

checked 二元关系失败
  -> replay 失败视图
  -> 对象层证书条件否定
  -> 有限自然数切分与 Rosser 比较

通用内部对角引理
  -> ZFC Rosser 对角句
  -> 纯 Hilbert Rosser 终局
  -> fs_zfc_rosser_incompleteness
```

这条依赖链固定为“成功反演层 + 失败适配层”。`FSReplayCodeFailure` 和逻辑失败
payload 只在适配器内部消费；公开 Rosser 谓词及终局定理只使用二元证明码关系。

## 后续收录规则

新的奖杯条目应直接引用公开 Lean 声明及源码，不增加仅用于展示的 theorem 别名。
若成果依赖重要基础设施，应分别登记终局与基础设施，避免把可复用资产压缩成一句
“某定理已完成”。构建状态或可信边界发生变化时，应同步更新本页日期与审计说明。
