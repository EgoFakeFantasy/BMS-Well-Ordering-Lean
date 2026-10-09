import BMSConstructibleBridge.PowerlessTruthSet
import BMSConstructibleBridge.PowerlessTruthCertificateUnion
import YesMetaZFC.Automation.BoundedFormulaCertificate

/-!
# 有符号真值证书工具

提供实际检查公式、局部规则单调性、二元并保持及条件可靠性。
阶段相关结论仍要求原定理中的实际层、求值器和有限理论假设。
不提供接受完备性；语义有效记录集不是可供内部收集的检查公式。
另提供任意语言中集合域上的有限参数 Δ₀ 等价证书及布尔合并；
该通用接口不要求或宣称任何具体对象理论具备此证书。
-/
