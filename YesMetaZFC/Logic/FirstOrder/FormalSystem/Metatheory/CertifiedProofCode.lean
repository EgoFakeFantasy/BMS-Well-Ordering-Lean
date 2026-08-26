import YesMetaZFC.Logic.FirstOrder.Hilbert
import YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofCode

/-!
# 带理论证书的 Hilbert 证明码

直接把 `theory formula` 放进证明码合法性谓词，只能得到半判定的证明关系。
本模块把理论公理行改为显式自然数证书：证书的有效性由外部枚举接口给出，
证明码本身不再要求对象层否定任意理论成员关系。

这里先建立外部证书化证明码的可靠性与完备性。对象层的有限 verifier、其
可表示性合同以及 Rosser 终局必须在此接口之上另行实现，不能退回已删除的
直接理论成员证明码。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofCode
universe u v w

/-- 递归可枚举理论所需的外部有限证书合同。

`certificate_complete` 只返回存在性，避免在基础接口中用选择公理把枚举索引
抽取成函数。布尔 verifier 使固定证书的有效性可直接检查；需要构造具体证明码时，
调用方在命题证明中拆出存在见证。

本结构只规定外部证书形状，不把 verifier 的对象语言可表示性混入接口；后者必须由
后续对象层合同单独给出。
-/
structure HilbertTheoryEnumeration
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    (theory : Theory σ) where
  certificate_verifier : Nat → Formula σ → Bool
  certificate_sound :
    ∀ {certificate : Nat} {formula : Formula σ},
      certificate_verifier certificate formula = true → theory formula
  certificate_complete :
    ∀ {formula : Formula σ},
      theory formula →
        ∃ certificate, certificate_verifier certificate formula = true

/-- 证书序列与公式序列共同组成的自然数证明码。 -/
def certified_hilbert_proof_code_value
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    (rowTokens : Formula σ → List Nat)
    (proof : List (Formula σ))
    (certificates : List HilbertLineCertificateCode) : Nat :=
  godel_pair_value
    (proof_sequence_code_value (proof.map rowTokens))
    (nat_sequence_code_value
      (certificates.map HilbertLineCertificateCode.value))

end ProofCode
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
