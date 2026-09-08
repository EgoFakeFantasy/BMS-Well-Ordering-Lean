import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportTemplate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportConclusion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxInstantiation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatPacketRoundtrip

/-! # 参数公理的原始码装配与当前 quotation

固定模板的项代入和自由参数闭合均在原始树上计算，再由交换定理连接原公理闭句。
这里连接实际计算结果；该装配算法的统一对象图及正负表示仍需另行实现。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportRealization
open Nonlogical.BasicSetTheory NatPacket SupportParameters SupportAssembly
set_option autoImplicit false

def assemble (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) : Tree :=
  SyntaxSubstitution.close parameters.free.length
    (SyntaxInstantiation.instantiate (SyntaxEncode.argumentsList parameters.args)
      (SyntaxEncode.formula (template kind)))

/-- 原始码装配逐节点等于当前类型安全内核的公理编码。 -/
theorem assemble_eq (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) :
    assemble kind parameters = SyntaxEncode.formula (sentence kind parameters) := by
  unfold assemble
  rw [SyntaxInstantiation.instantiate_encode, SyntaxSubstitution.close_encode]
  exact congrArg SyntaxEncode.formula (close_instantiate kind parameters)

theorem assemble_quote (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) :
    IntrinsicQuotation.tree (assemble kind parameters) = IntrinsicQuotation.quote (sentence kind parameters) := by
  rw [assemble_eq]
  rfl

/-- 仅先解析参数外壳；公理结论由固定模板和原始码变换产生。 -/
def run (kind : Kind) (input : Tree) : Option Tree :=
  (SyntaxParameters.decode kind.arity input).map (assemble kind)

theorem run_encode (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) :
    run kind (SyntaxParameters.encode parameters) = some (SyntaxEncode.formula (sentence kind parameters)) := by
  simp only [run, SyntaxParameters.decode_encode, Option.map_some, assemble_eq]

/-- 对全部原始输入包含失败分支，新装配计算与旧证书实际结论精确相同。 -/
theorem run_eq_actual (kind : Kind) (input : Tree) :
    run kind input = (SupportConclusion.actual kind input).map SyntaxEncode.formula := by
  rw [SupportConclusion.actual_eq_decode]
  simp only [run, Option.map_map, Function.comp_def]
  congr 1
  funext parameters
  exact assemble_eq kind parameters

theorem run_isSome (kind : Kind) (input : Tree) :
    (run kind input).isSome = SupportParameters.actual kind input := by
  simp only [run, Option.isSome_map, SupportParameters.actual_eq_decode]

theorem run_eq_some_iff (kind : Kind) (input output : Tree) :
    run kind input = some output ↔ ∃ parameters : SyntaxParameters.Parameters kind.arity,
      SyntaxParameters.encode parameters = input ∧ SyntaxEncode.formula (sentence kind parameters) = output := by
  simp only [run, Option.map_eq_some_iff, SyntaxParameters.decode_eq_some_iff, assemble_eq]

/-- 任意成功输入的装配结果都是对应原理论中可推导闭句的精确内核编码。 -/
theorem run_sound (kind : Kind) (input output : Tree) (h : run kind input = some output) :
    ∃ φ : SetSentence, output = SyntaxEncode.formula φ ∧ Derives (SupportConclusion.theory kind) [] φ := by
  obtain ⟨parameters, _, hOutput⟩ := (run_eq_some_iff kind input output).mp h
  exact ⟨sentence kind parameters, hOutput.symm, SupportConclusion.sentence_derives kind parameters⟩

/-- 版本一自然数包承载当前参数外壳，尚未包含外层理论并的完整路径。 -/
def packet (kind : Kind) (number : Nat) : Option Tree :=
  (NatPacket.decode number).bind (run kind)

theorem packet_eq_actual (kind : Kind) (number : Nat) :
    packet kind number = ((NatPacket.decode number).bind (SupportConclusion.actual kind)).map SyntaxEncode.formula := by
  unfold packet
  rw [Option.map_bind]
  congr 1
  funext input
  exact run_eq_actual kind input

theorem packet_encode (kind : Kind) (parameters : SyntaxParameters.Parameters kind.arity) :
    packet kind (NatPacket.encode (SyntaxParameters.encode parameters)) =
      some (SyntaxEncode.formula (sentence kind parameters)) := by
  simp only [packet, NatPacket.decode_encode, Option.bind_some, run_encode]

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SupportRealization
