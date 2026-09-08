import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxSubstitution

/-! # 有限项参数表上的内核模板代入

参数表的位置由模板的类型化自由上下文保证，合法变量不会使用越界默认分支。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxInstantiation
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

def slot (args : List Tree) (index : Nat) : Tree := args[index]?.getD (SyntaxSubstitution.fvar index)

theorem lookup_encode {free : SetContext} : {sorts : SetContext} →
    (args : Arguments signature [] free sorts) → {sort : SetSort} → (entry : Variable sorts sort) →
    (SyntaxEncode.argumentsList args)[entry.index]? = some (SyntaxEncode.term (SyntaxDecode.substitution args entry))
  | _, .nil, _, entry => nomatch entry
  | _, .cons head tail, _, .here => rfl
  | _, .cons head tail, _, .there entry => by
    simpa only [SyntaxEncode.argumentsList, Variable.index, List.getElem?_cons_succ,
      SyntaxDecode.substitution, VariableSubstitution.cons] using lookup_encode tail entry

theorem slot_encode {free sorts : SetContext} (args : Arguments signature [] free sorts)
    {sort : SetSort} (entry : Variable sorts sort) :
    slot (SyntaxEncode.argumentsList args) entry.index = SyntaxEncode.term (SyntaxDecode.substitution args entry) := by
  simp [slot, lookup_encode args entry]

def instantiate (args : List Tree) (input : Tree) : Tree :=
  SyntaxSubstitution.formula SyntaxSubstitution.bvar (slot args) input

theorem instantiate_encode {sorts free : SetContext} (args : Arguments signature [] free sorts)
    (input : SetOpenFormula sorts) :
    instantiate (SyntaxEncode.argumentsList args) (SyntaxEncode.formula input) =
      SyntaxEncode.formula (input.substituteFree (SyntaxDecode.substitution args)) := by
  apply SyntaxSubstitution.formula_substitute _ _ VariableSubstitution.boundId (SyntaxDecode.substitution args)
  · intro sort entry
    exact nomatch entry
  · intro sort entry
    exact slot_encode args entry

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxInstantiation
