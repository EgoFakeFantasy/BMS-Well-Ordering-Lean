import YesMetaZFC.Logic.Syntax

/-!
# bound 槽交换

`swapBoundTop` 直接交换最近的两个 bound 槽位。它由类型索引保证排序与作用域，
量词下的递归行为由 `VariableRenaming.lift` 自动给出。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

set_option autoImplicit false

namespace VariableRenaming

def weakenAt {S : Type u} (prefixContext : List S) {rest : List S} {introduced : S} :
    VariableRenaming (prefixContext ++ rest)
      (prefixContext ++ introduced :: rest) :=
  match prefixContext with
  | [] => fun entry => .there entry
  | _head :: tail => fun entry =>
      match entry with
      | .here => .here
      | .there previous => .there (weakenAt tail previous)

def swapAt {S : Type u} (prefixContext : List S) {rest : List S}
    {first second : S} :
    VariableRenaming (prefixContext ++ first :: second :: rest)
      (prefixContext ++ second :: first :: rest) :=
  match prefixContext with
  | [] => fun entry =>
      match entry with
      | .here => .there .here
      | .there previous =>
          match previous with
          | .here => .here
          | .there previous => .there (.there previous)
  | _head :: tail => fun entry =>
      match entry with
      | .here => .here
      | .there previous => .there (swapAt tail previous)

theorem weakenAt_cons_eq {S : Type u} (head : S)
    {prefixContext rest : List S} {introduced : S} :
    (weakenAt (head :: prefixContext) :
      VariableRenaming ((head :: prefixContext) ++ rest)
        ((head :: prefixContext) ++ introduced :: rest)) =
      @VariableRenaming.lift S
        (prefixContext ++ rest) (prefixContext ++ introduced :: rest)
        head (weakenAt prefixContext) := by
  funext resultSort entry
  cases entry <;> rfl

@[simp] theorem weakenAt_index {S : Type u} (prefixContext : List S)
    {rest : List S} {introduced s : S}
    (entry : Variable (prefixContext ++ rest) s) :
    (weakenAt (introduced := introduced) prefixContext entry).index =
      if entry.index < prefixContext.length then
        entry.index else entry.index + 1 := by
  induction prefixContext generalizing rest with
  | nil =>
      rfl
  | cons head tail ih =>
      cases entry with
      | here =>
          rfl
      | there previous =>
          by_cases hIndex : previous.index < tail.length
          · simp [weakenAt, Variable.index, ih, hIndex]
          · simp [weakenAt, Variable.index, ih, hIndex]

theorem swapAt_cons_eq {S : Type u} (head : S)
    {prefixContext rest : List S} {first second : S} :
    (swapAt (head :: prefixContext) :
      VariableRenaming ((head :: prefixContext) ++ first :: second :: rest)
        ((head :: prefixContext) ++ second :: first :: rest)) =
      @VariableRenaming.lift S
        (prefixContext ++ first :: second :: rest)
        (prefixContext ++ second :: first :: rest)
        head (swapAt prefixContext) := by
  funext resultSort entry
  cases entry <;> rfl

end VariableRenaming

namespace Term

def weakenBoundAt {σ : Signature.{u, v, w}}
    {rest free : SortContext σ}
    {introduced sort : σ.SortSymbol}
    (prefixContext : SortContext σ)
    (term : Term σ (prefixContext ++ rest) free sort) :
    Term σ (prefixContext ++ introduced :: rest) free sort :=
  term.renameMapped (VariableRenaming.weakenAt prefixContext)
    VariableRenaming.id

def swapBoundAt {σ : Signature.{u, v, w}}
    {rest free : SortContext σ}
    {first second sort : σ.SortSymbol}
    (prefixContext : SortContext σ)
    (term : Term σ (prefixContext ++ first :: second :: rest) free sort) :
    Term σ (prefixContext ++ second :: first :: rest) free sort :=
  term.renameMapped (VariableRenaming.swapAt prefixContext)
    VariableRenaming.id

end Term

namespace Arguments

def weakenBoundAt {σ : Signature.{u, v, w}}
    {rest free : SortContext σ} {introduced : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (prefixContext : SortContext σ)
    (arguments : Arguments σ (prefixContext ++ rest) free sorts) :
    Arguments σ (prefixContext ++ introduced :: rest) free sorts :=
  arguments.renameMapped (VariableRenaming.weakenAt prefixContext)
    VariableRenaming.id

def swapBoundAt {σ : Signature.{u, v, w}}
    {rest free : SortContext σ} {first second : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (prefixContext : SortContext σ)
    (arguments : Arguments σ (prefixContext ++ first :: second :: rest) free sorts) :
    Arguments σ (prefixContext ++ second :: first :: rest) free sorts :=
  arguments.renameMapped (VariableRenaming.swapAt prefixContext)
    VariableRenaming.id

end Arguments

namespace Formula

def weakenBoundAt {σ : Signature.{u, v, w}}
    {rest free : SortContext σ} {introduced : σ.SortSymbol}
    (prefixContext : SortContext σ)
    (formula : Formula σ (prefixContext ++ rest) free) :
    Formula σ (prefixContext ++ introduced :: rest) free :=
  formula.renameMapped (VariableRenaming.weakenAt prefixContext)
    VariableRenaming.id

def swapBoundAt {σ : Signature.{u, v, w}}
    {rest free : SortContext σ} {first second : σ.SortSymbol}
    (prefixContext : SortContext σ)
    (formula : Formula σ (prefixContext ++ first :: second :: rest) free) :
    Formula σ (prefixContext ++ second :: first :: rest) free :=
  formula.renameMapped (VariableRenaming.swapAt prefixContext)
    VariableRenaming.id

@[simp] theorem swapBoundAt_forallE
    {σ : Signature.{u, v, w}}
    {prefixContext rest free : SortContext σ}
    {first second introduced : σ.SortSymbol}
    (body : Formula σ
      (introduced :: (prefixContext ++ first :: second :: rest)) free) :
    (Formula.forallE introduced body).swapBoundAt prefixContext =
      .forallE introduced (body.swapBoundAt (introduced :: prefixContext)) := by
  change Formula.forallE introduced
      (body.renameMapped
        (@VariableRenaming.lift σ.SortSymbol
          (prefixContext ++ first :: second :: rest)
          (prefixContext ++ second :: first :: rest)
          introduced (VariableRenaming.swapAt prefixContext))
        VariableRenaming.id) =
      Formula.forallE introduced
        (body.renameMapped
          (VariableRenaming.swapAt (introduced :: prefixContext))
          VariableRenaming.id)
  rw [VariableRenaming.swapAt_cons_eq introduced]

@[simp] theorem swapBoundAt_existsE
    {σ : Signature.{u, v, w}}
    {prefixContext rest free : SortContext σ}
    {first second introduced : σ.SortSymbol}
    (body : Formula σ
      (introduced :: (prefixContext ++ first :: second :: rest)) free) :
    (Formula.existsE introduced body).swapBoundAt prefixContext =
      .existsE introduced (body.swapBoundAt (introduced :: prefixContext)) := by
  change Formula.existsE introduced
      (body.renameMapped
        (@VariableRenaming.lift σ.SortSymbol
          (prefixContext ++ first :: second :: rest)
          (prefixContext ++ second :: first :: rest)
          introduced (VariableRenaming.swapAt prefixContext))
        VariableRenaming.id) =
      Formula.existsE introduced
        (body.renameMapped
          (VariableRenaming.swapAt (introduced :: prefixContext))
          VariableRenaming.id)
  rw [VariableRenaming.swapAt_cons_eq introduced]

end Formula

def Term.swapBoundTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second sort : σ.SortSymbol}
    (term : Term σ (first :: second :: bound) free sort) :
    Term σ (second :: first :: bound) free sort :=
  term.renameMapped VariableRenaming.swapTop VariableRenaming.id

def Arguments.swapBoundTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ (first :: second :: bound) free sorts) :
    Arguments σ (second :: first :: bound) free sorts :=
  arguments.renameMapped VariableRenaming.swapTop VariableRenaming.id

def Formula.swapBoundTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol}
    (formula : Formula σ (first :: second :: bound) free) :
    Formula σ (second :: first :: bound) free :=
  formula.renameMapped VariableRenaming.swapTop VariableRenaming.id

@[simp] theorem Term.swapBoundTop_bvar
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second sort : σ.SortSymbol}
    (entry : Variable (first :: second :: bound) sort) :
    (Term.bvar entry : Term σ (first :: second :: bound) free sort).swapBoundTop =
      .bvar (VariableRenaming.swapTop entry) :=
  rfl

@[simp] theorem Term.swapBoundTop_fvar
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second sort : σ.SortSymbol}
    (entry : Variable free sort) :
    (Term.fvar entry : Term σ (first :: second :: bound) free sort).swapBoundTop =
      .fvar entry :=
  rfl

@[simp] theorem Term.swapBoundTop_app
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol}
    (function : σ.FuncSymbol)
    (arguments : Arguments σ (first :: second :: bound) free
      (σ.funcDomain function)) :
    (Term.app function arguments).swapBoundTop =
      .app function arguments.swapBoundTop :=
  rfl

@[simp] theorem Arguments.swapBoundTop_nil
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol} :
    (Arguments.nil : Arguments σ (first :: second :: bound) free []).swapBoundTop =
      .nil :=
  rfl

@[simp] theorem Arguments.swapBoundTop_cons
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second sort : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (head : Term σ (first :: second :: bound) free sort)
    (tail : Arguments σ (first :: second :: bound) free sorts) :
    (Arguments.cons head tail).swapBoundTop =
      .cons head.swapBoundTop tail.swapBoundTop :=
  rfl

@[simp] theorem Formula.swapBoundTop_falsum
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol} :
    (Formula.falsum : Formula σ (first :: second :: bound) free).swapBoundTop =
      .falsum :=
  rfl

@[simp] theorem Formula.swapBoundTop_truth
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol} :
    (Formula.truth : Formula σ (first :: second :: bound) free).swapBoundTop =
      .truth :=
  rfl

@[simp] theorem Formula.swapBoundTop_rel
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ (first :: second :: bound) free
      (σ.relDomain relation)) :
    (Formula.rel relation arguments).swapBoundTop =
      .rel relation arguments.swapBoundTop :=
  rfl

@[simp] theorem Formula.swapBoundTop_equal
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second sort : σ.SortSymbol}
    (left right : Term σ (first :: second :: bound) free sort) :
    (Formula.equal left right).swapBoundTop =
      .equal left.swapBoundTop right.swapBoundTop :=
  rfl

@[simp] theorem Formula.swapBoundTop_neg
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol}
    (body : Formula σ (first :: second :: bound) free) :
    (Formula.neg body).swapBoundTop =
      .neg body.swapBoundTop :=
  rfl

@[simp] theorem Formula.swapBoundTop_conj
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol}
    (left right : Formula σ (first :: second :: bound) free) :
    (Formula.conj left right).swapBoundTop =
      .conj left.swapBoundTop right.swapBoundTop :=
  rfl

@[simp] theorem Formula.swapBoundTop_disj
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol}
    (left right : Formula σ (first :: second :: bound) free) :
    (Formula.disj left right).swapBoundTop =
      .disj left.swapBoundTop right.swapBoundTop :=
  rfl

@[simp] theorem Formula.swapBoundTop_imp
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol}
    (left right : Formula σ (first :: second :: bound) free) :
    (Formula.imp left right).swapBoundTop =
      .imp left.swapBoundTop right.swapBoundTop :=
  rfl

@[simp] theorem Formula.swapBoundTop_iff
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol}
    (left right : Formula σ (first :: second :: bound) free) :
    (Formula.iff left right).swapBoundTop =
      .iff left.swapBoundTop right.swapBoundTop :=
  rfl

@[simp] theorem Formula.swapBoundTop_forallE
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second introduced : σ.SortSymbol}
    (body : Formula σ (introduced :: first :: second :: bound) free) :
    (Formula.forallE introduced body).swapBoundTop =
      .forallE introduced
        (body.renameMapped
          (VariableRenaming.lift VariableRenaming.swapTop)
          VariableRenaming.id) :=
  rfl

@[simp] theorem Formula.swapBoundTop_existsE
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second introduced : σ.SortSymbol}
    (body : Formula σ (introduced :: first :: second :: bound) free) :
    (Formula.existsE introduced body).swapBoundTop =
      .existsE introduced
        (body.renameMapped
          (VariableRenaming.lift VariableRenaming.swapTop)
          VariableRenaming.id) :=
  rfl

end FirstOrder
end Logic
end YesMetaZFC
