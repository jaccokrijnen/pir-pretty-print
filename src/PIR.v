From Coq Require Import String.
#[local] Open Scope string_scope.
(* Restricted version of the AST from plutus-cert *)

Inductive recursivity := NonRec | Rec.

Inductive strictness := NonStrict | Strict.

Inductive DefaultUni : Type :=
    | DefaultUniInteger
    | DefaultUniByteString
    | DefaultUniString
    | DefaultUniUnit
    | DefaultUniBool
    | DefaultUniProtoList
    | DefaultUniProtoPair
    | DefaultUniData
    | DefaultUniBLS12_381_G1_Element
    | DefaultUniBLS12_381_G2_Element
    | DefaultUniBLS12_381_MlResult

    | DefaultUniApply : DefaultUni -> DefaultUni -> DefaultUni
    .

Inductive DefaultFun :=
  | AddInteger
  | SubtractInteger
  | MultiplyInteger
  | DivideInteger
  | QuotientInteger
  | RemainderInteger
  | ModInteger
  | EqualsInteger
  | LessThanInteger
  | LessThanEqualsInteger
.

Definition name := string.
Definition tyname := string.
Definition binderName := string.
Definition binderTyname := string.

Inductive ty :=
  | Ty_Builtin : DefaultUni -> ty
  | Ty_Fun : ty -> ty -> ty
.

Inductive vdecl := VarDecl : binderName -> ty -> vdecl.

(* for now, we trust the string representing a value is correct *)
Inductive term :=
  | Let      : recursivity -> list binding -> term -> term
  | Var      : string -> term
  | LamAbs   : string -> ty -> term -> term
  | Apply    : term -> term -> term
  | Builtin  : DefaultFun -> term
  | Constant : ty -> string -> term
  | Error    : ty -> term

with binding :=
  | TermBind : strictness -> vdecl -> term -> binding
.
