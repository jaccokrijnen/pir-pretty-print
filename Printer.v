
Require Import Strings.String.
Open Scope string.

From SimpleIO Require Import SimpleIO.
From Coq Require Import String.
#[local] Open Scope string_scope.



Inductive DefaultUni : Type :=
  | DefaultUniInteger
.

Inductive ty :=
  | Ty_Builtin : DefaultUni -> ty
.

Inductive term :=
  | Var      : string -> term
  | LamAbs   : string -> ty -> term -> term
.


(* λ(x : Int) . x *)
Definition identity_ast : term :=
  LamAbs "x" (Ty_Builtin DefaultUniInteger) (Var "x")
.

Definition x := "test" ++ "test".

Definition parens : string -> string :=
  fun x => "(" ++ x ++ ")"
.

Fixpoint pretty_print_DefaultUni (D : DefaultUni) : string :=
  match D with
  | DefaultUniInteger => "integer"
  end
.

Fixpoint pretty_print_ty (T : ty) : string :=
  match T with
  | Ty_Builtin D => "con " ++ pretty_print_DefaultUni D
  end
.

Fixpoint pretty_print' (t : term) : string :=
  match t with
  | Var x => x
  | LamAbs x T t => parens (
      "lam " ++ x ++ " "
      ++ parens (pretty_print_ty T)
      ++ " " ++ (pretty_print' t)
    )
  end
.

Definition print_as_program (t : term) :=
  parens ("program" ++ " " ++ "1.1.0" ++ " " ++
    (pretty_print' t)
  )
.
Import IO.Notations.

Eval cbv in (print_as_program identity_ast).
Definition main : IO unit :=
  chan <- open_out "test.pir" ;;
  output_string chan (print_as_program identity_ast) ;;
  close_out chan
.

RunIO main.
