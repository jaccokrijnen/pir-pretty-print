From Coq Require Import String BinInt List.

(* printing functionality *)
From SimpleIO Require Import SimpleIO.
(* afaik Coq has no builtin string conversion methods
for its primitive types so we import the ones from QuickChick *)
From QuickChick Require Import Show.
Import ShowFunctions.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

From PPIR Require Import PIR.

Definition parens : string -> string :=
  fun x => "(" ++ x ++ ")"
.

Definition brackets : string -> string :=
  fun x => "[" ++ x ++ "]"
.

#[global]
Instance ShowRec : Show recursivity :=
{|
  show rec := match rec with
  | NonRec => "nonrec"
  | Rec    => "rec" 
  end
|}.

#[global]
Instance ShowStrictness : Show strictness :=
{|
  show st := match st with
  | NonStrict => "nonstrict"
  | Strict    => "strict" 
  end
|}.

Fixpoint show_DefaultUni (U : DefaultUni) : string :=
  match U with
  | DefaultUniInteger => "integer"
  | DefaultUniByteString => "bytestring"
  | DefaultUniString => "string"
  | DefaultUniUnit => "unit"
  | DefaultUniBool => "bool"
  | DefaultUniProtoList => "list" (* is this correct? *)
  | DefaultUniProtoPair => "pair"
  | DefaultUniData => "data"
  | DefaultUniBLS12_381_G1_Element => "bls12_381_G1_element"
  | DefaultUniBLS12_381_G2_Element => "bls12_381_G2_element"
  | DefaultUniBLS12_381_MlResult => "bls12_381_mlresult"

  | DefaultUniApply U1 U2 =>
      parens ((show_DefaultUni U1) ++ " " ++ (show_DefaultUni U2)) 
  end
.

#[global]
Instance ShowDefaultUni : Show DefaultUni :=
{|
  show := show_DefaultUni
|}.

(* Definition show_Constant (cst : constant) : string :=
  let val := match cst with
  (* | ValueOf uni val => "con " ++ show uni ++ " " ++ show val end in (* possible to infer show? *) *)
  | ValueOf DefaultUniInteger z => show_Z z
  | ValueOf DefaultUniByteString bs => "NotImplemented:bs"
  | ValueOf DefaultUniString str => "NotImplemented:str"
  | ValueOf DefaultUniUnit u => "unit"
  | ValueOf DefaultUniData d => "NotImplemented:data"
  | ValueOf DefaultUniBLS12_381_G1_Element z => show_Z z
  | ValueOf DefaultUniBLS12_381_G2_Element z => show_Z z
  | ValueOf DefaultUniBLS12_381_MlResult z => show_Z z
  | ValueOf DefaultUniBool b => show_bool b
  | _ => "UnknownUniverse" end in
  "con " ++ match cst with (ValueOf uni _) => show uni end ++ " " ++ val
. *)

(* #[global]
Instance ShowConstant : Show constant :=
{|
  show := show_Constant
|}. *)

#[global]
Instance ShowDefaultFun : Show DefaultFun :=
{|
  show df := match df with
  | AddInteger => "addInteger"
  | SubtractInteger => "subtractInteger"
  | MultiplyInteger => "multiplyInteger"
  | DivideInteger => "divideInteger"
  | QuotientInteger => "quotientInteger"
  | RemainderInteger => "remainderInteger"
  | ModInteger => "modInteger"
  | EqualsInteger => "equalsInteger"
  | LessThanInteger => "lessThanInteger"
  | LessThanEqualsInteger => "lessThanEqualsInteger"
  end
|}.

Fixpoint show_ty (T : ty) : string :=
  match T with
  | Ty_Builtin D => "con " ++ show D
  | Ty_Fun T1 T2 => "fun " ++ (show_ty T1) ++ " " ++ (show_ty T2)
  end
.

#[global]
Instance ShowTy : Show ty :=
{|
  show := show_ty
|}.

Definition show_vdecl (vd : vdecl) : string :=
  match vd with
  | VarDecl bn T => "vardecl " ++ bn ++ " " ++ parens (show T) end
.

#[global]
Instance ShowVDecl : Show vdecl :=
{|
  show := show_vdecl
|}.

Fixpoint show_term (t : term) : string :=
  match t with
  | Let rec bds t => parens (
      "let " ++ parens (show rec) ++ " "
      ++ string_concat (map show_binding bds)
      ++ " " ++ show_term t)
  | Var x => x
  | LamAbs x T t => parens (
      "lam " ++ x ++ " "
      ++ parens (show T)
      ++ " " ++ show_term t)
  | Apply t1 t2 => brackets ((show_term t1) ++ " " ++ show_term t2)
  | Builtin def => parens ("builtin " ++ (show def))
  | Error T => parens ("error " ++ show T)
  (* | Constant cst => parens (show cst) *)
  | Constant T cst => parens (show T) ++ " " ++ parens cst
  end

with show_binding (b : binding) : string := 
  match b with
  | TermBind strc vdecl t => parens (
      "termbind " ++ parens (show strc)
      ++ " " ++ parens (show vdecl)
      ++ " " ++ show_term t) end
.

#[global]
Instance ShowTerm : Show term :=
{|
  show := show_term
|}.

Definition print_as_program (t : term) :=
  parens ("program" ++ " " ++ "1.1.0" ++ " " ++ show t)
.

(* λ(x : Int) . x *)
Definition identity_ast : term :=
  LamAbs "x" (Ty_Builtin DefaultUniInteger) (Var "x")
.

(* (λ(x : Int) . (λ(y : Int). x + y)) 1 *)
Definition plus_ast : term :=
  (Apply
    (LamAbs "x" (Ty_Builtin DefaultUniInteger)
      (LamAbs "y" (Ty_Builtin DefaultUniInteger)
        (Apply (Apply (Builtin AddInteger) (Var "x")) (Var "y"))))
  (Constant (Ty_Builtin DefaultUniInteger) "1")).

Definition let_ast : term :=
  (Let NonRec 
    [(TermBind Strict 
        (VarDecl "x" (Ty_Builtin DefaultUniInteger)) 
        (Error (Ty_Builtin DefaultUniInteger)))]
    (Apply 
      (Apply (Builtin EqualsInteger)
             (Apply 
                (Apply (Builtin AddInteger) (Constant (Ty_Builtin DefaultUniInteger) "10"))
                (Var "x")))
      (Constant (Ty_Builtin DefaultUniInteger) "5"))).

Import IO.Notations.

Definition test_file := let_ast.
Eval cbv in (print_as_program test_file).
Definition main : IO unit :=
  chan <- open_out "printing/test.pir" ;;
  output_string chan (print_as_program test_file) ;;
  close_out chan
.

RunIO main.
