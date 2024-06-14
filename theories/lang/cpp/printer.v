(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** A pretty printer for Stmt. iteratively written by ChatGPT with some human fixes
 https://chatgpt.com/share/c03723c0-90b1-45cb-bae9-dfd746f3c01a *)

Require Import ExtLib.Programming.Show.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.bytestring_core.
Require Import bedrock.prelude.bytestring.
Require Import bedrock.lang.cpp.syntax.stmt.
Require Import bedrock.lang.cpp.syntax.expr.
Require Import Coq.Strings.String.
Require Import bedrock.lang.cpp.syntax.names.
Require Import bedrock.lang.cpp.syntax.types.

Definition bitsize_printer (size : bitsize) : string :=
  match size with
  | W8 => "8"
  | W16 => "16"
  | W32 => "32"
  | W64 => "64"
  | W128 => "128"
  end.

(* Pretty printer for integer types *)
Definition int_type_printer (size : int_type.t) : string :=
  match size with
  | W8 => "char"
  | W16 => "short"
  | W32 => "int"
  | W64 => "long long"
  | W128 => "toobigint"
  end.


(* Pretty printer for type qualifiers *)
Definition type_qualifiers_printer (tq : type_qualifiers) : string :=
  match tq with
  | QCV => "const volatile"
  | QC => "const"
  | QV => "volatile"
  | QM => ""
  end.
Import pretty.
(* Pretty printer for types *)
Fixpoint type_printer (t : type) : string :=
  match t with
  | Tptr t' => type_printer t' ++ "*"
  | Tref t' => type_printer t' ++ "&"
  | Trv_ref t' => type_printer t' ++ "&&"
  | Tnum size signed =>
      let sign := if signed then "signed " else "unsigned " in
      sign ++ int_type_printer size
  | Tchar_ _ => "char"
  | Tvoid => "void"
  | Tarray t' n => type_printer t' ++ "[" ++ pretty n ++ "]"
  | Tincomplete_array t' => type_printer t' ++ "[]"
  | Tvariable_array t' => type_printer t' ++ "[]"
  | Tnamed gn => BS.to_string gn
  | Tenum gn => "enum " ++ BS.to_string gn
  | @Tfunction cc ar ret args =>
      let args_str := String.concat ", " (map type_printer args) in
      type_printer ret ++ " (" ++ args_str ++ ")"
  | Tbool => "bool"
  | Tmember_pointer gn t' => BS.to_string gn ++ "::*" ++ type_printer t'
  | Tfloat_ ft => "" (* float_type_printer ft *)
  | Tqualified tq t' => type_qualifiers_printer tq ++ " " ++ type_printer t'
  | Tnullptr => "nullptr_t"
  | Tarch _ name => "arch(" ++ BS.to_string name ++ ")"
  | Tunsupported bs => "unsupported(" ++ BS.to_string bs ++ ")"
  end.


Definition ident_printer : ident -> string:= BS.to_string.
Definition bs_printer : bs -> string := BS.to_string.

Definition Z_to_string (z:Z) : string := pretty z.
(* SwitchBranch pretty printer *)
Definition SwitchBranch_printer (branch : SwitchBranch) : string :=
  match branch with
  | Exact z => "case " ++ Z_to_string z
  | Range z1 z2 => "case " ++ Z_to_string z1 ++ " ... " ++ Z_to_string z2
  end.

(* UnOp pretty printer *)
Definition unop_printer (op : UnOp) : string :=
  match op with
  | Uminus => "-"
  | Uplus => "+"
  | Unot => "!"
  | Ubnot => "~"
  | Uunsupported bs => "unsupported(" ++ bs_printer bs ++ ")"
  end.

(* BinOp pretty printer *)
Definition binop_printer (op : BinOp) : string :=
  match op with
  | Badd => "+"
  | Band => "&"
  | Bcmp => "<=>"
  | Bdiv => "/"
  | Beq => "=="
  | Bge => ">="
  | Bgt => ">"
  | Ble => "<="
  | Blt => "<"
  | Bmul => "*"
  | Bneq => "!="
  | Bor => "|"
  | Bmod => "%"
  | Bshl => "<<"
  | Bshr => ">>"
  | Bsub => "-"
  | Bxor => "^"
  | Bdotp => ".*"
  | Bdotip => "->*"
  | Bunsupported bs => "unsupported(" ++ bs_printer bs ++ ")"
  end.

(* Recursive pretty printer for expressions *)
Fixpoint Expr_printer (e : Expr) : string :=
  match e with
  | Evar name _ => BS.to_string name
  | Eglobal name _ => BS.to_string name
  | Eenum_const gn id => BS.to_string gn ++ "::" ++ BS.to_string id
  | Echar n _ => "'" ++ String (pretty.pretty_N_char n) EmptyString ++ "'"
  | Estring s _ => String.concat "" (List.map (fun n=> String (pretty.pretty_N_char n) EmptyString) s)
  | Eint z _ => Z_to_string z
  | Ebool b => if b then "true" else "false"
  | Eunop op e1 _ => unop_printer op ++ Expr_printer e1
  | Ebinop op e1 e2 _ => Expr_printer e1 ++ " " ++ binop_printer op ++ " " ++ Expr_printer e2
  | Ederef e _ => "*" ++ Expr_printer e
  | Eaddrof e => "&" ++ Expr_printer e
  | Eassign e1 e2 _ => Expr_printer e1 ++ " = " ++ Expr_printer e2
  | Eassign_op op e1 e2 _ => Expr_printer e1 ++ " " ++ binop_printer op ++ "= " ++ Expr_printer e2
  | Epreinc e _ => "++" ++ Expr_printer e
  | Epostinc e _ => Expr_printer e ++ "++"
  | Epredec e _ => "--" ++ Expr_printer e
  | Epostdec e _ => Expr_printer e ++ "--"
  | Eseqand e1 e2 => Expr_printer e1 ++ " && " ++ Expr_printer e2
  | Eseqor e1 e2 => Expr_printer e1 ++ " || " ++ Expr_printer e2
  | Ecomma e1 e2 => Expr_printer e1 ++ ", " ++ Expr_printer e2
  | Ecall f args _ => Expr_printer f ++ "(" ++ String.concat ", " (map Expr_printer args) ++ ")"
  | Ecast _ e _ _ => "(" ++ Expr_printer e ++ ")"
  | Emember e id _ _ => Expr_printer e ++ "." ++ BS.to_string id
  | Emember_call _ e args _ => Expr_printer e ++ "(" ++ String.concat ", " (map Expr_printer args) ++ ")"
  | Eoperator_call _ _ args _ => "(" ++ String.concat ", " (map Expr_printer args) ++ ")"
  | Esubscript e1 e2 _ => Expr_printer e1 ++ "[" ++ Expr_printer e2 ++ "]"
  | Esizeof _ _ => "sizeof"
  | Ealignof _ _ => "alignof"
  | Eoffsetof _ id _ => "offsetof(" ++ BS.to_string id ++ ")"
  | Econstructor name args _ => BS.to_string name ++ "(" ++ String.concat ", " (map Expr_printer args) ++ ")"
  | Eimplicit e => Expr_printer e
  | Eimplicit_init _ => "implicit_init"
  | Eif cond then_expr else_expr _ _ => "if (" ++ Expr_printer cond ++ ") " ++ Expr_printer then_expr ++ " else " ++ Expr_printer else_expr
  | Eif2 _ _ cond then_expr else_expr _ _ => "if (" ++ Expr_printer cond ++ ") " ++ Expr_printer then_expr ++ " else " ++ Expr_printer else_expr
  | Ethis _ => "this"
  | Enull => "null"
  | Einitlist exprs _ _ => "{" ++ String.concat ", " (map Expr_printer exprs) ++ "}"
  | Enew _ args _ _ _ _ => "new(" ++ String.concat ", " (map Expr_printer args) ++ ")"
  | Edelete _ _ e _ => "delete " ++ Expr_printer e
  | Eandclean e => Expr_printer e
  | Ematerialize_temp e _ => Expr_printer e
  | Eatomic _ exprs _ => "atomic(" ++ String.concat ", " (map Expr_printer exprs) ++ ")"
  | Eva_arg e _ => Expr_printer e
  | Epseudo_destructor _ _ e => Expr_printer e
  | Earrayloop_init _ e _ _ _ _ => Expr_printer e
  | Earrayloop_index _ _ => "arrayloop_index"
  | Eopaque_ref _ _ _ => "opaque_ref"
  | Eunsupported _ _ _ => "unsupported"
  end.

(* Helper function to handle option types *)
Definition option_map {A} (f : A -> string) (o : option A) : string :=
  match o with
  | Some x => f x
  | None => ""
  end.

Fixpoint VarDecl'_printer (v : VarDecl' obj_name type Expr) : string :=
  match v with
  | Dvar name t init =>
      type_printer t ++ " " ++ BS.to_string name ++
      match init with
      | Some e => " = " ++ Expr_printer e
      | None => ""
      end
  | _ => ""
(*  | Ddecompose e anon_var decls =>
      "decompose " ++ Expr_printer e ++ " " ++ BS.to_string anon_var ++
      String.concat ", " (map VarDecl'_printer decls)
  | Dinit thread_safe name t init =>
      (if thread_safe then "thread_local " else "") ++ name ++ " " ++ type_printer t ++
      match init with
      | Some e => " = " ++ Expr_printer e
      | None => ""
      end*)
  end.
Definition newline := String Char.chr_newline EmptyString.
(* Recursive pretty printer for statements *)
Open Scope string_scope.

(* Function to generate indentation *)
Search nat string.
Definition indent (n : nat) : string :=
  String.concat "" (map (fun _ => " ") (seq 0 n)).

(* Recursive pretty printer for statements with indentation *)
Fixpoint Stmt_printer (current_indentation : nat) (s : Stmt) : string :=
  let indent_str := indent current_indentation in
  match s with
  | Sseq stmts =>
      indent_str ++ "{" ++ newline ++
      String.concat newline (map (Stmt_printer (current_indentation + 2)) stmts) ++
      newline ++ indent_str ++ "}"
  | Sdecl decls =>
      indent_str ++ String.concat (String.append ";" newline) (map VarDecl'_printer decls) ++ ";"
  | Sif None cond then_stmt else_stmt =>
      indent_str ++ "if (" ++ Expr_printer cond ++ ")" ++ newline ++
      Stmt_printer (current_indentation + 2) then_stmt ++ newline ++
      indent_str ++ "else" ++ newline ++
      Stmt_printer (current_indentation + 2) else_stmt
  | Sif (Some decl) cond then_stmt else_stmt =>
      indent_str ++ "if (" ++ VarDecl'_printer decl ++ "; " ++ Expr_printer cond ++ ")" ++ newline ++
      Stmt_printer (current_indentation + 2) then_stmt ++ newline ++
      indent_str ++ "else" ++ newline ++
      Stmt_printer (current_indentation + 2) else_stmt
  | Swhile None cond body =>
      indent_str ++ "while (" ++ Expr_printer cond ++ ")" ++ newline ++
      Stmt_printer (current_indentation + 2) body
  | Swhile (Some decl) cond body =>
      indent_str ++ "while (" ++ VarDecl'_printer decl ++ "; " ++ Expr_printer cond ++ ")" ++ newline ++
      Stmt_printer (current_indentation + 2) body
  | Sfor init cond step body =>
      indent_str ++ "for (" ++ option_map (Stmt_printer 0) init ++ "; " ++
      option_map Expr_printer cond ++ "; " ++ option_map Expr_printer step ++ ")" ++ newline ++
      Stmt_printer (current_indentation + 2) body
  | Sdo body cond =>
      indent_str ++ "do" ++ newline ++
      Stmt_printer (current_indentation + 2) body ++ newline ++
      indent_str ++ "while (" ++ Expr_printer cond ++ ");"
  | Sswitch None cond body =>
      indent_str ++ "switch (" ++ Expr_printer cond ++ ")" ++ newline ++
      Stmt_printer (current_indentation + 2) body
  | Sswitch (Some decl) cond body =>
      indent_str ++ "switch (" ++ VarDecl'_printer decl ++ "; " ++ Expr_printer cond ++ ")" ++ newline ++
      Stmt_printer (current_indentation + 2) body
  | Scase branch =>
      indent_str ++ SwitchBranch_printer branch ++ ":"
  | Sdefault =>
      indent_str ++ "default:"
  | Sbreak =>
      indent_str ++ "break;"
  | Scontinue =>
      indent_str ++ "continue;"
  | Sreturn None =>
      indent_str ++ "return;"
  | Sreturn (Some expr) =>
      indent_str ++ "return " ++ Expr_printer expr ++ ";"
  | Sexpr expr =>
      indent_str ++ Expr_printer expr ++ ";"
  | Sattr attrs stmt =>
      indent_str ++ String.concat " " (map ident_printer attrs) ++ " " ++
      Stmt_printer current_indentation stmt
  | Sasm asm_code volatile inputs outputs clobbers =>
      indent_str ++ "__asm__ (" ++ bs_printer asm_code ++ ")"
      ++ (if volatile then " volatile" else "")
      ++ " : " ++ String.concat ", " (map (fun '(i, e) => ident_printer i ++ "(" ++ Expr_printer e ++ ")") outputs)
      ++ " : " ++ String.concat ", " (map (fun '(i, e) => ident_printer i ++ "(" ++ Expr_printer e ++ ")") inputs)
      ++ " : " ++ String.concat ", " (map ident_printer clobbers) ++ ";"
  | Slabeled label stmt =>
      indent_str ++ ident_printer label ++ ": " ++
      Stmt_printer current_indentation stmt
  | Sgoto label =>
      indent_str ++ "goto " ++ ident_printer label ++ ";"
  | Sunsupported _ => ""
  end.

(* Example use: Uncomment to test pretty printer *)
Locate Sreturn_val.
Require Import bedrock.lang.cpp.parser.

Definition     gcd_body : Stmt :=       (Sseq (
                (Swhile None
                  (Ebinop Bneq
                    (Ecast Cl2r (Evar "b" Tuint) Prvalue Tuint)
                    (Ecast Cintegral (Eint 0%Z Tint) Prvalue Tuint) Tbool)
                  (Sseq (
                      (Sdecl (
                          (Dvar "temp" Tuint
                            (Some
                              (Ecast Cl2r (Evar "b" Tuint) Prvalue Tuint))) :: nil)) ::
                      (Sexpr
                        (Eassign (Evar "b" Tuint)
                          (Ebinop Bmod
                            (Ecast Cl2r (Evar "a" Tuint) Prvalue Tuint)
                            (Ecast Cl2r (Evar "b" Tuint) Prvalue Tuint) Tuint) Tuint)) ::
                      (Sexpr
                        (Eassign (Evar "a" Tuint)
                          (Ecast Cl2r (Evar "temp" Tuint) Prvalue Tuint) Tuint)) :: nil))) ::
                (Sreturn_val
                  (Ecast Cl2r (Evar "a" Tuint) Prvalue Tuint)) :: nil)).

Open Scope bs_scope.
Import BS.Bytestring_notations.


  Definition split_body : Stmt :=
    (Sseq
   [Sdecl [Dvar "which" Tbool (Some (Ebool true))];
    Swhile None
      (Ecast Cptr2bool (Ecast Cl2r (Evar "ab" (Tptr (Tnamed "_Z4Node"))) Prvalue (Tptr (Tnamed "_Z4Node"))) Prvalue
         Tbool)
      (Sseq
         [Sdecl
            [Dvar "temp" (Tptr (Tnamed "_Z4Node"))
               (Some
                  (Ecast Cl2r
                     (expr.Emember
                        (Ederef (Ecast Cl2r (Evar "ab" (Tptr (Tnamed "_Z4Node"))) Prvalue (Tptr (Tnamed "_Z4Node")))
                           (Tnamed "_Z4Node")) "next_" false (Tptr (Tnamed "_Z4Node"))) Prvalue
                     (Tptr (Tnamed "_Z4Node"))))];
          Sif None (Ecast Cl2r (Evar "which" Tbool) Prvalue Tbool)
            (Sseq
               [Sexpr
                  (Eassign
                     (expr.Emember
                        (Ederef (Ecast Cl2r (Evar "ab" (Tptr (Tnamed "_Z4Node"))) Prvalue (Tptr (Tnamed "_Z4Node")))
                           (Tnamed "_Z4Node")) "next_" false (Tptr (Tnamed "_Z4Node")))
                     (Ecast Cl2r (Evar "a" (Tref (Tptr (Tnamed "_Z4Node")))) Prvalue (Tptr (Tnamed "_Z4Node")))
                     (Tptr (Tnamed "_Z4Node")));
                Sexpr
                  (Eassign (Evar "a" (Tref (Tptr (Tnamed "_Z4Node"))))
                     (Ecast Cl2r (Evar "ab" (Tptr (Tnamed "_Z4Node"))) Prvalue (Tptr (Tnamed "_Z4Node")))
                     (Tptr (Tnamed "_Z4Node")))])
            (Sseq
               [Sexpr
                  (Eassign
                     (expr.Emember
                        (Ederef (Ecast Cl2r (Evar "ab" (Tptr (Tnamed "_Z4Node"))) Prvalue (Tptr (Tnamed "_Z4Node")))
                           (Tnamed "_Z4Node")) "next_" false (Tptr (Tnamed "_Z4Node")))
                     (Ecast Cl2r (Evar "b" (Tref (Tptr (Tnamed "_Z4Node")))) Prvalue (Tptr (Tnamed "_Z4Node")))
                     (Tptr (Tnamed "_Z4Node")));
                Sexpr
                  (Eassign (Evar "b" (Tref (Tptr (Tnamed "_Z4Node"))))
                     (Ecast Cl2r (Evar "ab" (Tptr (Tnamed "_Z4Node"))) Prvalue (Tptr (Tnamed "_Z4Node")))
                     (Tptr (Tnamed "_Z4Node")))]);
          Sexpr
            (Eassign (Evar "ab" (Tptr (Tnamed "_Z4Node")))
               (Ecast Cl2r (Evar "temp" (Tptr (Tnamed "_Z4Node"))) Prvalue (Tptr (Tnamed "_Z4Node")))
               (Tptr (Tnamed "_Z4Node")));
          Sexpr (Eassign (Evar "which" Tbool) (Eunop Unot (Ecast Cl2r (Evar "which" Tbool) Prvalue Tbool) Tbool) Tbool)])]).
Definition foo: string :=
     "
{
  while ((b) != (0))
    {
      unsigned int temp = (b);
      b = (a) % (b);
      a = (temp);
    }
  return (a);
}".


(* this example may not run correctly in emacs+proof-general https://github.com/ProofGeneral/PG/issues/773 *)
 Example t1: (BS.of_string (newline++Stmt_printer 0 gcd_body))
     = "
{
  while ((b) != (0))
    {
      unsigned int temp = (b);
      b = (a) % (b);
      a = (temp);
    }
  return (a);
}".
 Proof.
   reflexivity.
 Abort.

Example t2: (BS.of_string (newline++Stmt_printer 0 split_body))
     = "
{
  bool which = true;
  while (((ab)))
    {
      _Z4Node* temp = (*(ab).next_);
      if ((which))
        {
          *(ab).next_ = (a);
          a = (ab);
        }
      else
        {
          *(ab).next_ = (b);
          b = (ab);
        }
      ab = (temp);
      which = !(which);
    }
}".
Proof.
  reflexivity.
Abort.
