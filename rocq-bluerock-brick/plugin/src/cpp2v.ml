(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
open Procq.Constr
open Stdarg

let lib_ref t =
  Rocqlib.lib_ref ("bedrock.lang.cpp.parser.translation_unit." ^ t)

let to_econstr t =
  match t with
  | Names.GlobRef.ConstRef c ->
    EConstr.mkConstU (c, EConstr.EInstance.empty)
  | _ ->
    Feedback.msg_debug Pp.(Names.GlobRef.print t) ;
    assert false

let decl_of_ref t =
  match lib_ref t with
  | Names.GlobRef.ConstRef c ->
    let decl = Global.lookup_constant c in
    decl
  | _ -> assert false

let force_body (t : _ Declarations.pconstant_body) =
  match t.const_body with
  | Declarations.Def d -> d
  | _ -> assert false

let cpp_command name (abi : Constrexpr.constr_expr) (defns : Constrexpr.constr_expr list) =
  (* Create the definition *)
  let env = Global.env() in
  let e_decl = to_econstr (lib_ref "t") in
  let e_decl_skip = to_econstr (lib_ref "skip") in
  let inst =
    match Constr.kind (decl_of_ref "empty_array").const_type with
    | Constr.App (f, _) ->
      begin
        match Constr.kind f with
        | Constr.Const (_, univs) -> univs
        | _ -> assert false
      end
    | _ -> assert false
  in
  let evd = Evd.from_env env in
  let abi , evd =
    let expected_type = Pretyping.OfType (to_econstr (lib_ref "abi_type")) in
    let abi , ustate = Constrintern.interp_constr ~expected_type env evd abi in
    (abi, Evd.from_ctx ustate)
  in
  let body , evd =
    let expected_type = Pretyping.OfType e_decl in
    List.fold_left (fun (acc, evd) defn ->
        (* TODO: the docs say that i should not use this function,
           but it doesn't seem like i can give an expected type to
           [Constrintern.interp_constr_evars] *)
        let body, ustate = Constrintern.interp_constr ~expected_type env evd defn in
        (body :: acc, Evd.from_ctx ustate)) ([], evd) defns
  in
  let body =
    EConstr.mkArray (EConstr.EInstance.make inst, Array.of_list (List.rev body), e_decl_skip, e_decl)
  in
  let body =
    EConstr.mkApp (to_econstr (lib_ref "decls"), [| body ; abi |])
  in
  let body =
    let rt = force_body (decl_of_ref "result_type") in
    Vnorm.cbv_vm env evd body (EConstr.of_constr rt)
  in
  match EConstr.kind evd body with
  | Constr.App (_, [| _ ; _ ; body ; err |]) ->
    begin
      match EConstr.kind evd err with
      | Constr.App (_, [| _ |]) ->
        let cinfo = Declare.CInfo.make ~name ~typ:None () in
        let info = Declare.Info.make () in
        let _ =
          Declare.declare_definition ~info ~cinfo ~opaque:false ~body evd
        in
        ()
      | _ -> assert false
    end
  | _ -> assert false
