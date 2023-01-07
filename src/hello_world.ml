open Pp

let compile (id : Names.Id.t) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let constant_name = Names.Constant.make1 (Names.KerName.make (Global.current_modpath ()) (Names.Label.of_id id)) in
  if not (Environ.mem_constant constant_name env) then
    CErrors.user_err (str "Constant " ++ Names.Constant.print constant_name ++ str " does not exist.");
  let cb = Environ.lookup_constant constant_name env in
  match Global.body_of_constant_body Library.indirect_accessor cb with
  | Some (body, _, _) ->
    let body = EConstr.of_constr body in
    Feedback.msg_notice (Printer.pr_econstr_env env sigma body);
    let info = Declare.Info.make () in
    let cinfo = Declare.CInfo.make ~name:((id |> Names.Id.to_string) ^ "_circuit" |> Names.Id.of_string) ~typ:None () in
    let vector_type = EConstr.of_constr (UnivGen.constr_of_monomorphic_global env (Coqlib.lib_ref "vcpu.vector.type")) in
    let r = Declare.declare_definition ~info ~cinfo ~opaque:false ~body:vector_type sigma in
    ()
  | None ->
    CErrors.user_err (str "Constant " ++ Names.Constant.print constant_name ++ str " has no value.")
