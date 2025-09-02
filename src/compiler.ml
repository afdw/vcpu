let entry_test () : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Feedback.msg_info (Pp.str "test")

let entry_compile (input_id : Names.Id.t) : unit =
  Feedback.msg_info (Pp.str "compile")
