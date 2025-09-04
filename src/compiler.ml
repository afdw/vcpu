let reduce_right (type a) (f : a -> a -> a) (l : a list) : a =
  List.fold_right f (CList.drop_last l) (CList.last l)

let reduce_right_i (type a) (f : int -> a -> a -> a) (l : a list) : a =
  CList.fold_right_i f 0 (CList.drop_last l) (CList.last l)

exception Dependent

let rec decompose_arrows (sigma : Evd.evar_map) (c : EConstr.t) : EConstr.t list * EConstr.t =
  match EConstr.kind sigma c with
  | Prod (_, hyp, c) ->
    let hyps', concl = decompose_arrows sigma c in
    if hyps' |> List.for_all (EConstr.Vars.noccurn sigma 1) && concl |> EConstr.Vars.noccurn sigma 1 then
      hyp :: (hyps' |> List.map (EConstr.Vars.subst1 EConstr.mkProp)), concl |> EConstr.Vars.subst1 EConstr.mkProp
    else
      raise Dependent
  | LetIn _ -> assert false
  | Cast (c, _, _) -> decompose_arrows sigma c
  | _ -> [], c

let rec compose_arrows (hyps : EConstr.t list) (concl : EConstr.t) : EConstr.t =
  match hyps with
  | [] -> concl
  | hyp :: hyps' -> EConstr.mkProd (EConstr.anonR, hyp, EConstr.Vars.lift 1 (compose_arrows hyps' concl))

let get_ref (env : Environ.env) (s : string) : EConstr.t =
  EConstr.of_constr (UnivGen.constr_of_monomorphic_global env (Rocqlib.lib_ref s))

let dest_const_ref (glob_ref : Names.GlobRef.t) : Names.Constant.t =
  match glob_ref with
  | ConstRef t -> t
  | _ -> assert false

let dest_ind_ref (glob_ref : Names.GlobRef.t) : Names.Ind.t =
  match glob_ref with
  | IndRef t -> t
  | _ -> assert false

let mk_bool_type (env : Environ.env) : EConstr.t =
  get_ref env "core.bool.type"

let to_bool_constr (env : Environ.env) (b : bool) : EConstr.t =
  if b then get_ref env "core.bool.true" else get_ref env "core.bool.false"

let mk_nat_type (env : Environ.env) : EConstr.t =
  get_ref env "num.nat.type"

let rec to_nat_constr (env : Environ.env) (n : int) : EConstr.t =
  assert (n >= 0);
  if n = 0 then
    get_ref env "num.nat.O"
  else
    EConstr.mkApp (
      get_ref env "num.nat.S",
      [|to_nat_constr env (n - 1)|]
    )

let mk_nat_add (env : Environ.env) (n : EConstr.t) (m : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "num.nat.add", [|n; m|])

let prove_nat_eq (env : Environ.env) (n : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "core.eq.refl", [|mk_nat_type env; n|])

let rec to_list_constr (env : Environ.env) (typ : EConstr.t) (l : EConstr.t list) : EConstr.t =
  match l with
  | [] -> EConstr.mkApp (get_ref env "core.list.nil", [|typ|])
  | c :: l' -> EConstr.mkApp (get_ref env "core.list.cons", [|typ; c; to_list_constr env typ l'|])

let rec of_list_constr (env : Environ.env) (sigma : Evd.evar_map) (c : EConstr.t) : EConstr.t list =
  match EConstr.kind sigma c with
  | App (head, [|_|]) when EConstr.eq_constr sigma head (get_ref env "core.list.nil") -> []
  | App (f, [|_; a; c'|]) when EConstr.eq_constr sigma f (get_ref env "core.list.cons") ->
    a :: of_list_constr env sigma c'
  | _ -> CErrors.user_err Pp.(str "Not an application of nil or cons:" ++ spc () ++ Printer.pr_econstr_env env sigma c)

let mk_vector_type (env : Environ.env) (element_typ : EConstr.t) (len : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "vcpu.vector.type", [|element_typ; len|])

let dest_vector_type (env : Environ.env) (sigma : Evd.evar_map) (typ : EConstr.t) : EConstr.t * EConstr.t =
  match EConstr.kind sigma typ with
  | App (typ_head, [|element_typ; len|]) when EConstr.eq_constr sigma typ_head (get_ref env "vcpu.vector.type") ->
    (element_typ, len)
  | _ -> CErrors.user_err Pp.(str "Not an application of vector:" ++ spc () ++ Printer.pr_econstr_env env sigma typ)

let to_vector_constr (env : Environ.env) (typ : EConstr.t) (l : EConstr.t list) : EConstr.t =
  EConstr.mkApp (
    get_ref env "vcpu.vector.constructor",
    [|
      typ;
      to_nat_constr env (l |> List.length);
      to_list_constr env typ l;
      prove_nat_eq env (to_nat_constr env (l |> List.length));
    |]
  )

let mk_vector_repeat (env : Environ.env) (typ : EConstr.t) (x : EConstr.t) (n : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "vcpu.vector.repeat", [|typ; x; n|])

let mk_vector_app (env : Environ.env) (typ : EConstr.t) (length_u : EConstr.t) (length_v : EConstr.t) (u : EConstr.t) (v : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "vcpu.vector.app", [|typ; length_u; length_v; u; v|])

type encoder = {
  encoder_len : EConstr.t;
  encoder_encode : EConstr.t;
}

let lift_encoder (n : int) (encoder : encoder) : encoder =
  {
    encoder_len = encoder.encoder_len |> EConstr.Vars.lift n;
    encoder_encode = encoder.encoder_encode |> EConstr.Vars.lift n;
  }

let saved_encoders : (Names.Ind.t * encoder) list ref = Summary.ref ~name:"vcpu_saved_encoders" []

let cache_saved_encoder ((ind, ind_encoder) : (Names.Ind.t * encoder)) : unit =
  saved_encoders := (ind, ind_encoder) :: !saved_encoders

let in_saved_encoders : (Names.Ind.t * encoder) -> Libobject.obj =
  Libobject.declare_object {
    (Libobject.default_object "vcpu_saved_encoders") with
    load_function = (fun _ -> cache_saved_encoder);
    cache_function = cache_saved_encoder;
    classify_function = (fun _ -> Keep);
  }

let add_saved_encoder ((ind, ind_encoder) : (Names.Ind.t * encoder)) : unit =
  Lib.add_leaf (in_saved_encoders (ind, ind_encoder))

let rec create_encoder (env : Environ.env) (sigma : Evd.evar_map) (context_encoders : encoder option list) (type_ : EConstr.t) : encoder option =
  let exception Static in
  Feedback.msg_info Pp.(str "create_encoder" ++ spc () ++ Printer.pr_econstr_env env sigma type_);
  let type_ = Tacred.hnf_constr0 env sigma type_ in
  let type_head, type_args = EConstr.decompose_app sigma type_ in
  match EConstr.kind sigma type_head, type_args with
  | Rel n, [||] -> List.nth context_encoders (n - 1)
  | Sort _, [||] -> None
  | Prod _, [||] -> None
  | Ind (ind, u), type_args ->
    let (mib, mip) = Inductive.lookup_mind_specif env ind in
    (match mip.mind_sort with
    | SProp | Prop -> None
    | QSort _ -> assert false
    | Set | Type _ ->
      if
        (mib.mind_record = NotRecord || mib.mind_record = FakeRecord) &&
        (mib.mind_finite = Finite || mib.mind_finite = BiFinite) &&
        mib.mind_ntypes = 1 &&
        mib.mind_hyps = [] &&
        mib.mind_nparams_rec = mib.mind_nparams &&
        List.length mib.mind_params_ctxt = mib.mind_nparams &&
        Array.length mip.mind_nf_lc > 0 &&
        mip.mind_nrealdecls = 0 &&
        mip.mind_consnrealargs = mip.mind_consnrealdecls &&
        Declareops.dest_subterms mip.mind_recargs |> Array.for_all (fun ras ->
          ras |> List.for_all (fun ra ->
            Declareops.dest_recarg ra = Norec
          )
        )
      then (
        assert (Array.length type_args = mib.mind_nparams);
        let params = type_args in
        let type_encoder_existing =
          try
            match !saved_encoders |> List.assoc_opt ind with
            | Some ind_encoder ->
              let param_encoders =
                params
                  |> Array.map (create_encoder env sigma context_encoders)
                  |> Array.map (fun encoder ->
                    match encoder with
                    | Some encoder -> encoder
                    | None -> raise Static
                  ) in
              let ind_encoder_args =
                Array.map2 (fun param param_encoder ->
                  [param; param_encoder.encoder_len; param_encoder.encoder_encode]
                ) params param_encoders |> Array.to_list |> List.flatten |> Array.of_list in
              Some {
                encoder_len = EConstr.mkApp (ind_encoder.encoder_len, ind_encoder_args);
                encoder_encode = EConstr.mkApp (ind_encoder.encoder_encode, ind_encoder_args);
              }
            | None -> None
          with Static -> None in
        match type_encoder_existing with
        | Some type_encoder_existing -> Some type_encoder_existing
        | None ->
          try
            let constructor_types_hyps_concl =
              mip.mind_nf_lc |> Array.map (fun (ctx, concl) ->
                decompose_arrows sigma (
                  EConstr.Vars.substl
                    (List.rev (Array.to_list params))
                    (EConstr.of_constr (Term.it_mkProd_or_LetIn concl (ctx |> List.take (List.length ctx - mib.mind_nparams))))
                )
              ) in
            constructor_types_hyps_concl |> Array.iter (fun (constructor_type_hyps, constructor_type_concl) ->
              assert (EConstr.eq_constr sigma constructor_type_concl type_);
              ()
            );
            let constructor_types_hyp_encoders =
              constructor_types_hyps_concl |> Array.map (fun (constructor_type_hyps, _) ->
                constructor_type_hyps
                  |> List.map (create_encoder env sigma context_encoders)
                  |> List.map (fun encoder ->
                    match encoder with
                    | Some encoder -> encoder
                    | None -> raise Static
                  )
              ) in
            let constructor_type_lens =
              constructor_types_hyp_encoders
                |> Array.map (fun constructor_type_hyp_encoders ->
                  List.fold_right (fun len_1 len_2 ->
                    mk_nat_add env len_1.encoder_len len_2
                  ) constructor_type_hyp_encoders (to_nat_constr env 0)
                ) in
            let type_len =
              constructor_type_lens
                |> Array.to_list
                |> reduce_right (fun len_1 len_2 ->
                  mk_nat_add env (to_nat_constr env 1) (mk_nat_add env len_1 len_2)
                ) in
            Feedback.msg_info Pp.(str "type_len" ++ spc () ++ Printer.pr_econstr_env env sigma type_len);
            let type_encode =
              EConstr.mkLambda (
                EConstr.anonR,
                type_,
                EConstr.mkCase (
                  Inductiveops.make_case_info env ind Constr.RegularStyle,
                  u,
                  params |> Array.map (EConstr.Vars.lift 1),
                  (
                    (
                      [|EConstr.anonR|],
                      mk_vector_type env (mk_bool_type env) (type_len |> EConstr.Vars.lift 2)
                    ),
                    EConstr.ERelevance.relevant
                  ),
                  Constr.NoInvert,
                  EConstr.mkRel 1,
                  constructor_types_hyp_encoders |> Array.mapi (fun constructor_1_i constructor_1_types_hyp_encoders ->
                    (
                      constructor_1_types_hyp_encoders |> CArray.map_of_list (fun _ -> EConstr.anonR),
                      (constructor_type_lens
                        |> Array.mapi (fun constructor_2_i constructor_2_type_len ->
                          let constructor_1_types_hyp_encoders =
                            constructor_1_types_hyp_encoders |> List.map (lift_encoder (1 + List.length constructor_1_types_hyp_encoders)) in
                          let constructor_2_type_len = constructor_2_type_len |> EConstr.Vars.lift (1 + List.length constructor_1_types_hyp_encoders) in
                          if constructor_2_i = constructor_1_i then
                            List.fold_right
                              (fun encoder_1 encoder_2 ->
                                {
                                  encoder_len =
                                    mk_nat_add env encoder_1.encoder_len encoder_2.encoder_len;
                                  encoder_encode =
                                    mk_vector_app env
                                      (mk_bool_type env)
                                      encoder_1.encoder_len
                                      encoder_2.encoder_len
                                      encoder_1.encoder_encode
                                      encoder_2.encoder_encode
                                }
                              )
                              (constructor_1_types_hyp_encoders |> List.mapi (fun i constructor_1_types_hyp_encoder ->
                                {
                                  encoder_len = constructor_1_types_hyp_encoder.encoder_len;
                                  encoder_encode =
                                    EConstr.mkApp (
                                      constructor_1_types_hyp_encoder.encoder_encode,
                                      [|EConstr.mkRel (List.length constructor_1_types_hyp_encoders - i)|]
                                    );
                                }
                              ))
                              {
                                encoder_len = to_nat_constr env 0;
                                encoder_encode = to_vector_constr env (mk_bool_type env) [];
                              }
                          else
                            {
                              encoder_len = constructor_2_type_len;
                              encoder_encode =
                                mk_vector_repeat env (mk_bool_type env) (to_bool_constr env false) constructor_2_type_len;
                            }
                        )
                        |> Array.to_list
                        |> reduce_right_i (fun i encoder_1 encoder_2 ->
                          {
                            encoder_len =
                              mk_nat_add env (to_nat_constr env 1) (mk_nat_add env encoder_1.encoder_len encoder_2.encoder_len);
                            encoder_encode =
                              mk_vector_app env
                                (mk_bool_type env)
                                (to_nat_constr env 1)
                                (mk_nat_add env encoder_1.encoder_len encoder_2.encoder_len)
                                (to_vector_constr env (mk_bool_type env) [to_bool_constr env (i = constructor_1_i)])
                                (mk_vector_app env
                                  (mk_bool_type env)
                                  encoder_1.encoder_len
                                  encoder_2.encoder_len
                                  encoder_1.encoder_encode
                                  encoder_2.encoder_encode)
                          }
                        ))
                        .encoder_encode
                    )
                  )
                )
              ) in
            Feedback.msg_info Pp.(str "type_encode" ++ spc () ++ Printer.pr_econstr_env env sigma type_encode);
            Feedback.msg_info Pp.(str "type_encode :" ++ spc () ++ Printer.pr_econstr_env env sigma (Typing.type_of env sigma type_encode |> snd));
            Some {
              encoder_len = type_len;
              encoder_encode = type_encode;
            }
          with Dependent | Static -> None
      ) else
        None)
  | _ -> CErrors.user_err Pp.(str "Unexpected type:" ++ spc () ++ Printer.pr_econstr_env env sigma type_)

let entry_derive_encoder (input_type_constr_expr : Constrexpr.constr_expr) (output_id : Names.Id.t option) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, input_type) = Constrintern.interp_constr_evars env sigma input_type_constr_expr in
  let input_type_type = Retyping.get_type_of env sigma input_type in
  let (input_type_type_hyps, input_type_type_concl) =
    try decompose_arrows sigma input_type_type
    with Dependent -> CErrors.user_err Pp.(str "Dependent type:" ++ spc () ++ Printer.pr_econstr_env env sigma input_type_type) in
  if not (input_type_type_hyps |> List.for_all (EConstr.isSort sigma)) then
    CErrors.user_err Pp.(str "Has non-type arguments:" ++ spc () ++ Printer.pr_econstr_env env sigma input_type_type);
  if not (input_type_type_concl |> EConstr.isSort sigma) then
    CErrors.user_err Pp.(str "Not an arity:" ++ spc () ++ Printer.pr_econstr_env env sigma input_type_type);
  let context =
    List.fold_left (fun context input_type_type_hyp ->
      Context.Rel.Declaration.LocalAssum (
        EConstr.anonR,
        EConstr.mkProd (EConstr.anonR, EConstr.mkRel 2, mk_vector_type env (mk_bool_type env) (EConstr.mkRel 2))
      ) ::
      Context.Rel.Declaration.LocalAssum (EConstr.anonR, mk_nat_type env) ::
      Context.Rel.Declaration.LocalAssum (EConstr.anonR, input_type_type_hyp) ::
      (EConstr.Vars.lift_rel_context 3 context)
    ) [] input_type_type_hyps in
  let context_encoders =
    List.fold_left (fun encoders input_type_type_hyp ->
      None ::
      None ::
      Some {encoder_len = EConstr.mkRel 2; encoder_encode = EConstr.mkRel 1} ::
      (encoders |> List.map (Option.map (lift_encoder 3)))
    ) [] input_type_type_hyps in
  let app_input_type =
    EConstr.mkApp (
      input_type,
      input_type_type_hyps |> List.mapi (fun i _ -> EConstr.mkRel (3 + i * 3)) |> List.rev |> Array.of_list
    ) in
  let app_input_type_encoder = create_encoder (env |> EConstr.push_rel_context context) sigma context_encoders app_input_type in
  match app_input_type_encoder with
  | Some app_input_type_encoder -> (
    let input_type_encoder = {
      encoder_len = EConstr.it_mkLambda_or_LetIn app_input_type_encoder.encoder_len context;
      encoder_encode = EConstr.it_mkLambda_or_LetIn app_input_type_encoder.encoder_encode context;
    } in
    Feedback.msg_info Pp.(str "len =" ++ spc () ++ Printer.pr_econstr_env env sigma input_type_encoder.encoder_len);
    Feedback.msg_info Pp.(str "encode =" ++ spc () ++ Printer.pr_econstr_env env sigma input_type_encoder.encoder_encode);
    Feedback.msg_info Pp.(str "encode :" ++ spc () ++ Printer.pr_econstr_env env sigma (Retyping.get_type_of env sigma input_type_encoder.encoder_encode));
    match output_id with
    | Some output_id -> (
      let input_type_len_constant =
        Declare.declare_definition
          ~info:(Declare.Info.make ())
          ~cinfo:(
            Declare.CInfo.make
            ~name:((output_id |> Names.Id.to_string) ^ "_len" |> Names.Id.of_string)
            ~typ:(Some (EConstr.it_mkProd_or_LetIn (mk_nat_type env) context))
            ()
          )
          ~opaque:false
          ~body:input_type_encoder.encoder_len
          sigma
        |> dest_const_ref in
      let input_type_encode_constant =
        Declare.declare_definition
          ~info:(Declare.Info.make ())
          ~cinfo:(
            Declare.CInfo.make
            ~name:((output_id |> Names.Id.to_string) ^ "_encode" |> Names.Id.of_string)
            ~typ:(Some (
              EConstr.it_mkProd_or_LetIn
                (EConstr.mkProd (
                  EConstr.anonR,
                  app_input_type,
                  mk_vector_type env
                    (mk_bool_type env)
                    (EConstr.mkApp (
                      EConstr.UnsafeMonomorphic.mkConst input_type_len_constant,
                      List.init (List.length context) (fun i -> EConstr.mkRel (2 + i)) |> List.rev |> Array.of_list
                    ))
                ))
                context
            ))
            ()
          )
          ~opaque:false
          ~body:input_type_encoder.encoder_encode
          sigma
        |> dest_const_ref in
      match EConstr.kind sigma input_type with
      | Ind (ind, _) ->
        let ind_encoder = {
          encoder_len = EConstr.UnsafeMonomorphic.mkConst (input_type_len_constant);
          encoder_encode = EConstr.UnsafeMonomorphic.mkConst (input_type_encode_constant);
        } in
        add_saved_encoder (ind, ind_encoder);
        ()
      | _ -> ()
    )
    | None -> ()
  )
  | None ->
    Feedback.msg_info Pp.(str "Type is static");
    ()

let entry_test () : unit =
  let env = Global.env () in
  let (mib, mip) = Inductive.lookup_mind_specif env (Names.MutInd.make1 (Names.KerName.make (Names.ModPath.MPfile (Names.DirPath.make [Names.Id.of_string "Datatypes"; Names.Id.of_string "Init"; Names.Id.of_string "Corelib"])) (Names.Label.make "list")), 0) in
  let truly_recursive =
    let is_rec ra = match Declareops.dest_recarg ra with Mrec _ -> true | Norec -> false in
    Array.exists
      (fun (mip : Declarations.one_inductive_body) -> Array.exists (List.exists is_rec) (Declareops.dest_subterms mip.mind_recargs))
      mib.mind_packets in
  Feedback.msg_info (Pp.bool (mib.mind_finite = BiFinite));
  Feedback.msg_info (Pp.bool truly_recursive);
  Feedback.msg_info (Pp.str "test")

let entry_compile (input_id : Names.Id.t) : unit =
  Feedback.msg_info (Pp.str "compile")
