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

let econstr_substl_opt (sigma : Evd.evar_map) (ts : EConstr.t option list) (c : EConstr.t) : EConstr.t =
  assert (ts |> CList.for_all_i (fun t_i t -> c |> EConstr.Vars.noccurn sigma (1 + t_i) || Option.has_some t) 0);
  c |> EConstr.Vars.substl (ts |> List.map (Option.default EConstr.mkProp))

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

let mk_eq_type (env : Environ.env) (typ : EConstr.t) (x : EConstr.t) (y : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "core.eq.type", [|typ; x; y|])

let mk_True_type (env : Environ.env) : EConstr.t =
  get_ref env "core.True.type"

let mk_True_I (env : Environ.env) : EConstr.t =
  get_ref env "core.True.I"

let mk_unit_type (env : Environ.env) : EConstr.t =
  get_ref env "core.unit.type"

let mk_unit_tt (env : Environ.env) : EConstr.t =
  get_ref env "core.unit.tt"

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

let prove_eq_nat (env : Environ.env) (n : EConstr.t) : EConstr.t =
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
      prove_eq_nat env (to_nat_constr env (l |> List.length));
    |]
  )

let mk_vector_repeat (env : Environ.env) (typ : EConstr.t) (x : EConstr.t) (n : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "vcpu.vector.repeat", [|typ; x; n|])

let mk_vector_app (env : Environ.env) (typ : EConstr.t) (length_u : EConstr.t) (length_v : EConstr.t) (u : EConstr.t) (v : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "vcpu.vector.app", [|typ; length_u; length_v; u; v|])

let mk_circuit_type (env : Environ.env) (n : EConstr.t) (m : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "vcpu.circuit.type", [|n; m|])

let mk_circuit_wf (env : Environ.env) (n : EConstr.t) (m : EConstr.t) (circuit : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "vcpu.circuit.wf", [|n; m; circuit|])

let mk_circuit_eval (env : Environ.env) (n : EConstr.t) (m : EConstr.t) (circuit : EConstr.t) (inputs : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "vcpu.circuit.eval", [|n; m; circuit; inputs|])

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
  | Rel n, type_args -> (
    List.nth context_encoders (n - 1) |> Option.map (fun context_encoder ->
      {
        encoder_len = EConstr.mkApp (context_encoder.encoder_len, type_args);
        encoder_encode = EConstr.mkApp (context_encoder.encoder_encode, type_args);
      }
    )
  )
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
            match !saved_encoders |> List.find_opt (fun (ind', _) -> Names.Ind.UserOrd.equal ind' ind) |> Option.map snd with
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
                (EConstr.mkProd (EConstr.anonR,
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

type repr =
  | ReprRaw
  | ReprTransformed
  | ReprFunctional of repr * repr

let dest_repr_functional (repr : repr) : repr * repr =
  match repr with
  | ReprFunctional (repr_1, repr_2) -> repr_1, repr_2
  | _ -> assert false

let rec repr_of_constr_expr (env : Environ.env) (sigma : Evd.evar_map) (constr_expr : Constrexpr.constr_expr) : repr =
  match constr_expr with
  | {v = CRef (n, None); _} when Libnames.string_of_qualid n = "R" ->
    ReprRaw
  | {v = CRef (n, None); _} when Libnames.string_of_qualid n = "T" ->
    ReprTransformed
  | {v = CApp ({v = CRef (n, None); _}, [(constr_expr_1, None); (constr_expr_2, None)]); _} when Libnames.string_of_qualid n = "F" ->
    ReprFunctional (repr_of_constr_expr env sigma constr_expr_1, repr_of_constr_expr env sigma constr_expr_2)
  | _ -> CErrors.user_err Pp.(str "Not a representation:" ++ spc () ++ Ppconstr.pr_constr_expr env sigma constr_expr)

let rec repr_to_constr_expr (repr : repr) : Constrexpr.constr_expr =
  match repr with
  | ReprRaw ->
    CAst.make (Constrexpr.CRef (Libnames.qualid_of_string "R", None))
  | ReprTransformed ->
    CAst.make (Constrexpr.CRef (Libnames.qualid_of_string "T", None))
  | ReprFunctional (repr_1, repr_2) ->
    CAst.make (Constrexpr.CApp (
      CAst.make (Constrexpr.CRef (Libnames.qualid_of_string "F", None)),
      [(repr_to_constr_expr repr_1, None); (repr_to_constr_expr repr_2, None)]
    ))

let rec enumerate_reprs (env : Environ.env) (sigma : Evd.evar_map) (context_encoders : encoder option list) (type_ : EConstr.t) : repr list =
  Feedback.msg_info Pp.(str "enumerate_reprs" ++ spc () ++ Printer.pr_econstr_env env sigma type_);
  let type_ = Tacred.hnf_constr0 env sigma type_ in
  let type_head, type_args = EConstr.decompose_app sigma type_ in
  match EConstr.kind sigma type_head, type_args with
  | Rel _, _ | Ind _, _ -> (
    let type_encoder = create_encoder env sigma context_encoders type_ in
    match type_encoder with
    | Some _ -> [ReprTransformed; ReprRaw]
    | None -> [ReprRaw]
  )
  | Prod (_, type_1, type_2), [||] ->
    if type_1 |> EConstr.isSort sigma then
      (enumerate_reprs
        (env |> EConstr.push_rel_context [
          Context.Rel.Declaration.LocalAssum (
            EConstr.anonR,
            EConstr.mkProd (EConstr.anonR, EConstr.mkRel 2, mk_vector_type env (mk_bool_type env) (EConstr.mkRel 2))
          );
          Context.Rel.Declaration.LocalAssum (EConstr.anonR, mk_nat_type env);
          Context.Rel.Declaration.LocalAssum (EConstr.anonR, type_1);
        ])
        sigma
        (
          None ::
          None ::
          Some {encoder_len = EConstr.mkRel 2; encoder_encode = EConstr.mkRel 1} ::
          (context_encoders |> List.map (Option.map (lift_encoder 3)))
        )
        (type_2 |> EConstr.Vars.liftn 3 2 |> EConstr.Vars.subst1 (EConstr.mkRel 3))
        |> List.map (fun type_2_repr -> ReprFunctional (ReprTransformed, type_2_repr))) @
      (enumerate_reprs
        (env |> EConstr.push_rel (Context.Rel.Declaration.LocalAssum (EConstr.anonR, type_1)))
        sigma
        (None :: (context_encoders |> List.map (Option.map (lift_encoder 1))))
        type_2
        |> List.map (fun type_2_repr -> ReprFunctional (ReprRaw, type_2_repr)))
    else if
      not (type_1 |> EConstr.decompose_prod sigma |> snd |> EConstr.isSort sigma) &&
      type_2 |> EConstr.Vars.noccurn sigma 1
    then
      enumerate_reprs env sigma context_encoders type_1
        |> List.map (fun type_1_repr ->
          enumerate_reprs env sigma context_encoders (type_2 |> econstr_substl_opt sigma [None])
            |> List.map (fun type_2_repr -> ReprFunctional (type_1_repr, type_2_repr))
        )
        |> List.flatten
    else
      [ReprRaw]
  | _ -> CErrors.user_err Pp.(str "Unexpected type:" ++ spc () ++ Printer.pr_econstr_env env sigma type_)

type compilation = {
  compilation_orig : EConstr.t;
  compilation_circuit : EConstr.t;
  compilation_wf_circuit : EConstr.t;
  compilation_eval_circuit : EConstr.t;
  compilation_circuit_erased : EConstr.t;
  compilation_eq_circuit_erased : EConstr.t;
}

let lift_compilation (n : int) (compilation : compilation) : compilation =
  {
    compilation_orig = compilation.compilation_orig |> EConstr.Vars.lift n;
    compilation_circuit = compilation.compilation_circuit |> EConstr.Vars.lift n;
    compilation_wf_circuit = compilation.compilation_wf_circuit |> EConstr.Vars.lift n;
    compilation_eval_circuit = compilation.compilation_eval_circuit |> EConstr.Vars.lift n;
    compilation_circuit_erased = compilation.compilation_circuit_erased |> EConstr.Vars.lift n;
    compilation_eq_circuit_erased = compilation.compilation_eq_circuit_erased |> EConstr.Vars.lift n;
  }

let compilation_type_to_context (compilation : compilation) : EConstr.rel_context =
  [
    Context.Rel.Declaration.LocalAssum (EConstr.anonR, compilation.compilation_eq_circuit_erased);
    Context.Rel.Declaration.LocalAssum (EConstr.anonR, compilation.compilation_circuit_erased);
    Context.Rel.Declaration.LocalAssum (EConstr.anonR, compilation.compilation_eval_circuit);
    Context.Rel.Declaration.LocalAssum (EConstr.anonR, compilation.compilation_wf_circuit);
    Context.Rel.Declaration.LocalAssum (EConstr.anonR, compilation.compilation_circuit);
    Context.Rel.Declaration.LocalAssum (EConstr.anonR, compilation.compilation_orig);
  ]

let compilation_to_array (compilation : compilation) : EConstr.t array =
  [|
    compilation.compilation_orig;
    compilation.compilation_circuit;
    compilation.compilation_wf_circuit;
    compilation.compilation_eval_circuit;
    compilation.compilation_circuit_erased;
    compilation.compilation_eq_circuit_erased;
  |]

let rec get_compilation_type (env : Environ.env) (sigma : Evd.evar_map) (context_encoders : encoder option list) (input_len : EConstr.t) (type_ : EConstr.t) (type_repr : repr) : compilation =
  Feedback.msg_info Pp.(str "get_compilation_type" ++ spc () ++ Printer.pr_econstr_env env sigma type_);
  let type_ = Tacred.hnf_constr0 env sigma type_ in
  let type_compilation_type =
  match type_repr with
  | ReprRaw ->
    {
      compilation_orig = type_;
      compilation_circuit = mk_unit_type env;
      compilation_wf_circuit = mk_True_type env;
      compilation_eval_circuit = mk_True_type env;
      compilation_circuit_erased = mk_unit_type env;
      compilation_eq_circuit_erased = mk_True_type env;
    }
  | _ ->
    let type_head, type_args = EConstr.decompose_app sigma type_ in
    match EConstr.kind sigma type_head, type_args with
    | Rel _, _ | Ind _, _ -> (
      assert (type_repr = ReprTransformed);
      let type_encoder = create_encoder env sigma context_encoders type_ |> Option.get in
      {
        compilation_orig = type_;
        compilation_circuit =
          mk_circuit_type env
            (input_len |> EConstr.Vars.lift 1)
            (type_encoder.encoder_len |> EConstr.Vars.lift 1);
        compilation_wf_circuit =
          mk_circuit_wf env
            (input_len |> EConstr.Vars.lift 2)
            (type_encoder.encoder_len |> EConstr.Vars.lift 2)
            (EConstr.mkRel 1);
        compilation_eval_circuit =
          EConstr.mkProd (EConstr.anonR,
            mk_vector_type env (mk_bool_type env) (input_len |> EConstr.Vars.lift 3),
            mk_eq_type env
              (mk_vector_type env (mk_bool_type env) (type_encoder.encoder_len |> EConstr.Vars.lift 4))
              (
                mk_circuit_eval env
                  (input_len |> EConstr.Vars.lift 4)
                  (type_encoder.encoder_len |> EConstr.Vars.lift 4)
                  (EConstr.mkRel 3)
                  (EConstr.mkRel 1)
              )
              (EConstr.mkApp (
                type_encoder.encoder_encode |> EConstr.Vars.lift 4,
                [|EConstr.mkRel 4|]
              ))
          );
        compilation_circuit_erased =
          mk_circuit_type env
            (input_len |> EConstr.Vars.lift 4)
            (type_encoder.encoder_len |> EConstr.Vars.lift 4);
        compilation_eq_circuit_erased =
          mk_eq_type env
            (mk_circuit_type env
              (input_len |> EConstr.Vars.lift 5)
              (type_encoder.encoder_len |> EConstr.Vars.lift 5))
            (EConstr.mkRel 1)
            (EConstr.mkRel 4);
      }
    )
    | Sort _, [||] -> assert false
    | Prod (_, type_1, type_2), [||] ->
      let type_1_repr, type_2_repr = dest_repr_functional type_repr in
      if type_1_repr = ReprRaw then
        let type_2_compilation_type =
          get_compilation_type
            (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (EConstr.anonR, type_1)) env)
            sigma
            (None :: (context_encoders |> List.map (Option.map (lift_encoder 1))))
            (input_len |> EConstr.Vars.lift 1)
            type_2
            type_2_repr in
        {
          compilation_orig =
            EConstr.mkProd (EConstr.anonR,
              type_1 |> EConstr.Vars.lift 0,
              type_2_compilation_type.compilation_orig
                |> EConstr.Vars.liftn 1 2
                |> EConstr.Vars.substl [
                  EConstr.mkRel 1;
                ]
            );
          compilation_circuit =
            EConstr.mkProd (EConstr.anonR,
              type_1 |> EConstr.Vars.lift 1,
              type_2_compilation_type.compilation_circuit
                |> EConstr.Vars.liftn 2 3
                |> EConstr.Vars.substl [
                  EConstr.mkApp (EConstr.mkRel 2, [|EConstr.mkRel 1|]);
                  EConstr.mkRel 1;
                ]
            );
          compilation_wf_circuit =
            EConstr.mkProd (EConstr.anonR,
              type_1 |> EConstr.Vars.lift 2,
              type_2_compilation_type.compilation_wf_circuit
                |> EConstr.Vars.liftn 3 4
                |> EConstr.Vars.substl [
                  EConstr.mkApp (EConstr.mkRel 2, [|EConstr.mkRel 1|]);
                  EConstr.mkApp (EConstr.mkRel 3, [|EConstr.mkRel 1|]);
                  EConstr.mkRel 1;
                ]
            );
          compilation_eval_circuit =
            EConstr.mkProd (EConstr.anonR,
              type_1 |> EConstr.Vars.lift 3,
              type_2_compilation_type.compilation_eval_circuit
                |> EConstr.Vars.liftn 4 5
                |> EConstr.Vars.substl [
                  EConstr.mkApp (EConstr.mkRel 2, [|EConstr.mkRel 1|]);
                  EConstr.mkApp (EConstr.mkRel 3, [|EConstr.mkRel 1|]);
                  EConstr.mkApp (EConstr.mkRel 4, [|EConstr.mkRel 1|]);
                  EConstr.mkRel 1;
                ]
            );
          compilation_circuit_erased =
            EConstr.mkProd (EConstr.anonR,
              type_1 |> EConstr.Vars.lift 4,
              type_2_compilation_type.compilation_circuit_erased
                |> EConstr.Vars.liftn 5 6
                |> EConstr.Vars.substl [
                  EConstr.mkApp (EConstr.mkRel 2, [|EConstr.mkRel 1|]);
                  EConstr.mkApp (EConstr.mkRel 3, [|EConstr.mkRel 1|]);
                  EConstr.mkApp (EConstr.mkRel 4, [|EConstr.mkRel 1|]);
                  EConstr.mkApp (EConstr.mkRel 5, [|EConstr.mkRel 1|]);
                  EConstr.mkRel 1;
                ]
            );
          compilation_eq_circuit_erased =
            EConstr.mkProd (EConstr.anonR,
              type_1 |> EConstr.Vars.lift 5,
              type_2_compilation_type.compilation_eq_circuit_erased
                |> EConstr.Vars.liftn 6 7
                |> EConstr.Vars.substl [
                  EConstr.mkApp (EConstr.mkRel 2, [|EConstr.mkRel 1|]);
                  EConstr.mkApp (EConstr.mkRel 3, [|EConstr.mkRel 1|]);
                  EConstr.mkApp (EConstr.mkRel 4, [|EConstr.mkRel 1|]);
                  EConstr.mkApp (EConstr.mkRel 5, [|EConstr.mkRel 1|]);
                  EConstr.mkApp (EConstr.mkRel 6, [|EConstr.mkRel 1|]);
                  EConstr.mkRel 1;
                ]
            );
        }
      else
        if type_1 |> EConstr.isSort sigma then (
          let type_1_context = [
            Context.Rel.Declaration.LocalAssum (
              EConstr.anonR,
              EConstr.mkProd (EConstr.anonR, EConstr.mkRel 2, mk_vector_type env (mk_bool_type env) (EConstr.mkRel 2))
            );
            Context.Rel.Declaration.LocalAssum (EConstr.anonR, mk_nat_type env);
            Context.Rel.Declaration.LocalAssum (EConstr.anonR, type_1);
          ] in
          let type_2_compilation_type =
            get_compilation_type
              (env |> EConstr.push_rel_context type_1_context)
              sigma
              (
                None ::
                None ::
                Some {encoder_len = EConstr.mkRel 2; encoder_encode = EConstr.mkRel 1} ::
                (context_encoders |> List.map (Option.map (lift_encoder 3)))
              )
              (input_len |> EConstr.Vars.lift 3)
              (type_2 |> EConstr.Vars.liftn 3 2 |> EConstr.Vars.subst1 (EConstr.mkRel 3))
              type_2_repr in
          {
            compilation_orig =
              EConstr.it_mkProd_or_LetIn
                (type_2_compilation_type.compilation_orig
                  |> EConstr.Vars.liftn 3 4
                  |> EConstr.Vars.substl [
                    EConstr.mkRel 1;
                    EConstr.mkRel 2;
                    EConstr.mkRel 3;
                  ])
                (type_1_context |> EConstr.Vars.lift_rel_context 0);
            compilation_circuit =
              EConstr.it_mkProd_or_LetIn
                (type_2_compilation_type.compilation_circuit
                  |> EConstr.Vars.liftn 4 5
                  |> EConstr.Vars.substl [
                    EConstr.mkApp (EConstr.mkRel 4, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkRel 1;
                    EConstr.mkRel 2;
                    EConstr.mkRel 3;
                  ])
                (type_1_context |> EConstr.Vars.lift_rel_context 1);
            compilation_wf_circuit =
              EConstr.it_mkProd_or_LetIn
                (type_2_compilation_type.compilation_wf_circuit
                  |> EConstr.Vars.liftn 5 6
                  |> EConstr.Vars.substl [
                    EConstr.mkApp (EConstr.mkRel 4, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 5, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkRel 1;
                    EConstr.mkRel 2;
                    EConstr.mkRel 3;
                  ])
                (type_1_context |> EConstr.Vars.lift_rel_context 2);
            compilation_eval_circuit =
              EConstr.it_mkProd_or_LetIn
                (type_2_compilation_type.compilation_eval_circuit
                  |> EConstr.Vars.liftn 6 7
                  |> EConstr.Vars.substl [
                    EConstr.mkApp (EConstr.mkRel 4, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 5, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 6, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkRel 1;
                    EConstr.mkRel 2;
                    EConstr.mkRel 3;
                  ])
                (type_1_context |> EConstr.Vars.lift_rel_context 3);
            compilation_circuit_erased =
              EConstr.it_mkProd_or_LetIn
                (type_2_compilation_type.compilation_circuit_erased
                  |> EConstr.Vars.liftn 7 8
                  |> EConstr.Vars.substl [
                    EConstr.mkApp (EConstr.mkRel 4, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 5, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 6, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 7, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkRel 1;
                    EConstr.mkRel 2;
                    EConstr.mkRel 3;
                  ])
                (type_1_context |> EConstr.Vars.lift_rel_context 5);
            compilation_eq_circuit_erased =
              EConstr.it_mkProd_or_LetIn
                (type_2_compilation_type.compilation_eq_circuit_erased
                  |> EConstr.Vars.liftn 8 9
                  |> EConstr.Vars.substl [
                    EConstr.mkApp (EConstr.mkRel 4, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 5, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 6, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 7, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 8, [|EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkRel 1;
                    EConstr.mkRel 2;
                    EConstr.mkRel 3;
                  ])
                (type_1_context |> EConstr.Vars.lift_rel_context 5);
          }
        ) else if
          not (type_1 |> EConstr.decompose_prod sigma |> snd |> EConstr.isSort sigma) &&
          type_2 |> EConstr.Vars.noccurn sigma 1
        then
          let type_1_compilation_type =
            get_compilation_type env sigma context_encoders input_len type_1 type_1_repr in
          let type_1_context = type_1_compilation_type |> compilation_type_to_context in
          let type_2_compilation_type =
            get_compilation_type
              (env |> EConstr.push_rel_context type_1_context)
              sigma
              (
                None ::
                None ::
                None ::
                None ::
                None ::
                None ::
                (context_encoders |> List.map (Option.map (lift_encoder 6)))
              )
              (input_len |> EConstr.Vars.lift 6)
              (type_2 |> EConstr.Vars.liftn 6 2 |> EConstr.Vars.subst1 (EConstr.mkRel 6))
              type_2_repr in
          {
            compilation_orig =
              EConstr.it_mkProd_or_LetIn
                (type_2_compilation_type.compilation_orig
                  |> EConstr.Vars.liftn 6 7
                  |> EConstr.Vars.substl [
                    EConstr.mkRel 1;
                    EConstr.mkRel 2;
                    EConstr.mkRel 3;
                    EConstr.mkRel 4;
                    EConstr.mkRel 5;
                    EConstr.mkRel 6;
                  ])
                (type_1_context |> EConstr.Vars.lift_rel_context 0);
            compilation_circuit =
              EConstr.it_mkProd_or_LetIn
                (type_2_compilation_type.compilation_circuit
                  |> EConstr.Vars.liftn 7 8
                  |> EConstr.Vars.substl [
                    EConstr.mkApp (EConstr.mkRel 7, [|EConstr.mkRel 6; EConstr.mkRel 5; EConstr.mkRel 4; EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkRel 1;
                    EConstr.mkRel 2;
                    EConstr.mkRel 3;
                    EConstr.mkRel 4;
                    EConstr.mkRel 5;
                    EConstr.mkRel 6;
                  ])
                (type_1_context |> EConstr.Vars.lift_rel_context 1);
            compilation_wf_circuit =
              EConstr.it_mkProd_or_LetIn
                (type_2_compilation_type.compilation_wf_circuit
                  |> EConstr.Vars.liftn 8 9
                  |> EConstr.Vars.substl [
                    EConstr.mkApp (EConstr.mkRel 7, [|EConstr.mkRel 6; EConstr.mkRel 5; EConstr.mkRel 4; EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 8, [|EConstr.mkRel 6; EConstr.mkRel 5; EConstr.mkRel 4; EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkRel 1;
                    EConstr.mkRel 2;
                    EConstr.mkRel 3;
                    EConstr.mkRel 4;
                    EConstr.mkRel 5;
                    EConstr.mkRel 6;
                  ])
                (type_1_context |> EConstr.Vars.lift_rel_context 2);
            compilation_eval_circuit =
              EConstr.it_mkProd_or_LetIn
                (type_2_compilation_type.compilation_eval_circuit
                  |> EConstr.Vars.liftn 9 10
                  |> EConstr.Vars.substl [
                    EConstr.mkApp (EConstr.mkRel 7, [|EConstr.mkRel 6; EConstr.mkRel 5; EConstr.mkRel 4; EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 8, [|EConstr.mkRel 6; EConstr.mkRel 5; EConstr.mkRel 4; EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 9, [|EConstr.mkRel 6; EConstr.mkRel 5; EConstr.mkRel 4; EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkRel 1;
                    EConstr.mkRel 2;
                    EConstr.mkRel 3;
                    EConstr.mkRel 4;
                    EConstr.mkRel 5;
                    EConstr.mkRel 6;
                  ])
                (type_1_context |> EConstr.Vars.lift_rel_context 3);
            compilation_circuit_erased =
              EConstr.mkProd (EConstr.anonR,
                type_1_compilation_type.compilation_circuit_erased
                  |> EConstr.Vars.liftn 4 5
                  |> econstr_substl_opt sigma [
                    None;
                    None;
                    None;
                    None;
                  ],
                type_2_compilation_type.compilation_circuit_erased
                  |> EConstr.Vars.liftn 5 11
                  |> econstr_substl_opt sigma [
                    None;
                    None;
                    None;
                    None;
                    None;
                    Some (EConstr.mkRel 1);
                    None;
                    None;
                    None;
                    None;
                  ]
              );
            compilation_eq_circuit_erased =
              EConstr.it_mkProd_or_LetIn
                (type_2_compilation_type.compilation_eq_circuit_erased
                  |> EConstr.Vars.liftn 11 12
                  |> EConstr.Vars.substl [
                    EConstr.mkApp (EConstr.mkRel 7, [|EConstr.mkRel 2|]);
                    EConstr.mkApp (EConstr.mkRel 8, [|EConstr.mkRel 6; EConstr.mkRel 5; EConstr.mkRel 4; EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 9, [|EConstr.mkRel 6; EConstr.mkRel 5; EConstr.mkRel 4; EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 10, [|EConstr.mkRel 6; EConstr.mkRel 5; EConstr.mkRel 4; EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkApp (EConstr.mkRel 11, [|EConstr.mkRel 6; EConstr.mkRel 5; EConstr.mkRel 4; EConstr.mkRel 3; EConstr.mkRel 2; EConstr.mkRel 1|]);
                    EConstr.mkRel 1;
                    EConstr.mkRel 2;
                    EConstr.mkRel 3;
                    EConstr.mkRel 4;
                    EConstr.mkRel 5;
                    EConstr.mkRel 6;
                  ])
                (type_1_context |> EConstr.Vars.lift_rel_context 5);
          }
        else
          assert false
    | _ -> CErrors.user_err Pp.(str "Unexpected type:" ++ spc () ++ Printer.pr_econstr_env env sigma type_)
    in
  let test_type_compilation_type = EConstr.it_mkLambda_or_LetIn EConstr.mkSProp (type_compilation_type |> compilation_type_to_context) in
  (* Feedback.msg_info Pp.(str "test_type_compilation_type" ++ spc () ++ Printer.pr_econstr_env env sigma type_ ++ str "=" ++ spc () ++ Printer.pr_econstr_env env sigma test_type_compilation_type); *)
  Typing.type_of env sigma test_type_compilation_type |> ignore;
  type_compilation_type

let rec create_compilations (env : Environ.env) (sigma : Evd.evar_map) (context_encoders : encoder option list) (context_reprs : repr list) (context_compilations : compilation option list) (input_len : EConstr.t) (c : EConstr.t) : (repr * compilation) Seq.t =
  Feedback.msg_info Pp.(str "create_compilations" ++ spc () ++ Printer.pr_econstr_env env sigma c);
  let c = Tacred.hnf_constr0 env sigma c in
  Seq.append
    (match EConstr.kind sigma c with
    | Rel n -> (
      match List.nth context_compilations (n - 1) with
      | Some context_compilation -> Seq.return (List.nth context_reprs (n - 1), context_compilation)
      | None -> Seq.empty
    )
    | Sort _ -> Seq.empty
    | Prod _ -> Seq.empty
    | Lambda (_, c_1, c_2) ->
      let c_2_type =
        Retyping.get_type_of (env |> EConstr.push_rel (Context.Rel.Declaration.LocalAssum (EConstr.anonR, c_1))) sigma c_2 in
      Seq.append
        (create_compilations
          (env |> EConstr.push_rel (Context.Rel.Declaration.LocalAssum (EConstr.anonR, c_1)))
          sigma
          (None :: (context_encoders |> List.map (Option.map (lift_encoder 1))))
          (ReprRaw :: context_reprs)
          (None :: (context_compilations |> List.map (Option.map (lift_compilation 1))))
          (input_len |> EConstr.Vars.lift 1)
          c_2
          |> Seq.map (fun (c_2_repr, c_2_compilation) ->
            (
              ReprFunctional (ReprRaw, c_2_repr),
              {
                compilation_orig =
                  EConstr.mkLambda (EConstr.anonR, c_1, c_2_compilation.compilation_orig);
                compilation_circuit =
                  EConstr.mkLambda (EConstr.anonR, c_1, c_2_compilation.compilation_circuit);
                compilation_wf_circuit =
                  EConstr.mkLambda (EConstr.anonR, c_1, c_2_compilation.compilation_wf_circuit);
                compilation_eval_circuit =
                  EConstr.mkLambda (EConstr.anonR, c_1, c_2_compilation.compilation_eval_circuit);
                compilation_circuit_erased =
                  EConstr.mkLambda (EConstr.anonR, c_1, c_2_compilation.compilation_circuit_erased);
                compilation_eq_circuit_erased =
                  EConstr.mkLambda (EConstr.anonR, c_1, c_2_compilation.compilation_eq_circuit_erased);
              }
            )
          ))
        (if c_1 |> EConstr.isSort sigma then
          let c_1_context = [
            Context.Rel.Declaration.LocalAssum (
              EConstr.anonR,
              EConstr.mkProd (EConstr.anonR, EConstr.mkRel 2, mk_vector_type env (mk_bool_type env) (EConstr.mkRel 2))
            );
            Context.Rel.Declaration.LocalAssum (EConstr.anonR, mk_nat_type env);
            Context.Rel.Declaration.LocalAssum (EConstr.anonR, c_1);
          ] in
          create_compilations
            (env |> EConstr.push_rel_context c_1_context)
            sigma
            (
              None ::
              None ::
              Some {encoder_len = EConstr.mkRel 2; encoder_encode = EConstr.mkRel 1} ::
              (context_encoders |> List.map (Option.map (lift_encoder 3)))
            )
            (ReprRaw :: ReprRaw :: ReprRaw :: context_reprs)
            (None :: None :: None :: (context_compilations |> List.map (Option.map (lift_compilation 3))))
            (input_len |> EConstr.Vars.lift 3)
            (c_2 |> EConstr.Vars.liftn 3 2 |> EConstr.Vars.subst1 (EConstr.mkRel 3))
            |> Seq.map (fun (c_2_repr, c_2_compilation) ->
              (
                ReprFunctional (ReprTransformed, c_2_repr),
                {
                  compilation_orig =
                    EConstr.it_mkLambda_or_LetIn c_2_compilation.compilation_orig c_1_context;
                  compilation_circuit =
                    EConstr.it_mkLambda_or_LetIn c_2_compilation.compilation_circuit c_1_context;
                  compilation_wf_circuit =
                    EConstr.it_mkLambda_or_LetIn c_2_compilation.compilation_wf_circuit c_1_context;
                  compilation_eval_circuit =
                    EConstr.it_mkLambda_or_LetIn c_2_compilation.compilation_eval_circuit c_1_context;
                  compilation_circuit_erased =
                    EConstr.it_mkLambda_or_LetIn c_2_compilation.compilation_circuit_erased c_1_context;
                  compilation_eq_circuit_erased =
                    EConstr.it_mkLambda_or_LetIn c_2_compilation.compilation_eq_circuit_erased c_1_context;
                }
              )
            )
        else if
          not (c_1 |> EConstr.decompose_prod sigma |> snd |> EConstr.isSort sigma) &&
          c_2_type |> EConstr.Vars.noccurn sigma 1
        then
          enumerate_reprs env sigma context_encoders c_1
            |> List.filter (fun c_1_repr -> c_1_repr <> ReprRaw)
            |> List.to_seq
            |> Seq.flat_map (fun c_1_repr ->
              let c_1_compilation_type =
                get_compilation_type env sigma context_encoders input_len c_1 c_1_repr in
              let c_1_context = c_1_compilation_type |> compilation_type_to_context in
              create_compilations
                (env |> EConstr.push_rel_context c_1_context)
                sigma
                (
                  None ::
                  None ::
                  None ::
                  None ::
                  None ::
                  None ::
                  (context_encoders |> List.map (Option.map (lift_encoder 6)))
                )
                (
                  ReprRaw ::
                  ReprRaw ::
                  ReprRaw ::
                  ReprRaw ::
                  ReprRaw ::
                  c_1_repr ::
                  context_reprs
                )
                (
                  None ::
                  None ::
                  None ::
                  None ::
                  None ::
                  Some {
                    compilation_orig = EConstr.mkRel 6;
                    compilation_circuit = EConstr.mkRel 5;
                    compilation_wf_circuit = EConstr.mkRel 4;
                    compilation_eval_circuit = EConstr.mkRel 3;
                    compilation_circuit_erased = EConstr.mkRel 2;
                    compilation_eq_circuit_erased = EConstr.mkRel 1;
                  } ::
                  (context_compilations |> List.map (Option.map (lift_compilation 6)))
                )
                (input_len |> EConstr.Vars.lift 6)
                (c_2 |> EConstr.Vars.liftn 6 2 |> EConstr.Vars.subst1 (EConstr.mkRel 6))
                |> Seq.map (fun (c_2_repr, c_2_compilation) ->
                  (
                    ReprFunctional (c_1_repr, c_2_repr),
                    {
                      compilation_orig =
                        EConstr.it_mkLambda_or_LetIn c_2_compilation.compilation_orig c_1_context;
                      compilation_circuit =
                        EConstr.it_mkLambda_or_LetIn c_2_compilation.compilation_circuit c_1_context;
                      compilation_wf_circuit =
                        EConstr.it_mkLambda_or_LetIn c_2_compilation.compilation_wf_circuit c_1_context;
                      compilation_eval_circuit =
                        EConstr.it_mkLambda_or_LetIn c_2_compilation.compilation_eval_circuit c_1_context;
                      compilation_circuit_erased =
                        EConstr.mkLambda (EConstr.anonR,
                          c_1_compilation_type.compilation_circuit_erased
                            |> econstr_substl_opt sigma [
                              None;
                              None;
                              None;
                              None;
                            ],
                          c_2_compilation.compilation_circuit_erased
                            |> EConstr.Vars.liftn 1 7
                            |> econstr_substl_opt sigma [
                              None;
                              Some (EConstr.mkRel 1);
                              None;
                              None;
                              None;
                              None;
                            ]
                        );
                      compilation_eq_circuit_erased =
                        EConstr.it_mkLambda_or_LetIn c_2_compilation.compilation_eq_circuit_erased c_1_context;
                    }
                  )
                )
            )
        else
          Seq.empty)
    | _ ->
      Feedback.msg_warning Pp.(str "Unexpected term:" ++ spc () ++ Printer.pr_econstr_env env sigma c);
      Seq.empty)
    (if
      context_reprs |> CList.for_all_i (fun context_i context_repr ->
        c |> EConstr.Vars.noccurn sigma (1 + context_i) ||
        context_repr = ReprRaw
      ) 0
    then
      Seq.return (
        ReprRaw,
        {
          compilation_orig = c;
          compilation_circuit = mk_unit_tt env;
          compilation_wf_circuit = mk_True_I env;
          compilation_eval_circuit = mk_True_I env;
          compilation_circuit_erased = mk_unit_tt env;
          compilation_eq_circuit_erased = mk_True_I env;
        }
      )
    else Seq.empty)

let entry_derive_compilation (input_c_constr_expr : Constrexpr.constr_expr) (input_repr_constr_expr : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, input_c) = Constrintern.interp_constr_evars env sigma input_c_constr_expr in
  let input_repr = repr_of_constr_expr env sigma input_repr_constr_expr in
  (* enumerate_reprs env sigma [] (Retyping.get_type_of env sigma input_c) |> List.iter (fun r ->
    Feedback.msg_info Pp.(str "repr" ++ spc () ++ Ppconstr.pr_constr_expr env sigma (repr_to_constr_expr r))
  ); *)
  (* CErrors.user_err Pp.(str "Representation:" ++ spc () ++ Ppconstr.pr_constr_expr env sigma (repr_to_constr_expr input_repr)); *)
  create_compilations env sigma [] [] [] (to_nat_constr env 42) input_c |> Seq.iter (fun (input_c_repr, input_c_compilaiton) ->
    Feedback.msg_info Pp.(str "input_c_repr" ++ (if input_c_repr = input_repr then str "!" else str "?") ++ spc () ++ Ppconstr.pr_constr_expr env sigma (repr_to_constr_expr input_c_repr));
    let input_c_compilation_type = get_compilation_type env sigma [] (to_nat_constr env 42) (Retyping.get_type_of env sigma input_c) input_c_repr in
    let test_term = EConstr.mkApp (EConstr.it_mkLambda_or_LetIn EConstr.mkSProp (input_c_compilation_type |> compilation_type_to_context), input_c_compilaiton |> compilation_to_array) in
    Feedback.msg_info Pp.(str "input_compilation_c" ++ spc () ++ Printer.pr_econstr_env env sigma test_term);
    Typing.type_of env sigma test_term |> ignore;
    ()
  );
  (* let input_compilation_type = get_compilation_type env sigma [] (to_nat_constr env 123) (Retyping.get_type_of env sigma input_c) input_repr in
  let aaa = EConstr.it_mkLambda_or_LetIn EConstr.mkSProp (input_compilation_type |> compilation_type_to_context) in
  Feedback.msg_info Pp.(str "aaa" ++ spc () ++ Printer.pr_econstr_env env sigma aaa);
  Typing.type_of env sigma aaa |> ignore; *)
  (* enumerate_reprs env sigma [] (Retyping.get_type_of env sigma input_c) |> List.iter (fun r ->
    let input_compilation_type_r = get_compilation_type env sigma [] (to_nat_constr env 456) (Retyping.get_type_of env sigma input_c) r in
    let bbb = EConstr.it_mkLambda_or_LetIn EConstr.mkSProp (input_compilation_type_r |> compilation_type_to_context) in
    Feedback.msg_info Pp.(str "bbb" ++ spc () ++ Printer.pr_econstr_env env sigma bbb);
    Typing.type_of env sigma bbb |> ignore;
    ()
  ); *)
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
