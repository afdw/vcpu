let list_index_of (type a) (x : a) (l : a list) : int =
  l |> List.mapi (fun i y -> (i, y)) |> List.find (fun (_, y) -> y = x) |> fst

let constr_list_mem (sigma : Evd.evar_map) (t : EConstr.t) (l : EConstr.t list) =
  l |> List.exists (fun t' -> EConstr.eq_constr sigma t t')

let constr_list_assoc (type a) (sigma : Evd.evar_map) (t : EConstr.t) (l : (EConstr.t * a) list) =
  l |> List.find (fun (t', _) -> EConstr.eq_constr sigma t t') |> snd

let constr_list_index_of (sigma : Evd.evar_map) (t : EConstr.t) (l : EConstr.t list) : int =
  l |> List.mapi (fun i t' -> (i, t')) |> List.find (fun (_, t') -> EConstr.eq_constr sigma t t') |> fst

let get_ref (env : Environ.env) (s : string) : EConstr.t =
  EConstr.of_constr (UnivGen.constr_of_monomorphic_global env (Coqlib.lib_ref s))

let rec to_nat (env : Environ.env) (n : int) : EConstr.t =
  assert (n >= 0);
  if n = 0
  then get_ref env "num.nat.O"
  else EConstr.mkApp (get_ref env "num.nat.S", [|to_nat env (pred n)|])

let rec of_nat (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.t) : int =
  match EConstr.kind sigma t with
  | _ when EConstr.eq_constr sigma t (get_ref env "num.nat.O") -> 0
  | App (f, [|t'|]) when EConstr.eq_constr sigma f (get_ref env "num.nat.S") -> succ (of_nat env sigma t')
  | _ -> CErrors.user_err Pp.(str "Not an application of O or S:" ++ spc () ++ Printer.pr_econstr_env env sigma t)

let prove_nat_eq (env : Environ.env) (n : int) : EConstr.t =
  EConstr.mkApp (get_ref env "core.eq.refl", [|get_ref env "num.nat.type"; to_nat env n|])

let rec prove_nat_le (env : Environ.env) (n : int) (m : int) : EConstr.t =
  assert (n <= m);
  if n == m
  then EConstr.mkApp (get_ref env "num.nat.le_n", [|to_nat env n|])
  else EConstr.mkApp (get_ref env "num.nat.le_S", [|to_nat env n; to_nat env (pred m); prove_nat_le env n (pred m)|])

let prove_nat_lt (env : Environ.env) (n : int) (m : int) : EConstr.t =
  assert (n < m);
  EConstr.mkCast (
    prove_nat_le env (succ n) m,
    Constr.DEFAULTcast,
    EConstr.mkApp (get_ref env "num.nat.lt", [|to_nat env n; to_nat env m|])
  )

let rec to_list (env : Environ.env) (typ : EConstr.t) (l : EConstr.t list) : EConstr.t =
  match l with
  | [] -> EConstr.mkApp (get_ref env "core.list.nil", [|typ|])
  | x :: l' -> EConstr.mkApp (get_ref env "core.list.cons", [|typ; x; to_list env typ l'|])

let rec of_list (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.t) : EConstr.t list =
  match EConstr.kind sigma t with
  | App (f, [|_|]) when EConstr.eq_constr sigma f (get_ref env "core.list.nil") -> []
  | App (f, [|_; a; t'|]) when EConstr.eq_constr sigma f (get_ref env "core.list.cons") -> a :: of_list env sigma t'
  | _ -> CErrors.user_err Pp.(str "Not an application of nil or cons:" ++ spc () ++ Printer.pr_econstr_env env sigma t)

let dest_vector_type (env : Environ.env) (sigma : Evd.evar_map) (typ : EConstr.t) : EConstr.t * int =
  match EConstr.kind sigma typ with
  | App (f, [|a1; a2|]) when EConstr.eq_constr sigma f (get_ref env "vcpu.vector.type") ->
    (a1, a2 |> Cbv.cbv_norm (Cbv.create_cbv_infos CClosure.all env sigma) |> of_nat env sigma)
  | _ -> CErrors.user_err Pp.(str "Not an application of vector:" ++ spc () ++ Printer.pr_econstr_env env sigma typ)

let to_vector (env : Environ.env) (typ : EConstr.t) (l : EConstr.t list) : EConstr.t =
  EConstr.mkApp (
    get_ref env "vcpu.vector.constructor",
    [|
      typ;
      to_nat env (l |> List.length);
      to_list env typ l;
      prove_nat_eq env (l |> List.length);
    |]
  )

let new_evars (env : Environ.env) (sigma : Evd.evar_map) (typ : EConstr.t) (n : int) : Evd.evar_map * EConstr.t list =
  List.init n (fun i -> i)
    |> List.fold_left (fun (sigma, evars) i ->
      let (sigma, evar) = Evarutil.new_evar env sigma typ in
      (sigma, evar :: evars)
    ) (sigma, [])

let mk_conj (env : Environ.env) (sigma : Evd.evar_map) (h1 : EConstr.t) (h2 : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "core.and.conj", [|Retyping.get_type_of env sigma h1; Retyping.get_type_of env sigma h2; h1; h2|])

let circuit_input_count (env : Environ.env) (sigma : Evd.evar_map) (c : EConstr.t) : int =
  match c |> EConstr.kind sigma with
  | App (constructor, [|c_input_count_constr; _; _; _; _|]) ->
    c_input_count_constr |> of_nat env sigma
  | _ ->
    EConstr.mkApp (get_ref env "vcpu.circuit.input_count", [|c|])
      |> Cbv.cbv_norm (Cbv.create_cbv_infos CClosure.all env sigma)
      |> of_nat env sigma

let circuit_wires (env : Environ.env) (sigma : Evd.evar_map) (c : EConstr.t) : EConstr.t list =
  match c |> EConstr.kind sigma with
  | App (constructor, [|_; c_wires_constr; _; _; _|]) ->
    c_wires_constr |> of_list env sigma
  | _ ->
    EConstr.mkApp (get_ref env "vcpu.circuit.wires", [|c|])
      |> Cbv.cbv_norm (Cbv.create_cbv_infos CClosure.all env sigma)
      |> of_list env sigma

let circuit_wire_count (env : Environ.env) (sigma : Evd.evar_map) (c : EConstr.t) : int =
  match c |> EConstr.kind sigma with
  | App (constructor, [|_; c_wires_constr; _; _; _|]) ->
    c_wires_constr |> of_list env sigma |> List.length
  | _ ->
    let typ = EConstr.mkApp (get_ref env "core.list.type", [|get_ref env "vcpu.binding.type"|]) in
    EConstr.mkApp (get_ref env "core.list.length", [|typ; EConstr.mkApp (get_ref env "vcpu.circuit.wires", [|c|])|])
      |> Cbv.cbv_norm (Cbv.create_cbv_infos CClosure.all env sigma)
      |> of_nat env sigma

let circuit_outputs (env : Environ.env) (sigma : Evd.evar_map) (c : EConstr.t) : int list =
  match c |> EConstr.kind sigma with
  | App (constructor, [|_; _; c_outputs_constr; _; _|]) ->
    c_outputs_constr |> of_list env sigma |> List.map (of_nat env sigma)
  | _ ->
    EConstr.mkApp (get_ref env "vcpu.circuit.outputs", [|c|])
      |> Cbv.cbv_norm (Cbv.create_cbv_infos CClosure.all env sigma)
      |> of_list env sigma
      |> List.map (of_nat env sigma)

let circuit_normalize (env : Environ.env) (sigma : Evd.evar_map) (c : EConstr.t) : EConstr.t =
  match c |> Redexpr.cbv_vm env sigma |> EConstr.kind sigma with
  | App (constructor, [|c_input_count_constr; c_wires_constr; c_outputs_constr; _; _|]) ->
    let c_input_count = c_input_count_constr |> of_nat env sigma in
    let c_wires = c_wires_constr |> of_list env sigma in
    let c_outputs = c_outputs_constr |> of_list env sigma |> List.map (of_nat env sigma) in
    let c_wires_wf =
      List.fold_right2 (fun i b t ->
        let (constructor, args) = EConstr.decompose_app sigma b in
        let t' =
          match EConstr.kind sigma constructor, args with
          | _, [] when EConstr.eq_constr sigma constructor (get_ref env "vcpu.binding.Zero") ->
            get_ref env "core.True.I"
          | _, [j_constr] when EConstr.eq_constr sigma constructor (get_ref env "vcpu.binding.Input") ->
            prove_nat_lt env (j_constr |> of_nat env sigma) c_input_count
          | _, [j_constr; k_constr] when EConstr.eq_constr sigma constructor (get_ref env "vcpu.binding.Nand") ->
            mk_conj env sigma
              (prove_nat_lt env (j_constr |> of_nat env sigma) i)
              (prove_nat_lt env (k_constr |> of_nat env sigma) i)
          | _ -> assert false in
        mk_conj env sigma t' t
      ) (List.init (c_wires |> List.length) (fun i -> i)) c_wires (get_ref env "core.True.I") in
    let c_outputs_wf =
      List.fold_right (fun i t ->
        mk_conj env sigma (prove_nat_lt env i (c_wires |> List.length)) t
      ) c_outputs (get_ref env "core.True.I") in
    EConstr.mkApp (constructor, [|c_input_count_constr; c_wires_constr; c_outputs_constr; c_wires_wf; c_outputs_wf|])
  | _ -> assert false

let circuit_set_outputs (env : Environ.env) (sigma : Evd.evar_map) (c : EConstr.t) (outputs : int list) : EConstr.t =
  let c_wire_count = circuit_wire_count env sigma c in
  EConstr.mkApp (
    get_ref env "vcpu.circuit.set_outputs",
    [|
      c;
      outputs |> List.map (to_nat env) |> to_list env (get_ref env "num.nat.type");
      List.fold_right (fun i t ->
        mk_conj env sigma (prove_nat_lt env i c_wire_count) t
      ) outputs (get_ref env "core.True.I");
    |]
  )

let circuit_empty (env : Environ.env) (input_count : int) : EConstr.t =
  EConstr.mkApp (get_ref env "vcpu.circuit.empty", [|to_nat env input_count|]) |> circuit_normalize env (Evd.from_env env)

let circuit_zero (env : Environ.env) : EConstr.t = get_ref env "vcpu.circuit.zero" |> circuit_normalize env (Evd.from_env env)

let circuit_one (env : Environ.env) : EConstr.t = get_ref env "vcpu.circuit.one" |> circuit_normalize env (Evd.from_env env)

let circuit_add (env : Environ.env) (sigma : Evd.evar_map) (c_parent : EConstr.t) (c_child : EConstr.t)
    (input_wires : int list) : EConstr.t * int list =
  let c_parent_wire_count = circuit_wire_count env sigma c_parent in
  let input_wires_term = input_wires |> List.map (to_nat env) |> to_list env (get_ref env "num.nat.type") in
  let h1 = prove_nat_eq env (input_wires |> List.length) in
  let h2 =
    List.fold_right (fun i t ->
      mk_conj env sigma (prove_nat_lt env i c_parent_wire_count) t
    ) input_wires (get_ref env "core.True.I") in
  (
    EConstr.mkApp (
      get_ref env "vcpu.circuit.add",
      [|c_parent; c_child; input_wires_term; h1; h2|]
    ) |> circuit_normalize env sigma,
    circuit_outputs env sigma c_child |> List.map (fun i -> c_parent_wire_count + List.length input_wires + i)
    (* EConstr.mkApp (
      get_ref env "vcpu.circuit.add_child_output_wires",
      [|c_parent; c_child; input_wires_term; h1; h2|]
    )
      |> Cbv.cbv_norm (Cbv.create_cbv_infos CClosure.all env sigma)
      |> of_list env sigma
      |> List.map (of_nat env sigma) *)
  )

let circuit_switch (env : Environ.env) (data_size : int) : EConstr.t =
  EConstr.mkApp (get_ref env "vcpu.circuit.switch", [|to_nat env data_size|])

let circuit_const (env : Environ.env) (sigma : Evd.evar_map) (data : bool list) : EConstr.t =
  let c_const = circuit_empty env 0 in
  let (c_const', zero_output_wires) = circuit_add env sigma c_const (circuit_zero env) [] in
  let (c_const'', one_output_wires) = circuit_add env sigma c_const' (circuit_one env) [] in
  let c_const''' = circuit_set_outputs env sigma c_const''
    (data |> List.map (fun b -> if b then one_output_wires else zero_output_wires) |> List.flatten) in
  c_const'''

let constructor_arg_types_of_inductive (env : Environ.env) (sigma : Evd.evar_map)
    (ind : Names.inductive) (params : EConstr.t list) : EConstr.t list list =
  (Inductive.lookup_mind_specif env ind |> snd).mind_user_lc
  |> Array.to_list
  |> List.map EConstr.of_constr
  |> List.map (fun branch_typ ->
    branch_typ
    |> EConstr.decompose_prod_n_assum sigma (params |> List.length)
    |> snd
    |> EConstr.Vars.substl params
    |> EConstr.decompose_prod sigma
    |> fst
    |> List.map snd
  )

let rec size_of_type (env : Environ.env) (sigma : Evd.evar_map) (typ : EConstr.t) : int =
  let f, args = EConstr.decompose_app sigma typ in
  match EConstr.kind sigma f, args with
  | _, _ when EConstr.eq_constr sigma typ (get_ref env "core.bool.type") -> 1
  | _, [a1; a2] when EConstr.eq_constr sigma f (get_ref env "vcpu.vector.type") ->
    (a1 |> size_of_type env sigma) *
    (a2 |> Cbv.cbv_norm (Cbv.create_cbv_infos CClosure.all env sigma) |> of_nat env sigma)
  | Ind (ind, _), params ->
    let constructor_arg_types = constructor_arg_types_of_inductive env sigma ind params in
    List.length constructor_arg_types +
      (
        constructor_arg_types
        |> List.map (fun arg_types ->
          arg_types
          |> List.map (size_of_type env sigma)
          |> List.fold_left (+) 0
        )
        |> List.fold_left max 0
      )
  | _ -> CErrors.user_err Pp.(str "Unknown type:" ++ spc () ++ Printer.pr_econstr_env env sigma typ)

exception Reduction_blocked of EConstr.t

let rec verify_reduction_not_blocked (sigma : Evd.evar_map) (evars : EConstr.t list) (t : EConstr.t) : unit =
  match EConstr.kind sigma t with
  | App (f, args) when EConstr.isFix sigma f ->
    args |> Array.iter (verify_reduction_not_blocked sigma evars)
  | Case (ci, _, _, _, _, scrutinee, _) ->
    if evars |> constr_list_mem sigma scrutinee &&
      Names.GlobRef.equal (Names.GlobRef.IndRef ci.ci_ind) (Coqlib.lib_ref "vcpu.vector.type")
    then raise (Reduction_blocked scrutinee)
    else verify_reduction_not_blocked sigma evars scrutinee
  | _ -> ()

let rec convert (env : Environ.env) (sigma : Evd.evar_map) (evars : EConstr.t list) (source : EConstr.t)
    : (EConstr.t * int list) list * EConstr.t =
  Feedback.msg_notice Pp.(str "convert" ++ spc () ++ Printer.pr_econstr_env env sigma source);

  (* Reduce the source *)
  let source = Cbv.cbv_norm (Cbv.create_cbv_infos CClosure.allnolet env sigma) source in

  (* Replace vector of let in with let in of vector and vector of match with match of vector *)
  let source =
    match EConstr.kind sigma source with
    | App (f, [|a1; a2; a3; a4|]) when EConstr.eq_constr sigma f (get_ref env "vcpu.vector.constructor") -> (
      match EConstr.kind sigma a3 with
      | LetIn (value_binder_annot, value, value_type, context) -> (
        let context' = EConstr.mkApp (f, [|a1; a2; context; a4 |> EConstr.Vars.lift 1|]) in
        EConstr.mkLetIn (value_binder_annot, value, value_type, context')
      )
      | Case (ci, u, params, p, iv, scrutinee, brs) ->
        let brs' = brs |> Array.map (fun (binder_annots, t) ->
          (binder_annots, EConstr.mkApp (f, [|a1; a2; t; a4 |> EConstr.Vars.lift (binder_annots |> Array.length)|]))
        ) in
        EConstr.mkCase (ci, u, params, p, iv, scrutinee, brs')
      | _ -> source
    )
    | _ -> source in

  (* Prune unneded evars *)
  let evars = evars |> List.filter (fun evar -> Termops.dependent sigma evar source) in

  (* Allocate input wires *)
  let (input_mapping, input_count) =
    evars |> List.fold_left (fun (input_mapping, input_count) evar ->
      let evar_size = size_of_type env sigma (Retyping.get_type_of env sigma evar) in
      (
        (evar, List.init evar_size (fun i -> input_count + i)) :: input_mapping,
        input_count + evar_size
      )
    ) ([], 0) in

  let c_source = circuit_empty env input_count in
  let (sigma, c_source') = try
    verify_reduction_not_blocked sigma evars source;
    match EConstr.kind sigma source with

    (* Evar *)
    | _ when evars |> constr_list_mem sigma source ->
      let input_wires = input_mapping |> constr_list_assoc sigma source in
      let c_body' = circuit_set_outputs env sigma c_source input_wires in
      (sigma, c_body')

    (* Let in *)
    | LetIn (_, value, value_type, context) ->
      let (value_input_mapping, c_value) = convert env sigma evars value in
      let value_input_wires = List.init (circuit_input_count env sigma c_value) (fun i ->
        let (evar, value_input_wires) =
          value_input_mapping |> List.find (fun (_, value_input_wires) -> value_input_wires |> List.mem i) in
        List.nth (input_mapping |> constr_list_assoc sigma evar) (value_input_wires |> list_index_of i)
      ) in
      let (c_source', value_output_wires) = circuit_add env sigma c_source c_value value_input_wires in
      let (sigma, value_evar) = Evarutil.new_evar env sigma value_type in
      let (context_input_mapping, c_context) =
        convert env sigma (evars @ [value_evar]) (context |> EConstr.Vars.subst1 value_evar) in
      let context_input_wires = List.init (circuit_input_count env sigma c_context) (fun i ->
        let (evar, context_input_wires) =
          context_input_mapping |> List.find (fun (_, context_input_wires) -> context_input_wires |> List.mem i) in
        if EConstr.eq_constr sigma evar value_evar
        then List.nth value_output_wires (context_input_wires |> list_index_of i)
        else List.nth (input_mapping |> constr_list_assoc sigma evar) (context_input_wires |> list_index_of i)
      ) in
      let (c_source'', context_output_wires) = circuit_add env sigma c_source' c_context context_input_wires in
      let c_source''' = circuit_set_outputs env sigma c_source'' context_output_wires in
      (sigma, c_source''')

    (* Match bool *)
    | Case (ci, _, _, (_, brs_type), _, scrutinee, brs) when
        Names.GlobRef.equal (Names.GlobRef.IndRef ci.ci_ind) (Coqlib.lib_ref "core.bool.type") ->
      let (scrutinee_input_mapping, c_scrutinee) = convert env sigma evars scrutinee in
      let scrutinee_input_wires = List.init (circuit_input_count env sigma c_scrutinee) (fun i ->
        let (evar, scrutinee_input_wires) =
          scrutinee_input_mapping |> List.find (fun (_, scrutinee_input_wires) -> scrutinee_input_wires |> List.mem i) in
        List.nth (input_mapping |> constr_list_assoc sigma evar) (scrutinee_input_wires |> list_index_of i)
      ) in
      let (c_source', scutinee_output_wires) = circuit_add env sigma c_source c_scrutinee scrutinee_input_wires in
      let (br_false_input_mapping, c_br_false) = convert env sigma evars (brs.(1) |> snd) in
      let br_false_input_wires = List.init (circuit_input_count env sigma c_br_false) (fun i ->
        let (evar, br_false_input_wires) =
          br_false_input_mapping |> List.find (fun (_, br_false_input_wires) -> br_false_input_wires |> List.mem i) in
        List.nth (input_mapping |> constr_list_assoc sigma evar) (br_false_input_wires |> list_index_of i)
      ) in
      let (c_source'', br_false_output_wires) = circuit_add env sigma c_source' c_br_false br_false_input_wires in
      let (br_true_input_mapping, c_br_true) = convert env sigma evars (brs.(0) |> snd) in
      let br_true_input_wires = List.init (circuit_input_count env sigma c_br_true) (fun i ->
        let (evar, br_true_input_wires) =
          br_true_input_mapping |> List.find (fun (_, br_true_input_wires) -> br_true_input_wires |> List.mem i) in
        List.nth (input_mapping |> constr_list_assoc sigma evar) (br_true_input_wires |> list_index_of i)
      ) in
      let (c_source''', br_true_output_wires) = circuit_add env sigma c_source'' c_br_true br_true_input_wires in
      let c_switch = circuit_switch env (size_of_type env sigma brs_type) in
      let (c_source'''', switch_output_wires) = circuit_add env sigma c_source''' c_switch
        (scutinee_output_wires @ br_false_output_wires @ br_true_output_wires) in
      let c_source''''' = circuit_set_outputs env sigma c_source'''' switch_output_wires in
      (sigma, c_source''''')

    (* Match inductive *)
    | Case (ci, _, params, (_, brs_type), _, scrutinee, brs) ->
      let constructor_arg_types = constructor_arg_types_of_inductive env sigma ci.ci_ind (params |> Array.to_list) in
      let constructor_count = constructor_arg_types |> List.length in
      let (scrutinee_input_mapping, c_scrutinee) = convert env sigma evars scrutinee in
      let scrutinee_input_wires = List.init (circuit_input_count env sigma c_scrutinee) (fun i ->
        let (evar, scrutinee_input_wires) =
          scrutinee_input_mapping |> List.find (fun (_, scrutinee_input_wires) -> scrutinee_input_wires |> List.mem i) in
        List.nth (input_mapping |> constr_list_assoc sigma evar) (scrutinee_input_wires |> list_index_of i)
      ) in
      let (c_source', scutinee_output_wires) = circuit_add env sigma c_source c_scrutinee scrutinee_input_wires in
      let (sigma, c_source'', brs_output_wires) =
        List.fold_left2
        (fun (sigma, c_source', brs_output_wires) arg_types br ->
          let (sigma, arg_evars) = arg_types |> List.fold_left (fun (sigma, evars) typ ->
            let (sigma, evar) = Evarutil.new_evar env sigma typ in
            (sigma, evar :: evars)
          ) (sigma, []) in
          let br' = br |> EConstr.Vars.substl (arg_evars |> List.rev) in
          let (br_input_mapping, c_br) = convert env sigma (evars @ arg_evars) br' in
          let br_input_wires = List.init (circuit_input_count env sigma c_br) (fun i ->
            let (evar, br_input_wires) =
              br_input_mapping |> List.find (fun (_, br_input_wires) -> br_input_wires |> List.mem i) in
            if arg_evars |> constr_list_mem sigma evar
            then
              let arg_offset =
                arg_types
                |> List.to_seq
                |> Seq.take (arg_evars |> constr_list_index_of sigma evar)
                |> Seq.map (size_of_type env sigma)
                |> Seq.fold_left (+) 0 in
              List.nth scutinee_output_wires (constructor_count + arg_offset + (br_input_wires |> list_index_of i))
            else List.nth (input_mapping |> constr_list_assoc sigma evar) (br_input_wires |> list_index_of i)
          ) in
          let (c_source'', br_output_wires) = circuit_add env sigma c_source' c_br br_input_wires in
          (sigma, c_source'', brs_output_wires @ [br_output_wires])
        )
        (sigma, c_source', [])
        constructor_arg_types
        (brs |> Array.to_list |> List.map snd) in
      let (c_source''', switches_output_wires) =
        List.fold_left2
        (fun (c_source', switches_output_wires) counstructor_index br_output_wires ->
          let c_switch = circuit_switch env (size_of_type env sigma brs_type) in
          let (c_source'', switch_output_wires) = circuit_add env sigma c_source' c_switch
            (List.nth scutinee_output_wires counstructor_index :: br_output_wires @ switches_output_wires) in
          (c_source'', switch_output_wires)
        )
        (c_source'', brs_output_wires |> List.hd)
        (List.init (constructor_count - 1) (fun i -> i + 1))
        (brs_output_wires |> List.tl) in
      let c_source'''' = circuit_set_outputs env sigma c_source''' switches_output_wires in
      (sigma, c_source'''')

    (* false and true *)
    | _ when EConstr.eq_constr sigma source (get_ref env "core.bool.false") ->
      let c_zero = circuit_zero env in
      let (c_source', zero_output_wires) = circuit_add env sigma c_source c_zero [] in
      let c_source'' = circuit_set_outputs env sigma c_source' zero_output_wires in
      (sigma, c_source'')
    | _ when EConstr.eq_constr sigma source (get_ref env "core.bool.true") ->
      let c_one = circuit_one env in
      let (c_source', one_output_wires) = circuit_add env sigma c_source c_one [] in
      let c_source'' = circuit_set_outputs env sigma c_source' one_output_wires in
      (sigma, c_source'')

    (* Vector *)
    | App (f, [|_; _; a3; _|]) when EConstr.eq_constr sigma f (get_ref env "vcpu.vector.constructor") ->
      verify_reduction_not_blocked sigma evars a3;
      let l = of_list env sigma a3 in
      let (c_source', children_output_wires) = l |> List.fold_left (fun (c_source', children_output_wires) child ->
        let (child_input_mapping, c_child) = convert env sigma evars child in
        let child_input_wires = List.init (circuit_input_count env sigma c_child) (fun i ->
          let (evar, child_input_wires) =
            child_input_mapping |> List.find (fun (_, child_input_wires) -> child_input_wires |> List.mem i) in
          List.nth (input_mapping |> constr_list_assoc sigma evar) (child_input_wires |> list_index_of i)
        ) in
        let (c_source'', child_output_wires) = circuit_add env sigma c_source' c_child child_input_wires in
        (c_source'', children_output_wires @ child_output_wires)
      ) (c_source, []) in
      let c_source'' = circuit_set_outputs env sigma c_source' children_output_wires in
      (sigma, c_source'')

    (* Indcutive *)
    | _ when source |> EConstr.decompose_app sigma |> fst |> EConstr.isConstruct sigma -> (
      let (f, params_args) = EConstr.decompose_app sigma source in
      match EConstr.kind sigma f with
      | Construct ((ind, contructor_index), _) ->
        let (_, one_inductive_body) = Inductive.lookup_mind_specif env ind in
        let params_count = one_inductive_body.mind_arity_ctxt |> List.length in
        let constructor_count = one_inductive_body.mind_user_lc |> Array.length in
        let args = params_args |> List.to_seq |> Seq.drop params_count in
        let c_constructor_index = circuit_const env sigma (List.init constructor_count (fun i -> i = contructor_index)) in
        let (c_source', contructor_index_output_wires) = circuit_add env sigma c_source c_constructor_index [] in
        let (c_source'', args_output_wires) = args |> Seq.fold_left (fun (c_source', args_output_wires) arg ->
          let (arg_input_mapping, c_arg) = convert env sigma evars arg in
          let arg_input_wires = List.init (circuit_input_count env sigma c_arg) (fun i ->
            let (evar, arg_input_wires) =
              arg_input_mapping |> List.find (fun (_, arg_input_wires) -> arg_input_wires |> List.mem i) in
            List.nth (input_mapping |> constr_list_assoc sigma evar) (arg_input_wires |> list_index_of i)
          ) in
          let (c_source'', arg_output_wires) = circuit_add env sigma c_source' c_arg arg_input_wires in
          (c_source'', args_output_wires @ arg_output_wires)
        ) (c_source', []) in
        let c_source''' = circuit_set_outputs env sigma c_source'' (contructor_index_output_wires @ args_output_wires) in
        (sigma, c_source''')
      | _ -> assert false
    )

    | _ -> CErrors.user_err Pp.(str "Unknown term:" ++ spc () ++ Printer.pr_econstr_env env sigma source)
  with

  (* Reduction was blocked, replace a vector variable by sample contents and try again *)
  | Reduction_blocked reduction_blocking_evar ->
    let (typ, length) = dest_vector_type env sigma (Retyping.get_type_of env sigma reduction_blocking_evar) in
    let (sigma, vector_evars) = new_evars env sigma typ length in
    let substituted = Termops.replace_term sigma reduction_blocking_evar (to_vector env typ vector_evars) source in
    let (substituted_input_mapping, c_substituted) = convert env sigma (evars @ vector_evars) substituted in
    let substituted_input_wires = List.init (circuit_input_count env sigma c_substituted) (fun i ->
      let (evar, substituted_input_wires) =
        substituted_input_mapping
        |> List.find (fun (_, substituted_input_wires) -> substituted_input_wires |> List.mem i) in
      if vector_evars |> constr_list_mem sigma evar
      then
        List.nth
          (input_mapping |> constr_list_assoc sigma reduction_blocking_evar)
          (
            size_of_type env sigma typ * (vector_evars |> constr_list_index_of sigma evar) +
            (substituted_input_wires |> list_index_of i)
          )
      else List.nth (input_mapping |> constr_list_assoc sigma evar) (substituted_input_wires |> list_index_of i)
    ) in
    let (c_source', substituted_output_wires) = circuit_add env sigma c_source c_substituted substituted_input_wires in
    let c_source'' = circuit_set_outputs env sigma c_source' substituted_output_wires in
    (sigma, c_source'') in

  (* Feedback.msg_notice Pp.(str "return" ++ spc () ++ Printer.pr_econstr_env env sigma c_source'); *)
  (input_mapping, c_source' |> circuit_normalize env sigma)

let compile (id : Names.Id.t) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let constant_name = Names.Constant.make1 (Names.KerName.make (Global.current_modpath ()) (Names.Label.of_id id)) in
  if not (Environ.mem_constant constant_name env) then
    CErrors.user_err Pp.(str "Constant " ++ Names.Constant.print constant_name ++ str " does not exist.");
  let cb = Environ.lookup_constant constant_name env in
  match Global.body_of_constant_body Library.indirect_accessor cb with
  | Some (body, _, _) -> (
    let body = EConstr.of_constr body in
    let typ = Retyping.get_type_of env sigma body in
    match EConstr.kind sigma typ with
    | Prod (_, typ_in, typ_out) -> (
      let typ_in_size = size_of_type env sigma typ_in in
      let (sigma, evar) = Evarutil.new_evar env sigma typ_in in
      let applied_body = EConstr.mkApp (body, [|evar|]) in
      let (input_mapping, c_applied_body) = convert env sigma [evar] applied_body in
      let c_body = circuit_empty env typ_in_size in
      let input_wires = if input_mapping = [] then [] else List.init typ_in_size (fun i -> i) in
      let (c_body', body_output_wires) = circuit_add env sigma c_body c_applied_body input_wires in
      let c_body'' = circuit_set_outputs env sigma c_body' body_output_wires in
      let info = Declare.Info.make () in
      let cinfo = Declare.CInfo.make ~name:((id |> Names.Id.to_string) ^ "_circuit" |> Names.Id.of_string) ~typ:None () in
      Declare.declare_definition ~info ~cinfo ~opaque:false ~body:c_body'' sigma |> ignore
    )
    | _ -> CErrors.user_err Pp.(str "Not a product:" ++ spc () ++ Printer.pr_econstr_env env sigma typ)
  )
  | None ->
    CErrors.user_err Pp.(str "Constant" ++ spc () ++ Names.Constant.print constant_name ++ str " has no value.")
