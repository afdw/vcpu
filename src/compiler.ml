let list_index_of (type a) (x : a) (l : a list) : int =
  l |> List.mapi (fun i y -> (i, y)) |> List.find (fun (_, y) -> y = x) |> fst

let list_select (type a) (values : a list) (indices : int list) : a list =
  indices |> List.map (fun i -> List.nth values i)

let constr_list_mem (sigma : Evd.evar_map) (t : EConstr.t) (l : EConstr.t list) =
  l |> List.exists (fun t' -> EConstr.eq_constr sigma t t')

let constr_list_assoc (type a) (sigma : Evd.evar_map) (t : EConstr.t) (l : (EConstr.t * a) list) =
  l |> List.find (fun (t', _) -> EConstr.eq_constr sigma t t') |> snd

let constr_list_index_of (sigma : Evd.evar_map) (t : EConstr.t) (l : EConstr.t list) : int =
  l |> List.mapi (fun i t' -> (i, t')) |> List.find (fun (_, t') -> EConstr.eq_constr sigma t t') |> fst

let ref_cache : EConstr.t CString.Map.t ref = ref CString.Map.empty

let get_ref (env : Environ.env) (s : string) : EConstr.t =
  match !ref_cache |> CString.Map.find_opt s with
  | Some t -> t
  | None ->
    let t = EConstr.of_constr (UnivGen.constr_of_monomorphic_global env (Coqlib.lib_ref s)) in
    ref_cache := !ref_cache |> CString.Map.add s t;
    t

let dest_const_ref (glob_ref : Names.GlobRef.t) : Names.Constant.t =
  match glob_ref with
  | ConstRef t -> t
  | _ -> assert false

let dest_ind_ref (glob_ref : Names.GlobRef.t) : Names.Ind.t =
  match glob_ref with
  | IndRef t -> t
  | _ -> assert false

let to_bool_constr (env : Environ.env) (b : bool) : EConstr.t =
  if b then get_ref env "core.bool.true" else get_ref env "core.bool.false"

let rec to_list_constr (env : Environ.env) (typ : EConstr.t) (l : EConstr.t list) : EConstr.t =
  match l with
  | [] -> EConstr.mkApp (get_ref env "core.list.nil", [|typ|])
  | x :: l' -> EConstr.mkApp (get_ref env "core.list.cons", [|typ; x; to_list_constr env typ l'|])

let rec of_list_constr (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.t) : EConstr.t list =
  match EConstr.kind sigma t with
  | App (f, [|_|]) when EConstr.eq_constr sigma f (get_ref env "core.list.nil") -> []
  | App (f, [|_; a; t'|]) when EConstr.eq_constr sigma f (get_ref env "core.list.cons") ->
    a :: of_list_constr env sigma t'
  | _ -> CErrors.user_err Pp.(str "Not an application of nil or cons:" ++ spc () ++ Printer.pr_econstr_env env sigma t)

let to_nat_constr (env : Environ.env) (n : int) : EConstr.t =
  assert (n >= 0);
  let rec aux n = if n = 0 then [] else not (n mod 2 = 0) :: aux (n / 2) in
  EConstr.mkApp (
    get_ref env "vcpu.bitlist_to_nat",
    [|
      n
      |> aux
      |> List.map (to_bool_constr env)
      |> to_list_constr env (get_ref env "core.bool.type");
    |]
  )

let to_binnat_constr (env : Environ.env) (n : int) : EConstr.t =
  assert (n >= 0);
  let rec aux n =
    if n = 1
    then get_ref env "num.pos.xH"
    else
      EConstr.mkApp (
        (if n mod 2 = 0 then get_ref env "num.pos.xO" else get_ref env "num.pos.xI"),
        [|aux (n / 2)|]
      ) in
  if n = 0
  then get_ref env "num.N.N0"
  else EConstr.mkApp (get_ref env "num.N.Npos", [|aux n|])

let rec of_nat_constr (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.t) : int =
  match EConstr.kind sigma t with
  | _ when EConstr.eq_constr sigma t (get_ref env "num.nat.O") -> 0
  | App (f, [|t'|]) when EConstr.eq_constr sigma f (get_ref env "num.nat.S") -> succ (of_nat_constr env sigma t')
  | _ -> CErrors.user_err Pp.(str "Not an application of O or S:" ++ spc () ++ Printer.pr_econstr_env env sigma t)

let of_binnat_constr (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.t) : int =
  let rec aux t =
    match EConstr.kind sigma t with
    | App (f, [|t'|]) when EConstr.eq_constr sigma f (get_ref env "num.pos.xI") -> (aux t') * 2 + 1
    | App (f, [|t'|]) when EConstr.eq_constr sigma f (get_ref env "num.pos.xO") -> (aux t') * 2
    | _ when EConstr.eq_constr sigma t (get_ref env "num.pos.xH") -> 1
    | _ -> CErrors.user_err Pp.(str "Not an application of xI, xO or xH:" ++ spc () ++ Printer.pr_econstr_env env sigma t) in
  match EConstr.kind sigma t with
  | _ when EConstr.eq_constr sigma t (get_ref env "num.N.N0") -> 0
  | App (f, [|t'|]) when EConstr.eq_constr sigma f (get_ref env "num.N.Npos") -> aux t'
  | _ -> CErrors.user_err Pp.(str "Not an application of N0 or Npos:" ++ spc () ++ Printer.pr_econstr_env env sigma t)

let prove_nat_eq (env : Environ.env) (n : int) : EConstr.t =
  EConstr.mkApp (get_ref env "core.eq.refl", [|get_ref env "num.nat.type"; to_nat_constr env n|])

let prove_binnat_eq (env : Environ.env) (n : int) : EConstr.t =
  EConstr.mkApp (get_ref env "core.eq.refl", [|get_ref env "num.N.type"; to_binnat_constr env n|])

let prove_nat_le (env : Environ.env) (n : int) (m : int) : EConstr.t =
  assert (n <= m);
  EConstr.mkApp (
    get_ref env "num.nat.prove_le",
    [|
      n |> to_nat_constr env;
      m |> to_nat_constr env;
      EConstr.mkApp (get_ref env "core.eq.refl", [|get_ref env "core.bool.type"; get_ref env "core.bool.true"|]);
    |]
  )

let prove_nat_lt (env : Environ.env) (n : int) (m : int) : EConstr.t =
  assert (n < m);
  EConstr.mkCast (
    prove_nat_le env (succ n) m,
    Constr.DEFAULTcast,
    EConstr.mkApp (get_ref env "num.nat.lt", [|to_nat_constr env n; to_nat_constr env m|])
  )

let mk_vector_type (env : Environ.env) (element_typ : EConstr.t) (length : int) : EConstr.t =
  EConstr.mkApp (get_ref env "vcpu.vector.type", [|element_typ; to_binnat_constr env length|])

let dest_vector_type (env : Environ.env) (sigma : Evd.evar_map) (typ : EConstr.t) : EConstr.t * int =
  match EConstr.kind sigma typ with
  | App (f, [|a1; a2|]) when EConstr.eq_constr sigma f (get_ref env "vcpu.vector.type") ->
    (a1, a2 |> Cbv.cbv_norm (Cbv.create_cbv_infos CClosure.all env sigma) |> of_binnat_constr env sigma)
  | _ -> CErrors.user_err Pp.(str "Not an application of vector:" ++ spc () ++ Printer.pr_econstr_env env sigma typ)

let to_vector_constr (env : Environ.env) (typ : EConstr.t) (l : EConstr.t list) : EConstr.t =
  EConstr.mkApp (
    get_ref env "vcpu.vector.constructor",
    [|
      typ;
      to_binnat_constr env (l |> List.length);
      to_list_constr env typ l;
      prove_binnat_eq env (l |> List.length);
    |]
  )

let new_evars (env : Environ.env) (sigma : Evd.evar_map) (typ : EConstr.t) (n : int) : Evd.evar_map * EConstr.t list =
  List.init n (fun i -> i)
    |> List.fold_left (fun (sigma, evars) i ->
      let (sigma, evar) = Evarutil.new_evar env sigma typ in
      (sigma, evar :: evars)
    ) (sigma, [])

type reference =
  | Reference_zero
  | Reference_one
  | Reference_input of int
  | Reference_wire of int

let to_reference_constr (env : Environ.env) (r : reference) : EConstr.t =
  match r with
  | Reference_zero ->
    get_ref env "vcpu.reference.Zero"
  | Reference_one ->
    get_ref env "vcpu.reference.One"
  | Reference_input i ->
    EConstr.mkApp (get_ref env "vcpu.reference.Input", [|i |> to_binnat_constr env|])
  | Reference_wire i ->
    EConstr.mkApp (get_ref env "vcpu.reference.Wire", [|i |> to_binnat_constr env|])

type binding =
  | Binding_immediate of reference
  | Binding_not of reference
  | Binding_and of reference * reference
  | Binding_or of reference * reference
  | Binding_xor of reference * reference
  | Binding_if of reference * reference * reference

let to_binding_constr (env : Environ.env) (b : binding) : EConstr.t =
  match b with
  | Binding_immediate r ->
    EConstr.mkApp (get_ref env "vcpu.binding.Immediate", [|r |> to_reference_constr env|])
  | Binding_not r ->
    EConstr.mkApp (get_ref env "vcpu.binding.Not", [|r |> to_reference_constr env|])
  | Binding_and (r1, r2) ->
    EConstr.mkApp (get_ref env "vcpu.binding.And", [|r1 |> to_reference_constr env; r2 |> to_reference_constr env|])
  | Binding_or (r1, r2) ->
    EConstr.mkApp (get_ref env "vcpu.binding.Or", [|r1 |> to_reference_constr env; r2 |> to_reference_constr env|])
  | Binding_xor (r1, r2) ->
    EConstr.mkApp (get_ref env "vcpu.binding.Or", [|r1 |> to_reference_constr env; r2 |> to_reference_constr env|])
  | Binding_if (r1, r2, r3) ->
    EConstr.mkApp (
      get_ref env "vcpu.binding.If",
      [|r1 |> to_reference_constr env; r2 |> to_reference_constr env; r3 |> to_reference_constr env|]
    )

type circuit = {
  circuit_input_count : int;
  circuit_wire_count : int;
  circuit_wires : binding list;
  circuit_output_wires : int list;
  circuit_with_wf_and_spec_constr : EConstr.t;
}

let reference_wf (input_count : int) (wire_count : int) (r : reference) : bool =
  match r with
  | Reference_zero -> true
  | Reference_one -> true
  | Reference_input i -> i < input_count
  | Reference_wire i -> i < wire_count

let binding_wf (input_count : int) (wire_count : int) (b : binding) : bool =
  match b with
  | Binding_immediate r -> reference_wf input_count wire_count r
  | Binding_not r -> reference_wf input_count wire_count r
  | Binding_and (r1, r2) ->
    reference_wf input_count wire_count r1 &&
    reference_wf input_count wire_count r2
  | Binding_or (r1, r2) ->
    reference_wf input_count wire_count r1 &&
    reference_wf input_count wire_count r2
  | Binding_xor (r1, r2) ->
    reference_wf input_count wire_count r1 &&
    reference_wf input_count wire_count r2
  | Binding_if (r1, r2, r3) ->
    reference_wf input_count wire_count r1 &&
    reference_wf input_count wire_count r2 &&
    reference_wf input_count wire_count r3

let circuit_wire_count_wf (c : circuit) : bool =
  List.length c.circuit_wires = c.circuit_wire_count

let circuit_wires_wf (c : circuit) : bool =
  List.for_all2 (binding_wf c.circuit_input_count) (List.init c.circuit_wire_count (fun i -> i)) c.circuit_wires

let circuit_output_wires_wf (c : circuit) : bool =
  c.circuit_output_wires |> List.for_all (fun i -> i < c.circuit_wire_count)

let circuit_wf (c : circuit) : bool =
  circuit_wire_count_wf c && circuit_wires_wf c && circuit_output_wires_wf c

let reference_compute (inputs : bool list) (intermediates : bool list) (r : reference) : bool =
  match r with
  | Reference_zero -> false
  | Reference_one -> true
  | Reference_input i -> List.nth inputs i
  | Reference_wire i -> List.nth intermediates i

let binding_compute (inputs : bool list) (intermediates : bool list) (b : binding) : bool =
  match b with
  | Binding_immediate r -> reference_compute inputs intermediates r
  | Binding_not r -> not (reference_compute inputs intermediates r)
  | Binding_and (r1, r2) ->
    reference_compute inputs intermediates r1 && reference_compute inputs intermediates r2
  | Binding_or (r1, r2) ->
    reference_compute inputs intermediates r1 || reference_compute inputs intermediates r2
  | Binding_xor (r1, r2) ->
    reference_compute inputs intermediates r1 <> reference_compute inputs intermediates r2
  | Binding_if (r1, r2, r3) ->
    if reference_compute inputs intermediates r1
    then reference_compute inputs intermediates r3
    else reference_compute inputs intermediates r2

let circuit_compute_wires_aux (start_intermediates : bool list) (wires : binding list) (inputs : bool list) : bool list =
  wires |> List.fold_left (fun intermediates b ->
    intermediates @ [binding_compute inputs (start_intermediates @ intermediates) b]
  ) []

let circuit_compute_wires (c : circuit) (inputs : bool list) : bool list =
  circuit_compute_wires_aux [] c.circuit_wires inputs

let circuit_compute (c : circuit) (inputs : bool list) : bool list =
  list_select (circuit_compute_wires c inputs) c.circuit_output_wires

let circuit_let_data (type a) (env : Environ.env) (f : (int -> circuit) -> circuit * a) (c : circuit) : circuit * a =
  let (c_res, x) = f (fun i ->
    {
      c with
      circuit_with_wf_and_spec_constr = EConstr.mkRel i
    }
  ) in
  (
    {
      c_res with
      circuit_with_wf_and_spec_constr =
        EConstr.mkLetIn (
          Context.anonR,
          c.circuit_with_wf_and_spec_constr,
          get_ref env "vcpu.circuit_with_wf_and_spec.type",
          c_res.circuit_with_wf_and_spec_constr
        )
    },
    x
  )

let circuit_let (env : Environ.env) (f : (int -> circuit) -> circuit) (c : circuit) : circuit =
  circuit_let_data env (fun c -> (f c, ())) c |> fst

let circuit_increase_input_count (env : Environ.env) (c : circuit) (additional_input_count : int) : circuit =
  {
    circuit_input_count = c.circuit_input_count + additional_input_count;
    circuit_wire_count = c.circuit_wire_count;
    circuit_wires = c.circuit_wires;
    circuit_output_wires = c.circuit_output_wires;
    circuit_with_wf_and_spec_constr =
      EConstr.mkApp (
        get_ref env "vcpu.circuit.increase_input_count_with_wf_and_spec",
        [|
          EConstr.mkApp (
            get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
            [|c.circuit_with_wf_and_spec_constr|]
          );
          additional_input_count |> to_binnat_constr env;
          EConstr.mkApp (get_ref env "core.eq.refl", [|get_ref env "core.bool.type"; get_ref env "core.bool.true"|]);
        |]
      );
  }

let circuit_set_output_wires (env : Environ.env) (c : circuit) (output_wires : int list) : circuit =
  assert (output_wires |> List.for_all (fun i -> i < c.circuit_wire_count));
  {
    circuit_input_count = c.circuit_input_count;
    circuit_wire_count = c.circuit_wire_count;
    circuit_wires = c.circuit_wires;
    circuit_output_wires = output_wires;
    circuit_with_wf_and_spec_constr =
      EConstr.mkApp (
        get_ref env "vcpu.circuit.set_output_wires_with_wf_and_spec",
        [|
          EConstr.mkApp (
            get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
            [|c.circuit_with_wf_and_spec_constr|]
          );
          output_wires |> List.length |> to_binnat_constr env;
          output_wires |> List.map (to_binnat_constr env) |> to_vector_constr env (get_ref env "num.N.type");
          EConstr.mkApp (get_ref env "core.eq.refl", [|get_ref env "core.bool.type"; get_ref env "core.bool.true"|]);
        |]
      );
  }

let circuit_add_translate_reference (parent_wire_count : int) (input_references : reference list) (r : reference) : reference =
  match r with
  | Reference_zero -> Reference_zero
  | Reference_one -> Reference_one
  | Reference_input i -> List.nth input_references i
  | Reference_wire i -> Reference_wire (parent_wire_count + i)

let circuit_add_translate_binding (parent_wire_count : int) (input_references : reference list) (b : binding) : binding =
  let translate_reference = circuit_add_translate_reference parent_wire_count input_references in
  match b with
  | Binding_immediate r -> Binding_immediate (translate_reference r)
  | Binding_not r -> Binding_not (translate_reference r)
  | Binding_and (r1, r2) -> Binding_and (translate_reference r1, translate_reference r2)
  | Binding_or (r1, r2) -> Binding_or (translate_reference r1, translate_reference r2)
  | Binding_xor (r1, r2) -> Binding_xor (translate_reference r1, translate_reference r2)
  | Binding_if (r1, r2, r3) -> Binding_if (translate_reference r1, translate_reference r2, translate_reference r3)

let circuit_add (env : Environ.env) (c_parent : circuit) (c_child : circuit)
    (input_references : reference list) : circuit * int list =
  assert (List.length input_references = c_child.circuit_input_count);
  assert (input_references |> List.for_all (reference_wf c_parent.circuit_input_count c_parent.circuit_wire_count));
  (
    {
      circuit_input_count = c_parent.circuit_input_count;
      circuit_wire_count = c_parent.circuit_wire_count + c_child.circuit_wire_count;
      circuit_wires =
        c_parent.circuit_wires @
          (c_child.circuit_wires |> List.map
            (circuit_add_translate_binding c_parent.circuit_wire_count input_references));
      circuit_output_wires = c_parent.circuit_output_wires;
      circuit_with_wf_and_spec_constr =
        EConstr.mkApp (
          get_ref env "vcpu.circuit.add_with_wf_and_spec",
          [|
            EConstr.mkApp (
              get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
              [|c_parent.circuit_with_wf_and_spec_constr|]
            );
            EConstr.mkApp (
              get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
              [|c_child.circuit_with_wf_and_spec_constr|]
            );
            input_references
              |> List.map (to_reference_constr env)
              |> to_vector_constr env (get_ref env "vcpu.reference.type");
            EConstr.mkApp (get_ref env "core.eq.refl", [|get_ref env "core.bool.type"; get_ref env "core.bool.true"|]);
          |]
        );
    },
    c_child.circuit_output_wires |> List.map (fun i -> c_parent.circuit_wire_count + i)
  )

let circuit_empty (env : Environ.env) (input_count : int) : circuit =
  {
    circuit_input_count = input_count;
    circuit_wire_count = 0;
    circuit_wires = [];
    circuit_output_wires = [];
    circuit_with_wf_and_spec_constr =
      EConstr.mkApp (get_ref env "vcpu.circuit.empty_with_wf_and_spec", [|to_binnat_constr env input_count|]);
  }

let circuit_id (env : Environ.env) (input_count : int) : circuit =
  {
    circuit_input_count = input_count;
    circuit_wire_count = input_count;
    circuit_wires = List.init input_count (fun i -> Binding_immediate (Reference_input i));
    circuit_output_wires = List.init input_count (fun i -> i);
    circuit_with_wf_and_spec_constr =
      EConstr.mkApp (get_ref env "vcpu.circuit.id_with_wf_and_spec", [|to_binnat_constr env input_count|]);
  }

let circuit_switch (env : Environ.env) (data_size : int) : circuit =
  let c_switch = {
    circuit_input_count = 1 + 2 * data_size;
    circuit_wire_count = data_size;
    circuit_wires =
      List.init data_size (fun i ->
        Binding_if (Reference_input 0, Reference_input (1 + i), Reference_input (1 + data_size + i))
      );
    circuit_output_wires = List.init data_size (fun i -> i);
    circuit_with_wf_and_spec_constr =
      EConstr.mkApp (get_ref env "vcpu.circuit.switch_with_wf_and_spec", [|to_binnat_constr env data_size|]);
  } in
  c_switch |> circuit_let env (fun c_switch ->
    let app =
      EConstr.mkApp (
        get_ref env "vcpu.vector.app",
        [|
          get_ref env "core.bool.type";
          to_binnat_constr env 1;
          to_binnat_constr env (2 * data_size);
          [EConstr.mkRel 3] |> to_vector_constr env (get_ref env "core.bool.type");
          EConstr.mkApp (
            get_ref env "vcpu.vector.app",
            [|
              get_ref env "core.bool.type";
              to_binnat_constr env data_size;
              to_binnat_constr env data_size;
              EConstr.mkRel 2;
              EConstr.mkRel 1;
            |]
          );
        |]
      ) in
    {
      (c_switch 0) with
      circuit_with_wf_and_spec_constr =
        EConstr.mkApp (
          get_ref env "vcpu.circuit_with_wf_and_spec.constructor",
          [|
            EConstr.mkApp (
              get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
              [|(c_switch 1).circuit_with_wf_and_spec_constr|]
            );
            EConstr.mkProd (
              Context.anonR,
              get_ref env "core.bool.type",
              EConstr.mkProd (
                Context.anonR,
                mk_vector_type env (get_ref env "core.bool.type") data_size,
                EConstr.mkProd (
                  Context.anonR,
                  mk_vector_type env (get_ref env "core.bool.type") data_size,
                  EConstr.mkApp (
                    get_ref env "vcpu.vector.similar",
                    [|
                      get_ref env "core.bool.type";
                      to_binnat_constr env data_size;
                      to_binnat_constr env data_size;
                      EConstr.mkApp (
                        get_ref env "vcpu.circuit_with_wf.compute_vec",
                        [|
                          EConstr.mkApp (
                            get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
                            [|(c_switch 4).circuit_with_wf_and_spec_constr|]
                          );
                          app;
                        |]
                      );
                      EConstr.mkCase (
                        Inductiveops.make_case_info
                          env
                          (Coqlib.lib_ref "core.bool.type" |> dest_ind_ref)
                          Sorts.Relevant
                          Constr.IfStyle,
                        EConstr.EInstance.empty,
                        [||],
                        (
                          [|Context.anonR|],
                          mk_vector_type env (get_ref env "core.bool.type") data_size
                        ),
                        Constr.NoInvert,
                        EConstr.mkRel 3,
                        [|
                          ([||], EConstr.mkRel 1);
                          ([||], EConstr.mkRel 2);
                        |];
                      )
                    |]
                  )
                )
              )
            );
            EConstr.mkLambda (
              Context.anonR,
              get_ref env "core.bool.type",
              EConstr.mkLambda (
                Context.anonR,
                mk_vector_type env (get_ref env "core.bool.type") data_size,
                EConstr.mkLambda (
                  Context.anonR,
                  mk_vector_type env (get_ref env "core.bool.type") data_size,
                  EConstr.mkApp (
                    EConstr.mkApp (
                      get_ref env "vcpu.circuit_with_wf_and_spec.spec",
                      [|(c_switch 4).circuit_with_wf_and_spec_constr|]
                    ),
                    [|
                      app;
                      EConstr.mkRel 3;
                      EConstr.mkRel 2;
                      EConstr.mkRel 1;
                      EConstr.mkApp (
                        get_ref env "core.eq.refl",
                        [|
                          EConstr.mkApp (get_ref env "core.list.type", [|get_ref env "core.bool.type"|]);
                          EConstr.mkApp (
                            get_ref env "vcpu.vector.list",
                            [|
                              get_ref env "core.bool.type";
                              to_binnat_constr env (1 + 2 * data_size);
                              app;
                            |]
                          )
                        |]
                      );
                    |]
                  )
                )
              )
            );
          |]
        )
    }
  )

let circuit_zero (env : Environ.env) : circuit =
  {
    circuit_input_count = 0;
    circuit_wire_count = 1;
    circuit_wires = [Binding_immediate Reference_zero];
    circuit_output_wires = [0];
    circuit_with_wf_and_spec_constr = get_ref env "vcpu.circuit.zero_with_wf_and_spec";
  }

let circuit_one (env : Environ.env) : circuit =
  {
    circuit_input_count = 0;
    circuit_wire_count = 1;
    circuit_wires = [Binding_immediate Reference_one];
    circuit_output_wires = [0];
    circuit_with_wf_and_spec_constr = get_ref env "vcpu.circuit.one_with_wf_and_spec";
  }

let circuit_not (env : Environ.env) : circuit =
  {
    circuit_input_count = 1;
    circuit_wire_count = 1;
    circuit_wires = [Binding_not (Reference_input 0)];
    circuit_output_wires = [0];
    circuit_with_wf_and_spec_constr = get_ref env "vcpu.circuit.not_with_wf_and_spec";
  }

let circuit_and (env : Environ.env) : circuit =
  {
    circuit_input_count = 2;
    circuit_wire_count = 1;
    circuit_wires = [Binding_and (Reference_input 0, Reference_input 1)];
    circuit_output_wires = [0];
    circuit_with_wf_and_spec_constr = get_ref env "vcpu.circuit.and_with_wf_and_spec";
  }

let circuit_or (env : Environ.env) : circuit =
  {
    circuit_input_count = 2;
    circuit_wire_count = 1;
    circuit_wires = [Binding_or (Reference_input 0, Reference_input 1)];
    circuit_output_wires = [0];
    circuit_with_wf_and_spec_constr = get_ref env "vcpu.circuit.or_with_wf_and_spec";
  }

let circuit_xor (env : Environ.env) : circuit =
  {
    circuit_input_count = 2;
    circuit_wire_count = 1;
    circuit_wires = [Binding_xor (Reference_input 0, Reference_input 1)];
    circuit_output_wires = [0];
    circuit_with_wf_and_spec_constr = get_ref env "vcpu.circuit.xor_with_wf_and_spec";
  }

let circuit_const (env : Environ.env) (data : bool list) : circuit =
  let c_const = circuit_empty env 0 in
  let (c_const, zero_output_wires) = circuit_add env c_const (circuit_zero env) [] in
  let (c_const, one_output_wires) = circuit_add env c_const (circuit_one env) [] in
  let c_const =
    circuit_set_output_wires env c_const
    (data |> List.map (fun b -> if b then one_output_wires else zero_output_wires) |> List.flatten) in
  c_const |> circuit_let env (fun c_const ->
    {
      (c_const 0) with
      circuit_with_wf_and_spec_constr =
        EConstr.mkApp (
          get_ref env "vcpu.circuit_with_wf_and_spec.constructor",
          [|
            EConstr.mkApp (
              get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
              [|(c_const 1).circuit_with_wf_and_spec_constr|]
            );
            EConstr.mkApp (
              get_ref env "vcpu.vector.similar",
              [|
                get_ref env "core.bool.type";
                to_binnat_constr env (data |> List.length);
                to_binnat_constr env (data |> List.length);
                EConstr.mkApp (
                  get_ref env "vcpu.circuit_with_wf.compute_vec",
                  [|
                    EConstr.mkApp (
                      get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
                      [|(c_const 1).circuit_with_wf_and_spec_constr|]
                    );
                    [] |> to_vector_constr env (get_ref env "core.bool.type");
                  |]
                );
                data |> List.map (to_bool_constr env) |> to_vector_constr env (get_ref env "core.bool.type");
              |]
            );
            EConstr.mkApp (
              get_ref env "vcpu.circuit_with_wf_and_spec.spec",
              [|
                (c_const 1).circuit_with_wf_and_spec_constr;
                [] |> to_vector_constr env (get_ref env "core.bool.type");
                data |> List.map (to_bool_constr env) |> to_vector_constr env (get_ref env "core.bool.type");
                EConstr.mkApp (
                  get_ref env "core.eq.refl",
                  [|
                    EConstr.mkApp (get_ref env "core.list.type", [|get_ref env "core.bool.type"|]);
                    data |> List.map (to_bool_constr env) |> to_list_constr env (get_ref env "core.bool.type");
                  |]
                )
              |]
            );
          |]
        )
    }
  )

let constructor_arg_types_of_inductive (env : Environ.env) (sigma : Evd.evar_map)
    (ind : Names.inductive) (params : EConstr.t list) : EConstr.t list list =
  let (_, one_inductive_body) = Inductive.lookup_mind_specif env ind in
  one_inductive_body.mind_user_lc
  |> Array.to_list
  |> List.map EConstr.of_constr
  |> List.map (fun branch_typ ->
    branch_typ
    |> EConstr.decompose_prod_n_decls sigma (params |> List.length)
    |> snd
    |> EConstr.Vars.substl params
    |> EConstr.decompose_prod sigma
    |> fst
    |> List.map snd
  )

let serialized : (EConstr.t * Names.Constant.t) list ref =
  Summary.ref ~name:"serialized" []

let compiled : ((Names.Constant.t * EConstr.t list) * circuit) list ref =
  Summary.ref ~name:"compiled" []

let rec size_of_type (env : Environ.env) (sigma : Evd.evar_map) (typ : EConstr.t) : int =
  let f, args = EConstr.decompose_app sigma typ in
  match EConstr.kind sigma f, args with
  | _, _ when EConstr.eq_constr sigma typ (get_ref env "core.bool.type") ->
    1
  | _, _ when EConstr.eq_constr sigma f (get_ref env "vcpu.vector.type") ->
    let (element_typ, length) = dest_vector_type env sigma typ in
    let element_typ_size = element_typ |> size_of_type env sigma in
    element_typ_size * length
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

let rec serialize (env : Environ.env) (sigma : Evd.evar_map) (typ : EConstr.t) : EConstr.t =
  if !serialized |> List.map fst |> constr_list_mem sigma typ then
    EConstr.mkConst (!serialized |> constr_list_assoc sigma typ)
  else
    let typ_size = size_of_type env sigma typ in
    let body =
      let f, args = EConstr.decompose_app sigma typ in
      match EConstr.kind sigma f, args with
      | _, _ when EConstr.eq_constr sigma typ (get_ref env "core.bool.type") ->
        [EConstr.mkRel 1] |> to_vector_constr env (get_ref env "core.bool.type")
      | _, _ when EConstr.eq_constr sigma f (get_ref env "vcpu.vector.type") ->
        let (element_typ, length) = dest_vector_type env sigma typ in
        let element_typ_size = element_typ |> size_of_type env sigma in
        List.init length (fun i -> i) |> List.fold_left (fun t i ->
          EConstr.mkLetIn (
            Context.anonR,
            EConstr.mkApp (
              get_ref env "vcpu.vector.dest",
              [|
                element_typ;
                to_binnat_constr env i;
                if i = length - 1 then
                  EConstr.mkRel 1
                else
                  EConstr.mkApp (
                    get_ref env "core.prod.proj2",
                    [|element_typ; mk_vector_type env element_typ (succ i); EConstr.mkRel 1|]
                  );
              |]
            ),
            EConstr.mkApp (
              get_ref env "core.prod.type",
              [|element_typ; mk_vector_type env element_typ i|]
            ),
            EConstr.mkApp (
              get_ref env "vcpu.vector.app",
              [|
                get_ref env "core.bool.type";
                to_binnat_constr env element_typ_size;
                to_binnat_constr env (element_typ_size * i);
                EConstr.mkApp (
                  serialize env sigma element_typ,
                  [|
                    EConstr.mkApp (
                      get_ref env "core.prod.proj1",
                      [|element_typ; mk_vector_type env element_typ i; EConstr.mkRel 1|]
                    );
                  |]
                );
                t;
              |]
            )
          )
        ) ([] |> to_vector_constr env (get_ref env "core.bool.type"))
      | Ind (ind, u), params ->
        let constructor_arg_types = constructor_arg_types_of_inductive env sigma ind params in
        let constructor_count = constructor_arg_types |> List.length in
        EConstr.mkCase (
          Inductiveops.make_case_info env ind Sorts.Relevant Constr.RegularStyle,
          u,
          params |> Array.of_list,
          (
            [|Context.anonR|],
            mk_vector_type env (get_ref env "core.bool.type") typ_size
          ),
          Constr.NoInvert,
          EConstr.mkRel 1,
          constructor_arg_types |> List.mapi (fun contructor_index arg_types ->
            let arg_count = arg_types |> List.length in
            let args_size =
              arg_types
              |> List.map (size_of_type env sigma)
              |> List.fold_left (+) 0 in
            let max_args_size =
              constructor_arg_types
              |> List.map (fun arg_types ->
                arg_types
                |> List.map (size_of_type env sigma)
                |> List.fold_left (+) 0
              )
              |> List.fold_left max 0 in
            let padding_size = max_args_size - args_size in
            (
              Array.init arg_count (fun _ -> Context.anonR),
              EConstr.mkApp (
                get_ref env "vcpu.vector.app",
                [|
                  get_ref env "core.bool.type";
                  to_binnat_constr env constructor_count;
                  to_binnat_constr env max_args_size;
                  List.init constructor_count (fun i -> to_bool_constr env (i = contructor_index))
                    |> to_vector_constr env (get_ref env "core.bool.type");
                  EConstr.mkApp (
                    get_ref env "vcpu.vector.app",
                    [|
                      get_ref env "core.bool.type";
                      to_binnat_constr env args_size;
                      to_binnat_constr env padding_size;
                      arg_types |> List.rev |> List.fold_left (fun ((i, t_size), t) arg_type ->
                        let arg_type_size = arg_type |> size_of_type env sigma in
                        (
                          (succ i, arg_type_size),
                          EConstr.mkApp (
                            get_ref env "vcpu.vector.app",
                            [|
                              get_ref env "core.bool.type";
                              to_binnat_constr env arg_type_size;
                              to_binnat_constr env t_size;
                              EConstr.mkApp (
                                serialize env sigma arg_type,
                                [|EConstr.mkRel (1 + i)|]
                              );
                              t;
                            |]
                          )
                        )
                      ) ((0, 0), [] |> to_vector_constr env (get_ref env "core.bool.type")) |> snd;
                      List.init padding_size (fun _ -> to_bool_constr env false)
                        |> to_vector_constr env (get_ref env "core.bool.type");
                    |]
                  );
                |]
              )
            )
          ) |> Array.of_list
        )
      | _ -> CErrors.user_err Pp.(str "Unknown type:" ++ spc () ++ Printer.pr_econstr_env env sigma typ) in
    EConstr.mkLambda (Context.anonR, typ, body)

let red_flags (env : Environ.env) (excluded : Names.Constant.t option) : CClosure.RedFlags.reds =
  let builtin = ["core.bool.negb"; "core.bool.andb"; "core.bool.orb"; "core.bool.xorb"] in
  let builtin_constants = builtin |> List.map Coqlib.lib_ref |> List.map dest_const_ref in
  let compiled_constants =
    !compiled
    |> List.map fst
    |> List.map fst
    |> List.filter (fun constant ->
      match excluded with
      | None -> true
      | Some excluded -> not (Environ.QConstant.equal env constant excluded)
    ) in
  builtin_constants @ compiled_constants
  |> List.fold_left (fun red_flags constant ->
    CClosure.RedFlags.red_sub red_flags (CClosure.RedFlags.fCONST constant)
  ) CClosure.allnolet

exception Reduction_blocked of EConstr.t

let rec verify_reduction_not_blocked (env : Environ.env) (sigma : Evd.evar_map)
    (evars : EConstr.t list) (t : EConstr.t) : unit =
  match EConstr.kind sigma t with
  | App (f, args) when EConstr.isFix sigma f ->
    args |> Array.iter (verify_reduction_not_blocked env sigma evars)
  | Case (ci, _, _, _, _, scrutinee, _) ->
    if evars |> constr_list_mem sigma scrutinee &&
      Environ.QInd.equal env ci.ci_ind (Coqlib.lib_ref "vcpu.vector.type" |> dest_ind_ref)
    then raise (Reduction_blocked scrutinee)
    else verify_reduction_not_blocked env sigma evars scrutinee
  | _ -> ()

let prove_any (env : Environ.env) (prop : EConstr.t) : EConstr.t =
  EConstr.mkApp (get_ref env "vcpu.prop.prove_any", [|prop|])

let prove_vector_similar (env : Environ.env) (typ : EConstr.t)
    (length : int) (v1 : EConstr.t) (v2 : EConstr.t) : EConstr.t =
  prove_any env (
    EConstr.mkApp (
      get_ref env "vcpu.vector.similar",
      [|
        typ;
        to_binnat_constr env length;
        to_binnat_constr env length;
        v1;
        v2;
      |]
    )
  )

let rec compile (env : Environ.env) (sigma : Evd.evar_map) (evars : EConstr.t list) (source : EConstr.t)
    : (EConstr.t * int list) list * circuit =
  Feedback.msg_info Pp.(str "compile" ++ spc () ++ Printer.pr_econstr_env env sigma source);

  let source_type = Retyping.get_type_of env sigma source in
  Feedback.msg_info Pp.(str "source_type" ++ spc () ++ Printer.pr_econstr_env env sigma source_type);
  let source_size = size_of_type env sigma source_type in
  let serialized_source = EConstr.mkApp(serialize env sigma source_type, [|source|]) in
  Feedback.msg_info Pp.(str "serialized_source" ++ spc () ++ Printer.pr_econstr_env env sigma serialized_source);

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
  let (input_count, input_mapping, serialized_evars) =
    evars |> List.fold_left (fun (input_count, input_mapping, serialized_evars) evar ->
      let evar_type = Retyping.get_type_of env sigma evar in
      let evar_size = size_of_type env sigma evar_type in
      (
        input_count + evar_size,
        (evar, List.init evar_size (fun i -> input_count + i)) :: input_mapping,
        EConstr.mkApp (
          get_ref env "vcpu.vector.app",
          [|
            get_ref env "core.bool.type";
            to_binnat_constr env input_count;
            to_binnat_constr env evar_size;
            serialized_evars;
            EConstr.mkApp (serialize env sigma evar_type, [|evar|]);
          |]
        )
      )
    ) (0, [], [] |> to_vector_constr env (get_ref env "core.bool.type")) in
  Feedback.msg_info Pp.(str "serialized_evars" ++ spc () ++ Printer.pr_econstr_env env sigma serialized_evars);

  let input_evar_mapping =
    input_mapping
    |> List.map (fun (evar, evar_inputs_wires) ->
      (evar, evar_inputs_wires |> List.map (fun i -> Reference_input i))
    ) in

  let circuit_add_applied c_source c_child input_references child_inputs child_outputs =
    let (c_source', child_output_wires) = circuit_add env c_source c_child input_references in
    (
      c_source' |> circuit_let env (fun c_source' ->
        let source_intermediates =
          EConstr.mkApp (
            get_ref env "vcpu.circuit_with_wf.compute_wires_vec",
            [|
              EConstr.mkApp (
                get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
                [|c_source.circuit_with_wf_and_spec_constr|]
              );
              serialized_evars;
            |]
          ) in
        let res_intermediates =
          EConstr.mkApp (
            get_ref env "vcpu.circuit_with_wf.compute_wires_vec",
            [|
              EConstr.mkApp (
                get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
                [|(c_source' 1).circuit_with_wf_and_spec_constr|]
              );
              serialized_evars;
            |]
          ) in
        let res_spec_1_typ =
          EConstr.mkApp (
            get_ref env "vcpu.vector.similar",
            [|
              get_ref env "core.bool.type";
              to_binnat_constr env c_source.circuit_wire_count;
              to_binnat_constr env c_source.circuit_wire_count;
              EConstr.mkApp (
                get_ref env "vcpu.vector.select_bin",
                [|
                  get_ref env "core.bool.type";
                  to_binnat_constr env (c_source.circuit_wire_count + c_child.circuit_wire_count);
                  to_binnat_constr env c_source.circuit_wire_count;
                  res_intermediates;
                  List.init c_source.circuit_wire_count (fun i -> to_binnat_constr env i)
                    |> to_vector_constr env (get_ref env "num.N.type");
                  get_ref env "core.bool.false";
                |]
              );
              source_intermediates;
            |]
          ) in
        let res_spec_2_typ =
          EConstr.mkApp (
            get_ref env "vcpu.vector.similar",
            [|
              get_ref env "core.bool.type";
              to_binnat_constr env (c_child.circuit_output_wires |> List.length);
              to_binnat_constr env (c_child.circuit_output_wires |> List.length);
              EConstr.mkApp (
                get_ref env "vcpu.vector.select_bin",
                [|
                  get_ref env "core.bool.type";
                  to_binnat_constr env c_child.circuit_wire_count;
                  to_binnat_constr env (c_child.circuit_output_wires |> List.length);
                  EConstr.mkApp (
                    get_ref env "vcpu.vector.select_bin",
                    [|
                      get_ref env "core.bool.type";
                      to_binnat_constr env (c_source.circuit_wire_count + c_child.circuit_wire_count);
                      to_binnat_constr env c_child.circuit_wire_count;
                      res_intermediates;
                      List.init c_child.circuit_wire_count (fun i ->
                        to_binnat_constr env (c_source.circuit_wire_count + i)
                      ) |> to_vector_constr env (get_ref env "num.N.type");
                      get_ref env "core.bool.false";
                    |]
                  );
                  c_child.circuit_output_wires
                    |> List.map (to_binnat_constr env)
                    |> to_vector_constr env (get_ref env "num.N.type");
                  get_ref env "core.bool.false";
                |]
              );
              child_outputs;
            |]
          ) in
        {
          (c_source' 0) with
          circuit_with_wf_and_spec_constr =
            EConstr.mkApp (
              get_ref env "vcpu.circuit_with_wf_and_spec.constructor",
              [|
                EConstr.mkApp (
                  get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
                  [|(c_source' 1).circuit_with_wf_and_spec_constr|]
                );
                EConstr.mkApp (get_ref env "core.and.type", [|res_spec_1_typ; res_spec_2_typ|]);
                EConstr.mkLetIn (
                  Context.anonR,
                  EConstr.mkApp (
                    get_ref env "vcpu.circuit_with_wf_and_spec.spec",
                    [|
                      (c_source' 1).circuit_with_wf_and_spec_constr;
                      serialized_evars;
                      child_inputs;
                      child_outputs;
                      prove_vector_similar
                        env
                        (get_ref env "core.bool.type")
                        c_child.circuit_input_count
                        child_inputs
                        (
                          input_references |> List.map (fun r ->
                            EConstr.mkApp (
                              get_ref env "vcpu.reference.compute",
                              [|
                                EConstr.mkApp (
                                  get_ref env "vcpu.vector.list",
                                  [|
                                    get_ref env "core.bool.type";
                                    to_binnat_constr env source_size;
                                    serialized_evars;
                                  |]
                                );
                                EConstr.mkApp (
                                  get_ref env "vcpu.vector.list",
                                  [|
                                    get_ref env "core.bool.type";
                                    to_binnat_constr env c_source.circuit_wire_count;
                                    source_intermediates;
                                  |]
                                );
                                to_reference_constr env r;
                              |]
                            )
                          ) |> to_vector_constr env (get_ref env "core.bool.type")
                        );
                      prove_vector_similar
                        env
                        (get_ref env "core.bool.type")
                        c_child.circuit_wire_count
                        child_outputs
                        (
                          EConstr.mkApp (
                            get_ref env "vcpu.circuit_with_wf.compute_vec",
                            [|
                              EConstr.mkApp (
                                get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
                                [|c_child.circuit_with_wf_and_spec_constr|]
                              );
                              child_inputs;
                            |]
                          )
                        );
                    |]
                  ),
                  EConstr.mkApp (get_ref env "core.and.type", [|res_spec_1_typ; res_spec_2_typ|]),
                  assert false
                );
              |]
            )
        }
      ),
      child_output_wires
    ) in

  let convert_child sigma c_source child child_evar_mapping =
    let (child_input_mapping, c_child) =
      compile env sigma (child_evar_mapping |> List.map fst) child in
    let child_input_references = List.init c_child.circuit_input_count (fun i ->
      let (evar, child_input_wires) =
        child_input_mapping |> List.find (fun (_, child_input_wires) -> child_input_wires |> List.mem i) in
      List.nth (child_evar_mapping |> constr_list_assoc sigma evar) (child_input_wires |> list_index_of i)
    ) in
    let (c_source', child_output_wires) = circuit_add env c_source c_child child_input_references in
    (c_source', child_output_wires) in

  let source_spec_statement c_source =
    EConstr.mkApp (
      get_ref env "vcpu.vector.similar",
      [|
        get_ref env "core.bool.type";
        to_binnat_constr env source_size;
        to_binnat_constr env source_size;
        EConstr.mkApp (
          get_ref env "vcpu.circuit_with_wf.compute_vec",
          [|
            EConstr.mkApp (
              get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
              [|c_source.circuit_with_wf_and_spec_constr|]
            );
            serialized_evars;
          |]
        );
        serialized_source;
      |]
    ) in

  let c_source = circuit_empty env input_count in

  let (sigma, c_source') = try
    verify_reduction_not_blocked env sigma evars source;
    match EConstr.kind sigma source with

    (* Evar *)
    | _ when evars |> constr_list_mem sigma source ->
      let evar_input_references = input_evar_mapping |> constr_list_assoc sigma source in
      let c_evar = circuit_id env (List.length evar_input_references) in
      let (c_source', evar_output_wires) = circuit_add env c_source c_evar evar_input_references in
      let c_source'' = circuit_set_output_wires env c_source' evar_output_wires in
      (sigma, c_source'')

    (* Not *)
    | App (f, [|arg|]) when EConstr.eq_constr sigma f (get_ref env "core.bool.negb") ->
      let (c_source', arg_output_wires) = convert_child sigma c_source arg input_evar_mapping in
      let (c_source'', not_output_wires) =
        circuit_add env c_source' (circuit_not env) (arg_output_wires |> List.map (fun i -> Reference_wire i)) in
      let c_source''' = circuit_set_output_wires env c_source'' not_output_wires in
      (sigma, c_source''')

    (* And *)
    | App (f, [|arg_1; arg_2|]) when EConstr.eq_constr sigma f (get_ref env "core.bool.andb") ->
      let (c_source', arg_1_output_wires) = convert_child sigma c_source arg_1 input_evar_mapping in
      let (c_source'', arg_2_output_wires) = convert_child sigma c_source' arg_2 input_evar_mapping in
      let (c_source''', and_output_wires) =
        circuit_add env c_source'' (circuit_and env) ((arg_1_output_wires @ arg_2_output_wires) |> List.map (fun i -> Reference_wire i)) in
      let c_source'''' = circuit_set_output_wires env c_source''' and_output_wires in
      (sigma, c_source'''')

    (* Or *)
    | App (f, [|arg_1; arg_2|]) when EConstr.eq_constr sigma f (get_ref env "core.bool.orb") ->
      let (c_source', arg_1_output_wires) = convert_child sigma c_source arg_1 input_evar_mapping in
      let (c_source'', arg_2_output_wires) = convert_child sigma c_source' arg_2 input_evar_mapping in
      let (c_source''', or_output_wires) =
        circuit_add env c_source'' (circuit_or env) ((arg_1_output_wires @ arg_2_output_wires) |> List.map (fun i -> Reference_wire i)) in
      let c_source'''' = circuit_set_output_wires env c_source''' or_output_wires in
      (sigma, c_source'''')

    (* Xor *)
    | App (f, [|arg_1; arg_2|]) when EConstr.eq_constr sigma f (get_ref env "core.bool.xorb") ->
      let (c_source', arg_1_output_wires) = convert_child sigma c_source arg_1 input_evar_mapping in
      let (c_source'', arg_2_output_wires) = convert_child sigma c_source' arg_2 input_evar_mapping in
      let (c_source''', xor_output_wires) =
        circuit_add env c_source'' (circuit_xor env) ((arg_1_output_wires @ arg_2_output_wires) |> List.map (fun i -> Reference_wire i)) in
      let c_source'''' = circuit_set_output_wires env c_source''' xor_output_wires in
      (sigma, c_source'''')

    (* Pre-compiled *)
    | App (func, params_args) when
        !compiled |> List.map fst |> List.map fst |> List.map EConstr.mkConst |> constr_list_mem sigma func ->
      let ((_, params), c_func) =
        !compiled
        |> List.find (fun ((input_constant, params), _) ->
          let params' = Array.sub params_args 0 (params |> List.length) |> Array.to_list in
          EConstr.eq_constr sigma func (EConstr.mkConst input_constant) &&
            List.for_all2 (EConstr.eq_constr sigma) params params'
        ) in
      let args = params_args |> Array.to_seq |> Seq.drop (List.length params) in
      let (c_source', args_output_wires) =
        args |> Seq.fold_left (fun (c_source', args_output_wires) arg ->
          let (c_source'', arg_output_wires) = convert_child sigma c_source' arg input_evar_mapping in
          (c_source'', args_output_wires @ arg_output_wires)
        ) (c_source, []) in
      let (c_source'', func_output_wires) =
        circuit_add env c_source' c_func (args_output_wires |> List.map (fun i -> Reference_wire i)) in
      let c_source''' = circuit_set_output_wires env c_source'' func_output_wires in
      (sigma, c_source''')

    (* Let in *)
    | LetIn (_, value, value_type, context) ->
      let (c_source', value_output_wires) = convert_child sigma c_source value input_evar_mapping in
      let (sigma, value_evar) = Evarutil.new_evar env sigma value_type in
      let (c_source'', context_output_wires) =
        convert_child sigma c_source' (context |> EConstr.Vars.subst1 value_evar)
        ((value_evar, value_output_wires |> List.map (fun i -> Reference_wire i)) :: input_evar_mapping) in
      let c_source''' = circuit_set_output_wires env c_source'' context_output_wires in
      (sigma, c_source''')

    (* Match bool *)
    | Case (ci, _, _, (_, brs_type), _, scrutinee, brs) when
        Environ.QInd.equal env ci.ci_ind (Coqlib.lib_ref "core.bool.type" |> dest_ind_ref) ->
      let (c_source', scutinee_output_wires) = convert_child sigma c_source scrutinee input_evar_mapping in
      let (c_source'', br_false_output_wires) = convert_child sigma c_source' (brs.(1) |> snd) input_evar_mapping in
      let (c_source''', br_true_output_wires) = convert_child sigma c_source'' (brs.(0) |> snd) input_evar_mapping in
      let c_switch = circuit_switch env (size_of_type env sigma brs_type) in
      let (c_source'''', switch_output_wires) = circuit_add env c_source''' c_switch
        (scutinee_output_wires @ br_false_output_wires @ br_true_output_wires |> List.map (fun i -> Reference_wire i)) in
      let c_source''''' = circuit_set_output_wires env c_source'''' switch_output_wires in
      (sigma, c_source''''')

    (* Match inductive *)
    | Case (ci, _, params, (_, brs_type), _, scrutinee, brs) ->
      let constructor_arg_types = constructor_arg_types_of_inductive env sigma ci.ci_ind (params |> Array.to_list) in
      let constructor_count = constructor_arg_types |> List.length in
      let (c_source', scutinee_output_wires) = convert_child sigma c_source scrutinee input_evar_mapping in
      let (sigma, c_source'', brs_output_wires) =
        List.fold_left2
        (fun (sigma, c_source', brs_output_wires) arg_types br ->
          let (sigma, _, arg_evars, br_evar_mapping) =
            arg_types |> List.fold_left (fun (sigma, offset, arg_evars, br_evar_mapping) arg_typ ->
              let (sigma, arg_evar) = Evarutil.new_evar env sigma arg_typ in
              let arg_size = arg_typ |> size_of_type env sigma in
              (
                sigma,
                offset + arg_size,
                arg_evars @ [arg_evar],
                br_evar_mapping @ [(
                  arg_evar,
                  list_select
                    (scutinee_output_wires |> List.map (fun i -> Reference_wire i))
                    (List.init arg_size (fun i -> offset + i))
                )]
              )
            ) (sigma, constructor_count, [], input_evar_mapping) in
          let (c_source'', br_output_wires) =
            convert_child sigma c_source'
            (br |> EConstr.Vars.substl (arg_evars |> List.rev))
            br_evar_mapping in
          (sigma, c_source'', brs_output_wires @ [br_output_wires])
        )
        (sigma, c_source', [])
        constructor_arg_types
        (brs |> Array.to_list |> List.map snd) in
      let (c_source''', switches_output_wires) =
        List.fold_left2
        (fun (c_source', switches_output_wires) counstructor_index br_output_wires ->
          let c_switch = circuit_switch env (size_of_type env sigma brs_type) in
          let (c_source'', switch_output_wires) =
            circuit_add env c_source' c_switch
            (List.nth scutinee_output_wires counstructor_index :: br_output_wires @ switches_output_wires
              |> List.map (fun i -> Reference_wire i)) in
          (c_source'', switch_output_wires)
        )
        (c_source'', brs_output_wires |> List.hd)
        (List.init (constructor_count - 1) (fun i -> i + 1))
        (brs_output_wires |> List.tl) in
      let c_source'''' = circuit_set_output_wires env c_source''' switches_output_wires in
      (sigma, c_source'''')

    (* false and true *)
    | _ when EConstr.eq_constr sigma source (get_ref env "core.bool.false") ->
      let c_zero = circuit_zero env in
      let (c_source, one_output_wires) = circuit_add env c_source c_zero [] in
      let c_source = circuit_set_output_wires env c_source one_output_wires in
      let c_source = c_source |> circuit_let env (fun c_source ->
        {
          (c_source 0) with
          circuit_with_wf_and_spec_constr =
            EConstr.mkApp (
              get_ref env "vcpu.circuit_with_wf_and_spec.constructor",
              [|
                EConstr.mkApp (
                  get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
                  [|(c_source 1).circuit_with_wf_and_spec_constr|]
                );
                source_spec_statement (c_source 1);
                EConstr.mkApp (
                  get_ref env "vcpu.circuit_with_wf_and_spec.spec",
                  [|
                    (c_source 1).circuit_with_wf_and_spec_constr;
                    serialized_evars;
                    [to_bool_constr env false] |> to_vector_constr env (get_ref env "core.bool.type");
                    prove_vector_similar
                      env
                      (get_ref env "core.bool.type")
                      1
                      ([to_bool_constr env false] |> to_vector_constr env (get_ref env "core.bool.type"))
                      ([to_bool_constr env false] |> to_vector_constr env (get_ref env "core.bool.type"));
                  |]
                );
              |]
            )
        }
      ) in
      (sigma, c_source)
    | _ when EConstr.eq_constr sigma source (get_ref env "core.bool.true") ->
      let c_one = circuit_one env in
      let (c_source, one_output_wires) = circuit_add_applied c_source c_one []
        ([] |> to_vector_constr env (get_ref env "core.bool.type"))
        ([to_bool_constr env true] |> to_vector_constr env (get_ref env "core.bool.type")) in
      let c_source = circuit_set_output_wires env c_source one_output_wires in
      (sigma, c_source)

    (* Vector *)
    | App (f, [|_; _; a3; _|]) when EConstr.eq_constr sigma f (get_ref env "vcpu.vector.constructor") ->
      verify_reduction_not_blocked env sigma evars a3;
      let l = of_list_constr env sigma a3 in
      let (c_source', elements_output_wires) = l |> List.fold_left (fun (c_source', children_output_wires) element ->
        let (c_source'', element_output_wires) = convert_child sigma c_source' element input_evar_mapping in
        (c_source'', children_output_wires @ element_output_wires)
      ) (c_source, []) in
      let c_source'' = circuit_set_output_wires env c_source' elements_output_wires in
      (sigma, c_source'')

    (* Indcutive *)
    | _ when source |> EConstr.decompose_app sigma |> fst |> EConstr.isConstruct sigma -> (
      let (f, params_args) = EConstr.decompose_app sigma source in
      match EConstr.kind sigma f with
      | Construct ((ind, contructor_index_succ), _) ->
        let contructor_index = pred contructor_index_succ in
        let (_, one_inductive_body) = Inductive.lookup_mind_specif env ind in
        let params_count = one_inductive_body.mind_arity_ctxt |> List.length in
        let constructor_count = one_inductive_body.mind_user_lc |> Array.length in
        let params = params_args |> List.to_seq |> Seq.take params_count in
        let args = params_args |> List.to_seq |> Seq.drop params_count in
        let constructor_arg_types = constructor_arg_types_of_inductive env sigma ind (params |> List.of_seq) in
        let arg_types = List.nth constructor_arg_types contructor_index in
        let args_size =
          arg_types
          |> List.map (size_of_type env sigma)
          |> List.fold_left (+) 0 in
        let max_args_size =
          constructor_arg_types
          |> List.map (fun arg_types ->
            arg_types
            |> List.map (size_of_type env sigma)
            |> List.fold_left (+) 0
          )
          |> List.fold_left max 0 in
        let padding_size = max_args_size - args_size in
        let c_constructor_index = circuit_const env (List.init constructor_count (fun i -> i = contructor_index)) in
        let (c_source', contructor_index_output_wires) = circuit_add env c_source c_constructor_index [] in
        let (c_source'', args_output_wires) = args |> Seq.fold_left (fun (c_source', args_output_wires) arg ->
          let (c_source'', arg_output_wires) = convert_child sigma c_source' arg input_evar_mapping in
          (c_source'', args_output_wires @ arg_output_wires)
        ) (c_source', []) in
        let c_padding = circuit_const env (List.init padding_size (fun _ -> false)) in
        let (c_source''', padding_output_wires) = circuit_add env c_source'' c_padding [] in
        let c_source'''' =
          circuit_set_output_wires env c_source'' (contructor_index_output_wires @ args_output_wires @ padding_output_wires) in
        (sigma, c_source'''')
      | _ -> assert false
    )

    | _ -> CErrors.user_err Pp.(str "Unknown term:" ++ spc () ++ Printer.pr_econstr_env env sigma source)
  with

  (* Reduction was blocked, replace a vector variable by sample contents and try again *)
  | Reduction_blocked reduction_blocking_evar ->
    let (element_typ, length) = dest_vector_type env sigma (Retyping.get_type_of env sigma reduction_blocking_evar) in
    let element_typ_size = size_of_type env sigma element_typ in
    let (sigma, vector_evars) = new_evars env sigma element_typ length in
    let vector_evar_mapping =
      vector_evars |> List.mapi (fun i vector_evar ->
        (
          vector_evar,
          list_select
            (input_evar_mapping |> constr_list_assoc sigma reduction_blocking_evar)
            (List.init element_typ_size (fun j -> element_typ_size * i + j))
        )
      ) in
    let substituted =
      Termops.replace_term sigma reduction_blocking_evar (to_vector_constr env element_typ vector_evars) source in
    let reduced_substituted = Cbv.cbv_norm (Cbv.create_cbv_infos (red_flags env None) env sigma) substituted in
    let (c_source', substituted_output_wires) =
      convert_child sigma c_source reduced_substituted
      (input_evar_mapping @ vector_evar_mapping) in
    let c_source'' = circuit_set_output_wires env c_source' substituted_output_wires in
    (sigma, c_source'') in

  (* Feedback.msg_info Pp.(str "return" ++ spc () ++
    Printer.pr_econstr_env env sigma c_source'.circuit_with_wf_and_spec_constr); *)
  (input_mapping, c_source')

let entry_test () : unit =
  ref_cache := CString.Map.empty;
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let circuit_with_wf_and_spec_constant =
    Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(
        Declare.CInfo.make
        ~name:("test" |> Names.Id.of_string)
        ~typ:(Some (get_ref env "vcpu.circuit_with_wf_and_spec.type"))
        ()
      )
      ~opaque:false
      ~body:(circuit_const env [true; false]).circuit_with_wf_and_spec_constr
      sigma
    |> dest_const_ref in
  ()

let entry_serialize (input_typ_constr_expr : Constrexpr.constr_expr) (output_id : Names.Id.t) : unit =
  ref_cache := CString.Map.empty;
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, input_typ) = Constrintern.interp_type_evars env sigma input_typ_constr_expr in
  let input_typ_size = size_of_type env sigma input_typ in
  let serialize_constant =
    Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(
        Declare.CInfo.make
        ~name:output_id
        ~typ:(Some (
          EConstr.mkArrowR
            input_typ
            (mk_vector_type env (get_ref env "core.bool.type") input_typ_size)
        ))
        ()
      )
      ~opaque:false
      ~body:(serialize env sigma input_typ)
      sigma
    |> dest_const_ref in
  serialized := !serialized @ [(input_typ, serialize_constant)]

let entry_compile (input_id : Names.Id.t) (param_constr_exprs : Constrexpr.constr_expr list)
    (output_id : Names.Id.t option) : unit =
  ref_cache := CString.Map.empty;
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, params) = param_constr_exprs |> List.fold_left (fun (sigma, params) param_constr_expr ->
    let (sigma, param) = Constrintern.interp_constr_evars env sigma param_constr_expr in
    (sigma, param :: params)
  ) (sigma, []) in
  let input_constant =
    Names.Constant.make1 (Names.KerName.make (Global.current_modpath ()) (Names.Label.of_id input_id)) in
  if not (Environ.mem_constant input_constant env) then
    CErrors.user_err Pp.(str "Constant " ++ Names.Constant.print input_constant ++ str " does not exist.");
  let applied_input = EConstr.mkApp (EConstr.mkConst input_constant, params |> Array.of_list) in
  let (sigma, input_type) = Typing.type_of env sigma applied_input in
  (match output_id with
  | Some output_id ->
    Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(Declare.CInfo.make ~name:output_id ~typ:(Some input_type) ())
      ~opaque:false ~body:applied_input sigma
    |> ignore
  | None -> ());
  let reduced_input =
    Cbv.cbv_norm (Cbv.create_cbv_infos (red_flags env (Some input_constant)) env sigma) applied_input in
  let (args, source) = reduced_input |> EConstr.decompose_lambda sigma in
  let arg_types = args |> List.map snd in
  let (sigma, args_size, arg_evars, source_evar_mapping) =
    arg_types |> List.fold_left (fun (sigma, offset, arg_evars, source_evar_mapping) arg_typ ->
      let (sigma, arg_evar) = Evarutil.new_evar env sigma arg_typ in
      let arg_size = arg_typ |> size_of_type env sigma in
      (
        sigma,
        offset + arg_size,
        arg_evars @ [arg_evar],
        source_evar_mapping @ [(
          arg_evar,
          List.init arg_size (fun i -> offset + i) |> List.map (fun i -> Reference_input i)
        )]
      )
    ) (sigma, 0, [], []) in
  Feedback.msg_info (Pp.str "Start");
  let (source_input_mapping, c_source) =
    compile env sigma arg_evars (source |> EConstr.Vars.substl (arg_evars |> List.rev)) in
  let c_result = circuit_empty env args_size in
  let source_input_references = List.init c_source.circuit_input_count (fun i ->
    let (evar, source_input_wires) =
      source_input_mapping |> List.find (fun (_, source_input_wires) -> source_input_wires |> List.mem i) in
    List.nth (source_evar_mapping |> constr_list_assoc sigma evar) (source_input_wires |> list_index_of i)
  ) in
  let (c_result', source_output_wires) = circuit_add env c_result c_source source_input_references in
  let c_result'' = circuit_set_output_wires env c_result' source_output_wires in
  Feedback.msg_info Pp.(str "Wire count:" ++ spc () ++ int (c_result''.circuit_wires |> List.length));
  let name_prefix = (output_id |> Option.default input_id) |> Names.Id.to_string in
  let circuit_with_wf_and_spec_constant =
    Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(
        Declare.CInfo.make
        ~name:(name_prefix ^ "_circuit_with_wf_and_spec" |> Names.Id.of_string)
        ~typ:(Some (get_ref env "vcpu.circuit_with_wf_and_spec.type"))
        ()
      )
      ~opaque:false
      ~body:((* c_result'' *) c_source.circuit_with_wf_and_spec_constr)
      sigma
    |> dest_const_ref in
  let circuit_with_wf_constant =
    Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(
        Declare.CInfo.make
        ~name:(name_prefix ^ "_circuit_with_wf" |> Names.Id.of_string)
        ~typ:(Some (get_ref env "vcpu.circuit_with_wf.type"))
        ()
      )
      ~opaque:false
      ~body:(
        EConstr.mkApp (
          get_ref env "vcpu.circuit_with_wf_and_spec.circuit_with_wf",
          [|EConstr.mkConst circuit_with_wf_and_spec_constant|]
        )
      )
      sigma
    |> dest_const_ref in
  let circuit_constant =
    Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(
        Declare.CInfo.make
        ~name:(name_prefix ^ "_circuit" |> Names.Id.of_string)
        ~typ:(Some (get_ref env "vcpu.circuit.type"))
        ()
      )
      ~opaque:false
      ~body:(
        EConstr.mkApp (
          get_ref env "vcpu.circuit_with_wf.circuit",
          [|EConstr.mkConst circuit_with_wf_constant|]
        )
      )
      sigma
    |> dest_const_ref in
  let circuit_wf_constant =
    Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(
        Declare.CInfo.make
        ~name:(name_prefix ^ "_circuit_wf" |> Names.Id.of_string)
        ~typ:(Some (EConstr.mkApp (get_ref env "vcpu.circuit.wf", [|EConstr.mkConst circuit_constant|])))
        ()
      )
      ~opaque:false
      ~body:(
        EConstr.mkApp (
          get_ref env "vcpu.circuit_with_wf.circuit_wf",
          [|EConstr.mkConst circuit_with_wf_constant|]
        )
      )
      sigma
    |> dest_const_ref in
  let circuit_spec_statement_constant =
    Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(
        Declare.CInfo.make
        ~name:(name_prefix ^ "_circuit_spec_statement" |> Names.Id.of_string)
        ~typ:(Some EConstr.mkProp)
        ()
      )
      ~opaque:false
      ~body:(
        EConstr.mkApp (
          get_ref env "vcpu.circuit_with_wf_and_spec.spec_statement",
          [|EConstr.mkConst circuit_with_wf_and_spec_constant|]
        )
      )
      sigma
    |> dest_const_ref in
  let circuit_spec_constant =
    Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(
        Declare.CInfo.make
        ~name:(name_prefix ^ "_circuit_spec" |> Names.Id.of_string)
        ~typ:(Some (EConstr.mkConst circuit_spec_statement_constant))
        ()
      )
      ~opaque:false
      ~body:(
        EConstr.mkApp (
          get_ref env "vcpu.circuit_with_wf_and_spec.spec",
          [|EConstr.mkConst circuit_with_wf_and_spec_constant|]
        )
      )
      sigma
    |> dest_const_ref in
  let c_output = {
    c_result'' with
    circuit_with_wf_and_spec_constr =
      EConstr.mkApp (
        get_ref env "vcpu.circuit_with_wf_and_spec.constructor",
        [|
          EConstr.mkApp (
            get_ref env "vcpu.circuit_with_wf.constructor",
            [|
              EConstr.mkConst circuit_constant;
              EConstr.mkConst circuit_wf_constant;
            |]
          );
          EConstr.mkConst circuit_spec_statement_constant;
          EConstr.mkConst circuit_spec_constant;
        |]
      )
  } in
  compiled := !compiled @ [((input_constant, params), c_output)]
