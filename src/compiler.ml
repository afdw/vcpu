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

let rec to_nat_constr (env : Environ.env) (n : int) : EConstr.t =
  assert (n >= 0);
  if n < 32 then
    if n = 0
    then get_ref env "num.nat.O"
    else EConstr.mkApp (get_ref env "num.nat.S", [|to_nat_constr env (pred n)|])
  else
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

let rec of_nat_constr (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.t) : int =
  match EConstr.kind sigma t with
  | _ when EConstr.eq_constr sigma t (get_ref env "num.nat.O") -> 0
  | App (f, [|t'|]) when EConstr.eq_constr sigma f (get_ref env "num.nat.S") -> succ (of_nat_constr env sigma t')
  | _ -> CErrors.user_err Pp.(str "Not an application of O or S:" ++ spc () ++ Printer.pr_econstr_env env sigma t)

let prove_nat_eq (env : Environ.env) (n : int) : EConstr.t =
  EConstr.mkApp (get_ref env "core.eq.refl", [|get_ref env "num.nat.type"; to_nat_constr env n|])

let rec prove_nat_le (env : Environ.env) (n : int) (m : int) : EConstr.t =
  assert (n <= m);
  if n < 8 && m < 8 then
    if n = m then
      EConstr.mkApp (
        get_ref env "num.nat.le_n",
        [|to_nat_constr env n|]
      )
    else
      EConstr.mkApp (
        get_ref env "num.nat.le_S",
        [|to_nat_constr env n; to_nat_constr env (pred m); prove_nat_le env n (pred m)|]
      )
  else
    EConstr.mkApp (
      get_ref env "vcpu.prove_le",
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

let dest_vector_type (env : Environ.env) (sigma : Evd.evar_map) (typ : EConstr.t) : EConstr.t * int =
  match EConstr.kind sigma typ with
  | App (f, [|a1; a2|]) when EConstr.eq_constr sigma f (get_ref env "vcpu.vector.type") ->
    (a1, a2 |> Cbv.cbv_norm (Cbv.create_cbv_infos CClosure.all env sigma) |> of_nat_constr env sigma)
  | _ -> CErrors.user_err Pp.(str "Not an application of vector:" ++ spc () ++ Printer.pr_econstr_env env sigma typ)

let to_vector (env : Environ.env) (typ : EConstr.t) (l : EConstr.t list) : EConstr.t =
  EConstr.mkApp (
    get_ref env "vcpu.vector.constructor",
    [|
      typ;
      to_nat_constr env (l |> List.length);
      to_list_constr env typ l;
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
    EConstr.mkApp (get_ref env "vcpu.reference.Input", [|i |> to_nat_constr env|])
  | Reference_wire i ->
    EConstr.mkApp (get_ref env "vcpu.reference.Wire", [|i |> to_nat_constr env|])

type binding =
  | Binding_immidiate of reference
  | Binding_not of reference
  | Binding_and of reference * reference
  | Binding_or of reference * reference
  | Binding_xor of reference * reference
  | Binding_if of reference * reference * reference

let to_binding_constr (env : Environ.env) (b : binding) : EConstr.t =
  match b with
  | Binding_immidiate r ->
    EConstr.mkApp (get_ref env "vcpu.binding.Immidiate", [|r |> to_reference_constr env|])
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
  circuit_wires : binding list;
  circuit_outputs : int list;
  circuit_constr : Environ.env -> Evd.evar_map -> EConstr.t;
  circuit_wf_constr : Environ.env -> Evd.evar_map -> EConstr.t;
}

let reference_wf (input_count : int) (wire_count : int) (r : reference) : bool =
  match r with
  | Reference_zero -> true
  | Reference_one -> true
  | Reference_input i -> i < input_count
  | Reference_wire i -> i < wire_count

let binding_wf (input_count : int) (wire_count : int) (b : binding) : bool =
  match b with
  | Binding_immidiate r -> reference_wf input_count wire_count r
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

let circuit_wires_wf (c : circuit) : bool =
  List.for_all2 (binding_wf c.circuit_input_count) (List.init (List.length c.circuit_wires) (fun i -> i)) c.circuit_wires

let circuit_outputs_wf (c : circuit) : bool =
  c.circuit_outputs |> List.for_all (fun i -> i < List.length c.circuit_wires)

let circuit_wf (c : circuit) : bool =
  circuit_wires_wf c && circuit_outputs_wf c

let prove_reference_wf (env : Environ.env) (sigma : Evd.evar_map)
    (input_count : int) (wire_count : int) (r : reference) : EConstr.t =
  match r with
  | Reference_zero -> get_ref env "core.True.I"
  | Reference_one -> get_ref env "core.True.I"
  | Reference_input i -> prove_nat_lt env i input_count
  | Reference_wire i -> prove_nat_lt env i wire_count

let prove_binding_wf (env : Environ.env) (sigma : Evd.evar_map)
    (input_count : int) (wire_count : int) (b : binding) : EConstr.t =
  match b with
  | Binding_immidiate r ->
    prove_reference_wf env sigma input_count wire_count r
  | Binding_not r ->
    prove_reference_wf env sigma input_count wire_count r
  | Binding_and (r1, r2) ->
    mk_conj env sigma
      (prove_reference_wf env sigma input_count wire_count r1)
      (prove_reference_wf env sigma input_count wire_count r2)
  | Binding_or (r1, r2) ->
    mk_conj env sigma
      (prove_reference_wf env sigma input_count wire_count r1)
      (prove_reference_wf env sigma input_count wire_count r2)
  | Binding_xor (r1, r2) ->
    mk_conj env sigma
      (prove_reference_wf env sigma input_count wire_count r1)
      (prove_reference_wf env sigma input_count wire_count r2)
  | Binding_if (r1, r2, r3) ->
    mk_conj env sigma
      (prove_reference_wf env sigma input_count wire_count r1)
      (
        mk_conj env sigma
          (prove_reference_wf env sigma input_count wire_count r2)
          (prove_reference_wf env sigma input_count wire_count r3)
      )

let reference_compute (inputs : bool list) (intermediates : bool list) (r : reference) : bool =
  match r with
  | Reference_zero -> false
  | Reference_one -> true
  | Reference_input i -> List.nth inputs i
  | Reference_wire i -> List.nth intermediates i

let binding_compute (inputs : bool list) (intermediates : bool list) (b : binding) : bool =
  match b with
  | Binding_immidiate r -> reference_compute inputs intermediates r
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
  list_select (circuit_compute_wires c inputs) c.circuit_outputs

let circuit_set_outputs (c : circuit) (outputs : int list) : circuit =
  assert (outputs |> List.for_all (fun i -> i < List.length c.circuit_wires));
  {
    circuit_input_count = c.circuit_input_count;
    circuit_wires = c.circuit_wires;
    circuit_outputs = outputs;
    circuit_constr = (fun env sigma ->
      EConstr.mkApp (
        get_ref env "vcpu.circuit.set_outputs",
        [|
          c.circuit_constr env sigma;
          outputs |> List.map (to_nat_constr env) |> to_list_constr env (get_ref env "num.nat.type");
        |]
      )
    );
    circuit_wf_constr = (fun env sigma ->
      EConstr.mkApp (
        get_ref env "vcpu.circuit.set_outputs_wf",
        [|
          c.circuit_constr env sigma;
          outputs |> List.map (to_nat_constr env) |> to_list_constr env (get_ref env "num.nat.type");
          c.circuit_wf_constr env sigma;
          List.fold_right (fun i t ->
            mk_conj env sigma (prove_nat_lt env i (c.circuit_wires |> List.length)) t
          ) outputs (get_ref env "core.True.I");
        |]
      )
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
  | Binding_immidiate r -> Binding_immidiate (translate_reference r)
  | Binding_not r -> Binding_not (translate_reference r)
  | Binding_and (r1, r2) -> Binding_and (translate_reference r1, translate_reference r2)
  | Binding_or (r1, r2) -> Binding_or (translate_reference r1, translate_reference r2)
  | Binding_xor (r1, r2) -> Binding_xor (translate_reference r1, translate_reference r2)
  | Binding_if (r1, r2, r3) -> Binding_if (translate_reference r1, translate_reference r2, translate_reference r3)

let circuit_add (c_parent : circuit) (c_child : circuit) (input_references : reference list) : circuit * int list =
  assert (List.length input_references = c_child.circuit_input_count);
  assert (input_references |> List.for_all (reference_wf c_parent.circuit_input_count (List.length c_parent.circuit_wires)));
  (
    {
      circuit_input_count = c_parent.circuit_input_count;
      circuit_wires =
        c_parent.circuit_wires @
          (c_child.circuit_wires |> List.map
            (circuit_add_translate_binding (List.length c_parent.circuit_wires) input_references));
      circuit_outputs = c_parent.circuit_outputs;
      circuit_constr = (fun env sigma ->
        EConstr.mkApp (
          get_ref env "vcpu.circuit.add",
          [|
            c_parent.circuit_constr env sigma;
            c_child.circuit_constr env sigma;
            input_references
              |> List.map (to_reference_constr env)
              |> to_list_constr env (get_ref env "vcpu.reference.type");
          |]
        )
      );
      circuit_wf_constr = (fun env sigma ->
        EConstr.mkApp (
          get_ref env "vcpu.circuit.add_wf",
          [|
            c_parent.circuit_constr env sigma;
            c_child.circuit_constr env sigma;
            input_references
              |> List.map (to_reference_constr env)
              |> to_list_constr env (get_ref env "vcpu.reference.type");
            c_parent.circuit_wf_constr env sigma;
            c_child.circuit_wf_constr env sigma;
            prove_nat_eq env (input_references |> List.length);
            List.fold_right (fun r t ->
              mk_conj env sigma
                (prove_reference_wf env sigma c_parent.circuit_input_count (List.length c_parent.circuit_wires) r)
                t
            ) input_references (get_ref env "core.True.I");
          |]
        )
      );
    },
    c_child.circuit_outputs |> List.map (fun i -> List.length c_parent.circuit_wires + i)
  )

let circuit_empty (input_count : int) : circuit =
  {
    circuit_input_count = input_count;
    circuit_wires = [];
    circuit_outputs = [];
    circuit_constr = (fun env sigma ->
      EConstr.mkApp (get_ref env "vcpu.circuit.empty", [|to_nat_constr env input_count|])
    );
    circuit_wf_constr = (fun env sigma ->
      EConstr.mkApp (get_ref env "vcpu.circuit.empty_wf", [|to_nat_constr env input_count|])
    );
  }

let circuit_id (input_count : int) : circuit =
  {
    circuit_input_count = input_count;
    circuit_wires = List.init input_count (fun i -> Binding_immidiate (Reference_input i));
    circuit_outputs = List.init input_count (fun i -> i);
    circuit_constr = (fun env sigma ->
      EConstr.mkApp (get_ref env "vcpu.circuit.id", [|to_nat_constr env input_count|])
    );
    circuit_wf_constr = (fun env sigma ->
      EConstr.mkApp (get_ref env "vcpu.circuit.id_wf", [|to_nat_constr env input_count|])
    );
  }

let circuit_zero : circuit =
  {
    circuit_input_count = 0;
    circuit_wires = [Binding_immidiate Reference_zero];
    circuit_outputs = [0];
    circuit_constr = (fun env sigma -> get_ref env "vcpu.circuit.zero");
    circuit_wf_constr = (fun env sigma -> get_ref env "vcpu.circuit.zero_wf");
  }

let circuit_one : circuit =
  {
    circuit_input_count = 0;
    circuit_wires = [Binding_immidiate Reference_one];
    circuit_outputs = [0];
    circuit_constr = (fun env sigma -> get_ref env "vcpu.circuit.one");
    circuit_wf_constr = (fun env sigma -> get_ref env "vcpu.circuit.one_wf");
  }

let circuit_not : circuit =
  {
    circuit_input_count = 1;
    circuit_wires = [Binding_not (Reference_input 0)];
    circuit_outputs = [0];
    circuit_constr = (fun env sigma -> get_ref env "vcpu.circuit.not");
    circuit_wf_constr = (fun env sigma -> get_ref env "vcpu.circuit.not_wf");
  }

let circuit_and : circuit =
  {
    circuit_input_count = 2;
    circuit_wires = [Binding_and (Reference_input 0, Reference_input 1)];
    circuit_outputs = [0];
    circuit_constr = (fun env sigma -> get_ref env "vcpu.circuit.and");
    circuit_wf_constr = (fun env sigma -> get_ref env "vcpu.circuit.and_wf");
  }

let circuit_or : circuit =
  {
    circuit_input_count = 2;
    circuit_wires = [Binding_or (Reference_input 0, Reference_input 1)];
    circuit_outputs = [0];
    circuit_constr = (fun env sigma -> get_ref env "vcpu.circuit.or");
    circuit_wf_constr = (fun env sigma -> get_ref env "vcpu.circuit.or_wf");
  }

let circuit_xor : circuit =
  {
    circuit_input_count = 2;
    circuit_wires = [Binding_xor (Reference_input 0, Reference_input 1)];
    circuit_outputs = [0];
    circuit_constr = (fun env sigma -> get_ref env "vcpu.circuit.xor");
    circuit_wf_constr = (fun env sigma -> get_ref env "vcpu.circuit.xor_wf");
  }

let circuit_switch (data_size : int) : circuit =
  {
    circuit_input_count = 1 + 2 * data_size;
    circuit_wires =
      List.init data_size (fun i ->
        Binding_if (Reference_input 0, Reference_input (1 + i), Reference_input (1 + data_size + i))
      );
    circuit_outputs = List.init data_size (fun i -> i);
    circuit_constr = (fun env sigma ->
      EConstr.mkApp (get_ref env "vcpu.circuit.switch", [|to_nat_constr env data_size|])
    );
    circuit_wf_constr = (fun env sigma ->
      EConstr.mkApp (get_ref env "vcpu.circuit.switch_wf", [|to_nat_constr env data_size|])
    );
  }

let circuit_const (data : bool list) : circuit =
  let c_const = circuit_empty 0 in
  let (c_const', zero_output_wires) = circuit_add c_const circuit_zero [] in
  let (c_const'', one_output_wires) = circuit_add c_const' circuit_one [] in
  let c_const''' = circuit_set_outputs c_const''
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
    (a2 |> Cbv.cbv_norm (Cbv.create_cbv_infos CClosure.all env sigma) |> of_nat_constr env sigma)
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

let compiled : ((Names.Constant.t * EConstr.t list) * circuit) list ref =
  Summary.ref ~name:"compiled" []

let red_flags (excluded : Names.Constant.t option) : CClosure.RedFlags.reds =
  let builtin = ["core.bool.negb"; "core.bool.andb"; "core.bool.orb"; "core.bool.xorb"] in
  let builtin_constants = builtin |> List.map Coqlib.lib_ref |> List.map dest_const_ref in
  let compiled_constants =
    !compiled
    |> List.map fst
    |> List.map fst
    |> List.filter (fun constant ->
      match excluded with
      | None -> true
      | Some excluded -> not (Names.Constant.CanOrd.equal constant excluded)
    ) in
  builtin_constants @ compiled_constants
  |> List.fold_left (fun red_flags constant ->
    CClosure.RedFlags.red_sub red_flags (CClosure.RedFlags.fCONST constant)
  ) CClosure.allnolet

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
    : (EConstr.t * int list) list * circuit =
  (* Feedback.msg_notice Pp.(str "convert" ++ spc () ++ Printer.pr_econstr_env env sigma source); *)

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

  let input_evar_mapping =
    input_mapping
    |> List.map (fun (evar, evar_inputs_wires) ->
      (evar, evar_inputs_wires |> List.map (fun i -> Reference_input i))
    ) in

  let convert_child sigma c_source child child_evar_mapping =
    let (child_input_mapping, c_child) =
      convert env sigma (child_evar_mapping |> List.map fst) child in
    let child_input_references = List.init c_child.circuit_input_count (fun i ->
      let (evar, child_input_wires) =
        child_input_mapping |> List.find (fun (_, child_input_wires) -> child_input_wires |> List.mem i) in
      List.nth (child_evar_mapping |> constr_list_assoc sigma evar) (child_input_wires |> list_index_of i)
    ) in
    let (c_source', child_output_wires) = circuit_add c_source c_child child_input_references in
    (c_source', child_output_wires) in

  let c_source = circuit_empty input_count in
  let (sigma, c_source') = try
    verify_reduction_not_blocked sigma evars source;
    match EConstr.kind sigma source with

    (* Evar *)
    | _ when evars |> constr_list_mem sigma source ->
      let evar_input_references = input_evar_mapping |> constr_list_assoc sigma source in
      let c_evar = circuit_id (List.length evar_input_references) in
      let (c_source', evar_output_wires) = circuit_add c_source c_evar evar_input_references in
      let c_source'' = circuit_set_outputs c_source' evar_output_wires in
      (sigma, c_source'')

    (* Not *)
    | App (f, [|arg|]) when EConstr.eq_constr sigma f (get_ref env "core.bool.negb") ->
      let (c_source', arg_output_wires) = convert_child sigma c_source arg input_evar_mapping in
      let (c_source'', not_output_wires) =
        circuit_add c_source' circuit_not (arg_output_wires |> List.map (fun i -> Reference_wire i)) in
      let c_source''' = circuit_set_outputs c_source'' not_output_wires in
      (sigma, c_source''')

    (* And *)
    | App (f, [|arg_1; arg_2|]) when EConstr.eq_constr sigma f (get_ref env "core.bool.andb") ->
      let (c_source', arg_1_output_wires) = convert_child sigma c_source arg_1 input_evar_mapping in
      let (c_source'', arg_2_output_wires) = convert_child sigma c_source' arg_2 input_evar_mapping in
      let (c_source''', and_output_wires) =
        circuit_add c_source'' circuit_and ((arg_1_output_wires @ arg_2_output_wires) |> List.map (fun i -> Reference_wire i)) in
      let c_source'''' = circuit_set_outputs c_source''' and_output_wires in
      (sigma, c_source'''')

    (* Or *)
    | App (f, [|arg_1; arg_2|]) when EConstr.eq_constr sigma f (get_ref env "core.bool.orb") ->
      let (c_source', arg_1_output_wires) = convert_child sigma c_source arg_1 input_evar_mapping in
      let (c_source'', arg_2_output_wires) = convert_child sigma c_source' arg_2 input_evar_mapping in
      let (c_source''', or_output_wires) =
        circuit_add c_source'' circuit_or ((arg_1_output_wires @ arg_2_output_wires) |> List.map (fun i -> Reference_wire i)) in
      let c_source'''' = circuit_set_outputs c_source''' or_output_wires in
      (sigma, c_source'''')

    (* Xor *)
    | App (f, [|arg_1; arg_2|]) when EConstr.eq_constr sigma f (get_ref env "core.bool.xorb") ->
      let (c_source', arg_1_output_wires) = convert_child sigma c_source arg_1 input_evar_mapping in
      let (c_source'', arg_2_output_wires) = convert_child sigma c_source' arg_2 input_evar_mapping in
      let (c_source''', xor_output_wires) =
        circuit_add c_source'' circuit_xor ((arg_1_output_wires @ arg_2_output_wires) |> List.map (fun i -> Reference_wire i)) in
      let c_source'''' = circuit_set_outputs c_source''' xor_output_wires in
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
        circuit_add c_source' c_func (args_output_wires |> List.map (fun i -> Reference_wire i)) in
      let c_source''' = circuit_set_outputs c_source'' func_output_wires in
      (sigma, c_source''')

    (* Let in *)
    | LetIn (_, value, value_type, context) ->
      let (c_source', value_output_wires) = convert_child sigma c_source value input_evar_mapping in
      let (sigma, value_evar) = Evarutil.new_evar env sigma value_type in
      let (c_source'', context_output_wires) =
        convert_child sigma c_source' (context |> EConstr.Vars.subst1 value_evar)
        ((value_evar, value_output_wires |> List.map (fun i -> Reference_wire i)) :: input_evar_mapping) in
      let c_source''' = circuit_set_outputs c_source'' context_output_wires in
      (sigma, c_source''')

    (* Match bool *)
    | Case (ci, _, _, (_, brs_type), _, scrutinee, brs) when
        Names.GlobRef.equal (Names.GlobRef.IndRef ci.ci_ind) (Coqlib.lib_ref "core.bool.type") ->
      let (c_source', scutinee_output_wires) = convert_child sigma c_source scrutinee input_evar_mapping in
      let (c_source'', br_false_output_wires) = convert_child sigma c_source' (brs.(1) |> snd) input_evar_mapping in
      let (c_source''', br_true_output_wires) = convert_child sigma c_source'' (brs.(0) |> snd) input_evar_mapping in
      let c_switch = circuit_switch (size_of_type env sigma brs_type) in
      let (c_source'''', switch_output_wires) = circuit_add c_source''' c_switch
        (scutinee_output_wires @ br_false_output_wires @ br_true_output_wires |> List.map (fun i -> Reference_wire i)) in
      let c_source''''' = circuit_set_outputs c_source'''' switch_output_wires in
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
          let c_switch = circuit_switch (size_of_type env sigma brs_type) in
          let (c_source'', switch_output_wires) =
            circuit_add c_source' c_switch
            (List.nth scutinee_output_wires counstructor_index :: br_output_wires @ switches_output_wires
              |> List.map (fun i -> Reference_wire i)) in
          (c_source'', switch_output_wires)
        )
        (c_source'', brs_output_wires |> List.hd)
        (List.init (constructor_count - 1) (fun i -> i + 1))
        (brs_output_wires |> List.tl) in
      let c_source'''' = circuit_set_outputs c_source''' switches_output_wires in
      (sigma, c_source'''')

    (* false and true *)
    | _ when EConstr.eq_constr sigma source (get_ref env "core.bool.false") ->
      let c_zero = circuit_zero in
      let (c_source', zero_output_wires) = circuit_add c_source c_zero [] in
      let c_source'' = circuit_set_outputs c_source' zero_output_wires in
      (sigma, c_source'')
    | _ when EConstr.eq_constr sigma source (get_ref env "core.bool.true") ->
      let c_one = circuit_one in
      let (c_source', one_output_wires) = circuit_add c_source c_one [] in
      let c_source'' = circuit_set_outputs c_source' one_output_wires in
      (sigma, c_source'')

    (* Vector *)
    | App (f, [|_; _; a3; _|]) when EConstr.eq_constr sigma f (get_ref env "vcpu.vector.constructor") ->
      verify_reduction_not_blocked sigma evars a3;
      let l = of_list_constr env sigma a3 in
      let (c_source', elements_output_wires) = l |> List.fold_left (fun (c_source', children_output_wires) element ->
        let (c_source'', element_output_wires) = convert_child sigma c_source' element input_evar_mapping in
        (c_source'', children_output_wires @ element_output_wires)
      ) (c_source, []) in
      let c_source'' = circuit_set_outputs c_source' elements_output_wires in
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
        let c_constructor_index = circuit_const (List.init constructor_count (fun i -> i = contructor_index)) in
        let (c_source', contructor_index_output_wires) = circuit_add c_source c_constructor_index [] in
        let (c_source'', args_output_wires) = args |> Seq.fold_left (fun (c_source', args_output_wires) arg ->
          let (c_source'', arg_output_wires) = convert_child sigma c_source' arg input_evar_mapping in
          (c_source'', args_output_wires @ arg_output_wires)
        ) (c_source', []) in
        let c_padding = circuit_const (List.init padding_size (fun _ -> false)) in
        let (c_source''', padding_output_wires) = circuit_add c_source'' c_padding [] in
        let c_source'''' =
          circuit_set_outputs c_source'' (contructor_index_output_wires @ args_output_wires @ padding_output_wires) in
        (sigma, c_source'''')
      | _ -> assert false
    )

    | _ -> CErrors.user_err Pp.(str "Unknown term:" ++ spc () ++ Printer.pr_econstr_env env sigma source)
  with

  (* Reduction was blocked, replace a vector variable by sample contents and try again *)
  | Reduction_blocked reduction_blocking_evar ->
    let (typ, length) = dest_vector_type env sigma (Retyping.get_type_of env sigma reduction_blocking_evar) in
    let typ_size = size_of_type env sigma typ in
    let (sigma, vector_evars) = new_evars env sigma typ length in
    let vector_evar_mapping =
      vector_evars |> List.mapi (fun i vector_evar ->
        (
          vector_evar,
          list_select
            (input_evar_mapping |> constr_list_assoc sigma reduction_blocking_evar)
            (List.init typ_size (fun j -> typ_size * i + j))
        )
      ) in
    let substituted = Termops.replace_term sigma reduction_blocking_evar (to_vector env typ vector_evars) source in
    let reduced_substituted = Cbv.cbv_norm (Cbv.create_cbv_infos (red_flags None) env sigma) substituted in
    let (c_source', substituted_output_wires) =
      convert_child sigma c_source reduced_substituted
      (input_evar_mapping @ vector_evar_mapping) in
    let c_source'' = circuit_set_outputs c_source' substituted_output_wires in
    (sigma, c_source'') in

  (* Feedback.msg_notice Pp.(str "return" ++ spc () ++ Printer.pr_econstr_env env sigma c_source'.circuit_constr); *)
  (input_mapping, c_source')

let compile (input_id : Names.Id.t) (param_constr_exprs : Constrexpr.constr_expr list)
    (output_id : Names.Id.t option) : unit =
  let env = Global.env () in
  ref_cache := CString.Map.empty;
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
  let reduced_input = Cbv.cbv_norm (Cbv.create_cbv_infos (red_flags (Some input_constant)) env sigma) applied_input in
  let (args, source) = reduced_input |> EConstr.decompose_lam sigma in
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
  Feedback.msg_notice (Pp.str "Start");
  let (source_input_mapping, c_source) =
    convert env sigma arg_evars (source |> EConstr.Vars.substl (arg_evars |> List.rev)) in
  let c_result = circuit_empty args_size in
  let source_input_references = List.init c_source.circuit_input_count (fun i ->
    let (evar, source_input_wires) =
      source_input_mapping |> List.find (fun (_, source_input_wires) -> source_input_wires |> List.mem i) in
    List.nth (source_evar_mapping |> constr_list_assoc sigma evar) (source_input_wires |> list_index_of i)
  ) in
  let (c_result', source_output_wires) = circuit_add c_result c_source source_input_references in
  let c_result'' = circuit_set_outputs c_result' source_output_wires in
  Feedback.msg_notice Pp.(str "Wire count:" ++ spc() ++ int (c_result''.circuit_wires |> List.length));
  let result_circuit_constr = c_result''.circuit_constr env sigma in
  Feedback.msg_notice (Pp.str "Circuit constr");
  let circuit_constant =
    Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(
        Declare.CInfo.make
        ~name:(((output_id |> Option.default input_id) |> Names.Id.to_string) ^ "_circuit" |> Names.Id.of_string)
        ~typ:(Some (get_ref env "vcpu.circuit.type"))
        ()
      )
      ~opaque:false ~body:result_circuit_constr sigma
    |> dest_const_ref in
  let result_circuit_wf_constr = c_result''.circuit_wf_constr env sigma in
  Feedback.msg_notice (Pp.str "Circuit wf constr");
  let circuit_wf_constant =
    Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(
        Declare.CInfo.make
        ~name:(((output_id |> Option.default input_id) |> Names.Id.to_string) ^ "_circuit_wf" |> Names.Id.of_string)
        ~typ:(Some (EConstr.mkApp (get_ref env "vcpu.circuit.wf", [|EConstr.mkConst circuit_constant|])))
        ()
      )
      ~opaque:false ~body:result_circuit_wf_constr sigma
    |> dest_const_ref in
  let c_output = {
    c_result'' with
    circuit_constr = (fun env sigma -> EConstr.mkConst circuit_constant);
    circuit_wf_constr = (fun env sigma -> EConstr.mkConst circuit_wf_constant);
  } in
  compiled := !compiled @ [((input_constant, params), c_output)]
