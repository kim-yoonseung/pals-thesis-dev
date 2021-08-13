open AppSystem
open DriverUtil
open EventImplInterface

let int_retval_gen (fname: char list) (args: val0 list): int =
  let int_retval_max: int = 10 in
  Random.int int_retval_max

let rand_bool_gen (tid: nat): bool =
  let false_ratio_inv: int = 5 in
  let c = Random.int false_ratio_inv in
  (* let _ = print_endline ("RB: " ^ if c = 0 then "false" else "true") in *)
  (c != 0)

let rand_nat_gen (tid: nat): nat =
  (* let rand_nat_max: int = 30 in
   * let c = Random.int rand_nat_max in
   * (\* let _ = print_endline ("RN: " ^ string_of_int c) in *\)
   * int2nat c *)
  int2nat 9999

let val2int (v: val0): int =
  match v with
  | Vint z -> z2int z
  | _ -> 0

let rec string_of_charlist (chl: char list): string =
  match chl with
  | [] -> ""
  | h::t -> (Char.escaped h) ^ (string_of_charlist t)


let extcall_handler (tid: nat)
      (ec_e: 'a extcallE): __ =
  match ec_e with
  | ExtcallEvent_Int (fname, args) ->
     print_extcall fname args;
     let r_int: int = call_event_impl (string_of_charlist fname) (map0 val2int args) in
     (* let r_int: int = int_retval_gen fname args in *)
     print_string (" => " ^ string_of_int r_int);
     Obj.magic (int2z r_int)
  | ExtcallEvent_Void (fname, args) ->
     print_extcall fname args;
     let _ = call_event_impl (string_of_charlist fname) (map0 val2int args) in
     print_string (" => ()");
     Obj.magic ()

let ext_evt_handler (tid: nat)
      (ext_e: (__ extcallE, __, __) sum1): __ =
  match ext_e with
  | Inl1 ec_e ->
     extcall_handler tid ec_e
  | Inr1 _ ->
     print_string ("[[ UB ]]");
     Obj.magic ()

let random_handler (tid: nat)
      (rand_e: 'a randE): __ =
  match rand_e with
  | RandFailure ->
     Obj.magic (* (rand_bool_gen tid) *) true
  | RandRecovery ->
     Obj.magic (* (rand_bool_gen tid) *) true
  | RandFuel ->
     Obj.magic (rand_nat_gen tid)
