open TestInterface
open AppSystem
open DriverUtil
open EventHandlers
(* open Test_interface_ml *)

let option_map (f: 'a -> 'b) (x: 'a option): 'b option =
  match x with
  | None -> None
  | Some a -> Some (f a)

let conv_inb (inb: (bytes option) list): ((int list) option) list =
  let f: bytes -> int list = List.map z2int in
  List.map (option_map f) inb

let conv_outb (outb: ((int list) option) list): (bytes option) list =
  let f: int list -> bytes = List.map int2z in
  List.map (option_map f) outb

let call_cprog_job (sytm: z) (tid: nat) (inb: (bytes option) list)
    : (bytes option) list =
  let outb = run_job_interface (nat2int tid) (z2int64 sytm) (conv_inb inb) in
  conv_outb outb

(* cprog_job_interface handler (z2int sytm) (nat2int tid) inbs  *)

let rec interp_capp_invok
          (sytm: int)
          (itr: ((('a1, __) app_invkE, __ tspE, __) sum1, unit) itree)
        : unit =
  match observe itr with
  | RetF r -> ()
  | TauF itr' -> interp_capp_invok sytm itr'
  | VisF (e, k) ->
     match e with
     | Inl1 (AppInvok (sytm_z, tid, inbs)) ->
        let outb = call_cprog_job sytm_z tid inbs in
        interp_capp_invok sytm (k (Obj.magic outb))
     | Inr1 tsp_e ->
        let nsytm = z2int tsp_e in
        print_endline ("[[ period " ^ (string_of_int nsytm) ^ " ]]");
        interp_capp_invok nsytm (k (Obj.magic ()))

let random_handler_interface
      (tid: int) (kind: int): int =
  let tid_n = int2nat tid in
  if kind = 0 then
    let r: bool = Obj.obj (random_handler tid_n RandFailure) in
    if r then 1 else 0
  else if kind = 1 then
    let r: bool = Obj.obj (random_handler tid_n RandRecovery) in
    if r then 1 else 0
  else
    let r: nat = Obj.obj (random_handler tid_n RandFuel) in
    (nat2int r)

(* http://caml.inria.fr/pub/old_caml_site/FAQ/FAQ_EXPERT-eng.html#strings *)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let val0_of_int (n: int): val0 = Vint (int2z n)

let conv_extcall
      (retty: int) (fname: string) (args: int list)
    : 'a extcallE =
  let fname': char list = explode fname in
  let argvs = List.map val0_of_int args in
  if retty = 0 then
    ExtcallEvent_Void (fname', argvs)
  else
    ExtcallEvent_Int (fname', argvs)

let extcall_handler_interface
      (tid: int) (retty: int)
      (fname: string) (args: int list): int =
  let ec_e = conv_extcall retty fname args in
  print_string ("  <Task " ^  string_of_int tid ^ ": ");
  let r = extcall_handler (int2nat tid) ec_e in
  print_endline(">");
  if retty = 0 then 0 else
    let n: z = Obj.obj r in
    (z2int n)

let send_handler_interface
      (nts: nat) (mcs: (nat list) list) (sntz: z list -> (z list) option)
      (outb: inbox_t)
      (tid_dest: int) (msg: int list)
    : inbox_t =
  if tid_dest < 0 then outb else
    let bs: z list = List.map int2z msg in
    let outb1 = conv_outb outb in
    let outb2 = ExecutableSpec.update_outbox
                  nts mcs sntz
                  outb1 (int2nat tid_dest) bs in
    conv_inb outb2


let pals_period_int: int = get_period ()
let pals_period: z = int2z pals_period_int
let num_tasks_int: int = get_num_tasks ()
let num_tasks: nat = int2nat num_tasks_int
let msg_size_int: int = get_msg_size ()
let msg_size: nat = int2nat msg_size_int

let rec build_row (r: int) (c: int): nat list =
  if num_tasks_int <= c then [] else
    let flag: int = check_mcast_member r c in
    if 0 < flag then (int2nat c) :: build_row r (c + 1)
    else build_row r (c + 1)

let rec build_mcasts_i (n: int) (m: int): (nat list) list =
  if m <= n then [] else
    build_row n 0 :: build_mcasts_i (n + 1) m

let mcasts: (nat list) list =
  let m = get_num_mcasts () in
  build_mcasts_i 0 m

let sntz: z list -> (z list) option =
  resize_bytes0 msg_size

let run_cprog_system
      (* (num_tasks: nat) (mcs: (nat list) list)
       * (sntz: z list -> (z list) option) *)
      (* (prd: z) *)
      (tm_init: z) (tm_end: z option)
    : unit =
  let _ = register_callbacks
            random_handler_interface
            extcall_handler_interface
            (send_handler_interface num_tasks mcasts sntz)
  in
  let itr = ExecutableSpec.synch_itree
              num_tasks pals_period
              tm_init tm_end in
  let _ = interp_capp_invok 0 itr in
  let _ = remove_callbacks () in
  ()


(* let mcasts: (nat list) list = [[int2nat 1 ; int2nat 2]] *)

(* let sys_num_tasks: nat =
 *   length (ExecutableSpec.apps exec_sys')
 * let sys_mcasts: (nat list) list =
 *   ExecutableSpec.mcasts exec_sys'
 * let sys_sntz: z list -> (z list) option =
 *   ExecutableSpec.sanitize_msg exec_sys' *)
