open AppSystem
open DriverUtil
open EventHandlers

type itree_t = (((((__ extcallE, __, __) sum1, __ randE, __) sum1, __) tgd, __ tspE, __) sum1, unit) itree

let rec step (sytm: int) (itr: itree_t): 'r option =
  match observe itr with
  | RetF r -> Some r
  | TauF itr -> step sytm itr
  | VisF (e, k) ->
     match e with
     | Inl1 (Tagged (tid, loc_e)) ->
        (match loc_e with
         | Inl1 ext_e ->
            print_string ("  <Task " ^  string_of_int (nat2int tid) ^ ": ");
            let r_ext = ext_evt_handler tid ext_e in
            print_endline(">");
            step sytm (k r_ext)
         | Inr1 rand_e ->
            let r_rand = random_handler tid rand_e in
            step sytm (k r_rand)
        )
     | Inr1 tsp_e ->
        let nsytm = z2int tsp_e in
        print_endline ("[[ period " ^ string_of_int nsytm ^ " ]]");
        step nsytm (k (Obj.magic ()))

let tm_init: z = Z.mul system_synch_period (int2z 3)
let tm_end: z = Z.mul system_synch_period (int2z 100)

let res = step 0 (system_itree tm_init (Some tm_end))
let _ = print_string "hello"
