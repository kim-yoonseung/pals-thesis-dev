type inbox_t = ((int list) option) list

external register_callbacks:
  (* random *) (int -> int -> int) ->
  (* event *) (int(*tid*) -> int(*retty*) ->
               string -> int list -> int) ->
  (* send *) (inbox_t ->
              int -> int list -> inbox_t) ->
  unit =
  "register_callbacks"

external remove_callbacks: unit -> unit =
  "remove_callbacks"

external run_job_interface: int -> int64 -> inbox_t -> inbox_t =
  "run_job_interface"


external get_num_tasks: unit -> int =
  "get_num_tasks"

external get_msg_size: unit -> int =
  "get_msg_size"

external get_period: unit -> int =
  "get_period"

external get_num_mcasts: unit -> int =
  "get_num_tasks"

external check_mcast_member: int -> int -> int =
  "check_mcast_member"
