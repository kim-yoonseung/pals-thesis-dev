open Int64Util
open AppSystem

let _ = Random.self_init ()

let rec nat2int (n: nat): int =
  match n with
  | O -> 0
  | S n' -> (nat2int n') + 1

let rec int2nat (n: int): nat =
  if n <= 0 then O else S (int2nat (n - 1))

let rec pos2int (p: positive): int =
  match p with
  | XH -> 1
  | XI p1 -> (pos2int p1) * 2 + 1
  | XO p1 -> (pos2int p1) * 2


let rec pos2int64 (p: positive): int64 =
  match p with
  | XH -> 1L
  | XI p1 -> (int64_add (int64_mul (pos2int64 p1) 2L) 1L)
  | XO p1 -> (int64_mul (pos2int64 p1) 2L)

let z2int (n: z): int =
  match n with
  | Z0 -> 0
  | Zpos p -> pos2int p
  | Zneg p -> - (pos2int p)

let rec pint2pos (n: int): positive =
  if n = 1 then XH else
    let r = n mod 2 in
    let m = n / 2 in
    let l = (pint2pos m) in
    if r = 0 then XO l else XI l

(* let rec pint64_to_pos (n: int64): positive =
 *   if n = 1L then XH else
 *     let r = n mod 2 in
 *     let m = n / 2 in
 *     let l = (pint64_to_pos m) in
 *     if r = 0 then XO l else XI l *)


let int2z (n: int): z =
  if n = 0 then Z0 else
    if 0 < n then Zpos (pint2pos n)
    else Zneg (pint2pos (- n))

let z2int64 (n: z): int64 =
  match n with
  | Z0 -> 0L
  | Zpos p -> pos2int64 p
  | Zneg p -> int64_neg (pos2int64 p)

(* let int64_to_z (n: int64): z =
 *   if n = 0L then Z0 else
 *     if 0 < n then Zpos (pint64_to_pos n)
 *     else Zneg (pint2pos (- n)) *)


let rec print_charlist (chl: char list): unit =
  match chl with
  | [] -> print_string " "
  | h::t -> print_string (Char.escaped h) ;
            print_charlist t

let string_of_value (v: val0): string =
  match v with
  | Vundef -> "Undef"
  | Vint z -> string_of_int (z2int z)
  | Vlong z -> (* string_of_int (z2int z) ^ "L" *)
     "<long_value>"
  | Vfloat f -> "<float_value>"
  | Vsingle f -> "<float32_value>"
  | Vptr (b, ofs) -> "<ptr_value>"

let print_extcall (fname: char list) (args: val0 list): unit =
  print_charlist fname ;
  let args_str = String.concat "," (map0 string_of_value args) in
  print_string ("(" ^ args_str ^ ")")
