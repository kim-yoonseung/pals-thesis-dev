open TestInterface
open AppSystem
open DriverUtil
open EventHandlers
open CProgUtil

let tm_init: z = Z.mul pals_period (int2z 3)
let tm_end: z = Z.mul pals_period (int2z 100)

let _ = run_cprog_system
          tm_init (Some tm_end)
