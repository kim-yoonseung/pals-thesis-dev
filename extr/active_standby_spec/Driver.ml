open AppSystem
open DriverUtil
open EventHandlers
open ITreeExecutor

let tm_init: z = Z.mul (ExecutableSpec.period app_system) (int2z 3)
let tm_end: z = Z.mul (ExecutableSpec.period app_system) (int2z 100)

let res = ITreeExecutor.run 0 (app_system_itree tm_init (Some tm_end))
let _ = print_endline "Done"
