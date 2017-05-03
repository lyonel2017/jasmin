open Prog

val live_fd : 'info func -> (Sv.t * Sv.t) func

val liveness : 'info prog -> (Sv.t * Sv.t) prog

val pp_info : Format.formatter -> Sv.t * Sv.t -> unit