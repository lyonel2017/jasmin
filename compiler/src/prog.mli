(* ------------------------------------------------------------------------ *)
open Utils
open Wsize
module E = Expr
module L = Location
module B = Bigint

module Name : sig
  type t = string
end

type uid
val int_of_uid : uid -> int

(* ------------------------------------------------------------------------ *)
type base_ty =
  | Bool
  | Int              (* Unbounded integer for pexpr *)
  | U   of wsize (* U(n): unsigned n-bit integer *)

  [@@deriving compare,sexp]

type 'len gty =
  | Bty of base_ty
  | Arr of wsize * 'len (* Arr(n,de): array of n-bit integers with dim. *)
           (* invariant only Const variable can be used in expression *)
           (* the type of the expression is [Int] *)

type writable = Constant | Writable
type pointer = Direct | Pointer of writable

type v_kind =
  | Const             (* global parameter  *)
  | Stack of pointer  (* stack variable    *)
  | Reg   of pointer  (* register variable *)
  | Inline            (* inline variable   *)
  | Global            (* global (in memory) constant *) 
  [@@deriving compare,sexp]

type 'len gvar = private {
  v_name : Name.t;
  v_id   : uid;
  v_kind : v_kind;
  v_ty   : 'len gty;
  v_dloc : L.t   (* location where declared *)
}

type 'len gvar_i = 'len gvar L.located

type 'len ggvar = {
  gv : 'len gvar_i;
  gs : E.v_scope;
}


type 'len gexpr =
  | Pconst of B.zint
  | Pbool  of bool
  | Parr_init of 'len
  | Pvar   of 'len ggvar
  | Pget   of Warray_.arr_access * wsize * 'len ggvar * 'len gexpr
  | Psub   of Warray_.arr_access * wsize * 'len * 'len ggvar * 'len gexpr
  | Pload  of wsize * 'len gvar_i * 'len gexpr
  | Papp1  of E.sop1 * 'len gexpr
  | Papp2  of E.sop2 * 'len gexpr * 'len gexpr
  | PappN of E.opN * 'len gexpr list
  | Pif    of 'len gty * 'len gexpr * 'len gexpr * 'len gexpr

type 'len gexprs = 'len gexpr list

val u8    : 'e gty
val u16   : 'e gty
val u32   : 'e gty
val u64   : 'e gty
val u128  : 'e gty
val u256  : 'e gty
val tu    : wsize -> 'e gty
val tint  : 'e gty
val tbool : 'e gty

val is_stack_kind   : v_kind -> bool
val is_reg_kind     : v_kind -> bool
val is_ptr          : v_kind -> bool
val is_reg_ptr_kind : v_kind -> bool
val is_stk_ptr_kind : v_kind -> bool


(* ------------------------------------------------------------------------ *)

type assgn_tag =
  | AT_none   (* The compiler can do what it want *)
  | AT_keep   (* Assignment should be kept by the compiler *)
  | AT_rename (* use as equality constraint in reg-alloc and compile to no-op *)
  | AT_inline (* the assignement should be inline, and propagate *)
  | AT_phinode (* renaming during SSA transformation *)

type 'len glval =
 | Lnone of L.t * 'len gty
 | Lvar  of 'len gvar_i
 | Lmem  of wsize * 'len gvar_i * 'len gexpr
 | Laset of Warray_.arr_access * wsize * 'len gvar_i * 'len gexpr
 | Lasub of Warray_.arr_access * wsize * 'len * 'len gvar_i * 'len gexpr

type 'len glvals = 'len glval list

type inline_info =
  | DoInline
  | NoInline

type funname = private {
  fn_name : Name.t;
  fn_id   : uid;
}

type range_dir = UpTo | DownTo
type 'len grange = range_dir * 'len gexpr * 'len gexpr

type i_loc = L.t * L.t list

type ('len,'info) ginstr_r =
  | Cassgn of 'len glval * assgn_tag * 'len gty * 'len gexpr
  | Copn   of 'len glvals * assgn_tag * E.sopn * 'len gexprs
  | Cif    of 'len gexpr * ('len,'info) gstmt * ('len,'info) gstmt
  | Cfor   of 'len gvar_i * 'len grange * ('len,'info) gstmt
  | Cwhile of E.align * ('len,'info) gstmt * 'len gexpr * ('len,'info) gstmt
  | Ccall  of inline_info * 'len glvals * funname * 'len gexprs

and ('len,'info) ginstr = {
  i_desc : ('len,'info) ginstr_r;
  i_loc  : i_loc;
  i_info : 'info;
}

and ('len,'info) gstmt = ('len,'info) ginstr list

(* ------------------------------------------------------------------------ *)
type subroutine_info = {
    returned_params : int option list; 
  }

type call_conv =
  | Export                 (* The function should be exported to the outside word *)
  | Subroutine of subroutine_info (* internal function that should not be inlined *)
  | Internal                   (* internal function that should be inlined *)

type ('len,'info) gfunc = {
    f_loc  : L.t;
    f_cc   : call_conv;
    f_name : funname;
    f_tyin : 'len gty list;
    f_args : 'len gvar list;
    f_body : ('len,'info) gstmt;
    f_tyout : 'len gty list;
    f_ret  : 'len gvar_i list
  }

type 'len ggexpr = 
  | GEword of 'len gexpr
  | GEarray of 'len gexprs

type ('len,'info) gmod_item =
  | MIfun   of ('len,'info) gfunc
  | MIparam of ('len gvar * 'len gexpr)
  | MIglobal of ('len gvar * 'len ggexpr)

type ('len,'info) gprog = ('len,'info) gmod_item list
   (* first declaration occur at the end (i.e reverse order) *)

(* ------------------------------------------------------------------------ *)
(* Parametrized expression *)

type pty    = pexpr gty
and  pvar   = pexpr gvar
and  pvar_i = pexpr gvar_i
and  plval  = pexpr glval
and  plvals = pexpr glvals
and  pexpr  = pexpr gexpr

type 'info pinstr = (pexpr,'info) ginstr
type 'info pstmt  = (pexpr,'info) gstmt

type 'info pfunc     = (pexpr,'info) gfunc
type 'info pmod_item = (pexpr,'info) gmod_item
type 'info pprog     = (pexpr,'info) gprog

(* -------------------------------------------------------------------- *)
module PV : sig
  type t = pvar

  val mk : Name.t -> v_kind -> pty -> L.t -> pvar

  val compare : pvar -> pvar -> int

  val equal : pvar -> pvar -> bool

  val hash : pvar -> int

  val is_glob : pvar -> bool
end

val gkglob : 'len gvar_i -> 'len ggvar
val gkvar : 'len gvar_i -> 'len ggvar
val is_gkvar : 'len ggvar -> bool

module Mpv : Map.S  with type key = pvar
module Spv : Set.S  with type elt = pvar

val pty_equal : pty -> pty -> bool
val pexpr_equal : pexpr -> pexpr -> bool

(* ------------------------------------------------------------------------ *)
(* Non parametrized expression                                              *)

type ty    = int gty
type var   = int gvar
type var_i = int gvar_i
type lval  = int glval
type lvals = int glval list
type expr  = int gexpr
type exprs = int gexpr list

type 'info instr = (int,'info) ginstr
type 'info stmt  = (int,'info) gstmt

type 'info func     = (int,'info) gfunc
type 'info mod_item = (int,'info) gmod_item
type global_decl    = var * Global.glob_value
type 'info prog     = global_decl list * 'info func list


(* -------------------------------------------------------------------- *)
module V : sig
  type t = var

  val mk : Name.t -> v_kind -> ty -> L.t -> var

  val clone : var -> var

  val compare : var -> var -> int

  val equal : var -> var -> bool

  val hash : var -> int

  val is_glob : var -> bool
end

module Sv : Set.S  with type elt = var
module Mv : Map.S  with type key = var
module Hv : Hash.S with type key = var

val rip : var
val rsp : var 

(* -------------------------------------------------------------------- *)
val kind_i : 'len gvar_i -> v_kind
val ty_i   : 'len gvar_i -> 'len gty 

(* -------------------------------------------------------------------- *)
module F : sig
  val mk : Name.t -> funname

  val compare : funname -> funname -> int

  val equal : funname -> funname -> bool

  val hash : funname -> int
end

module Sf : Set.S  with type elt = funname
module Mf : Map.S  with type key = funname
module Hf : Hash.S with type key = funname

(* -------------------------------------------------------------------- *)
(* used variables                                                       *)

val rvars_lv : Sv.t -> lval -> Sv.t
val vars_e  : expr -> Sv.t
val vars_es : expr list -> Sv.t
val vars_i  : 'info instr -> Sv.t
val vars_c  : 'info stmt  -> Sv.t
val vars_fc : 'info func  -> Sv.t

val locals  : 'info func -> Sv.t

(* -------------------------------------------------------------------- *)
(* Written variables & called functions *)
val written_vars_fc : 'info func -> Sv.t * Sf.t

(* -------------------------------------------------------------------- *)
(* Functions on types                                                   *)

val int_of_ws  : wsize -> int
val string_of_ws : wsize -> string
val size_of_ws : wsize -> int
val uptr       : wsize 

val wsize_lt : wsize -> wsize -> bool
val wsize_le : wsize -> wsize -> bool

val int_of_pe  : pelem -> int

val int_of_velem : velem -> int 

val is_ty_arr : 'e gty -> bool
val array_kind : ty -> wsize * int
val ws_of_ty   : 'e gty -> wsize
val arr_size : wsize -> int -> int

(* -------------------------------------------------------------------- *)
(* Functions on variables                                               *)

val is_stack_var : var -> bool
val is_reg_arr   : var -> bool


(* -------------------------------------------------------------------- *)
(* Functions over expressions                                           *)

val ( ++ ) : 'len gexpr -> 'len gexpr -> 'len gexpr
val ( ** ) : 'len gexpr -> 'len gexpr -> 'len gexpr
val cnst   : B.zint -> 'len gexpr
val icnst  : int -> 'len gexpr
val cast64 : 'len gexpr -> 'len gexpr

(* -------------------------------------------------------------------- *)
(* Functions over lvalue                                                *)

val expr_of_lval : 'len glval -> 'len gexpr option

(* -------------------------------------------------------------------- *)
(* Functions over instruction                                           *)

val destruct_move : ('len, 'info) ginstr -> 'len glval * assgn_tag * 'len gty * 'len gexpr

(* -------------------------------------------------------------------- *)
val clamp : wsize -> Bigint.zint -> Bigint.zint
val clamp_pe : pelem -> Bigint.zint -> Bigint.zint

(* -------------------------------------------------------------------- *)
type 'info sfundef = Expr.stk_fun_extra * 'info func 
type 'info sprog   = 'info sfundef list * Expr.sprog_extra
